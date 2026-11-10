-- Prove2me | Definitions.Def_BilatMatch_envelope
-- name    : BilatMatch_envelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:57.30289+00:00
-- url     : https://prove2.me/theorems/f078cbcf-3b92-43d9-b700-357d3a1d2146
-- title:
--   Report domains and normalized envelope payments (1), (18), (19)
-- statement:
--   On a bounded interval report domain $[L,U]$ the normalized envelope payments for monotone interim trade probabilities $\bar x_B,\bar x_S$ are
--   $$p_B(v)=v\,\bar x_B(v)-\int_L^v\bar x_B(u)\,du,\qquad p_S(c)=-c\,\bar x_S(c)-\int_c^U\bar x_S(u)\,du,$$
--   and on a finite ordered domain the integrals are the sums $\sum_{t<\ell}(v_{t+1}-v_t)\bar x_B(v_t)$ and $\sum_{r>k}(c_r-c_{r-1})\bar x_S(c_r)$. They give zero utility to the lowest buyer and the highest seller report.
--
--   The module defines: the **auxiliary report domain** of an agent (a nonempty finite set or a bounded interval carrying the prior's mass); the profiles inside the domains; when a mechanism **uses normalized own-report envelope transfers** (at every domain profile each payment is the envelope payment of the agent's own interim trade probability at her own report); and when it **trades only on strictly positive-surplus edges** ($v_i>c_j$ on every traded edge).
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), eq. (1), p.6 (pdf p.8); eqs. (18)–(19), p.27 (pdf p.29); below eq. (5), p.9 (pdf p.11)

import Mathlib
import Definitions.Def_BilatMatch_Mechanism

open MeasureTheory

namespace BilatMatch

/-!
# Report domains of auxiliary markets and normalized envelope payments

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…): eq. (1), p.6 (pdf p.8); eqs. (18)–(19),
p.27 (pdf p.29); the discrete meanings stated below eq. (5), p.9 (pdf p.11); §3.1, p.8.

**Formalization Note**
* A report domain is a set `D ⊆ ℝ`. On a finite domain `d_1 < ⋯ < d_n` the information rents are
  the discrete sums of (18)–(19); on an infinite domain (a bounded interval `[L, U]`, `L = inf D`,
  `U = sup D`) they are the integrals of (1).
* `buyerRent D g v` is `∫_L^v g(u) du`, resp. `∑_{d ∈ D, d < v} (d⁺ − d) g(d)` with `d⁺` the next
  point of `D`; `sellerRent D h c` is `∫_c^U h(u) du`, resp. `∑_{d ∈ D, d > c} (d − d⁻) h(d)` with
  `d⁻` the previous point.
* The normalized envelope payments give zero utility to the lowest buyer report and the highest
  seller report: `p_B(v) = v x_B(v) − buyerRent`, `p_S(c) = −c x_S(c) − sellerRent` (payments to the
  mechanism).
-/

/-- The next point of `D` above `d`. -/
noncomputable def succIn (D : Set ℝ) (d : ℝ) : ℝ := sInf {y | y ∈ D ∧ d < y}

/-- The previous point of `D` below `d`. -/
noncomputable def predIn (D : Set ℝ) (d : ℝ) : ℝ := sSup {y | y ∈ D ∧ y < d}

open Classical in
/-- The buyer information rent at report `v` for interim trade probability `g` on the report
domain `D`: `∫_{inf D}^v g` (interval domain, eq. (1)) or `∑_{t<ℓ} (v_{t+1} − v_t) g(v_t)` (finite
domain, eq. (18)). -/
noncomputable def buyerRent (D : Set ℝ) (g : ℝ → ℝ) (v : ℝ) : ℝ :=
  if D.Finite then ∑ᶠ d ∈ {d | d ∈ D ∧ d < v}, (succIn D d - d) * g d
  else ∫ u in (sInf D)..v, g u

open Classical in
/-- The seller information rent at report `c` for interim trade probability `h` on the report
domain `D`: `∫_c^{sup D} h` (interval domain, eq. (1)) or `∑_{r>k} (c_r − c_{r−1}) h(c_r)` (finite
domain, eq. (19)). -/
noncomputable def sellerRent (D : Set ℝ) (h : ℝ → ℝ) (c : ℝ) : ℝ :=
  if D.Finite then ∑ᶠ d ∈ {d | d ∈ D ∧ c < d}, (d - predIn D d) * h d
  else ∫ u in c..(sSup D), h u

/-- The normalized envelope payment of a buyer, `p_B(v) = v x_B(v) − rent` (eqs. (1), (18)). -/
noncomputable def buyerEnvelopePay (D : Set ℝ) (g : ℝ → ℝ) (v : ℝ) : ℝ :=
  v * g v - buyerRent D g v

/-- The normalized envelope payment of a seller, `p_S(c) = −c x_S(c) − rent` (eqs. (1), (19)). -/
noncomputable def sellerEnvelopePay (D : Set ℝ) (h : ℝ → ℝ) (c : ℝ) : ℝ :=
  -(c * h c) - sellerRent D h c

/-- A report domain of an auxiliary market for an agent with prior `μ` (§3.1, p.8): a nonempty
finite ordered set or a bounded interval `[L, U]`, carrying all the prior's mass. -/
def IsAuxDomain (μ : Measure ℝ) (D : Set ℝ) : Prop :=
  ((D.Finite ∧ D.Nonempty) ∨ ∃ L U : ℝ, L ≤ U ∧ D = Set.Icc L U) ∧ μ Dᶜ = 0

variable {B S : Type*}

/-- The report profiles inside the report domains `D`. -/
def domainProfiles (D : B ⊕ S → Set ℝ) : Set (Profile B S) :=
  {θ | (∀ i, θ.1 i ∈ D (Sum.inl i)) ∧ ∀ j, θ.2 j ∈ D (Sum.inr j)}

/-- The mechanism uses normalized own-report envelope transfers on the report domains `D`: at every
profile in the domains, each agent's payment is the normalized envelope payment computed from its
own interim trade probability at its own report. -/
def Mechanism.IsNormalizedEnvelope {I : Market B S} (A : Mechanism I)
    (D : B ⊕ S → Set ℝ) : Prop :=
  ∀ θ ∈ domainProfiles D,
    (∀ i, A.pay θ (Sum.inl i) = buyerEnvelopePay (D (Sum.inl i)) (A.interimXB i) (θ.1 i)) ∧
    ∀ j, A.pay θ (Sum.inr j) = sellerEnvelopePay (D (Sum.inr j)) (A.interimXS j) (θ.2 j)

/-- The mechanism trades only on strictly positive-surplus edges at the profiles in `P`. -/
def Mechanism.PosSurplusOn {I : Market B S} (A : Mechanism I) (P : Set (Profile B S)) : Prop :=
  ∀ θ ∈ P, ∀ ω, ∀ e ∈ A.alloc θ ω, θ.2 e.2 < θ.1 e.1

end BilatMatch


