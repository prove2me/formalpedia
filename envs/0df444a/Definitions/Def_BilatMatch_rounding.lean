-- Prove2me | Definitions.Def_BilatMatch_rounding
-- name    : BilatMatch_rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:57.422754+00:00
-- url     : https://prove2.me/theorems/7610bb67-8c27-4eca-9487-47cce39ff225
-- title:
--   Projection, grid rounding and payment-preserving report extensions
-- statement:
--   This module collects the objects of the report-extension argument of App. B.2.
--
--   1. The prior of agent $u$, and the market with the same graph and feasible family but other priors (the **target market**).
--   2. The projection $\Pi(t)=\max\{L,\min\{U,t\}\}$ onto $[L,U]$; **downward rounding** of a type to the largest grid point not above it (buyers) and **upward rounding** to the smallest grid point not below it (sellers); the combined map that projects to $[L,U]$ and then rounds agents with finite domains, and the **projected market** whose priors are the image priors under $\Pi$.
--   3. $R$, the maximum number of edges in a feasible matching.
--   4. The joint law of the payment vector, and the common conclusion of Lemma B.4: an extension of a target mechanism to the original market is BIC and IIR on the whole line, has the same joint law of payments, and trades only on strictly positive-surplus edges whenever the target mechanism does.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), App. B.2, pp.32–34 (pdf pp.34–36): Lemma B.4, Lemma B.5, and R on p.32

import Mathlib
import Definitions.Def_BilatMatch_envelope

open MeasureTheory

namespace BilatMatch

/-!
# Projection, grid rounding and payment-preserving report extensions

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), App. B.2, pp.32–34 (pdf pp.34–36):
Lemma B.4 (report extension), Lemma B.5 (projected first best), and the maximum matching size `R`
(p.32).

**Formalization Note**
* `Market.law I u` is the prior of agent `u ∈ B ⊕ S`; `Market.withLaws I G` keeps the graph and the
  feasible family of `I` and replaces the priors by `G` (the "target market" of Lemma B.4 and the
  projected markets of Lemma B.5 share the original graph and family).
* `proj L U t = max L (min U t)` is the projection `Π` onto `[L, U]`.
* `floorTo D t` is the largest point of `D` not exceeding `t` (downward rounding of buyers) and
  `ceilTo D t` the smallest point of `D` not below `t` (upward rounding of sellers); on a finite grid
  containing `L` and `U` and for `t ∈ [L, U]` both are attained.
* `roundMap L U D u` first projects to `[L, U]` and then rounds agent `u` on its finite domain
  `D u` (downward for buyers, upward for sellers), or leaves the projected type unchanged when the
  domain is the full interval. On types already in `[L, U]` the projection is the identity, so the
  same map describes case (i) and case (ii) of Lemma B.4.
-/

variable {B S : Type*}

/-- The prior of agent `u`: `F_{B_i}` for a buyer `u = inl i`, `F_{S_j}` for a seller `u = inr j`. -/
def Market.law (I : Market B S) : B ⊕ S → Measure ℝ := Sum.elim I.buyerLaw I.sellerLaw

/-- The market with the graph and feasible family of `I` and the priors `G`. -/
def Market.withLaws (I : Market B S) (G : B ⊕ S → Measure ℝ) : Market B S :=
  { I with buyerLaw := fun i => G (Sum.inl i), sellerLaw := fun j => G (Sum.inr j) }

/-- The projection `Π` onto `[L, U]`. -/
def proj (L U t : ℝ) : ℝ := max L (min U t)

/-- Downward rounding onto `D`: the largest point of `D` not exceeding `t`. -/
noncomputable def floorTo (D : Set ℝ) (t : ℝ) : ℝ := sSup {d | d ∈ D ∧ d ≤ t}

/-- Upward rounding onto `D`: the smallest point of `D` not below `t`. -/
noncomputable def ceilTo (D : Set ℝ) (t : ℝ) : ℝ := sInf {d | d ∈ D ∧ t ≤ d}

open Classical in
/-- Projection to `[L, U]` followed by grid rounding: finite-domain buyers are rounded down and
finite-domain sellers up on their domains `D u`; full-interval agents keep the projected type. -/
noncomputable def roundMap (L U : ℝ) (D : B ⊕ S → Set ℝ) : B ⊕ S → ℝ → ℝ
  | Sum.inl i, t => if (D (Sum.inl i)).Finite then floorTo (D (Sum.inl i)) (proj L U t)
      else proj L U t
  | Sum.inr j, t => if (D (Sum.inr j)).Finite then ceilTo (D (Sum.inr j)) (proj L U t)
      else proj L U t

/-- The projected market `I` with every type projected onto `[L, U]` (Lemma B.5). -/
noncomputable def Market.projected (I : Market B S) (L U : ℝ) : Market B S :=
  I.withLaws fun u => (I.law u).map (proj L U)

/-- `R`, the maximum number of edges in a feasible matching (p.32). -/
noncomputable def maxMatchSize (I : Market B S) : ℕ := sSup (Set.ncard '' I.family)

namespace Mechanism

variable {I : Market B S}

/-- Every interim payment integrand (one agent's report replaced by any real) is integrable, so the
interim utilities entering BIC and IIR are not junk values (part of admissibility, footnote 1). -/
def InterimIntegrable (A : Mechanism I) : Prop :=
  (∀ i r, Integrable (fun θ => A.pay (updateBuyer θ i r) (Sum.inl i)) (typeMeasure I)) ∧
  (∀ j r, Integrable (fun θ => A.pay (updateSeller θ j r) (Sum.inr j)) (typeMeasure I))

/-- The joint law of the payment vector `(p_u)_{u ∈ B ⊕ S}` under truthful reporting. -/
noncomputable def payLaw (A : Mechanism I) : Measure (B ⊕ S → ℝ) :=
  (typeMeasure I).map fun θ u => A.pay θ u

end Mechanism

/-- The common conclusion of Lemma B.4 for an extension `A'` (on the original market `I`) of a target
mechanism `A` (on the target market `J` with report domains `D`): `A'` is BIC and IIR on the whole
line (with integrable interim payments), has the same joint law of payments as `A`, and trades only
on strictly positive-surplus edges whenever `A` does so on its report domains. -/
def IsPaymentPreservingExtension {I J : Market B S} (D : B ⊕ S → Set ℝ) (A : Mechanism J)
    (A' : Mechanism I) : Prop :=
  A'.InterimIntegrable ∧ A'.IsBICOn (wholeLine B S) ∧ A'.IsIIROn (wholeLine B S) ∧
    A'.payLaw = A.payLaw ∧ (A.PosSurplusOn (domainProfiles D) → A'.PosSurplusOn Set.univ)

end BilatMatch


