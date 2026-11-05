-- Prove2me | Definitions.Def_StateIndepNRM_IsAdmissible
-- name    : StateIndepNRM_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:05.80961+00:00
-- url     : https://prove2.me/theorems/4065d647-670d-4823-9d16-1b160bac90ee
-- title:
--   Admissible pricing policies, expected revenue and the optimal value $\Pi_C$
-- statement:
--   A **pricing system** on a probability space $(\Omega,\mathcal F,P)$ consists of a filtration on $[0,T]$, a rate process $\lambda_t$ and sales processes $X_n$. It is **admissible** for an instance if
--
--   1. $\lambda$ is progressively measurable with $\lambda_t\in\Lambda_t$ for $t\in[0,T]$, and its paths are almost surely integrable on $[0,T]$;
--   2. each $X_n$ is adapted, and almost surely starts at $0$, is nondecreasing and right-continuous with jumps of size one;
--   3. $X_n(t)-\int_0^t\lambda_{n,s}\,ds$ is a martingale on $[0,T]$;
--   4. almost surely $\sum_n a_{m,n}X_n(T)\le b_m$ for every resource $m$;
--   5. $(t,\omega)\mapsto R_t(\lambda_t(\omega))$ is integrable on $[0,T]\times\Omega$.
--
--   Its **expected revenue** is $\mathbb E\int_0^TR_t(\lambda_t)\,dt$, and the **optimal value** is the supremum over admissible systems:
--
--   $$
--   \Pi_C=\sup\Big\{\mathbb E\int_0^TR_t(\lambda_t)\,dt\Big\}.
--   $$
--
--   Condition 3 is the meaning of "Poisson demand at rate $\lambda_t$, chosen without looking ahead": a filtration that sees future sales fails it, while a policy using past sales and outside randomization passes it.
--
--   **Formalization Note** The filtration is indexed by `Set.Icc 0 T`. Path integrability prevents a junk compensator, since a non-integrable Lean integral is $0$. Capacity bounds sales through the positive entry of each column, so a true martingale is no restriction relative to a local one. $\Pi_C$ is a real `sSup`: the set is nonempty (the null policy) and bounded above (`eq_1`). Sample spaces range over `Type`.
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, §3, p.6 (non-anticipatory policies, capacity, revenue rate, Π_C)

import Mathlib
import Definitions.Def_StateIndepNRM_IsPoissonDemand
import Definitions.Def_StateIndepNRM_Instance

open MeasureTheory ProbabilityTheory Set

namespace StateIndepNRM

/-- The data of a pricing policy on `[0, T]` run on a sample space: a filtration `𝓕`, a rate
process `lam` and a sales process `X` (SSRN 3831496, §3, p.6). -/
structure PricingSystem (T : ℝ) (N : ℕ) {Ω : Type} (mΩ : MeasurableSpace Ω) where
  𝓕 : Filtration (Icc (0 : ℝ) T) mΩ
  lam : ℝ → Ω → Fin N → ℝ
  X : Fin N → ℝ → Ω → ℕ

/-- Every jump of the path `x` on `(0, T]` has size at most one: `x t` exceeds `x s` by at most
one for some earlier `s` (Manchiraju–Dawande–Janakiraman, SSRN 3831496, §3, p.5: demand is
Poisson).

**Formalization Note.** For a nondecreasing `ℕ`-valued path this is `x t ≤ x (t−) + 1`, without
left limits. -/
def HasUnitJumps (T : ℝ) (x : ℝ → ℕ) : Prop :=
  ∀ t ∈ Ioc 0 T, ∃ s ∈ Ico 0 t, x t ≤ x s + 1

/-- A non-anticipatory pricing policy of `P_C` that respects capacity
(Manchiraju–Dawande–Janakiraman, SSRN 3831496, §3, p.6: "a non-anticipatory pricing policy that
specifies, in real-time, ... λ_t ∈ Λ_t, t ∈ [0, T]", "for every m, the total consumption of
resource m is less than or equal to b_m").

The rate `lam` is progressively measurable with `lam t ∈ Λ_t`, and each sales process `X n` is an
adapted counting process with unit jumps whose compensator is `∫₀ᵗ lam s n ds`, i.e.
`X n t - ∫₀ᵗ lam s n ds` is an `𝓕`-martingale on `[0, T]`.

**Formalization Note.** The compensator condition is what "Poisson with rate `λ_t`, chosen
without looking ahead" means: a filtration that sees future sales fails it, while any policy
depending on past sales and on outside randomization passes. The filtration is indexed by
`Set.Icc 0 T`, so nothing is required after `T`. Path integrability of `lam` rules out a junk
compensator (a non-integrable interval integral is `0`); it holds for any finite counting process.
Integrability of the revenue rate on `[0, T] × Ω` keeps `revenue` a true expectation (Lean's
integral of a non-integrable function is `0`). Capacity at `T` is enough, as sales are
nondecreasing. Capacity bounds sales through the positive entry of each column, so the martingale
property is no restriction relative to a local martingale. -/
structure IsAdmissible {M N : ℕ} (I : Instance M N) {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (sys : PricingSystem I.T N mΩ) : Prop where
  lam_prog : IsStronglyProgressive sys.𝓕 (fun (t : Icc (0 : ℝ) I.T) ω => sys.lam t ω)
  lam_mem : ∀ t ∈ Icc 0 I.T, ∀ ω, sys.lam t ω ∈ I.rateSet t
  lam_pathInt : ∀ n, ∀ᵐ ω ∂P, IntervalIntegrable (fun s => sys.lam s ω n) volume 0 I.T
  X_adapted : ∀ n, StronglyAdapted sys.𝓕 (fun (t : Icc (0 : ℝ) I.T) ω => sys.X n t ω)
  X_path : ∀ n, ∀ᵐ ω ∂P, IsCountingPath I.T (fun t => sys.X n t ω)
  X_unitJumps : ∀ n, ∀ᵐ ω ∂P, HasUnitJumps I.T (fun t => sys.X n t ω)
  compensator : ∀ n, Martingale
    (fun (t : Icc (0 : ℝ) I.T) ω => (sys.X n t ω : ℝ) - ∫ s in (0 : ℝ)..t, sys.lam s ω n) sys.𝓕 P
  capacity : ∀ᵐ ω ∂P, ∀ m, ∑ n, I.a m n * (sys.X n I.T ω : ℝ) ≤ I.b m
  revenue_integrable : Integrable (fun p : ℝ × Ω => I.revRate p.1 (sys.lam p.1 p.2))
    ((volume.restrict (Ioc 0 I.T)).prod P)

/-- The expected revenue `E ∫₀ᵀ R_t(λ_t) dt` of a policy (SSRN 3831496, §3, p.6: "the
instantaneous expected revenue rate at time t is given by the concave function R_t(λ_t)"). -/
noncomputable def revenue {M N : ℕ} (I : Instance M N) {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (sys : PricingSystem I.T N mΩ) : ℝ :=
  ∫ ω, (∫ t in (0 : ℝ)..I.T, I.revRate t (sys.lam t ω)) ∂P

/-- The set of expected revenues of admissible policies on all probability spaces. -/
def valueSet {M N : ℕ} (I : Instance M N) : Set ℝ :=
  {v | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (sys : PricingSystem I.T N mΩ), IsAdmissible I P sys ∧ v = revenue I P sys}

/-- The optimal objective value `Π_C` of `P_C` (SSRN 3831496, §3, p.6).

**Formalization Note.** A real `sSup`, which would be `0` on an empty or unbounded set. Neither
happens: the null policy is admissible (checked in the sanity file) and `eq_1` states that the set
is bounded above. Sample spaces range over `Type`. -/
noncomputable def optimalRevenue {M N : ℕ} (I : Instance M N) : ℝ :=
  sSup (valueSet I)

end StateIndepNRM


