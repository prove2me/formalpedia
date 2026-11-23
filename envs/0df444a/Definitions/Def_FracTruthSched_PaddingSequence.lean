-- Prove2me | Definitions.Def_FracTruthSched_PaddingSequence
-- name    : FracTruthSched_PaddingSequence
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:18:06.547928+00:00
-- url     : https://prove2.me/theorems/de9f3d90-950b-41a4-8cb5-58ef5b2baa18
-- title:
--   Padded mechanisms with the vanishing-error estimates of Appendix A.1
-- statement:
--   Fix $n\ge1$, $\ell$, a family $(R_m)$ of fractional mechanisms, and a real $\rho$. A `PaddingSequence` is the sequence of mechanisms produced by the padding construction of Appendix A.1. Its stage-$K$ mechanism is feasible, truthful, and symmetric under within-class task relabelling on graph inputs of $MC_\ell$, and it has the following properties, directly corresponding to Claims 4–7 of the paper:
--
--   1. **Load:** for every $\rho'$ for which the original family satisfies (3), every machine's core load at a graph input $t$ is at most $$\rho'\Bigl(C(t)+\frac1{K+1}\Bigr).$$
--   2. **Eligibility error:** if machine $i$ is not incident to core task $e$, then $$x^{(K)}_{ie}(t)\le \frac{\rho(C(t)+1/(K+1))}{(K+1)^2}.$$
--   3. **Unique-zero error:** at every rational graph input, eventually $x^{(K)}_{je}\le \rho(C(t)+1/(K+1))/((K+2)a)$ when $t_{ie}=0<t_{je}=a$.
--   4. **Zero-type irrelevance error:** at rational graph inputs differing only between two zero types on one edge, every other allocation changes by at most $4/(K+2)$, eventually in $K$.
--
--   The index shift $K_{\text{Lean}}+1=K_{\text{paper}}$ makes every denominator positive, including at stage zero. This interface separates the explicit finite construction from the diagonal-limit and real-rounding arguments.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Appendix A.1, pp.23–26, Claims 2–7 (index shifted by one).

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsClassSymmetric

set_option autoImplicit false

namespace FracTruthSched

/-- A graph input all of whose entries are rational (embedded in `ℝ`). -/
def IsRatGraphInput {n ℓ : ℕ} (t : Fin n → CoreTask n ℓ → ℝ) : Prop :=
  IsGraphInput t ∧ ∀ i e, ∃ q : ℚ, t i e = q

/-- The output of Appendix A.1: a sequence of feasible truthful symmetric mechanisms on the
core tasks, with the load bound and the vanishing-error estimates of Claims 4--7.  Index `K`
here corresponds to the paper's index `K+1`, so all denominators are nonzero at `K = 0`. -/
structure PaddingSequence {n : ℕ} [NeZero n] (R : (m : ℕ) → FracMech n (Fin m))
    (ρ : ℝ) (ℓ : ℕ) where
  /-- The padded mechanism at each stage. -/
  M : ℕ → FracMech n (CoreTask n ℓ)
  feasible : ∀ K, IsFeasibleOn IsGraphInput (M K)
  truthful : ∀ K, IsTruthfulOn IsGraphInput (M K)
  symmetric : ∀ K, IsClassSymmetric (M K)
  /-- Claim 4, for every ratio bound enjoyed by the original family. -/
  load : ∀ (ρ' : ℝ), (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ' * opt t) →
    ∀ (K : ℕ) (t : Fin n → CoreTask n ℓ → ℝ), IsGraphInput t → ∀ i,
      ∑ e, t i e * (M K).x t i e ≤ ρ' * (C t + 1 / ((K : ℝ) + 1))
  /-- Claim 5 (Eligibility), with error tending to zero. -/
  eligibility : ∀ (K : ℕ) (t : Fin n → CoreTask n ℓ → ℝ), IsGraphInput t →
    ∀ i e, ¬ incident i e →
      (M K).x t i e ≤ ρ * (C t + 1 / ((K : ℝ) + 1)) / (((K : ℝ) + 1) ^ 2)
  /-- Claim 6 (Unique zeros), eventually at each rational graph input. -/
  unique_zeros : ∀ (t : Fin n → CoreTask n ℓ → ℝ), IsRatGraphInput t →
    ∀ (e : CoreTask n ℓ) (i j : Fin n), e.isLeft → incident i e → incident j e → i ≠ j →
      t i e = 0 → 0 < t j e → ∃ K₀ : ℕ, ∀ K ≥ K₀,
        (M K).x t j e ≤ ρ * (C t + 1 / ((K : ℝ) + 1)) / (((K : ℝ) + 2) * t j e)
  /-- Claim 7 (Zero-type irrelevance), eventually at each pair of rational graph inputs. -/
  zero_type_irrelevance : ∀ (t t' : Fin n → CoreTask n ℓ → ℝ),
    IsRatGraphInput t → IsRatGraphInput t' → ∀ e : CoreTask n ℓ, e.isLeft →
    (∀ u f, f ≠ e → t u f = t' u f) →
    (∃ u, incident u e ∧ t u e = 0) → (∃ u, incident u e ∧ t' u e = 0) →
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ u f, f ≠ e →
      |(M K).x t u f - (M K).x t' u f| ≤ 4 / ((K : ℝ) + 2)

end FracTruthSched


