-- Prove2me | Definitions.Def_XuZeevi_Variance_Estimator
-- name    : XuZeevi_Variance_Estimator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:09:04.771608+00:00
-- url     : https://prove2.me/theorems/e967cb13-42e8-468f-9e24-f0512a59a235
-- title:
--   Auxiliary ERM and exact second-stage moment-penalized objective
-- statement:
--   Put $C_n=2\log_2 n+5$. An auxiliary empirical-risk minimizer $\widehat h_{ERM}(S')$ satisfies $P_{S'}\ell(\widehat h_{ERM};z)\le P_{S'}\ell(h;z)$ for every $h$. Its attained value is $\widehat L_0^*=P_{S'}\ell(\widehat h_{ERM};z)$; no infimum default or accuracy guarantee is used.
--
--   For any preliminary center $a$ the second-stage objective is
--   $$J_S(h;a,\delta)=P_n\ell(h;z)+\psi_S\left(16P_n[(\ell(h;z)-a)^2];\delta/C_n\right).$$
--   An estimator is any selected exact minimizer of $J_S$, for each primary sample and auxiliary input. The auxiliary input type is arbitrary; independence is imposed by the product probability law in the theorem, and the main theorem specializes it to $S'$. The two stages presume attainment as printed. No deviation bound, fixed-point existence, or first-stage accuracy is part of either minimizer predicate.
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Strategy 1 p. 11, Strategy 2 and Theorem 2 p. 12 (PDF pages equal printed pages)

import Definitions.Def_XuZeevi_Variance_Surrogate

open MeasureTheory NatureSLT.Consistency

namespace XuZeevi.Variance

noncomputable def confidenceDivisor (n : ℕ) : ℝ :=
  2 * (Real.log n / Real.log 2) + 5

/-- The first-stage optimal empirical value is evaluated at a chosen auxiliary ERM. -/
noncomputable def auxiliaryValue {H Z : Type*} {n : ℕ}
    (loss : H → Z → ℝ) (erm : (Fin n → Z) → H) (s' : Fin n → Z) : ℝ :=
  empiricalRisk loss s' (erm s')

/-- Exact attainment of the auxiliary empirical minimum, with no accuracy assumption. -/
def IsAuxiliaryERM {H Z : Type*} {n : ℕ}
    (loss : H → Z → ℝ) (erm : (Fin n → Z) → H) : Prop :=
  ∀ s' h, empiricalRisk loss s' (erm s') ≤ empiricalRisk loss s' h

/-- Strategy 2's exact objective, including 16 and δ/C_n. -/
noncomputable def momentObjective {H Z : Type*} {n : ℕ}
    (loss : H → Z → ℝ) (ψ : (Fin n → Z) → ℝ → ℝ → ℝ)
    (δ : ℝ) (s : Fin n → Z) (center : ℝ) (h : H) : ℝ :=
  empiricalRisk loss s h +
    ψ s (16 * empiricalMean s (fun z => (loss h z - center) ^ 2))
      (δ / confidenceDivisor n)

/-- Any exact second-stage minimizer, with arbitrary independent auxiliary input. -/
def IsMomentEstimator {H Z A : Type*} {n : ℕ}
    (loss : H → Z → ℝ) (ψ : (Fin n → Z) → ℝ → ℝ → ℝ)
    (δ : ℝ) (center : A → ℝ) (est : (Fin n → Z) × A → H) : Prop :=
  ∀ s a h, momentObjective loss ψ δ s (center a) (est (s, a)) ≤
    momentObjective loss ψ δ s (center a) h

end XuZeevi.Variance


