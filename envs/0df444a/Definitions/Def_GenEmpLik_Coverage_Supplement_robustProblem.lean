-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_robustProblem
-- name    : GenEmpLik_Coverage_Supplement_robustProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:10:25.236428+00:00
-- url     : https://prove2.me/theorems/1783cbc1-5e5e-4428-b696-9581aee39e8b
-- title:
--   Robust risk, minimax value and empirical solution set
-- statement:
--   For a decision region $X\subset\mathbb R^d$, real loss $\ell$ and sample $z_0,\ldots,z_{n-1}$ with $n\ge1$, let $\mathcal P_{n,\rho}$ be the published empirical $f$-divergence weight ball. Set
--   $$\widehat F_n(x)=\sup_{p\in\mathcal P_{n,\rho}}\sum_i p_i\ell(x;z_i),\qquad \widehat v_n=\inf_{x\in X}\widehat F_n(x),\qquad \widehat S_n=\operatorname*{argmin}_{x\in X}\widehat F_n(x).$$
--   These are the empirical robust objective, minimax value and solution set in (4a) and (23). The argmin is the published real-objective argmin, and the risk uses the published robust mean.
--
--   **Formalization Note** The infimum is taken in the extended reals. It is $+\infty$ on an empty domain and $-\infty$ on an objective unbounded below. Thus early samples with unbounded-below risk cannot acquire a spurious value zero. Theorems use nonempty $X$ and converge to a finite population optimum.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 2, (4a); 16, (23); 48

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Consistency_argminSet
import Definitions.Def_GenEmpLik_Consistency_inclDist

open MeasureTheory

namespace GenEmpLik.Coverage.Supplement

/-- Fhat_n(x) in Appendix E.2, p. 48: supremum before minimization. -/
noncomputable def robustRisk {d n : ℕ} {Ξ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (f : ℝ → EReal) (ρ : ℝ)
    (z : Fin n → Ξ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  GenEmpLik.Expansion.robustMean f ρ (fun i => ℓ x (z i))

/-- Minimax value (4a), with genuine extended-real infimum even on early samples
whose robust risk is unbounded below. This is not sup_P inf_x E_P loss. -/
noncomputable def robustValue {d n : ℕ} {Ξ : Type*}
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (f : ℝ → EReal) (ρ : ℝ)
    (z : Fin n → Ξ) : EReal :=
  ⨅ x : X, (robustRisk ℓ f ρ z x : EReal)

/-- The empirical robust solution set of (23), p. 16. -/
noncomputable def robustSolutions {d n : ℕ} {Ξ : Type*}
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (f : ℝ → EReal) (ρ : ℝ)
    (z : Fin n → Ξ) : Set (EuclideanSpace ℝ (Fin d)) :=
  GenEmpLik.Consistency.argminSet X (robustRisk ℓ f ρ z)

end GenEmpLik.Coverage.Supplement


