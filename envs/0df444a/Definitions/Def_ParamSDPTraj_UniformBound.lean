-- Prove2me | Definitions.Def_ParamSDPTraj_UniformBound
-- name    : ParamSDPTraj_UniformBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:29.118437+00:00
-- url     : https://prove2.me/theorems/8533cef0-2601-4d46-8c29-8368d5b89b6e
-- title:
--   Uniform boundedness of $\mathcal A$ and of its pseudo-inverse
-- statement:
--   The operator $\mathcal A(t)$ and its pseudo-inverse $\mathcal A^*(t)(\mathcal A(t)\mathcal A^*(t))^{-1}$ have uniformly bounded norm: there is one constant $M$ such that for every $t\in T$,
--
--   $$\|\mathcal A(t)[X]\|\le M\|X\|_F\quad(X\in\mathbb S^n),\qquad \big\|\mathcal A^*(t)(\mathcal A(t)\mathcal A^*(t))^{-1}v\big\|_F\le M\|v\|\quad(v\in\mathbb R^m).$$
--
--   **Formalization Note** The operator norms are taken for the Frobenius and Euclidean norms. All norms on these spaces are equivalent, so the existence of $M$ does not depend on this choice.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Assumption 3.1, p.12

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ParamSDPTraj_opA
import Definitions.Def_ParamSDPTraj_pinv
import Definitions.Def_ParamSDPTraj_frob

namespace ParamSDPTraj

/-- **Uniform boundedness of 𝒜 and of its pseudo-inverse.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Assumption 3.1, p.12: "Furthermore the operator A(t) and its pseudo-inverse
A∗(t)(A(t)A∗(t))−1 have a uniformly bounded norm".

**Formalization Note** One constant `M` for all t ∈ T, bounding both operator norms for the
Frobenius norm on Sⁿ and the Euclidean norm `ApproxVI.euclNorm` on ℝᵐ. All norms on these finite-dimensional spaces
are equivalent, so the existence of `M` does not depend on this choice. -/
def UniformBound {n m : ℕ} (T : Set ℝ) (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ M : ℝ, ∀ t ∈ T,
    (∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsSymm → ApproxVI.euclNorm (opA A t X) ≤ M * frob X) ∧
    (∀ v : Fin m → ℝ, frob (pinv A t v) ≤ M * ApproxVI.euclNorm v)

end ParamSDPTraj


