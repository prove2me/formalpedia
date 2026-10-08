-- Prove2me | Definitions.Def_GenEmpLik_Coverage_AssumptionB
-- name    : GenEmpLik_Coverage_AssumptionB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:03:39.62817+00:00
-- url     : https://prove2.me/theorems/26621982-94b5-47c0-9d11-ced91d742b0c
-- title:
--   Assumption B — compact decisions and Lipschitz losses
-- statement:
--   Let $\mathcal X$ be a compact subset of a finite dimensional Euclidean decision space. For each observation $z$, the real loss $\ell(\cdot;z)$ is Lipschitz on $\mathcal X$ with a measurable nonnegative coefficient $M(z)$:
--
--   $$|\ell(x;z)-\ell(y;z)|\le M(z)\,\|x-y\|_2\quad(x,y\in\mathcal X).$$
--
--   This is the regularity assumption used to control the whole loss class. Its square integrability is imposed separately in the theorems.
--
--   **Formalization Note** The paper permits any norm on $\mathbb R^d$; the Euclidean norm is equivalent in finite dimension and preserves the square moment condition after rescaling $M$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 7, Assumption B

import Mathlib

namespace GenEmpLik.Coverage

/-- Assumption B, p. 7, with the Euclidean norm on the decision space. -/
def AssumptionB {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (M : Ξ → ℝ) : Prop :=
  IsCompact X ∧ Measurable M ∧ (∀ z, 0 ≤ M z) ∧
  ∀ z x, x ∈ X → ∀ y, y ∈ X → |ℓ x z - ℓ y z| ≤ M z * ‖x - y‖

end GenEmpLik.Coverage


