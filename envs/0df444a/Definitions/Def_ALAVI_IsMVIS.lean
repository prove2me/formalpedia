-- Prove2me | Definitions.Def_ALAVI_IsMVIS
-- name    : ALAVI_IsMVIS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:35.963498+00:00
-- url     : https://prove2.me/theorems/07307499-323e-4edf-9755-fb96cf8086b1
-- title:
--   Solutions of the mixed Minty variational inequality system (MVIS)
-- statement:
--   A pair $(u^\natural,p^\natural)\in U\times C^*$ with $J(u^\natural)<+\infty$ **solves (MVIS)** if
--
--   $$
--   \langle G(u),u-u^\natural\rangle+J(u)-J(u^\natural)+\langle p^\natural,\Theta(u)-\Theta(u^\natural)\rangle\ge0\quad\forall u\in U,\qquad
--   \langle\Theta(u^\natural),p-p^\natural\rangle\le0\quad\forall p\in C^*.
--   $$
--
--   The operator is evaluated at the test point $u$, not at $u^\natural$ as in (VIS). Assumption B (the primal-dual variational coherence condition, Definition 2) is $\mathbb S_{MVIS}\ne\emptyset$.
--
--   **Formalization Note.** As for (VIS): $C^*$ is the dual cone and the first inequality is required at $u\in U\cap\operatorname{dom}J$.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, (MVIS), displays (20)–(21), and Definition 2, p.7

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **(MVIS), displays (20)–(21)** (the mixed Minty system). `(u, p) ∈ U × C*` with
`⟨G(w), w - u⟩ + J(w) - J(u) + ⟨p, Θ(w) - Θ(u)⟩ ≥ 0` for all `w ∈ U` and
`⟨Θ(u), p' - p⟩ ≤ 0` for all `p' ∈ C*`. Note `G(w)`, at the test point, unlike (VIS).

Zhao, Zhu & Zhang, arXiv:2306.01214v1, (MVIS), (20)–(21), p.7.

Formalization Notes: as for `IsVIS`: `C*` is `ProperCone.innerDual`, `u ∈ dom J` is required and
(20) is required at `w ∈ U ∩ dom J` with real values. Assumption B / Definition 2
(`S_MVIS ≠ ∅`) is `∃ u p, IsMVIS U C G J Θ u p`. -/
def IsMVIS {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (u : E) (p : F) :
    Prop :=
  u ∈ U ∧ u ∈ GoldenRatioVI.Fixed.effDom J ∧ p ∈ ProperCone.innerDual (C : Set F) ∧
    (∀ w ∈ U, w ∈ GoldenRatioVI.Fixed.effDom J →
      0 ≤ inner ℝ (G w) (w - u) + (J w).toReal - (J u).toReal + inner ℝ p (Θ w - Θ u)) ∧
    ∀ p' ∈ ProperCone.innerDual (C : Set F), inner ℝ (Θ u) (p' - p) ≤ 0

end ALAVI


