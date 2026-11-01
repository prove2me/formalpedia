-- Prove2me | Definitions.Def_ALAVI_IsVIS
-- name    : ALAVI_IsVIS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:07.738557+00:00
-- url     : https://prove2.me/theorems/afef7ee1-0513-47cd-9302-9af2fc48ab13
-- title:
--   Solutions of the Lagrangian variational inequality system (VIS)
-- statement:
--   A pair $(u^*,p^*)\in U\times C^*$ with $J(u^*)<+\infty$ **solves (VIS)** if
--
--   $$
--   \langle G(u^*),u-u^*\rangle+J(u)-J(u^*)+\langle p^*,\Theta(u)-\Theta(u^*)\rangle\ge0\quad\forall u\in U,\qquad
--   \langle\Theta(u^*),p-p^*\rangle\le0\quad\forall p\in C^*.
--   $$
--
--   Here $C^*=\{p:\langle x,p\rangle\ge0\ \forall x\in C\}$ is the dual cone. A solution is a KKT point of (VIP); $\mathbb S_{VIS}$ denotes the solution set.
--
--   **Formalization Note.** The paper never defines $C^*$ but uses it as the dual cone (p.7; Example A.4 gives $C^*=\mathbb R^m$ for $C=\{0\}$); it is Mathlib's `ProperCone.innerDual`. The first inequality is required at $u\in U\cap\operatorname{dom}J$ in real arithmetic.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, (VIS), displays (13)–(14), p.6

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **(VIS), displays (13)–(14).** `(u, p) ∈ U × C*` with
`⟨G(u), w - u⟩ + J(w) - J(u) + ⟨p, Θ(w) - Θ(u)⟩ ≥ 0` for all `w ∈ U` and
`⟨Θ(u), p' - p⟩ ≤ 0` for all `p' ∈ C*`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, (VIS), (13)–(14), p.6.

Formalization Notes: `C*` is the dual cone `{p | ⟨x, p⟩ ≥ 0 ∀ x ∈ C}`
(`ProperCone.innerDual`); the paper never defines `C*`, but uses it this way (p.7, and `C = {0}`
gives `C* = ℝᵐ`). `u ∈ dom J` is required and (13) is required at `w ∈ U ∩ dom J` with real
values `toReal`; at `w ∉ dom J` the printed inequality reads `+∞ ≥ 0`. -/
def IsVIS {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (u : E) (p : F) :
    Prop :=
  u ∈ U ∧ u ∈ GoldenRatioVI.Fixed.effDom J ∧ p ∈ ProperCone.innerDual (C : Set F) ∧
    (∀ w ∈ U, w ∈ GoldenRatioVI.Fixed.effDom J →
      0 ≤ inner ℝ (G u) (w - u) + (J w).toReal - (J u).toReal + inner ℝ p (Θ w - Θ u)) ∧
    ∀ p' ∈ ProperCone.innerDual (C : Set F), inner ℝ (Θ u) (p' - p) ≤ 0

end ALAVI


