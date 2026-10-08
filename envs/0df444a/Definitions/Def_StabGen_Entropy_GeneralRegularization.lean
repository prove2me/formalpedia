-- Prove2me | Definitions.Def_StabGen_Entropy_GeneralRegularization
-- name    : StabGen_Entropy_GeneralRegularization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:48:23.686256+00:00
-- url     : https://prove2.me/theorems/f8ab5742-3f7d-4c68-8151-553eff77cb74
-- title:
--   The Bregman divergence $d_F$ of Appendix C
-- statement:
--   This file fixes the Bregman divergence of Appendix C of Bousquet and Elisseeff, *Stability and Generalization*, used by Lemma 21.
--   For a differentiable $F:E\to\mathbb R$ on a real normed space $E$ and $g,g'\in E$,
--   $$d_F(g,g')=F(g)-F(g')-\langle g-g',\nabla F(g')\rangle .$$
--   Lemma 21 bounds the symmetrized Bregman divergence of the regularizer between a minimizer of (19) and a minimizer of (20); Definition 19 ($\sigma$-admissibility) and the objectives (19) and (20) are taken from the shared module `StabGen.RKHS.Regularization`, which this file imports.
--   **Formalization Note** The pairing $\langle g-g',\nabla F(g')\rangle$ is the Fréchet derivative of $F$ at $g'$ applied to $g-g'$; it is meaningful only where $F$ is differentiable (Lean's `fderiv` is $0$ elsewhere), and every statement using `bregmanDiv` assumes differentiability.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 512, Definition 19, Eqs. (19), (20); p. 525, Appendix C (Bregman divergence d_F)

import Mathlib
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_StabGen_RKHS_Regularization

namespace StabGen.Entropy

open FoundationsML.Stability

/-- The Bregman divergence of Appendix C, p. 525, for a differentiable `F` on a real normed space:
`d_F(g, g') = F(g) − F(g') − ⟨g − g', ∇F(g')⟩`, the pairing being the Fréchet derivative of `F`
at `g'` applied to `g − g'`. -/
noncomputable def bregmanDiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (g g' : E) : ℝ :=
  F g - F g' - fderiv ℝ F g' (g - g')

end StabGen.Entropy


