-- Prove2me | Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ForwardDifference
-- name    : GallegoOzerADI_PositiveSetup_Supplement_ForwardDifference
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:40:37.528509+00:00
-- url     : https://prove2.me/theorems/863021aa-0731-4827-a7d4-76650f7512ab
-- title:
--   Unit forward difference $\nabla F(x,o)=F(x+1,o)-F(x,o)$ (Appendix B)
-- statement:
--   For a function $F(x,o)$ of the inventory position $x\in\mathbb R$ and the observed-demand vector $o$, the unit forward difference in the first variable is
--   $$
--   \nabla F(x,o)=F(x+1,o)-F(x,o),
--   $$
--   defined at every real $x$. Appendix B uses it to compare the slopes of the finite-horizon cost functions in Lemma 5.
--
--   **Formalization Note.** This is a difference with step $1$, not a derivative, and the inventory variable stays real.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1356, Appendix B, first line

import Mathlib

namespace GallegoOzerADI.PositiveSetup.Supplement

/-- The unit forward difference of Appendix B (p. 1356): `∇F(x, o) = F(x + 1, o) − F(x, o)`,
taken in the first (inventory) variable, for every real `x`. -/
def fwdDiff {M : ℕ} (F : ℝ → (Fin M → ℝ) → ℝ) (x : ℝ) (o : Fin M → ℝ) : ℝ :=
  F (x + 1) o - F x o

end GallegoOzerADI.PositiveSetup.Supplement


