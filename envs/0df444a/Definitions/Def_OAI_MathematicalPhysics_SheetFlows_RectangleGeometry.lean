-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
-- name    : OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:01:11.930732+00:00
-- url     : https://prove2.me/theorems/96f652d3-7361-4603-afe8-44a1a47d803e
-- title:
--   Rectangles in the coding square $[2,3]^2$ have half-widths at most $1/2$
-- statement:
--   A *rectangle* $R$ is given by rational corner vectors $\ell=(\ell_0,\ell_1)$ and $u=(u_0,u_1)$ with $\ell_j<u_j$ for $j=0,1$; its carrier is the closed box $\{y\in\mathbb{R}^2:\ \ell_j\le y_j\le u_j\ (j=0,1)\}$ and its half-widths are $w_j(R)=(u_j-\ell_j)/2$. The rectangle *lies in the coding square* if $2\le\ell_j$ and $u_j\le3$ for $j=0,1$, i.e. its carrier is contained in $[2,3]^2$.
--
--   This file records the elementary bound: if $R$ lies in the coding square, then for each $j\in\{0,1\}$
--   $$
--   w_j(R)\le\frac12 .
--   $$
--
--   The bound is used to check that the smooth bumps localized around such a rectangle, whose half-width is $w_j(R)$ plus a collar of width at most $1/10$, fit inside a single period interval $[0,10]$; this is what makes the vertical transport pulses attached to the rectangle have zero mean over a period cell.
--
--   **Formalization Note** The statement is `Rectangle.halfWidth_le_half`; the hypothesis `Rectangle.inCodingSquare` is formulated for the rational corners.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/RectangleGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/RectangleGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities

namespace OAI

/-! SheetFlows rectangle geometry. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

namespace Rectangle

theorem halfWidth_le_half (R : Rectangle) (h : R.inCodingSquare) (j : Fin 2) :
    R.halfWidth j ≤ 1 / 2 := by
  have hl : (2 : ℝ) ≤ R.lower j := by exact_mod_cast (h j).1
  have hu : (R.upper j : ℝ) ≤ 3 := by exact_mod_cast (h j).2
  dsimp [halfWidth]
  linarith

end Rectangle

end Solenoidal
end

end OAI


