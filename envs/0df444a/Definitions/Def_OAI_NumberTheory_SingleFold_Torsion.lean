-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
-- name    : OAI_NumberTheory_SingleFold_Torsion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:20:32.572976+00:00
-- url     : https://prove2.me/theorems/2f81260c-fe5f-499b-92a8-c58dfe118795
-- title:
--   The integer height of points and nondegenerate points
-- statement:
--   Let $E$ be the elliptic curve $y^2=x^3-25x$ over $\mathbb{Q}$, with point at infinity $O$.
--
--   1. The integer height of a point is $H(O)=1$ and
--   $$
--   H(x,y)=\max(|\mathrm{num}(x)|,\mathrm{den}(x)) .
--   $$
--   2. A point is nondegenerate if it is an affine point $(x,y)$ with $y\ne0$, i.e. it is not one of the $2$-torsion points.
--
--   Doubling strictly increases $H$ on nondegenerate points of large height. This is used to identify the torsion subgroup.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Torsion.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Torsion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication

namespace OAI

namespace SingleFold.Torsion
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

abbrev E : WeierstrassCurve.Affine ℚ := ⟨0,0,0,-25,0⟩
instance : E.IsElliptic := by
  constructor
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

open DuplicationBound

noncomputable def H : E.Point → ℕ
  | .zero => 1
  | .some x _ _ => height x

def Nondegenerate (P : E.Point) : Prop :=
  ∃ x y h, y ≠ 0 ∧ P = some x y h

end SingleFold.Torsion

end OAI


