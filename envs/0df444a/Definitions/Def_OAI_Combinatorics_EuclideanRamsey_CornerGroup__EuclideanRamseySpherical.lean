-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:18:19.188677+00:00
-- url     : https://prove2.me/theorems/00c8743a-04e5-4553-986c-5eba924665d2
-- title:
--   The corner of a semigroup at an element
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $S$ be a semigroup and $p\in S$. The corner of $S$ at $p$ is the set
--   $$
--   S_p=\{x\in S:\ px=x=xp\}.
--   $$
--   It is closed under multiplication: if $px=x=xp$ and $py=y=yp$, then $p(xy)=xy=(xy)p$. With the restricted multiplication it is a semigroup. When $p$ is idempotent, $S_p=pSp$, and corners at idempotents is used to locate groups inside compact semigroups.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseySpherical

namespace OAI

universe uSemigroup

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter

open Set
namespace EuclideanRamsey

def Corner {S : Type uSemigroup} [Semigroup S] (p : S) := {x : S // p*x=x ∧ x*p=x}
namespace Corner
variable {S : Type uSemigroup} [Semigroup S] {p : S}
instance : Mul (Corner p) := ⟨fun x y => ⟨x.val*y.val, by
  constructor
  · rw [← mul_assoc,x.property.1]
  · rw [mul_assoc,y.property.2]⟩⟩
@[simp] lemma val_mul (x y : Corner p) : (x*y).val=x.val*y.val := rfl
instance : Semigroup (Corner p) where
  mul_assoc _x _y _z := Subtype.ext (mul_assoc _ _ _)

end Corner
end EuclideanRamsey

end

end OAI


