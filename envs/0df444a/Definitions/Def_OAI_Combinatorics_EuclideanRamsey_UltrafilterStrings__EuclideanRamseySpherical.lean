-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:16:10.270248+00:00
-- url     : https://prove2.me/theorems/1346f12f-e940-4078-b50c-7114af6b76b8
-- title:
--   Products of ultrafilters with principal ultrafilters
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $M$ be a monoid. Ultrafilters on $M$ carry the convolution product, $U\cdot V$, which makes them a semigroup. This module records how this product acts when one factor is principal:
--   $$
--   \langle x\rangle\cdot V=(x\cdot{-})_*V,\qquad U\cdot\langle y\rangle=({-}\cdot y)_*U,
--   $$
--   where $\langle x\rangle$ is the principal ultrafilter at $x$ and $f_*$ denotes the image ultrafilter under $f$. Such identities are used when ultrafilter limits of strings of points are combined coordinatewise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean by skeleton subtraction
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

namespace OAI

universe uModule uIndex uAlpha

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
namespace EuclideanRamsey
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

section Ultrafilters
variable {M : Type uModule} [Monoid M]
@[simp] lemma pure_mul_ultra (x : M) (V : Ultrafilter M) :
    (pure x : Ultrafilter M)*V = V.map (x*·) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]
@[simp] lemma mul_pure_ultra (U : Ultrafilter M) (y : M) :
    U*(pure y : Ultrafilter M) = U.map (·*y) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]

end Ultrafilters

namespace UltraColumn
variable {ι : Type uIndex} {M : Type uModule}
end UltraColumn
end EuclideanRamsey
namespace EuclideanRamsey
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

end EuclideanRamsey

end

end OAI


