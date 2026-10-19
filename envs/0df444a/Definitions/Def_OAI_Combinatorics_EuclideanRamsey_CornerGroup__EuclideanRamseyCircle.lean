-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyCircle
-- name    : OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:08:10.949248+00:00
-- url     : https://prove2.me/theorems/086e454c-0304-41c2-acc1-68dc8320ec75
-- title:
--   The corner of an element of a semigroup and its group structure
-- statement:
--   Let $S$ be a semigroup and $p\in S$. The *corner* of $p$ is the subset
--   $$C(p)=\{\,x\in S:\ px=x\ \text{ and }\ xp=x\,\}.$$
--
--   1. **Corner semigroup.** $C(p)$ is closed under the multiplication of $S$: if $x,y\in C(p)$ then $p(xy)=(px)y=xy$ and $(xy)p=x(yp)=xy$. With the inherited product, $C(p)$ is a semigroup, and the product of two elements of $C(p)$ is computed in $S$.
--   2. **Group structure on the corner.** Suppose that $p$ is idempotent, $pp=p$, and that for every $y\in S$ with $py=y$ and $yp=y$ there is $v\in S$ with $pv=v$, $vp=v$ and $vy=p$. Then $C(p)$ is a group whose identity element is $p$; the inverse of $y\in C(p)$ is such an element $v$, chosen once and for all.
--
--   For an idempotent $p$ the corner is $C(p)=pSp$, the largest subsemigroup having $p$ as a two-sided identity. In a nonempty compact Hausdorff semigroup in which every map $x\mapsto xy$ is continuous, such as the semigroup of ultrafilters on finite strings of points, one can find an idempotent $p$ satisfying the hypothesis of item 2. The corner $C(p)$ is then a group, and the universal property of free groups yields a homomorphism from the free group on the points into $C(p)$ that sends each generator $z$ to $p\,\delta_z\,p$, where $\delta_z$ is the principal ultrafilter of the one-letter string $z$. This is the bridge from paths in the free group to ultrafilters.
--
--   **Formalization Note** `Corner p` is the subtype `{x : S // p*x=x ∧ x*p=x}` with `Mul` and `Semigroup` instances (unnamed); `val_mul` is the simp lemma for the product. `Corner.group hp hi` is a definition, not a global instance, built with `Group.ofLeftAxioms` from associativity, the left identity law $px=x$ and the left inverse law $vy=p$; the inverse is selected by choice from the hypothesis `hi`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyCircle

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

@[instance_reducible] def group (hp : p*p=p)
    (hi : ∀ y : S, p*y=y → y*p=y → ∃ v : S,p*v=v ∧ v*p=v ∧ v*y=p) : Group (Corner p) := by
  letI : One (Corner p) := ⟨⟨p,hp,hp⟩⟩
  letI : Inv (Corner p) := ⟨fun y =>
    ⟨(hi y.val y.property.1 y.property.2).choose,
      (hi y.val y.property.1 y.property.2).choose_spec.1,
      (hi y.val y.property.1 y.property.2).choose_spec.2.1⟩⟩
  exact Group.ofLeftAxioms (fun x y z => mul_assoc x y z)
    (fun x => Subtype.ext x.property.1)
    (fun x => Subtype.ext (hi x.val x.property.1 x.property.2).choose_spec.2.2)

end Corner
end EuclideanRamsey

end

end OAI


