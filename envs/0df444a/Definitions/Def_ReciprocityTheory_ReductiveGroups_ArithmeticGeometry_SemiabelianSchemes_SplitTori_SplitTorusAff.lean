-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:31.421243+00:00
-- url     : https://prove2.me/theorems/a37aab4c-c13b-441e-abf1-abf04c8936b3
-- title:
--   Split Torus Aff
-- statement:
--   Definitions and structural lemmas for Split Torus Aff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/SplitTori/SplitTorusAff.lean

import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
abbrev ZU : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
noncomputable abbrev torusRing (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] : CommRingCat.{u} :=
  CommRingCat.of (AddMonoidAlgebra R X)
noncomputable instance (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] :
    HopfAlgebra R (torusRing R X) :=
  inferInstanceAs (HopfAlgebra R (AddMonoidAlgebra R X))
noncomputable abbrev splitTorusAff (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] :
    Over (Spec R) :=
  (Spec (torusRing R X)).asOver (Spec R)
noncomputable example (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] : GrpObj (splitTorusAff R X) :=
  inferInstance
noncomputable def toZ (S : Scheme.{u}) : S ⟶ Spec ZU := specULiftZIsTerminal.from S
noncomputable def splitTorus (S : Scheme.{u}) (X : Type u) [AddCommGroup X] : Over S :=
  (Over.pullback (toZ S)).obj (splitTorusAff ZU X)
noncomputable instance (S : Scheme.{u}) (X : Type u) [AddCommGroup X] :
    GrpObj (splitTorus S X) :=
  Functor.grpObjObj
noncomputable abbrev Gm (S : Scheme.{u}) : Over S := splitTorus S (ULift.{u} ℤ)
variable {S : Scheme.{u}}
def characters (G : Over S) [GrpObj G] : Type u := {f : G ⟶ Gm S // IsMonHom f}
noncomputable def mulN (G : Over S) [GrpObj G] : ℕ → (G ⟶ G)
  | 0 => toUnit G ≫ η
  | n + 1 => lift (mulN G n) (𝟙 G) ≫ μ
noncomputable def torsion (G : Over S) [GrpObj G] (N : ℕ) : Over S :=
  pullback (mulN G N) (η : 𝟙_ (Over S) ⟶ G)
noncomputable def torsion.ι (G : Over S) [GrpObj G] (N : ℕ) : torsion G N ⟶ G :=
  pullback.fst _ _
end ReciprocityTheory.ChartRestriction.G.Semi


