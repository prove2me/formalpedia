-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:48.472918+00:00
-- url     : https://prove2.me/theorems/0a7be5f8-bdc0-51b8-9bff-7a1486e23ed3
-- title:
--   Same B
-- statement:
--   Definitions and structural lemmas for Same B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/SameB.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
structure Match (U : PreU I D.toPre A G) (U' : UnifPre I D A G) : Prop where
  gen : U'.gen = U.gen
  LG : U'.LG = U.P.L
  cub : HEq U'.cubG U.P.c
  sym : HEq U'.symG U.P.sym
  gt : U'.gt = U.gt
  w : HEq U'.w U.w
def SameG {L : LB G.left} {k : ℕ} (σ : H0 L k)
    (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ G).left) (z : Z) (J), Good L z J →
    sval σ' r z J = sval σ (r ≫ (snd _ G).left) z J
def SameB {D : DegPre R} {k : ℕ} (f : ∀ α, D.SecB k α) (f' : ∀ α, SecBT D (𝟙_ _) k α) : Prop :=
  ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval (f' α) r z J = sval (f α) (r ≫ (snd _ D.P.A).left) z J
def PreU.SameK {D : DegPre R} (U : PreU I D A G) {k : ℕ}
    (σ : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) (FractionRing R)))) : Prop :=
  ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left),
    rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left → ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) (FractionRing R)) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
        sval σ y z JG
end GlobalTheory.UU
end


