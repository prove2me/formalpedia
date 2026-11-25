-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:42:30.354483+00:00
-- url     : https://prove2.me/theorems/87ae5658-ec64-4ec2-98ff-4e10c34632bb
-- title:
--   Sec Cmp
-- statement:
--   Definitions and structural lemmas for Sec Cmp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SecCmp.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
namespace GlobalTheory.PsiRing
def FibNZ {Y S : Scheme.{0}} (p : Y ⟶ S) {M : LB Y} (s : LB.Sec M) : Prop :=
  ∀ y : S, ∃ z : Y, p z = y ∧ z ∈ nonzeroLocus s
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
def Mult (D : DegPre R) (th g : SecBT D (𝟙_ _) 1 0) (b : R) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval g r z J = cst (r ≫ (𝟙_ _ ⊗ D.P.A).hom) z b * sval th r z J
def Coef (D : DegPre R) (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (th : SecBT D (𝟙_ _) 1 0) (g : SecBT D (𝟙_ _) 1 χ) (b : R) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    sval g (lift (toUnit T) y).left z J = cst T.hom z b * ((val u (toUnit T).left z J * rigV D z J).val *
      sval th (lift (toUnit T) (y * cT D T χ)).left z J)
def SecCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α) : Prop :=
  ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
    r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' →
      sval (f (xe α)) r z J = (∏ i : Fin 4, gw v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ β))
        (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε 1 i).val * sval (f' α) r' z J'
abbrev RigCmp (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) : Prop :=
  PMaps v (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ)
abbrev PsiCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (gam : (TK V).left ⟶ (TK R).left) : Prop :=
  ∀ x, PMaps v (K := PUnit) (fun _ => D'.xK x) (fun _ => D.xK (xe x)) (fun _ => -1) (D'.psi x) (D.psi (xe x)) gam
end GlobalTheory.PsiRing
end


