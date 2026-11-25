-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:07.213351+00:00
-- url     : https://prove2.me/theorems/5b984c71-a880-5f01-ad5e-d74af84d83f6
-- title:
--   Cocycle Pullback Iff Preimage Affine Hom
-- statement:
--   Definitions and structural lemmas for Cocycle Pullback Iff Preimage Affine Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocyclePullbackIffPreimageAffineHom.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbCoh
section Pre
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]
def preToPair : AffOp X ⥤ (Pair φ)ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ prePair φ U) fun _ _ h ↦
    (show prePair φ _ ≤ prePair φ _ from ⟨preU_mono φ h, h⟩)).op
def pairToPre (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPair φ s') (OPre φ s') where
  G := preToPair φ
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl
def preToPairRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPre φ s') (OPair φ s') where
  G := pairSnd φ
  α p := (Sec.res s' p.unop.2 : Sec s' (preU φ p.unop.1.2).1 →ₐ[R'] Sec s' p.unop.1.1.1).toRingHom
  naturality {p q} a b := by
    exact (Sec.res_res s' (U := (preU φ p.unop.1.2).1) _ _ b).symm.trans (Sec.res_res s' _ _ b)
  smul p r b := map_smul (Sec.res s' p.unop.2) r b
end Pre
section Lemmas
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {φ : X' ⟶ X} [IsAffineHom φ]
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}
def preIncl : pairSnd φ ⋙ preAff φ ⟶ pairFst φ where
  app p := (homOfLE p.unop.2).op
variable (h : φ ≫ s = s' ≫ spMap σ)
end Lemmas
end GlobalTheory.AbCoh


