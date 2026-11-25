-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyClassPullbackReductionPairs
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyClassPullbackReductionPairs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T15:20:10.17257+00:00
-- url     : https://prove2.me/theorems/277cf870-2847-47cc-981a-f5946ecaae4d
-- title:
--   Cohomology Class Pullback Reduction Pairs
-- statement:
--   Definitions and structural lemmas for Cohomology Class Pullback Reduction Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CohomologyClassPullbackReductionPairs.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHomStatement
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh
section PairNat
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}}
  {φ : X' ⟶ X} {χ : Y' ⟶ Y} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X'}
theorem pre_le_pre (e : ψ' ≫ φ = χ ≫ ψ) {V : Y.Opens} {U : X.Opens} (hp : V ≤ ψ ⁻¹ᵁ U) :
    χ ⁻¹ᵁ V ≤ ψ' ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ hp hx
variable [IsAffineHom φ] [IsAffineHom χ]
def prePairMap (e : ψ' ≫ φ = χ ≫ ψ) (p : Pair ψ) : Pair ψ' :=
  ⟨(preU χ p.1.1, preU φ p.1.2), pre_le_pre e p.2⟩
theorem prePairMap_mono (e : ψ' ≫ φ = χ ≫ ψ) : Monotone (prePairMap e) := fun _ _ h ↦
  show _ ∧ _ from ⟨preU_mono χ (Pair.le_fst h), preU_mono φ (Pair.le_snd h)⟩
def preFun (e : ψ' ≫ φ = χ ≫ ψ) : (Pair ψ)ᵒᵖ ⥤ (Pair ψ')ᵒᵖ := (prePairMap_mono e).functor.op
variable {s' : X' ⟶ Sp R'} {q' : Y' ⟶ Sp R'}
variable (s' q') in

def preCoefPair (e : ψ' ≫ φ = χ ≫ ψ) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) :
    CoefMap (RingHom.id R') (OPre φ s') (pairFst ψ ⋙ OPre χ q') where
  G := pairSnd ψ
  α p := secPull s' q' (prePairMap e p.unop)
  naturality a b := (pairPull w').naturality ((preFun e).map a) b
  smul p := semiHom_secPull w' (prePairMap e p.unop)
end PairNat
end GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
end GlobalTheory.AbCoh


