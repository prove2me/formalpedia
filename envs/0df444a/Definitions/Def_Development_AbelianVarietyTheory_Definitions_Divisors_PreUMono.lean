-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:42:08.037893+00:00
-- url     : https://prove2.me/theorems/07c7b31e-1d9f-41c8-8969-5f61f7eccefd
-- title:
--   Pre UMono
-- statement:
--   Definitions and structural lemmas for Pre UMono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PreUMono.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
namespace GlobalTheory.AbCoh
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]
def preU (U : X.affineOpens) : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, U.2.preimage φ⟩
theorem preU_mono : Monotone (preU φ) := fun _ _ h _ hx ↦ h hx
def prePair (U : X.affineOpens) : Pair φ := ⟨(preU φ U, U), le_rfl⟩
def preAff : AffOp X ⥤ AffOp X' := (preU_mono φ).functor.op
abbrev OPre (s' : X' ⟶ Sp R') : AffOp X ⥤ CommAlgCat.{0} R' := preAff φ ⋙ OAff s'
def preRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OAff s') (OPre φ s') := CoefMap.restrict _ _
def preα (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (U : AffOp X) : (OAff s).obj U →+* (OPre φ s').obj U :=
  secPull s s' (prePair φ U.unop)
variable {φ} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}
def preCoef (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OAff s) (OPre φ s') where
  G := 𝟭 _
  α U := preα φ s s' U
  naturality {p q} a b := (pairPull h).naturality
    (homOfLE (show prePair φ q.unop ≤ prePair φ p.unop from
      ⟨preU_mono φ (leOfHom a.unop), leOfHom a.unop⟩)).op b
  smul U := semiHom_secPull h (prePair φ U.unop)
example (U : X.affineOpens) : preU (𝟙 X) U = U := rfl
end GlobalTheory.AbCoh


