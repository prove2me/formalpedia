-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:51:00.549643+00:00
-- url     : https://prove2.me/theorems/9cb4078d-5c0e-473d-97c2-6e500d79dc1c
-- title:
--   Exists Pow Eq Zero
-- statement:
--   Definitions and structural lemmas for Exists Pow Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsPowEqZero.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_orthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)
noncomputable section
namespace GlobalTheory.CompanionTheory.KWeightMajor
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
def shift (μ : Fin n → ℝ) (a b : Fin n) (k : ℕ) : Fin n → ℝ :=
  fun c => μ c + k * ((if c = a then 1 else 0) - (if c = b then 1 else 0))
end GlobalTheory.CompanionTheory.KWeightMajor


