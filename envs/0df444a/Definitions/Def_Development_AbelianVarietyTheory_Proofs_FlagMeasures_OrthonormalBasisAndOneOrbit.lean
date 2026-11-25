-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:36.639251+00:00
-- url     : https://prove2.me/theorems/36059b34-9616-5170-9205-f9cf7b625d29
-- title:
--   Orthonormal Basis And One Orbit
-- statement:
--   Definitions and structural lemmas for Orthonormal Basis And One Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrthonormalBasisAndOneOrbit.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
noncomputable def transfer (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (b b' : Fin n → Fin n → E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun x := ∑ i, hf L Hm x (b i) • b' i
  map_add' x y := by simp [hf_add_l, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [hf_smul_l, Finset.smul_sum, mul_smul]
end GlobalTheory.HL.SelfDual


