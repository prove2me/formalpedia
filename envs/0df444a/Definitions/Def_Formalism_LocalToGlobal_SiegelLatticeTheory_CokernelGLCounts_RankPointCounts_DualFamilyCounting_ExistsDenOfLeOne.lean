-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:55.155959+00:00
-- url     : https://prove2.me/theorems/bf8514dc-68f2-514c-91ad-a93b4c8df82a
-- title:
--   Exists Den Of Le One
-- statement:
--   Definitions and structural lemmas for Exists Den Of Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsDenOfLeOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsUnitDetOfIsometry
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_trF_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Pf.Lem3Mass
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
section Trace
variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)
def trF (y : E) : F :=
  Classical.choose (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))
theorem trF_spec (y : E) : algebraMap F E (trF σ hσ hfix y) = y + σ y :=
  Classical.choose_spec (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))
theorem trF_add (y z : E) : trF σ hσ hfix (y + z) = trF σ hσ hfix y + trF σ hσ hfix z := by
  apply (algebraMap F E).injective
  rw [map_add, trF_spec, trF_spec, trF_spec, map_add]
  abel
theorem trF_smul (c : F) (y : E) : trF σ hσ hfix (c • y) = c * trF σ hσ hfix y := by
  apply (algebraMap F E).injective
  rw [map_mul, trF_spec, trF_spec, Algebra.smul_def, map_mul, AlgHom.commutes, mul_add]
def trA : E ⊗[F] v.adicCompletion F →ₗ[F] v.adicCompletion F :=
  TensorProduct.lift (LinearMap.mk₂ F (fun (e : E) (r : v.adicCompletion F) => trF σ hσ hfix e • r)
    (fun e e' r => by rw [trF_add, add_smul])
    (fun c e r => by rw [trF_smul, mul_smul])
    (fun e r r' => by rw [smul_add])
    (fun c e r => by rw [smul_comm]))
end Trace
section D1
variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)
end D1
end Formalism.L2.SG.Pf.Lem3Mass


