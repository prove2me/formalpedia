-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
-- name    : GroundTheory_AutomorphicForms_ReductionFinite
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:08:39.571149+00:00
-- url     : https://prove2.me/theorems/ba80db91-413d-4790-a9c1-de909b5ae17d
-- title:
--   Reduction Finite
-- statement:
--   Definitions and structural lemmas for Reduction Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
namespace GroundTheory.Automorphic
noncomputable section
namespace Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
theorem mem_of_norm_le_one (v : HeightOneSpectrum (𝓞 K)) {x : v.adicCompletion K} (hx : ‖x‖ ≤ 1) :
    x ∈ v.adicCompletionIntegers K :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).2
    ((Valued.toNormedField.norm_le_one_iff).1 hx)
def mkIdele (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) : IdeleGroup K :=
  (prodRestrictedEquiv K).symm
    (MulEquiv.piUnits.symm fun w => Units.mk0 (a w) (ha w),
     ⟨fun v => Units.mk0 (b v) (hb v), by
        filter_upwards [hb1] with v hv
        rw [SetLike.mem_coe, Submonoid.mem_units_iff]
        refine ⟨mem_of_norm_le_one v hv.le, mem_of_norm_le_one v ?_⟩
        rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hv, inv_one]⟩)
end Reduction
end
end GroundTheory.Automorphic


