-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
-- name    : GroundTheory_GlobalFields_IdeleGroups_UnitBound
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:18.47709+00:00
-- url     : https://prove2.me/theorems/5f295c41-5578-4c33-80f1-bb59ea91db1b
-- title:
--   Unit Bound
-- statement:
--   Definitions and structural lemmas for Unit Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
instance InfinitePlace.Completion.properSpace (w : InfinitePlace K) : ProperSpace w.Completion := by
  let _ : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) 2
        rw [map_ofNat] at h
        rw [← h]
        norm_num⟩ }
  exact ProperSpace.of_locallyCompactSpace w.Completion
namespace IdeleGroup
def unitsToUnits : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
variable {K}
def logVector (x : IdeleGroup K) : logSpace K :=
  fun w ↦ (w.1.mult : ℝ) * Real.log ‖(x : 𝔸[K]).1 w.1‖
end IdeleGroup
end
end GroundTheory.Global


