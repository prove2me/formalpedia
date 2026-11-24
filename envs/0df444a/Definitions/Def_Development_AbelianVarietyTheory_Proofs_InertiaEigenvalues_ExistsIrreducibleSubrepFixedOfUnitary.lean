-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:11.182806+00:00
-- url     : https://prove2.me/theorems/0e17e93d-147c-4a2f-ac8f-abeaf808bda1
-- title:
--   Exists Irreducible Subrep Fixed Of Unitary
-- statement:
--   Definitions and structural lemmas for Exists Irreducible Subrep Fixed Of Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIrreducibleSubrepFixedOfUnitary.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
def orbSpan (ρ : Representation ℂ H W) (y : W) : Subrepresentation ρ :=
  ⟨Submodule.span ℂ (Set.range fun g => ρ g y), by
    intro g v hv
    have hle : (Submodule.span ℂ (Set.range fun g => ρ g y)).map (ρ g) ≤
        Submodule.span ℂ (Set.range fun g => ρ g y) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp [map_mul]⟩
    exact hle (Submodule.mem_map_of_mem hv)⟩
end GlobalTheory.UnitarySemisimple
namespace GlobalTheory.UnitarySemisimple
end GlobalTheory.UnitarySemisimple


