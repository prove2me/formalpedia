-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CentralProducts_UnitarisableHypotheses_IrrSub
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CentralProducts_UnitarisableHypotheses_IrrSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:35.077156+00:00
-- url     : https://prove2.me/theorems/21c3f972-0510-41ac-b3f5-589de106c29b
-- title:
--   Irr Sub
-- statement:
--   Definitions and structural lemmas for Irr Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PositivityTheory.RgUd.Prod.Asm
open GlobalTheory.PRep
section Gen
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
def genSub (M : Submodule ℂ V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x}
  apply_mem_toSubmodule := by
    intro g v hv
    have : Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x} ≤
        (Submodule.span ℂ {w | ∃ g : G, ∃ x ∈ M, w = ρ g x}).comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      intro w hw
      obtain ⟨h, x, hx, rfl⟩ := hw
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨g * h, x, hx, ?_⟩
      simp [map_mul]
    exact this hv
end Gen
end PositivityTheory.RgUd.Prod.Asm


