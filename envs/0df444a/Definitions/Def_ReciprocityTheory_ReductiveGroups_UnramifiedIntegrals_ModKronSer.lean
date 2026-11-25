-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:53.78448+00:00
-- url     : https://prove2.me/theorems/598c249e-a728-5d79-a281-ca9c37f4d69b
-- title:
--   Mod Kron Ser
-- statement:
--   Definitions and structural lemmas for Mod Kron Ser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModKronSer.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_xp_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_xp_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
def Cg (p : ℕ) (f g : PowerSeries ℂ) : Prop :=
  CoeffIn (Rm p) g ∧ ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ f = g + PowerSeries.C (1 - zetaC p) * w
theorem Cg.xp {p : ℕ} {f g : PowerSeries ℂ} (h1 : Cg p f g) (k : ℕ) : Cg p (xp k f) (xp k g) := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  exact ⟨hg.xp k, ReciprocityTheory.ChartRestriction.L1.xp k w, hw.xp k, by rw [xp_add, xp_C_mul]⟩
end ReciprocityTheory.ChartRestriction.L1


