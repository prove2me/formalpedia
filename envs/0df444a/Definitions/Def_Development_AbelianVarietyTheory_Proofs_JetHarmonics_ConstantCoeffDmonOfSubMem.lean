-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:31:10.476895+00:00
-- url     : https://prove2.me/theorems/010da997-f0ba-4778-9596-3d7eed733aa6
-- title:
--   Constant Coeff Dmon Of Sub Mem
-- statement:
--   Definitions and structural lemmas for Constant Coeff Dmon Of Sub Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfSubMem.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.EigenCongruence
variable {R : Type} [CommRing R] {d : ℕ}
def coeffIdeal {σ : Type} (I : Ideal R) : Ideal (MvPowerSeries σ R) where
  carrier := {g | ∀ mo, coeff mo g ∈ I}
  add_mem' := by
    intro a b ha hb mo
    rw [map_add]
    exact I.add_mem (ha mo) (hb mo)
  zero_mem' := by
    intro mo
    rw [map_zero]
    exact I.zero_mem
  smul_mem' := by
    classical
    intro c x hx mo
    rw [smul_eq_mul, coeff_mul]
    exact I.sum_mem fun p _ => I.mul_mem_left _ (hx p.2)
end GlobalTheory.EigenCongruence
namespace GlobalTheory
end GlobalTheory


