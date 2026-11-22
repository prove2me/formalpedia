-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand
-- name    : Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:16.40724+00:00
-- url     : https://prove2.me/theorems/bd0b5678-b5ed-4d51-8d6b-0505f867c716
-- title:
--   Jp Subst Expand
-- statement:
--   Definitions and structural lemmas for Jp Subst Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
section Supp
variable {R σ Pl : Type} [CommRing R]
def SuppOn (π : σ → Pl) (v : Pl) : Subring (MvPowerSeries σ R) where
  carrier := {f | ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v}
  mul_mem' := by
    classical
    intro f g hf hg m hm x hx
    rw [MvPowerSeries.coeff_mul] at hm
    obtain ⟨ab, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [← hab] at hx
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    · exact hf _ (left_ne_zero_of_mul hne) x h
    · exact hg _ (right_ne_zero_of_mul hne) x h
  one_mem' := by
    classical
    intro m hm x hx
    rw [MvPowerSeries.coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp at hx
    · exact absurd rfl hm
  add_mem' := by
    intro f g hf hg m hm x hx
    rw [map_add] at hm
    by_cases h : MvPowerSeries.coeff m f = 0
    · rw [h, zero_add] at hm; exact hg m hm x hx
    · exact hf m h x hx
  zero_mem' := by
    intro m hm
    exact absurd (map_zero _) hm
  neg_mem' := by
    intro f hf m hm x hx
    rw [map_neg, neg_ne_zero] at hm
    exact hf m hm x hx
end Supp
def resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) : MvPowerSeries (ι v) R :=
  fun m => MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen


