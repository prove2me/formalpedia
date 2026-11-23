-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
-- name    : ReciprocityTheory_DualLattices_InvolutionPermApplyZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:28.743561+00:00
-- url     : https://prove2.me/theorems/4776eb26-e25d-4170-b3da-7c87f9e641c8
-- title:
--   Involution Perm Apply Zero
-- statement:
--   Definitions and structural lemmas for Involution Perm Apply Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InvolutionPermApplyZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Inv
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O}
def pi2 {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i)) :
    Equiv.Perm (Fin m) := by
  classical
  exact Equiv.ofBijective (fun k => if e k = 0 then k else π k) (by
    apply Finite.injective_iff_bijective.1
    intro a b hab
    simp only at hab
    by_cases ha : e a = 0 <;> by_cases hb : e b = 0
    · simpa [ha, hb] using hab
    · rw [if_pos ha, if_neg hb] at hab
      exfalso; apply hb
      have h := hσ b
      rw [← hab, ha] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    · rw [if_neg ha, if_pos hb] at hab
      exfalso; apply ha
      have h := hσ a
      rw [hab, hb] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    · rw [if_neg ha, if_neg hb] at hab
      exact π.injective hab)
end Inv
end ReciprocityTheory.PGsh.Up


