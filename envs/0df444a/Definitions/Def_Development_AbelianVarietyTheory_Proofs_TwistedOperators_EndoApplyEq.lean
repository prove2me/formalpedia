-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EndoApplyEq
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_EndoApplyEq
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-27T05:53:50.571669+00:00
-- url     : https://prove2.me/theorems/904461cc-c808-5e3f-bdf7-85abc111b802
-- title:
--   Endo Apply Eq
-- statement:
--   Definitions and structural lemmas for Endo Apply Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EndoApplyEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
namespace GlobalTheory.OrthogonalProjectionOnto
open Module
section
variable {R : Type u_1} [Ring R] {ι : Type u_2} [Fintype ι] [DecidableEq ι]
  (M : ι → Type u_3) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
theorem endo_apply_eq (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0)
    (g : (Π i, M i) →ₗ[R] (Π i, M i)) (x : Π i, M i) (i : ι) :
    g x i = g (Pi.single i (x i)) i := by
  have hx : x = ∑ j, Pi.single j (x j) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    have h0 := h j i hji ((LinearMap.proj i).comp (g.comp (LinearMap.single R M j)))
    exact LinearMap.congr_fun h0 (x j)
  · intro hi
    exact absurd (Finset.mem_univ i) hi
def projOnto (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0) (i₀ : ι) :
    End (End R (Π i, M i)) (Π i, M i) where
  toFun x := fun i => if i = i₀ then x i else 0
  map_add' x y := by
    funext i
    split_ifs <;> simp_all
  map_smul' g x := by
    funext i
    simp only [RingHom.id_apply, Module.End.smul_def]
    rw [endo_apply_eq M h g x i, endo_apply_eq M h g (fun i => if i = i₀ then x i else 0) i]
    split_ifs with hi
    · rfl
    · simp
end
end GlobalTheory.OrthogonalProjectionOnto


