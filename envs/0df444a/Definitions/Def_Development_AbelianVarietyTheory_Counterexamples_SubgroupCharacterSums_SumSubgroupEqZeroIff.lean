-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
-- name    : Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:50.1467+00:00
-- url     : https://prove2.me/theorems/716afce0-5a86-4d5e-8a7a-f8ff720bf4ac
-- title:
--   Sum Subgroup Eq Zero Iff
-- statement:
--   Definitions and structural lemmas for Sum Subgroup Eq Zero Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
namespace GlobalTheory.CuspCharCheck
section Group
variable {G : Type} [Group G]
end Group
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
theorem mem_unipBlock_iff (d a : ℕ) (u : GL (Fin d) F) :
    u ∈ (unipBlock d a : Set (GL (Fin d) F)) ↔
      ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → ((u : Matrix (Fin d) (Fin d) F) - 1) i j = 0 := by
  unfold unipBlock
  refine forall₂_congr fun i j => ?_
  rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply]
  tauto
omit [Fintype F] [DecidableEq F] in
theorem block_mul_eq_zero {d a : ℕ} {X Y : Matrix (Fin d) (Fin d) F}
    (hX : ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → X i j = 0)
    (hY : ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → Y i j = 0) : X * Y = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k.val < a
  · rw [hX i k (by omega), zero_mul]
  · rw [hY k j (by omega), mul_zero]
def unipSubgroup (d a : ℕ) : Subgroup (GL (Fin d) F) where
  carrier := unipBlock d a
  one_mem' := (mem_unipBlock_iff d a 1).2 fun i j _ => by simp
  mul_mem' := by
    intro u v hu hv
    rw [mem_unipBlock_iff] at hu hv ⊢
    intro i j hij
    have h0 := block_mul_eq_zero hu hv
    have : ((u * v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) - 1 =
        ((u : Matrix (Fin d) (Fin d) F) - 1) + ((v : Matrix (Fin d) (Fin d) F) - 1) := by
      rw [Units.val_mul, ← sub_eq_zero, ← h0]; noncomm_ring
    rw [this, Matrix.add_apply, hu i j hij, hv i j hij, add_zero]
  inv_mem' := by
    intro u hu
    rw [mem_unipBlock_iff] at hu ⊢
    intro i j hij
    have h0 := block_mul_eq_zero hu hu
    have h1 : (u : Matrix (Fin d) (Fin d) F) * (1 - ((u : Matrix (Fin d) (Fin d) F) - 1)) = 1 := by
      rw [← sub_eq_zero, ← neg_eq_zero, ← h0]; noncomm_ring
    have h2 : ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 - ((u : Matrix (Fin d) (Fin d) F) - 1) :=
      Units.inv_eq_of_mul_eq_one_right h1
    rw [h2, sub_sub_cancel_left, Matrix.neg_apply, hu i j hij, neg_zero]
def permOfGL (d : ℕ) : GL (Fin d) F →* Equiv.Perm (Fin d → F) :=
  MonoidHom.toHomPerm
    { toFun := fun (g : GL (Fin d) F) => (fun v => (g : Matrix (Fin d) (Fin d) F).mulVec v : Function.End (Fin d → F))
      map_one' := funext fun v => Matrix.one_mulVec v
      map_mul' := fun g h => funext fun v => (Matrix.mulVec_mulVec v _ _).symm }
def signChar : GL (Fin 2) (ZMod 2) →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (Equiv.Perm.sign.comp (permOfGL 2))
def transv : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩
end GlobalTheory.CuspCharCheck


