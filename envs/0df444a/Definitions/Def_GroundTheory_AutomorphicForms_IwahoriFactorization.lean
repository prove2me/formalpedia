-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
-- name    : GroundTheory_AutomorphicForms_IwahoriFactorization
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:56.845958+00:00
-- url     : https://prove2.me/theorems/f3b19b68-ef88-5208-9988-b262ed9c1c41
-- title:
--   Iwahori Factorization
-- statement:
--   Definitions and structural lemmas for Iwahori Factorization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
section Elimination
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
def elimKey (i : Fin n) : α ×ₗ Fin n := toLex (β i, i)
variable {β}
variable (β)
def elimCol (h : Matrix (Fin n) (Fin n) F) (a : Fin n) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i k => if k = a ∧ elimKey β a < elimKey β i then h i a / h a a else 0
variable {β}
theorem elimCol_apply (h : Matrix (Fin n) (Fin n) F) (a i k : Fin n) :
    elimCol β h a i k = if k = a ∧ elimKey β a < elimKey β i then h i a / h a a else 0 := rfl
theorem elimCol_mul_elimCol (h : Matrix (Fin n) (Fin n) F) (a : Fin n) :
    elimCol β h a * elimCol β h a = 0 := by
  ext i l
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = a
  · subst hk
    rw [elimCol_apply h k k l, if_neg (fun h => lt_irrefl _ h.2), mul_zero]
  · rw [elimCol_apply, if_neg (fun h => hk h.1), zero_mul]
variable (β)
def elimGL (h : Matrix (Fin n) (Fin n) F) (a : Fin n) : GL (Fin n) F where
  val := 1 - elimCol β h a
  inv := 1 + elimCol β h a
  val_inv := by
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, elimCol_mul_elimCol]
    abel
  inv_val := by
    rw [add_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, elimCol_mul_elimCol]
    abel
variable {β}
end Elimination
section Local
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
end Local
section LocalSymm
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
end LocalSymm
section Contraction
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
end Contraction
section Jacquet
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
end Jacquet
end Parabolic
end GroundTheory.Automorphic


