-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
-- name    : GroundTheory_ProfiniteCohomology_Supernatural
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:50.848801+00:00
-- url     : https://prove2.me/theorems/9f8c548c-0413-4a52-8c97-9ffb5f6d8ca8
-- title:
--   Supernatural
-- statement:
--   Definitions and structural lemmas for Supernatural, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
def Supernatural : Type := Nat.Primes → ℕ∞
namespace Supernatural
def mk (f : Nat.Primes → ℕ∞) : Supernatural := f
def exp (a : Supernatural) (p : Nat.Primes) : ℕ∞ := a p
@[simp] theorem exp_mk (f : Nat.Primes → ℕ∞) (p : Nat.Primes) : (mk f).exp p = f p := rfl
@[ext] theorem ext {a b : Supernatural} (h : ∀ p, a.exp p = b.exp p) : a = b := funext h
noncomputable instance : CompleteLattice Supernatural := inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))
@[simp] theorem exp_iSup {ι : Sort*} (f : ι → Supernatural) (p : Nat.Primes) :
    (⨆ i, f i).exp p = ⨆ i, (f i).exp p :=
  iSup_apply (f := fun i => (f i : Nat.Primes → ℕ∞)) (a := p)
instance : One Supernatural := ⟨mk fun _ => 0⟩
instance : Mul Supernatural := ⟨fun a b => mk fun p => a.exp p + b.exp p⟩
@[simp] theorem exp_one (p : Nat.Primes) : (1 : Supernatural).exp p = 0 := rfl
@[simp] theorem exp_mul (a b : Supernatural) (p : Nat.Primes) :
    (a * b).exp p = a.exp p + b.exp p := rfl
instance : CommMonoid Supernatural where
  mul_assoc a b c := by ext p; simp [add_assoc]
  one_mul a := by ext p; simp
  mul_one a := by ext p; simp
  mul_comm a b := by ext p; simp [add_comm]
def ofNat (n : ℕ) : Supernatural := mk fun p => (n.factorization p : ℕ∞)
end Supernatural
end GroundTheory.ProfCoh


