-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
-- name    : Formalism_LocalToGlobal_CharacterGerms_GeNatCast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:50.564215+00:00
-- url     : https://prove2.me/theorems/fdd5a972-9c5f-45d7-807a-6263b109ff44
-- title:
--   Ge Nat Cast
-- statement:
--   Definitions and structural lemmas for Ge Nat Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
structure VF (C : Type*) [Field C] where
  v : AddValuation C (WithTop ℝ)
  l : ℕ
  l_prime : l.Prime
  v_l : v (l : C) = 1
variable {C : Type*} [Field C]
namespace VF
variable (V : VF C)
def Ge (w : ℝ) (a : C) : Prop := (w : WithTop ℝ) ≤ V.v a
variable {V}
end VF
section Ops
variable {N : Type*}
def teich (l : ℕ) (c : C) (x : ℕ → N → C) : ℕ → N → C := fun i n => c ^ (l ^ i) * x i n
def Vpow (s : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => if i < s then 0 else x (i - s) n
def Fs (l : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => (l : C) * x (i + 1) n
def sumV (y : ℕ → ℕ → N → C) : ℕ → N → C := fun i n => ∑ s ∈ range (i + 1), y s (i - s) n
def const0 (h : N → C) : ℕ → N → C := fun i n => if i = 0 then h n else 0
end Ops
structure Cart (V : VF C) (d : ℕ) (I J : Type*) where

  ty : I ⊕ J → ZMod d
  Ty : AddSubgroup (ℕ → I ⊕ J → C)
  teich_mem : ∀ c, V.Ge 0 c → ∀ x ∈ Ty, teich V.l c x ∈ Ty
  V_mem : ∀ x ∈ Ty, Vpow 1 x ∈ Ty
  F_mem : ∀ x ∈ Ty, Fs V.l x ∈ Ty
  sumV_mem : ∀ y : ℕ → ℕ → I ⊕ J → C, (∀ s, y s ∈ Ty) → sumV y ∈ Ty

  t2 : ∀ x ∈ Ty, ∀ s, (∀ i < s, x i = 0) → ∀ n, V.Ge 0 (x s n)

  t3 : ∀ ζ : J → C, (∀ j, V.Ge 0 (ζ j)) → const0 (Sum.elim 0 ζ) ∈ Ty

  t4 : ∀ (a : ZMod d) (u : I → C), (∀ c, V.Ge 0 (u c)) → (∀ c, ty (Sum.inl c) ≠ a → u c = 0) →
    ∃ x ∈ Ty, x 0 = Sum.elim u 0 ∧ ∀ (i : ℕ) n, ty n ≠ a + i → x i n = 0
end
end Formalism.L2.FormalSeriesBounds


