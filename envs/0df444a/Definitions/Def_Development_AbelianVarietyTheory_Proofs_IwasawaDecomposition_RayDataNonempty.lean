-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:52.512372+00:00
-- url     : https://prove2.me/theorems/3ffaa0a8-2aae-4a04-8d3c-92fd378313dc
-- title:
--   Ray Data Nonempty
-- statement:
--   Definitions and structural lemmas for Ray Data Nonempty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
section General
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
def S : Submonoid (Ideal R) where
  carrier := {I | IsCoprime I m}
  mul_mem' := fun ha hb => IsCoprime.mul_left ha hb
  one_mem' := isCoprime_one_left
def Rel (I J : Ideal R) : Prop :=
  ∃ a b : R, a - 1 ∈ m ∧ b - 1 ∈ m ∧ Ideal.span {a} * I = Ideal.span {b} * J
variable {m}
theorem mul_sub_one_mem {a b : R} (ha : a - 1 ∈ m) (hb : b - 1 ∈ m) : a * b - 1 ∈ m := by
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  exact m.add_mem (m.mul_mem_left _ hb) ha
theorem Rel.refl (I : Ideal R) : Rel m I I := ⟨1, 1, by simp, by simp, rfl⟩
theorem Rel.symm {I J : Ideal R} (h : Rel m I J) : Rel m J I := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  exact ⟨b, a, hb, ha, h.symm⟩
theorem Rel.mul {I J I' J' : Ideal R} (h : Rel m I J) (h' : Rel m I' J') : Rel m (I * I') (J * J') := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨a * c, b * d, mul_sub_one_mem ha hc, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_mul_mul_comm, h, h', mul_mul_mul_comm]
theorem Rel.trans {I J L : Ideal R} (h : Rel m I J) (h' : Rel m J L) : Rel m I L := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨c * a, b * d, mul_sub_one_mem hc ha, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_assoc, h, mul_left_comm, h', mul_assoc]
variable (m) in

def con : Con (S m) where
  r I J := Rel m I.1 J.1
  iseqv := ⟨fun I => Rel.refl _, Rel.symm, Rel.trans⟩
  mul' := fun h h' => Rel.mul h h'
end General
end GlobalTheory.Mem.RayEx
end


