-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:00.188513+00:00
-- url     : https://prove2.me/theorems/79db94e3-d69d-43a9-91ae-510b265fcb6c
-- title:
--   Card Fiber Mul Card Range
-- statement:
--   Definitions and structural lemmas for Card Fiber Mul Card Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
section Inv
variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)
def fixSub : AddSubgroup A where
  carrier := {w | w ∈ I ∧ σ w = w}
  zero_mem' := ⟨I.zero_mem, map_zero σ⟩
  add_mem' := fun ha hb => ⟨I.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩
  neg_mem' := fun ha => ⟨I.neg_mem ha.1, by rw [map_neg, ha.2]⟩
variable {σ I}
def trI (σ : A →+* A) (I : Ideal A) : I →+ A :=
  AddMonoidHom.mk' (fun w => (w : A) + σ w) (fun a b => by
    simp only [Submodule.coe_add, map_add]; abel)
end Inv
section Lift
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}
def linPart (σ : A →+* A) (I : Ideal A) {M : ℕ} (y : Fin M → A) : (Fin M → I) →+ A :=
  AddMonoidHom.mk' (fun δ => ∑ i, (σ (y i) * (δ i : A) + σ (δ i) * y i)) (fun a b => by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Submodule.coe_add, map_add]; ring)
end Lift
end Formalism.HermitianLattices.Ext.L3.NormLifting


