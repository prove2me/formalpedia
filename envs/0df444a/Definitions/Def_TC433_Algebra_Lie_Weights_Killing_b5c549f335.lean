-- Prove2me | Definitions.Def_TC433_Algebra_Lie_Weights_Killing_b5c549f335
-- name    : TC433_Algebra_Lie_Weights_Killing_b5c549f335
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T15:19:52.666464+00:00
-- url     : https://prove2.me/theorems/c6c3450b-1ed3-4f6c-a7b1-9070347db3b1
-- title:
--   TauCeti: Algebra / Lie / Weights / Killing
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.Weights.Killing for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/Weights/Killing.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Killing pairings of root spaces

This file records consequences of the non-degeneracy of the Killing form for the root spaces of a
splitting Cartan subalgebra, and the vanishing of brackets inside the Cartan subalgebra itself.

## Main results

* `TauCeti.killingForm_ne_zero_of_mem_rootSpace`: nonzero vectors in opposite root spaces have
  nonzero Killing pairing.
* `TauCeti.rootSpace_neg_eq_bot_iff`: the roots are closed under negation, so a functional on the
  Cartan subalgebra is a root exactly when its negative is.
* `TauCeti.lie_cartan_cartan_eq_zero`: the Cartan subalgebra is abelian, so two of its elements
  have zero bracket in the ambient Lie algebra.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace LieAlgebra.IsKilling
open LieModule
variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
lemma toSubmodule_rootSpace_eq_span (α : Weight K H L) (hα : α.IsNonZero) (x : L)
    (hx₀ : x ≠ 0) (hx : x ∈ rootSpace H α) :
    (rootSpace H α).toSubmodule = K ∙ x := by
  have := (finrank_eq_one_iff_of_nonzero' ⟨x, hx⟩ (by simpa)).mp (finrank_rootSpace_eq_one α hα)
  ext y
  rw [Submodule.mem_span_singleton]
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨t, ht⟩ := this ⟨y, hy⟩
    use t
    aesop
  · rintro ⟨t, rfl⟩
    exact SMulMemClass.smul_mem t hx


lemma exists_mem_rootSpace_lie_ne_zero
    {α β : Weight K H L} (hα : α.IsNonZero) (h_ne_bot : rootSpace H (α + β) ≠ ⊥) :
    ∃ a ∈ rootSpace H α, ∃ b ∈ rootSpace H β, ⁅a, b⁆ ≠ 0 := by
  obtain ⟨_, e, f, ef_sl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := ef_sl2.h_eq_coroot hα he hf
  obtain ⟨x, hx, hx₀⟩ := (chainTop α β).exists_ne_zero
  refine ⟨e, he, (toEnd K L L f ^ chainTopCoeff α β) x, ?_, ?_⟩
  · have : chainTopCoeff α β • (-⇑α) + chainTop α β = β := by rw [coe_chainTop', smul_neg]; abel
    rw [← this]
    exact toEnd_pow_apply_mem hf hx (chainTopCoeff α β)
  · have hq₀ : 0 < chainTopCoeff α β := by
      have := (rootSpace_zsmul_add_ne_bot_iff α β hα 1).mp <| by rwa [one_smul]
      exact_mod_cast this.1
    obtain ⟨n, hn⟩ : ∃ n, chainTopCoeff α β = n + 1 := ⟨chainTopCoeff α β - 1, by lia⟩
    have h_prim : ef_sl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
      { ne_zero := hx₀
        lie_h := (chainLength_smul α β hx).symm
        lie_e := by
          have hmem := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
          rwa [genWeightSpace_add_chainTop α β hα] at hmem }
    rw [hn, h_prim.lie_e_pow_succ_toEnd_f n]
    have : chainTopCoeff α β ≤ chainLength α β := chainTopCoeff_le_chainLength α β
    refine smul_ne_zero (mul_ne_zero (by exact_mod_cast n.succ_ne_zero) ?_)
      (h_prim.pow_toEnd_f_ne_zero_of_eq_nat rfl (by lia))
    rw [sub_ne_zero, Nat.cast_injective.ne_iff]
    lia


@[expose] noncomputable instance : InvolutiveNeg H.root where
  neg i := ⟨-i, by aesop⟩
  neg_neg i := by aesop

@[simp] lemma val_neg_root {i : H.root} : (-i).val = -i.val := rfl

lemma rootSystem_reflectionPerm_self_eq_neg (i : H.root) :
    (rootSystem H).reflectionPerm i i = - i := by
  apply (rootSystem H).root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  simp

end LieAlgebra.IsKilling


namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- Nonzero vectors in opposite root spaces have nonzero Killing pairing. -/
theorem killingForm_ne_zero_of_mem_rootSpace {α : Weight K H L} (hα : α.IsNonZero) {e f : L}
    (he : e ∈ rootSpace H α) (he₀ : e ≠ 0) (hf : f ∈ rootSpace H (-α)) (hf₀ : f ≠ 0) :
    killingForm K L e f ≠ 0 := by
  intro hef
  have hspan := LieAlgebra.IsKilling.toSubmodule_rootSpace_eq_span (-α) hα.neg f hf₀ hf
  have heker := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H he fun y hy ↦ by
    have hspan' : (rootSpace H (-((α : Weight K H L) : H → K))).toSubmodule = K ∙ f := by
      simpa only [Weight.coe_neg] using hspan
    -- Passing from a Lie submodule to its underlying submodule is definitional.
    change y ∈ (rootSpace H (-((α : Weight K H L) : H → K))).toSubmodule at hy
    rw [hspan'] at hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [hef]
  rw [ker_killingForm_eq_bot] at heker
  exact he₀ heker

omit [CharZero K] in
/-- The roots of a Lie algebra with non-degenerate Killing form are closed under negation, so a
functional on the Cartan subalgebra is a root exactly when its negative is. -/
@[simp]
theorem rootSpace_neg_eq_bot_iff (χ : H → K) :
    rootSpace H (-χ) = ⊥ ↔ rootSpace H χ = ⊥ := by
  have key : ∀ ψ : H → K, rootSpace H ψ ≠ ⊥ → rootSpace H (-ψ) ≠ ⊥ := fun ψ hψ ↦
    (-(⟨ψ, hψ⟩ : Weight K H L)).genWeightSpace_ne_bot
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    exact key χ hne h
  · by_contra hne
    exact key (-χ) hne (by rwa [neg_neg])

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- **A splitting Cartan subalgebra is abelian**, so any two of its elements have zero bracket in
the ambient Lie algebra. -/
theorem lie_cartan_cartan_eq_zero (y z : H) : ⁅(y : L), (z : L)⁆ = 0 := by
  have h := trivial_lie_zero H H y z
  simpa only [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using congrArg Subtype.val h

end TauCeti


