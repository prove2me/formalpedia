-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_GenCoprime
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_GenCoprime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:39.840811+00:00
-- url     : https://prove2.me/theorems/08ca2492-667e-4894-b991-88e7a561fe07
-- title:
--   Gen Coprime
-- statement:
--   Definitions and structural lemmas for Gen Coprime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/GenCoprime.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
namespace PI.RayBoundIQW
variable {K0 : Type} [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))
abbrev PrimeTo := {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤}
noncomputable def cls (J : PrimeTo qq) : ClassGroup (𝓞 K0) :=
  ClassGroup.mk0 ⟨J.1, mem_nonZeroDivisors_of_ne_zero J.2.1⟩
noncomputable def base (c : ClassGroup (𝓞 K0)) : PrimeTo qq := by
  classical
  exact if h : ∃ I : PrimeTo qq, cls qq I = c then h.choose else ⟨⊤, top_ne_bot, top_sup_eq _⟩
theorem cls_base (J : PrimeTo qq) : cls qq (base qq (cls qq J)) = cls qq J := by
  classical
  have h : ∃ I : PrimeTo qq, cls qq I = cls qq J := ⟨J, rfl⟩
  unfold base
  rw [dif_pos h]
  exact h.choose_spec
theorem principal (J : PrimeTo qq) : ∃ m : 𝓞 K0,
    Ideal.span {m} = J.1 * (base qq (cls qq J)).1 ^ (classNumber K0 - 1) := by
  set B := base qq (cls qq J) with hB
  have hJ0 : J.1 ∈ (Ideal (𝓞 K0))⁰ := mem_nonZeroDivisors_of_ne_zero J.2.1
  have hB0 : B.1 ∈ (Ideal (𝓞 K0))⁰ := mem_nonZeroDivisors_of_ne_zero B.2.1
  have hP0 : J.1 * B.1 ^ (classNumber K0 - 1) ∈ (Ideal (𝓞 K0))⁰ :=
    ((⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1)).2
  have hone : ClassGroup.mk0 ⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ = 1 := by
    have e : (⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ : (Ideal (𝓞 K0))⁰) =
        (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1) := by
      apply Subtype.ext
      simp
    rw [e, map_mul, map_pow]
    have h1 : ClassGroup.mk0 (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J := cls_base qq J
    have h2 : ClassGroup.mk0 (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J := rfl
    rw [h1, h2, ← pow_succ']
    have hpos : 0 < classNumber K0 := classNumber_pos K0
    rw [Nat.sub_add_cancel hpos]
    exact pow_card_eq_one
  have hpr := (ClassGroup.mk0_eq_one_iff hP0).mp hone
  exact ⟨Submodule.IsPrincipal.generator _, Submodule.IsPrincipal.span_singleton_generator _⟩
noncomputable def gen (J : PrimeTo qq) : 𝓞 K0 := (principal qq J).choose
noncomputable def inv (J : PrimeTo qq) : ClassGroup (𝓞 K0) × (𝓞 K0 ⧸ qq) :=
  (cls qq J, Ideal.Quotient.mk qq (gen qq J))
end PI.RayBoundIQW


