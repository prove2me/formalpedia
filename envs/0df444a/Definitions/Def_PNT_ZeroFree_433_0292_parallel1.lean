-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0292_parallel1
-- name    : PNT_ZeroFree_433_0292_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:15:01.425022+00:00
-- url     : https://prove2.me/theorems/a033bc93-4438-4e03-92a7-9ce35efedfbb
-- title:
--   Zero-free region foundations: Moments.Correlation, Moments.PrimePower, Moments.CRT [0292_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Moments.Correlation
--   - OAI.NumberTheory.DirichletL.Moments.PrimePower
--   - OAI.NumberTheory.DirichletL.Moments.CRT
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L15-L287
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L14-L127
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L12-L118

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/Correlation.lean#L15-L287
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L14-L127
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L12-L118
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Moments.Correlation
section
namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

def fourierSum (ψ : AddChar R ℂ) (place : X → R) (f : X → ℂ) (h : R) : ℂ :=
  ∑ x, f x * ψ (h * place x)

def fullCorrelation (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) : ℂ :=
  ∑ x, ∑ y, if left x - right y = j then f x * star (g y) else 0

omit [Fintype R] in
theorem fullCorrelation_swap (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) :
    fullCorrelation left right f g j = star (fullCorrelation right left g f (-j)) := by
  classical
  simp only [fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have heq : left x - right y = j ↔ right y - left x = -j := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : left x - right y = j
  · simp [h, heq.mp h, star_mul]
  · simp [h, not_congr heq |>.mp h]

theorem fullCorrelation_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (j : R) :
    (∑ h : R, fourierSum ψ left f h * star (fourierSum ψ right g h) * ψ (-(h * j))) =
      (Fintype.card R : ℂ) * fullCorrelation left right f g j := by
  classical
  simp only [fourierSum, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hphase (h : R) (x : X) (y : Y) :
      (f x * ψ (h * left x) * (star (ψ (h * right y)) * star (g y))) * ψ (-(h * j)) =
        (f x * star (g y)) * ψ (h * (left x - right y - j)) := by
    have hs : star (ψ (h * right y)) = ψ (-(h * right y)) := by
      simpa only [← starRingEnd_apply] using (AddChar.map_neg_eq_conj ψ (h * right y)).symm
    rw [hs]
    calc
      _ = (f x * star (g y)) *
          (ψ (h * left x) * ψ (-(h * right y)) * ψ (-(h * j))) := by ring
      _ = _ := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
  simp_rw [hphase, ← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
  simp only [fullCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : left x - right y = j
  · simp [hxy, mul_comm]
  · simp [sub_ne_zero.mpr hxy, hxy]

section FiniteField
variable {F : Type*} [Field F] [Fintype F]

def shiftCorrelation (χ : MulChar F ℂ) (k : F) : ℂ :=
  ∑ x : F, χ x * star (χ (x - k))

lemma character_mul_star (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * star (χ a) = 1 := by
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  exact mul_inv_cancel₀ (χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr ha))

theorem shiftCorrelation_scale (χ : MulChar F ℂ) {k : F} (hk : k ≠ 0) :
    shiftCorrelation χ k = shiftCorrelation χ 1 := by
  unfold shiftCorrelation
  rw [← (Equiv.mulLeft₀ k hk).sum_comp]
  swap
  · simp
  apply Finset.sum_congr rfl
  intro x _
  simp only [Equiv.mulLeft₀_apply]
  rw [show k * x - k = k * (x - 1) by ring, map_mul, map_mul, star_mul]
  calc
    _ = (χ k * star (χ k)) * (χ x * star (χ (x - 1))) := by ring
    _ = _ := by rw [character_mul_star χ hk, one_mul]

theorem shiftCorrelation_one (χ : MulChar F ℂ) :
    shiftCorrelation χ 1 = χ⁻¹ (-1) * jacobiSum χ χ⁻¹ := by
  simp only [shiftCorrelation, jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [MulChar.star_apply', show x - 1 = (-1) * (1 - x) by ring, map_mul]
  ring

theorem shiftCorrelation_zero (χ : MulChar F ℂ) :
    shiftCorrelation χ 0 = (Fintype.card F : ℂ) - 1 := by
  classical
  simp only [shiftCorrelation, sub_zero, MulChar.star_apply', ← MulChar.mul_apply,
    mul_inv_cancel]
  rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
  simp

theorem shiftCorrelation_nonprincipal (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {k : F} (hk : k ≠ 0) : shiftCorrelation χ k = -1 := by
  rw [shiftCorrelation_scale χ hk, shiftCorrelation_one, jacobiSum_nontrivial_inv hχ,
    mul_neg, ← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))]

theorem shiftCorrelation_principal {k : F} (hk : k ≠ 0) :
    shiftCorrelation (1 : MulChar F ℂ) k = (Fintype.card F : ℂ) - 2 := by
  rw [shiftCorrelation_scale _ hk, shiftCorrelation_one, inv_one,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)), one_mul, jacobiSum_one_one]

def localCorrelation (χ : MulChar F ℂ) (n₁ n₂ k : F) : ℂ :=
  fullCorrelation (fun x : F => n₂ * x) (fun y : F => n₁ * y) χ χ k

theorem localCorrelation_eq_shift (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) * shiftCorrelation χ (k / n₁) := by
  classical
  have hsolve (x y : F) : n₂ * x - n₁ * y = k ↔ y = (n₂ * x - k) / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  unfold localCorrelation fullCorrelation
  simp only [hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Equiv.mulLeft₀ (n₁ / n₂) (div_ne_zero h₁ h₂)).sum_comp]
  swap
  · simp
  simp only [Equiv.mulLeft₀_apply, shiftCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  have heq : (n₂ * (n₁ / n₂ * x) - k) / n₁ = x - k / n₁ := by
    field_simp
  rw [heq, mul_assoc]

theorem localCorrelation_units (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) *
      (if k = 0 then (Fintype.card F : ℂ) - 1
       else if χ = 1 then (Fintype.card F : ℂ) - 2 else -1) := by
  rw [localCorrelation_eq_shift χ h₁ h₂]
  by_cases hk : k = 0
  · simp [hk, shiftCorrelation_zero]
  · by_cases hχ : χ = 1
    · simp [hk, hχ, shiftCorrelation_principal (div_ne_zero hk h₁)]
    · simp [hk, hχ, shiftCorrelation_nonprincipal χ hχ (div_ne_zero hk h₁)]

lemma character_sum (χ : MulChar F ℂ) :
    (∑ x : F, χ x) = if χ = 1 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
    simp
  · simp [hχ, MulChar.sum_eq_zero_of_ne_one hχ]

theorem localCorrelation_first_zero (χ : MulChar F ℂ) {n₂ : F} (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ 0 n₂ k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (x : F) : n₂ * x = k ↔ x = k / n₂ := by
    rw [eq_div_iff h₂, mul_comm]
  have hsum : localCorrelation χ 0 n₂ k = χ (k / n₂) * star (∑ y : F, χ y) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, sub_zero, hsolve]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum, ← star_sum]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero hk h₂))]
      simp [hk]
  · simp [hχ]

theorem localCorrelation_second_zero (χ : MulChar F ℂ) {n₁ : F} (h₁ : n₁ ≠ 0) (k : F) :
    localCorrelation χ n₁ 0 k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (y : F) : -(n₁ * y) = k ↔ y = -k / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  have hsum : localCorrelation χ n₁ 0 k = (∑ x : F, χ x) * star (χ (-k / n₁)) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, zero_sub, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_mul]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hk) h₁))]
      simp [hk]
  · simp [hχ]

end FiniteField

variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

def reductionMultiplicity (π : A →+* B) : ℕ :=
  (Finset.univ.filter fun x : A => π x = 0).card

theorem sum_reduction (π : A →+* B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ x : A, f (π x)) = (reductionMultiplicity π : ℂ) * ∑ y : B, f y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => f (π x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x : A with π x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      have hc := AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hc]
      rfl

theorem reductionMultiplicity_mul_card (π : A →+* B) (hπ : Function.Surjective π) :
    reductionMultiplicity π * Fintype.card B = Fintype.card A := by
  have h := sum_reduction π hπ (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

theorem reductionMultiplicity_eq_pow (π : A →+* B) (hπ : Function.Surjective π)
    {P c : ℕ} (hP : 0 < P) (hc : 1 ≤ c)
    (hA : Fintype.card A = P ^ c) (hB : Fintype.card B = P) :
    reductionMultiplicity π = P ^ (c - 1) := by
  apply Nat.eq_of_mul_eq_mul_right hP
  rw [← hB, reductionMultiplicity_mul_card π hπ, hA, hB, ← pow_succ,
    Nat.sub_add_cancel hc]

theorem fullCorrelation_unit_right (u : Aˣ) (v k : A) (f g : A → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => (u : A) * y) f g k =
      ∑ x : A, f x * star (g ((↑u⁻¹ : A) * (v * x - k))) := by
  classical
  have hsolve (x y : A) : v * x - (u : A) * y = k ↔
      y = (↑u⁻¹ : A) * (v * x - k) := by
    constructor
    · intro h
      have heq : v * x - k = (u : A) * y := by linear_combination h
      rw [heq, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
      ring
  simp only [fullCorrelation, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_reduction_unit_right (π : A →+* B)
    (hπ : Function.Surjective π) (u : Aˣ) (v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => v * x) (fun y : A => (u : A) * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_unit_right]
  have hright := fullCorrelation_unit_right (Units.map π.toMonoidHom u) (π v) (π k) f g
  change fullCorrelation _ (fun y : B => π u * y) _ _ _ = _ at hright
  rw [hright]
  change (∑ x : A, f (π x) * star (g (π ((↑u⁻¹ : A) * (v * x - k))))) =
    (reductionMultiplicity π : ℂ) *
      ∑ x : B, f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k)))
  simpa only [map_mul, map_sub] using
    sum_reduction π hπ (fun x => f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k))))

theorem fullCorrelation_reduction_unit_left (π : A →+* B)
    (hπ : Function.Surjective π) (u : A) (v : Aˣ) (k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => (v : A) * x) (fun y : A => u * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_swap, fullCorrelation_reduction_unit_right π hπ v u (-k) g f]
  rw [fullCorrelation_swap (fun x : B => π v * x) (fun y : B => π u * y) f g (π k)]
  simp only [map_neg, star_mul, star_natCast]
  ring

end
end SevenEighths.CenteredMomentCorrelation

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Moments.PrimePower
section
namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
local instance p2mAnonymous_PNT_ZeroFree_433_0292_1 : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

def primePowerReduction (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)

omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

theorem primePowerReduction_multiplicity (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)] :
    reductionMultiplicity (primePowerReduction P hc) = Ideal.absNorm P ^ (c - 1) := by
  have hcard (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
      Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine reductionMultiplicity_eq_pow _ (primePowerReduction_surjective P hc)
      (P := Ideal.absNorm P) ?_ hc ?_ ?_
  · rw [← hcard P]
    exact Fintype.card_pos
  · rw [hcard, map_pow]
  · exact hcard P

def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)

omit [NumberField K] in
@[simp] theorem primePowerCharacter_apply (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl

section Local
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
local instance p2mAnonymous_PNT_ZeroFree_433_0292_2 : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P

theorem primePower_localCorrelation (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by
  rw [fullCorrelation_reduction_unit_right _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  rfl

theorem primePower_localCorrelation_units (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      χ (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, localCorrelation_units _ hu hv,
    MulChar.pow_apply' _ (by omega), hcard, hpow, mul_assoc]
  split_ifs <;> rfl

theorem primePower_localCorrelation_second_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, hv, localCorrelation_second_zero _ hu, hcard, hpow]
  split_ifs <;> rfl

theorem primePower_localCorrelation_first_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : 𝓞 K ⧸ P ^ c) (v : (𝓞 K ⧸ P ^ c)ˣ)
    (k : 𝓞 K ⧸ P ^ c) (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ P ^ c) * x) (fun y => u * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hv : primePowerReduction P hc v ≠ 0 :=
    (isUnit_iff_ne_zero.mp (v.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  change (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) = _
  rw [hu, localCorrelation_first_zero _ hv, hcard, hpow]
  split_ifs <;> rfl

end Local
end
end SevenEighths.CenteredMomentCorrelation

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Moments.CRT
section
namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem fullCorrelation_ringEquiv (e : A ≃+* B) (u v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f (e x)) (fun y => g (e y)) k =
      fullCorrelation (fun x => e v * x) (fun y => e u * y) f g (e k) := by
  unfold fullCorrelation
  apply Fintype.sum_equiv e.toEquiv
  intro x
  apply Fintype.sum_equiv e.toEquiv
  intro y
  have heq : v * x - u * y = k ↔ e v * e x - e u * e y = e k := by
    rw [← map_mul, ← map_mul, ← map_sub, e.injective.eq_iff]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, heq]

theorem fullCorrelation_product (u v k : A × B) (f₁ g₁ : A → ℂ) (f₂ g₂ : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f₁ x.1 * f₂ x.2) (fun y => g₁ y.1 * g₂ y.2) k =
      fullCorrelation (fun x => v.1 * x) (fun y => u.1 * y) f₁ g₁ k.1 *
        fullCorrelation (fun x => v.2 * x) (fun y => u.2 * y) f₂ g₂ k.2 := by
  classical
  simp only [fullCorrelation, Fintype.sum_prod_type]
  have hterm (x₁ y₁ : A) (x₂ y₂ : B) :
      (if v * (x₁, x₂) - u * (y₁, y₂) = k
       then (f₁ x₁ * f₂ x₂) * star (g₁ y₁ * g₂ y₂) else 0) =
      (if v.1 * x₁ - u.1 * y₁ = k.1 then f₁ x₁ * star (g₁ y₁) else 0) *
      (if v.2 * x₂ - u.2 * y₂ = k.2 then f₂ x₂ * star (g₂ y₂) else 0) := by
    have heq : v * (x₁, x₂) - u * (y₁, y₂) = k ↔
        v.1 * x₁ - u.1 * y₁ = k.1 ∧ v.2 * x₂ - u.2 * y₂ = k.2 := by
      exact Prod.ext_iff
    by_cases h₁ : v.1 * x₁ - u.1 * y₁ = k.1 <;>
      by_cases h₂ : v.2 * x₂ - u.2 * y₂ = k.2 <;>
      simp [heq, h₁, h₂, star_mul] ; ring
  simp_rw [hterm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x₁ _
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x₂ _
  rw [Finset.mul_sum]

theorem fullCorrelation_pi {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]
    (u v k : ∀ i, R i) (f g : ∀ i, R i → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (fun x => v i * x) (fun y => u i * y) (f i) (g i) (k i) := by
  classical
  have hterm (x y : ∀ i, R i) :
      (if v * x - u * y = k then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if v i * x i - u i * y i = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, v i * x i - u i * y i = k i
    · have heq : v * x - u * y = k := funext h
      simp only [heq, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hne : v * x - u * y ≠ k := fun heq => hi (congrFun heq i)
      rw [if_neg hne]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, R i, ∏ i, ∑ y : R i,
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : R i) =>
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => ∑ y : R i,
      if v i * x - u i * y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_idealCRT {S ι : Type*} [CommRing S] [Fintype ι]
    (I : ι → Ideal S) (hI : Pairwise (Function.onFun IsCoprime I))
    [Fintype (S ⧸ ⨅ i, I i)] [∀ i, Fintype (S ⧸ I i)]
    (u v k : S ⧸ ⨅ i, I i) (f g : ∀ i, S ⧸ I i → ℂ) :
    let e := Ideal.quotientInfRingEquivPiQuotient I hI
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (e x i)) (fun y => ∏ i, g i (e y i)) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (f i) (g i) (e k i) := by
  classical
  dsimp only
  rw [fullCorrelation_ringEquiv (Ideal.quotientInfRingEquivPiQuotient I hI) u v k
    (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)), fullCorrelation_pi]

def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

@[simp] theorem crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI

end


