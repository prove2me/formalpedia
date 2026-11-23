-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:44.700121+00:00
-- url     : https://prove2.me/theorems/65906feb-d9f4-4a41-944d-032217c1dfb5
-- title:
--   Exists Bimultiplicative Of Second Quot Const
-- statement:
--   Definitions and structural lemmas for Exists Bimultiplicative Of Second Quot Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
namespace GlobalTheory
section SecondDifference
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]
def secondDiff (f : X → A) (a μ ν : X) : A :=
  f (a + μ + ν) - f (a + μ) - f (a + ν) + f a
def HasConstSecondDiff (f : X → A) : Prop :=
  ∀ a a' μ ν : X, secondDiff f a μ ν = secondDiff f a' μ ν
theorem secondDiff_comm (f : X → A) (a μ ν : X) : secondDiff f a μ ν = secondDiff f a ν μ := by
  simp only [secondDiff, add_right_comm a μ ν]
  abel
theorem secondDiff_add_left (f : X → A) (a μ μ' ν : X) :
    secondDiff f a (μ + μ') ν = secondDiff f a μ ν + secondDiff f (a + μ) μ' ν := by
  simp only [secondDiff, ← add_assoc]
  abel
theorem secondDiff_zero (f : X → A) (μ ν : X) :
    secondDiff f 0 μ ν = f (μ + ν) - f μ - f ν + f 0 := by
  simp [secondDiff]
namespace HasConstSecondDiff
variable {f : X → A}
def bilin (h : HasConstSecondDiff f) : X →ₗ[ℤ] X →ₗ[ℤ] A :=
  have hl : ∀ μ μ' ν : X,
      secondDiff f 0 (μ + μ') ν = secondDiff f 0 μ ν + secondDiff f 0 μ' ν := fun μ μ' ν => by
    rw [secondDiff_add_left, h (0 + μ) 0]
  have hr : ∀ μ ν ν' : X,
      secondDiff f 0 μ (ν + ν') = secondDiff f 0 μ ν + secondDiff f 0 μ ν' := fun μ ν ν' => by
    rw [secondDiff_comm, hl, secondDiff_comm f 0 ν, secondDiff_comm f 0 ν']
  (AddMonoidHom.mk' (fun μ => (AddMonoidHom.mk' (fun ν => secondDiff f 0 μ ν) (hr μ)).toIntLinearMap)
    (fun μ μ' => LinearMap.ext fun ν => hl μ μ' ν)).toIntLinearMap
theorem bilin_apply_zero (h : HasConstSecondDiff f) (μ ν : X) :
    h.bilin μ ν = f (μ + ν) - f μ - f ν + f 0 :=
  secondDiff_zero f μ ν
theorem map_add (h : HasConstSecondDiff f) (μ ν : X) :
    f (μ + ν) - f 0 = (f μ - f 0) + (f ν - f 0) + h.bilin μ ν := by
  rw [h.bilin_apply_zero]; abel
theorem bilin_self (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (x : X) :
    h.bilin x x = 2 • (f x - f 0) := by
  have h₁ := h.map_add x (-x)
  rw [add_neg_cancel, sub_self, he, map_neg] at h₁
  rw [two_smul]
  exact (add_neg_eq_zero.1 h₁.symm).symm
theorem map_zsmul (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (n : ℤ) (x : X) :
    f (n • x) - f 0 = (n * n) • (f x - f 0) := by
  have hn : ∀ n : ℕ, f ((n : ℤ) • x) - f 0 = ((n : ℤ) * n) • (f x - f 0) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, one_smul, h.map_add, ih, map_smul, LinearMap.smul_apply,
        h.bilin_self he]
      module
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact hn m
  · rw [neg_smul, he, neg_mul_neg, hn]
def quadraticMap (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) : QuadraticMap ℤ X A where
  toFun x := f x - f 0
  toFun_smul := h.map_zsmul he
  exists_companion' := ⟨h.bilin, h.map_add⟩
@[simp] theorem quadraticMap_apply (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (x : X) :
    h.quadraticMap he x = f x - f 0 := rfl
theorem comp_left {A' : Type*} [AddCommGroup A'] (h : HasConstSecondDiff f) (v : A →+ A') :
    HasConstSecondDiff (v ∘ f) := fun a a' μ ν => by
  simpa [secondDiff] using congrArg v (h a a' μ ν)
end HasConstSecondDiff
end SecondDifference
section Definite
end Definite
section RealExtension
variable {X : Type*} [AddCommGroup X]
noncomputable def realExtBilin (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : LinearMap.BilinForm ℝ (ℝ ⊗[ℤ] X) :=
  LinearMap.liftBaseChange ℝ
    ((LinearMap.liftBaseChangeEquiv (R := ℤ) (M := X) (N := ℝ) ℝ).toLinearMap.restrictScalars ℤ
      ∘ₗ B)
noncomputable def realExt (Q : QuadraticMap ℤ X ℝ) : QuadraticForm ℝ (ℝ ⊗[ℤ] X) :=
  (2⁻¹ : ℝ) • (realExtBilin Q.polarBilin).toQuadraticMap
example : HasConstSecondDiff (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) ∧
    (∀ x : ℤ, (((-x : ℤ) : ℝ) ^ 2 + 1) = (x : ℝ) ^ 2 + 1) ∧
    Tendsto (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) cofinite atTop := by
  refine ⟨fun a a' μ ν => ?_, fun x => by simp, tendsto_atTop_add_const_right _ _ ?_⟩
  · simp only [secondDiff]
    push_cast
    ring
  · have h : Tendsto (fun x : ℤ => |(x : ℝ)|) cofinite atTop := by
      rw [Int.cofinite_eq, tendsto_sup]
      exact ⟨tendsto_abs_atBot_atTop.comp (tendsto_intCast_atBot_iff.2 tendsto_id),
        tendsto_abs_atTop_atTop.comp tendsto_intCast_atTop_atTop⟩
    simpa [Function.comp_def] using (tendsto_pow_atTop two_ne_zero).comp h
end RealExtension
end GlobalTheory


