-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CenteredHermiteFirstOrder_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CenteredHermiteFirstOrder_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:37:22.603702+00:00
-- url     : https://prove2.me/theorems/e3355a6c-028d-459a-9fb4-18564b2f07b7
-- title:
--   FLT.Assumptions.MazurProof.N13CenteredHermiteFirstOrder source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CenteredHermiteFirstOrder

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CenteredHermiteFirstOrder
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordCenteredDoublingJet_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

A concrete Hermite numerator calculation. If uBase*A+b*y vanishes twice
on the conjugates of an actual disk pair, where A is monic quadratic and
b is linear, its coefficients are forced to the centered-square values
modulo the moving coordinate ideal squared. Constructing such a normalized
numerator for the actual principal comparison remains a separate goal.
-/

namespace MazurProof.N13CenteredHermiteFirstOrder

noncomputable section
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev R₂ := ℤ_[2]
abbrev DiskPair := N13TwoAdicAbelChartData.DiskPair

private theorem cancel_unit_mem {R : Type*} [CommRing R]
    (I : Ideal R) {a u : R} (hu : IsUnit u) (h : a * u ∈ I) : a ∈ I :=
  (Ideal.unit_mul_mem_iff_mem I hu).mp (by simpa [mul_comm] using h)

/-- Evaluation at two points separated by a unit detects both coefficients
of a linear polynomial modulo any ideal. -/
theorem linear_coeff_mem {R : Type*} [CommRing R]
    (I : Ideal R) (x₀ x₁ c₀ c₁ : R) (hd : IsUnit (x₁ - x₀))
    (h₀ : c₀ + c₁ * x₀ ∈ I) (h₁ : c₀ + c₁ * x₁ ∈ I) :
    c₀ ∈ I ∧ c₁ ∈ I := by
  have hm : c₁ * (x₁ - x₀) ∈ I := by
    convert I.sub_mem h₁ h₀ using 1 <;> ring
  have hc₁ := cancel_unit_mem I hd hm
  refine ⟨?_, hc₁⟩
  convert I.sub_mem h₀ (I.mul_mem_right x₀ hc₁) using 1 <;> ring

def x (P : DiskPair) : Fin 2 → R₂ := ![P.x₀, P.x₁]
def oppositeY (P : DiskPair) : Fin 2 → R₂ :=
  ![-N13GoodModelTwo.h P.x₀ - P.y₀,
    -N13GoodModelTwo.h P.x₁ - P.y₁]
def I (P : DiskPair) : Ideal R₂ :=
  N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P

theorem uBase_eval_mem (P : DiskPair) (j : Fin 2) :
    x P j ^ 2 + x P j ∈ I P := by
  have hx₀ : P.x₀ ∈ I P := Ideal.subset_span (Set.mem_range_self (0 : Fin 2))
  have hx₁ : P.x₁ + 1 ∈ I P := Ideal.subset_span (Set.mem_range_self (1 : Fin 2))
  fin_cases j
  · convert (I P).mul_mem_right (P.x₀ + 1) hx₀ using 1 <;> simp [x] <;> ring
  · convert (I P).mul_mem_left P.x₁ hx₁ using 1 <;> simp [x] <;> ring

theorem uBase_derivative_unit (P : DiskPair) (j : Fin 2) :
    IsUnit (2 * x P j + 1) := by
  fin_cases j
  · apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.x₀_mem using 1 <;>
      simp [x] <;> ring
  · apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.x₁_add_one_mem using 1 <;>
      simp [x] <;> ring

theorem oppositeY_unit (P : DiskPair) (j : Fin 2) : IsUnit (oppositeY P j) := by
  have h₀ : IsUnit (P.y₀ + N13GoodModelTwo.h P.x₀) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
    convert P.y₀_spec.2 using 1 <;> ring
  have h₁ : IsUnit (P.y₁ + N13GoodModelTwo.h P.x₁) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk P.x₁_add_one_mem)
    convert P.y₁_spec.2 using 1 <;> ring
  fin_cases j
  · convert h₀.neg using 1 <;> simp [oppositeY] <;> ring
  · convert h₁.neg using 1 <;> simp [oppositeY] <;> ring

/-- The equations are value and derivative vanishing of the actual
numerator uBase*A+b*y on the opposite sheet. The tangent slopes are
arbitrary integral values here; only their integrality is used. -/
theorem hermite_coefficients_mod_square
    (P : DiskPair) (a₀ a₁ b₀ b₁ : R₂) (slope : Fin 2 → R₂)
    (hvalue : ∀ j,
      (x P j ^ 2 + x P j) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (b₀ + b₁ * x P j) * oppositeY P j = 0)
    (hderivative : ∀ j,
      (2 * x P j + 1) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (x P j ^ 2 + x P j) * (2 * x P j + a₁) +
        b₁ * oppositeY P j + (b₀ + b₁ * x P j) * slope j = 0) :
    b₀ ∈ I P * I P ∧ b₁ ∈ I P * I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P := by
  let A (j : Fin 2) := x P j ^ 2 + a₁ * x P j + a₀
  let b (j : Fin 2) := b₀ + b₁ * x P j
  let u (j : Fin 2) := x P j ^ 2 + x P j
  have hu (j : Fin 2) : u j ∈ I P := uBase_eval_mem P j
  have hb (j : Fin 2) : b j ∈ I P := by
    apply cancel_unit_mem (I P) (oppositeY_unit P j)
    have he : b j * oppositeY P j = -(u j * A j) := by
      dsimp [A, b, u]
      linear_combination hvalue j
    rw [he]
    exact (I P).neg_mem ((I P).mul_mem_right (A j) (hu j))
  have hbc := linear_coeff_mem (I P) P.x₀ P.x₁ b₀ b₁
    P.x₁_sub_x₀_isUnit (hb 0) (hb 1)
  have hA (j : Fin 2) : A j ∈ I P := by
    apply cancel_unit_mem (I P) (uBase_derivative_unit P j)
    have he : A j * (2 * x P j + 1) =
        -(u j * (2 * x P j + a₁) + b₁ * oppositeY P j + b j * slope j) := by
      dsimp [A, b, u]
      linear_combination hderivative j
    rw [he]
    exact (I P).neg_mem ((I P).add_mem
      ((I P).add_mem ((I P).mul_mem_right _ (hu j))
        ((I P).mul_mem_right _ hbc.2)) ((I P).mul_mem_right _ (hb j)))
  have hlinear (j : Fin 2) : a₀ + (a₁ - 1) * x P j ∈ I P := by
    convert (I P).sub_mem (hA j) (hu j) using 1 <;> dsimp [A, u] <;> ring
  have hac := linear_coeff_mem (I P) P.x₀ P.x₁ a₀ (a₁ - 1)
    P.x₁_sub_x₀_isUnit (hlinear 0) (hlinear 1)
  have hb₂ (j : Fin 2) : b j ∈ I P * I P := by
    apply cancel_unit_mem (I P * I P) (oppositeY_unit P j)
    have he : b j * oppositeY P j = -(u j * A j) := by
      dsimp [A, b, u]
      linear_combination hvalue j
    rw [he]
    exact (I P * I P).neg_mem (Ideal.mul_mem_mul (hu j) (hA j))
  have hbc₂ := linear_coeff_mem (I P * I P) P.x₀ P.x₁ b₀ b₁
    P.x₁_sub_x₀_isUnit (hb₂ 0) (hb₂ 1)
  have hAu (j : Fin 2) : A j + u j ∈ I P * I P := by
    apply cancel_unit_mem (I P * I P) (uBase_derivative_unit P j)
    have he : (A j + u j) * (2 * x P j + 1) =
        -(b₁ * oppositeY P j + b j * slope j + u j * (a₁ - 1)) := by
      dsimp [A, b, u]
      linear_combination hderivative j
    rw [he]
    exact (I P * I P).neg_mem ((I P * I P).add_mem
      ((I P * I P).add_mem ((I P * I P).mul_mem_right _ hbc₂.2)
        ((I P * I P).mul_mem_right _ (hb₂ j))) (Ideal.mul_mem_mul (hu j) hac.2))
  have hzero : (a₀ - 2 * P.x₀ * P.x₁) +
      (a₁ + 2 * (P.x₀ + P.x₁) + 1) * P.x₀ ∈ I P * I P := by
    convert hAu 0 using 1 <;> dsimp [A, u, x] <;> ring
  have hone : (a₀ - 2 * P.x₀ * P.x₁) +
      (a₁ + 2 * (P.x₀ + P.x₁) + 1) * P.x₁ ∈ I P * I P := by
    convert hAu 1 using 1 <;> dsimp [A, u, x] <;> ring
  have hcenter := linear_coeff_mem (I P * I P) P.x₀ P.x₁
    (a₀ - 2 * P.x₀ * P.x₁) (a₁ + 2 * (P.x₀ + P.x₁) + 1)
    P.x₁_sub_x₀_isUnit hzero hone
  exact ⟨hbc₂.1, hbc₂.2, hcenter.1, hcenter.2⟩

end
end MazurProof.N13CenteredHermiteFirstOrder


