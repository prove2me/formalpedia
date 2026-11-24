-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:28.085665+00:00
-- url     : https://prove2.me/theorems/44d516b1-5799-48a0-9283-60d80eeecfa3
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem prod_zpow_single {M : Type*} [CommGroupWithZero M] (f : ι → M) (k₀ : ι) :
    ∏ k, f k ^ ((Pi.single k₀ 1 : ι → ℤ) k) = f k₀ := by
  rw [Finset.prod_eq_single k₀ (fun k _ hk ↦ by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (fun h ↦ absurd (Finset.mem_univ k₀) h), Pi.single_eq_same, zpow_one]
omit [Fintype ι] in
theorem single_cast (k₀ k : ι) : (((Pi.single k₀ 1 : ι → ℕ) k : ℕ) : ℤ) = (Pi.single k₀ 1 : ι → ℤ) k := by
  by_cases h : k = k₀
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]
namespace ArithVariety
variable (n : ι → ℕ)
omit [Fintype ι] in
theorem whole_mkF_X_ne_zero (v : Coord n) : (whole n).mkF (X v) ≠ 0 := fun h ↦
  X_ne_zero v ((Submodule.mem_bot _).mp (((whole n).mkF_eq_zero_iff _).mp h))
end ArithVariety
variable (n : ι → ℕ) (k₀ : ι)
def blockAddData : AddBlockData (ArithVariety.whole n) where
  deg := Pi.single k₀ 1
  size := n k₀
  elt j := (ArithVariety.whole n).mkF (X ⟨k₀, j⟩)
  elt_deg j := ⟨X ⟨k₀, j⟩, 1, (Pi.single k₀ 1 : ι → ℕ), 0, isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k₀, j⟩,
    isWeightedHomogeneous_one ℤ (coordDeg n), fun k ↦ by simp [single_cast],
    (Ideal.ne_top_iff_one _).mp (ArithVariety.whole n).isPrime.ne_top, by rw [map_one, div_one]⟩
  chart_mem c _ j := by
    rw [ArithVariety.chartPow, prod_zpow_single]
    exact Subring.subset_closure ⟨⟨k₀, j⟩, rfl⟩
  generating c _ := by
    refine ⟨Pi.single (c k₀) 1, fun j ↦ ?_, ?_⟩
    · by_cases h : j = c k₀
      · subst h; rw [Pi.single_eq_same]; exact Subring.one_mem _
      · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _
    · rw [Finset.sum_eq_single (c k₀) (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul])
        (fun h ↦ absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
        ArithVariety.chartPow, prod_zpow_single]
      exact div_self (ArithVariety.whole_mkF_X_ne_zero n _)
def blockForms : ((k : ι) → Fin (n k + 1)) → Fin ((blockAddData n k₀).size + 1) →
    MvPolynomial (Coord n) ℤ :=
  fun c j ↦ chartMonomial c 1 * X ⟨k₀, j⟩
def blockLine : HermLine n where
  deg := Pi.single k₀ 1
  metric z := l2Norm (z k₀)
  metric_pos z hz := vectorL2Norm_pos (hz k₀)
  metric_smul c z _ _ := by
    rw [vectorL2Norm_const_mul, prod_zpow_single (fun k ↦ ‖c k‖) k₀]
  metric_smooth := contDiffOn_l2Norm_block k₀
def blockVal : Coord (blockAddData n k₀).extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => X ⟨k₀, j⟩
  | ⟨some k, i⟩ => X ⟨k, i⟩
def blockSubst :
    MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ →+* MvPolynomial (Option ι) (MvPolynomial (Coord n) ℤ) :=
  eval₂Hom (Int.castRingHom _) fun v ↦ C (blockVal n k₀ v) * X v.1
omit [DecidableEq ι] in
theorem standard_quot_deg :
    (0 : ι → ℤ) = (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv).deg := by
  funext k
  simp [HermLine.pow, HermLine.mul, HermLine.inv, HermLine.standard]
def gaussianIntegerBasis : Module.Basis (Fin (1 + 1)) ℤ (𝓞 GaussianField) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  haveI : IsCyclotomicExtension {4} ℚ GaussianField := CyclotomicField.isCyclotomicExtension 4 ℚ
  exact (IsCyclotomicExtension.zeta_spec 4 ℚ GaussianField).integralPowerBasis.basis.reindex
    (finCongr (by rw [IsPrimitiveRoot.integralPowerBasis_dim]; decide))
def ratIntegerBasis : Module.Basis (Fin (0 + 1)) ℤ (𝓞 ℚ) :=
  (Module.Basis.singleton (Fin 1) ℤ).map Rat.ringOfIntegersEquiv.symm.toAddEquiv.toIntLinearEquiv
end
end GroundTheory.Heights₂.Heights


