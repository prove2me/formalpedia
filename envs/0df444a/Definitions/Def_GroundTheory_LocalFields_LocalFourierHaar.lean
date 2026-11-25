-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
-- name    : GroundTheory_LocalFields_LocalFourierHaar
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:09.754655+00:00
-- url     : https://prove2.me/theorems/17b11bff-9c29-4a7b-aa91-3dc6027c846c
-- title:
--   Local Fourier Haar
-- statement:
--   Definitions and structural lemmas for Local Fourier Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_le_one_iff
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Topology
instance t2Space_nonarchimedeanLocalField : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
theorem mem_valBall_iff_le_ord {n : ℤ} {x : K} (hx : x ≠ 0) : x ∈ valBall K n ↔ n ≤ ord x := by
  rw [mem_valBall, normalizedValuation_eq_exp_ord hx, WithZero.exp_le_exp]
  omega
theorem mem_valBall_ord {x : K} : x ∈ valBall K (ord x) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_mem _
  · exact (mem_valBall_iff_le_ord hx).mpr le_rfl
theorem ord_inv {x : K} (hx : x ≠ 0) : ord x⁻¹ = -ord x := by
  have h := ord_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ord_one] at h
  omega
theorem mem_valBall_zero_iff {x : K} : x ∈ valBall K 0 ↔ x ∈ 𝒪[K] := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, normalizedValuation_le_one_iff]
theorem smul_valBall {c : K} (hc : c ≠ 0) (n : ℤ) :
    c • (valBall K n : Set K) = valBall K (n + ord c) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := mul_mem_valBall (mem_valBall_ord (x := c)) hy
    rw [add_comm]
    exact this
  · intro hx
    refine ⟨c⁻¹ * x, ?_, by simp [smul_eq_mul, hc]⟩
    have h1 : c⁻¹ ∈ valBall K (-ord c) := by
      rw [← ord_inv hc]; exact mem_valBall_ord
    have := mul_mem_valBall h1 hx
    simpa using this
theorem isCompact_valBall (n : ℤ) : IsCompact (valBall K n : Set K) := by
  obtain ⟨c, hc, hcn⟩ := exists_ord_eq K n
  have h0 : IsCompact (valBall K 0 : Set K) := by
    have : (valBall K 0 : Set K) = {x : K | valuation K x ≤ 1} := by
      ext x
      exact mem_valBall_zero_iff
    rw [this]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have := h0.smul c
  rwa [smul_valBall hc, zero_add, hcn] at this
theorem exists_mem_valBall_neg_nat (x : K) : ∃ m : ℕ, x ∈ valBall K (-(m : ℤ)) := by
  refine ⟨(-ord x).toNat, valBall_antitone ?_ mem_valBall_ord⟩
  omega
instance sigmaCompactSpace_localField : SigmaCompactSpace K :=
  ⟨⟨fun m : ℕ => (valBall K (-(m : ℤ)) : Set K), fun _ => isCompact_valBall _, by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, SetLike.mem_coe]
    exact exists_mem_valBall_neg_nat x⟩⟩
instance secondCountableTopology_localField : SecondCountableTopology K := by
  let := nontriviallyNormedField K
  exact EMetric.secondCountable_of_sigmaCompact K
end Topology
section Residue
variable (K) in

def residueCard : ℕ := Nat.card 𝓀[K]
end Residue
section Modulus
def modulus (x : K) : ℝ≥0 := by
  classical exact if x = 0 then 0 else (residueCard K : ℝ≥0) ^ (-ord x)
end Modulus
section Haar
variable [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure]
variable (K) in

def integersPositiveCompacts : PositiveCompacts K where
  carrier := valBall K 0
  isCompact' := isCompact_valBall 0
  interior_nonempty' := by
    rw [(isOpen_valBall 0).interior_eq]
    exact ⟨0, zero_mem _⟩
variable (K) in

def haarIntegers : Measure K := addHaarMeasure (integersPositiveCompacts K)
instance : (haarIntegers K).IsAddHaarMeasure := by
  unfold haarIntegers
  infer_instance
end Haar
end GroundTheory.LocalField


