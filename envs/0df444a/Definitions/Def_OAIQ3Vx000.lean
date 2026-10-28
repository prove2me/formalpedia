-- Prove2me | Definitions.Def_OAIQ3Vx000
-- name    : OAIQ3Vx000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:26:18.747118+00:00
-- url     : https://prove2.me/theorems/8a34ad6c-716a-4462-b10d-04bc0171cece
-- title:
--   Definitions bundle OAIQ3Vx000 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 375 declarations of OpenAI's Lean: 87 definitions, 1 inductive type or structure, 1 instance and 286 theorems. The definitions and types are `OAI.StronglyRationalVOA.BoundedFlow.boundedFlowRationalNormedAlgebra`, `OAI.StronglyRationalVOA.BoundedFlow.flow`, `OAI.StronglyRationalVOA.CFTTypeVOA.BlockControl`, `OAI.StronglyRationalVOA.CFTTypeVOA.BlockGrowth`, `OAI.StronglyRationalVOA.CFTTypeVOA.ColumnControl`, `OAI.StronglyRationalVOA.CFTTypeVOA.ColumnGrowth`, `OAI.StronglyRationalVOA.CFTTypeVOA.IsPrimary`, `OAI.StronglyRationalVOA.CFTTypeVOA.IsQuasiPrimary`, `OAI.StronglyRationalVOA.CFTTypeVOA.SharpDegreeGrowth`, `OAI.StronglyRationalVOA.CFTTypeVOA.SharpGrowth`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.AdjointColumnControl`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.CKLWStrongLocal`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.IsHermitian`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.StressPath`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.adjointPhysicalMode`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.closedSmearedOperator`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.closedSmoothField`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.coreEnergyCoordinates`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.energyCoordinates`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.energyCutoff`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.energyOperator`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.energyPower`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.gradeEmbedding`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.hermitianConjugation`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.intervalAlgebra`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.inverseCoreEnergy`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.inverseSobolev`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.localAlgebra`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.localGraphData`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.smearedPowerCommutator`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.smoothEnergySpace`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.smoothSmearedField`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.sobolevExtension`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.spectralCoreMap`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressCore`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressCutoff`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressNormalized`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.truncatedEnergyPower`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.weightedSmearedMap`, `OAI.StronglyRationalVOA.CFTTypeVOA.ZeroGrowth` and 48 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_ApproximatingFlowDerivative`, `VertexAlgebra_BlockGrowth`, `VertexAlgebra_BoundedFlows`, `VertexAlgebra_BoundedMultiplierSingle`, `VertexAlgebra_ColumnControl`, `VertexAlgebra_ConstrainedSquareBound`, `VertexAlgebra_EnergyCutoff`, `VertexAlgebra_EnergyCutoffNorm`, `VertexAlgebra_EnergyShiftPow`, `VertexAlgebra_FiniteSums`, `VertexAlgebra_GradeComponentC`, `VertexAlgebra_GraphCommutants`, `VertexAlgebra_GraphEquiv`, `VertexAlgebra_HilbertCore`, `VertexAlgebra_HilbertRegularization`, `VertexAlgebra_InverseEnergySelf`, `VertexAlgebra_LoweringNormSq`, `VertexAlgebra_RegularizerFactorAdd`, `VertexAlgebra_StressCutoffNormalized`, `VertexAlgebra_StressEvolution`, `VertexAlgebra_SummableNormSobolev`, `VertexAlgebra_SymmetricWeakCommute`, `VertexAlgebra_VacuumMemNegative`, `VertexAlgebra_VirasoroLinearEnergy`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx003`, `OAIQ3Vx004` and `OAIQ3Vx005`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet

section
-- module Solutions.OAIQ3_Vtx.Compat
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_FiniteSums
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section



 

namespace StronglyRationalVOA

universe u v

 

theorem finite_sum_power_contraction {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (P : ℕ) (hP : 1 ≤ P) (R : ℝ) (hR : 1 ≤ R)
    (hx : ∀ i ∈ s, 0 ≤ x i)
    (H : ∀ i ∈ s, (x i)^P ≤ R * (1 + ∑ j ∈ s, x j)^(P - 1)) :
    1 + ∑ i ∈ s, x i ≤ ((s.card : ℝ) + 1)^P * R := by
  classical
  let B : ℝ := 1 + ∑ i ∈ s, x i
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [Finset.sum_nonneg hx]
  have hRhs : 1 ≤ R * B^(P - 1) := by
    nlinarith [one_le_pow₀ hB (n := P - 1)]
  have hmax : ∃ M : ℝ, 1 ≤ M ∧ (∀ i ∈ s, x i ≤ M) ∧ M^P ≤ R * B^(P - 1) := by
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hmax⟩ := s.exists_max_image x hs
      refine ⟨max 1 (x i), le_max_left _ _, ?_, ?_⟩
      · intro j hj
        exact (hmax j hj).trans (le_max_right _ _)
      · rcases le_total (x i) 1 with h | h
        · rw [max_eq_left h, one_pow]
          exact hRhs
        · rw [max_eq_right h]
          exact H i hi
    · refine ⟨1, le_rfl, ?_, ?_⟩
      · intro i hi
        exact (hs ⟨i, hi⟩).elim
      · simpa only [one_pow] using hRhs
  obtain ⟨M, hM, hmax, hMP⟩ := hmax
  have hBM : B ≤ ((s.card : ℝ) + 1) * M := by
    have hsum : ∑ i ∈ s, x i ≤ (s.card : ℝ) * M := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => hmax i hi)
    dsimp [B]
    nlinarith
  have hp : B^P ≤ (((s.card : ℝ) + 1)^P * R) * B^(P - 1) := by
    calc
      _ ≤ (((s.card : ℝ) + 1) * M)^P := pow_le_pow_left₀ (by linarith) hBM P
      _ = ((s.card : ℝ) + 1)^P * M^P := mul_pow _ _ _
      _ ≤ ((s.card : ℝ) + 1)^P * (R * B^(P - 1)) :=
        mul_le_mul_of_nonneg_left hMP (by positivity)
      _ = _ := by ring
  have he : P - 1 + 1 = P := by omega
  rw [← he, pow_succ] at hp
  have hpos : 0 < B^(P - 1) := pow_pos (by linarith) _
  change B ≤ _
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  simpa only [he, mul_comm] using hp

 

theorem finite_weighted_poly_uniform {ι κ : Type*} {B : ℕ → ℝ}
    (hB : ∀ N, 1 ≤ B N) (s : Finset ι) (f : ι → ℕ → κ → ℝ)
    (w : ι → ℕ) (T : ℕ → κ → Prop)
    (H : ∀ i ∈ s, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N x, T N x →
      f i N x ≤ C * (1 + (N : ℝ))^p * B N ^ w i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i ∈ s, ∀ N x, T N x →
      f i N x ≤ C * (1 + (N : ℝ))^p * B N ^ w i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, p, hp⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, q, hq⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, p + q, ?_⟩
    intro j hj N x hx
    have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
    have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
    have hpq : (1 + (N : ℝ))^p ≤ (1 + (N : ℝ))^(p + q) :=
      pow_le_pow_right₀ hN1 (by omega)
    have hqp : (1 + (N : ℝ))^q ≤ (1 + (N : ℝ))^(p + q) :=
      pow_le_pow_right₀ hN1 (by omega)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply (hp N x hx).trans
      gcongr
      exact le_add_of_nonneg_right hD
    · apply (hq j hj N x hx).trans
      gcongr
      exact le_add_of_nonneg_left hC

section FiniteSums

variable {E : Type*} [AddCommMonoid E]

 
theorem finsum_nat_split (f : ℕ → E) (hf : Function.HasFiniteSupport f) (n : ℕ) :
    (∑ᶠ j : ℕ, f j) = (∑ j ∈ Finset.range n, f j) + ∑ᶠ j : ℕ, f (n + j) := by
  classical
  let N := hf.toFinset.sup id + 1
  have hN : ∀ j, N ≤ j → f j = 0 := by
    intro j hj
    by_contra h
    have hjmem : j ∈ hf.toFinset := by exact (Set.Finite.mem_toFinset hf).mpr h
    have hh := Finset.le_sup (f := id) hjmem
    change j ≤ hf.toFinset.sup id at hh
    omega
  have hs : Function.support f ⊆ (Finset.range (n + N) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hj (hN j (by omega))
  have ht : Function.support (fun j => f (n + j)) ⊆ (Finset.range N : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hj (hN (n + j) (by omega))
  rw [finsum_eq_sum_of_support_subset f hs,
    finsum_eq_sum_of_support_subset _ ht, Finset.sum_range_add]

end FiniteSums

section Algebraic

variable {V : Type u} [AddCommGroup V] [Module ℂ V]



@[simp]
theorem mode_zero {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (n : ℤ) : mode Y 0 n = 0 := by
  simp [mode]

@[simp]
theorem mode_add {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (a b : V) (n : ℤ) :
    mode Y (a + b) n = mode Y a n + mode Y b n := by
  simp [mode]

@[simp]
theorem mode_smul {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (z : ℂ) (a : V) (n : ℤ) :
    mode Y (z • a) n = z • mode Y a n := by
  simp [mode]

 

theorem mode_lower_truncation {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (a : V) (b : W) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode Y a n b = 0 := by
  let o := HahnSeries.order ((HahnModule.of ℂ).symm (Y a b))
  refine ⟨-o, fun n hn => ?_⟩
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  change -n - 1 < o
  omega

 
theorem mode_shift_hasFiniteSupport {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : StateField V W) (a : V) (b : W) (n : ℤ) :
    (Function.support fun j : ℕ => mode Y a (n + j) b).Finite := by
  obtain ⟨N, hN⟩ := mode_lower_truncation Y a b
  refine (Set.finite_Iio (N - n).toNat).subset ?_
  intro j hj
  have hn : n + (j : ℤ) < N := by
    by_contra h
    exact hj (hN (n + j) (by omega))
  change j < (N - n).toNat
  omega



namespace VertexAlgebra

variable (A : VertexAlgebra V)

 

theorem mode_commutator (a b c : V) (m k : ℤ) :
    mode A.fields a m (mode A.fields b k c) -
      mode A.fields b k (mode A.fields a m c) =
    ∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      mode A.fields (mode A.fields a j b) (m + k - j) c := by
  have h := A.jacobi a b c m 0 k
  have hz (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 := by
    rw [← Nat.cast_zero, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]
  conv_rhs at h =>
    rw [finsum_eq_single _ 0 (by
      intro j hj
      simp only [Int.cast_zero, hz j hj, mul_zero, zero_smul])]
  simpa using h.symm

 

theorem mode_commutator_nat (a b c : V) (m : ℕ) (k : ℤ) :
    mode A.fields a m (mode A.fields b k c) -
      mode A.fields b k (mode A.fields a m c) =
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) •
      mode A.fields (mode A.fields a j b) ((m : ℤ) + k - j) c := by
  rw [A.mode_commutator]
  simp only [Int.cast_natCast, Ring.choose_natCast]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  have he : m.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
  apply hj
  simp only [he, Nat.cast_zero, zero_smul]



theorem mode_normal_product (a b c : V) (k : ℤ) :
    mode A.fields (mode A.fields a (-1) b) k c =
      ∑ᶠ j : ℕ,
        (mode A.fields a (-1 - j) (mode A.fields b (k + j) c) +
         mode A.fields b (k - 1 - j) (mode A.fields a j c)) := by
  have h := A.jacobi a b c 0 (-1) k
  have hz (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 := by
    rw [← Nat.cast_zero, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]
  have hcoef (j : ℕ) : (-1 : ℂ)^j * Ring.choose (-1 : ℂ) j = 1 := by
    simp only [Ring.choose_neg', Ring.multichoose_one, Units.smul_def,
      Int.coe_negOnePow_natCast, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, mul_one, ← mul_pow]
    simp
  conv_lhs at h =>
    rw [finsum_eq_single _ 0 (by
      intro j hj
      simp only [Int.cast_zero, hz j hj, zero_smul])]
  have hn : (-1 : ℂ)^(-1 : ℤ) = -1 := by norm_num
  simpa only [Int.cast_zero, Int.cast_neg, Int.cast_one, Ring.choose_zero_right, Nat.cast_zero, add_zero,
    sub_zero, zero_add, one_smul, hcoef, hn, neg_one_smul, sub_neg_eq_add,
    show (-1 : ℤ) + k = k - 1 by omega] using h



theorem mode_normal_product_resplit (a b c : V) (k : ℤ) (t : ℕ) :
    mode A.fields (mode A.fields a (-1) b) k c =
      (∑ᶠ j : ℕ, mode A.fields a ((t : ℤ) - 1 - j)
        (mode A.fields b (k - t + j) c)) +
      (∑ᶠ j : ℕ, mode A.fields b (k - 1 - t - j)
        (mode A.fields a ((t : ℤ) + j) c)) -
      ∑ i ∈ Finset.range t,
        (mode A.fields a i (mode A.fields b (k - 1 - i) c) -
          mode A.fields b (k - 1 - i) (mode A.fields a i c)) := by
  classical
  have hleft (s : ℤ) : Function.HasFiniteSupport (fun j : ℕ =>
      mode A.fields a (s - 1 - j) (mode A.fields b (k - s + j) c)) := by
    apply (mode_shift_hasFiniteSupport A.fields b c (k - s)).subset
    intro j hj
    change _ ≠ 0 at hj ⊢
    intro hz
    exact hj (by dsimp at hz ⊢; rw [hz, map_zero])
  have hright (s : ℤ) : Function.HasFiniteSupport (fun j : ℕ =>
      mode A.fields b (k - 1 - s - j) (mode A.fields a (s + j) c)) := by
    apply (mode_shift_hasFiniteSupport A.fields a c s).subset
    intro j hj
    change _ ≠ 0 at hj ⊢
    intro hz
    exact hj (by dsimp at hz ⊢; rw [hz, map_zero])
  have hL := finsum_nat_split
    (fun j : ℕ => mode A.fields a ((t : ℤ) - 1 - j)
      (mode A.fields b (k - t + j) c)) (hleft t) t
  have hR := finsum_nat_split
    (fun j : ℕ => mode A.fields b (k - 1 - j) (mode A.fields a j c))
    (by simpa only [sub_zero, zero_add] using hright 0) t
  have htail : (∑ᶠ j : ℕ, mode A.fields a ((t : ℤ) - 1 - (t + j : ℕ))
      (mode A.fields b (k - t + (t + j : ℕ)) c)) =
      ∑ᶠ j : ℕ, mode A.fields a (-1 - j) (mode A.fields b (k + j) c) := by
    apply finsum_congr
    intro j
    simp only [Nat.cast_add]
    rw [show (t : ℤ) - 1 - (t + j) = -1 - j by omega,
      show k - (t : ℤ) + (t + j) = k + j by omega]
  have htailR : (∑ᶠ j : ℕ, mode A.fields b (k - 1 - (t + j : ℕ))
      (mode A.fields a (t + j : ℕ) c)) =
      ∑ᶠ j : ℕ, mode A.fields b (k - 1 - t - j)
        (mode A.fields a ((t : ℤ) + j) c) := by
    apply finsum_congr
    intro j
    simp only [Nat.cast_add]
    rw [show k - 1 - ((t : ℤ) + j) = k - 1 - t - j by omega]
  have hhead : (∑ j ∈ Finset.range t,
      mode A.fields a ((t : ℤ) - 1 - j) (mode A.fields b (k - t + j) c)) =
      ∑ j ∈ Finset.range t, mode A.fields a j (mode A.fields b (k - 1 - j) c) := by
    rw [← Finset.sum_range_reflect
      (fun j : ℕ => mode A.fields a j (mode A.fields b (k - 1 - j) c)) t]
    apply Finset.sum_congr rfl
    intro j hj
    have hcast : ((t - 1 - j : ℕ) : ℤ) = (t : ℤ) - 1 - j := by
      simp only [Finset.mem_range] at hj
      omega
    rw [hcast, show k - 1 - ((t : ℤ) - 1 - j) = k - t + j by omega]
  rw [htail, hhead] at hL
  rw [htailR] at hR
  rw [A.mode_normal_product, finsum_add_distrib
    (by simpa only [zero_sub, sub_zero] using hleft 0)
    (by simpa only [sub_zero, zero_add] using hright 0), Finset.sum_sub_distrib]
  rw [hL, hR]
  abel



end VertexAlgebra
end Algebraic
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_VacuumMemNegative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
section Algebraic
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
namespace VertexAlgebra
variable (A : VertexAlgebra V)


theorem mode_neg_two_mem_c2 (a b : V) : mode A.fields a (-2) b ∈ A.c2 := by
  exact Submodule.subset_span ⟨a, b, rfl⟩


end VertexAlgebra



namespace CFTTypeVOA

variable (A : CFTTypeVOA V)


def IsQuasiPrimary (a : V) : Prop := A.virasoroMode 1 a = 0



def gradeComponent (d : ℕ) : Module.End ℂ V :=
  (A.grade d).subtype.comp ((DirectSum.component ℂ ℕ (fun d => A.grade d) d).comp
    A.gradingEquiv.toLinearMap)

@[simp]
theorem gradeComponent_apply (d : ℕ) (a : V) :
    A.gradeComponent d a = (A.gradingEquiv a d : V) := rfl

theorem gradeComponent_mem (d : ℕ) (a : V) : A.gradeComponent d a ∈ A.grade d :=
  (A.gradingEquiv a d).property

theorem gradeComponent_of_mem {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    A.gradeComponent d a = a := by
  exact congrArg Subtype.val (A.grading_internal.ofBijective_coeLinearMap_of_mem ha)

theorem gradeComponent_of_mem_ne {d e : ℕ} (hde : e ≠ d) {a : V}
    (ha : a ∈ A.grade e) : A.gradeComponent d a = 0 := by
  exact congrArg Subtype.val
    (A.grading_internal.ofBijective_coeLinearMap_of_mem_ne hde ha)

 
def gradeSupport (a : V) : Finset ℕ := by
  classical
  exact (A.gradingEquiv a).support

 
theorem sum_gradeComponents (a : V) :
    ∑ d ∈ A.gradeSupport a, A.gradeComponent d a = a := by
  classical
  change ∑ d ∈ (A.gradingEquiv a).support, A.gradeComponent d a = a
  calc
    _ = DirectSum.coeLinearMap A.grade
        (∑ d ∈ (A.gradingEquiv a).support,
          DirectSum.of (fun d => A.grade d) d (A.gradingEquiv a d)) := by
      simp only [map_sum, DirectSum.coeLinearMap_of, gradeComponent_apply]
    _ = DirectSum.coeLinearMap A.grade (A.gradingEquiv a) := by
      rw [DirectSum.sum_support_of]
    _ = a := (LinearEquiv.ofBijective (DirectSum.coeLinearMap A.grade)
      A.grading_internal).apply_symm_apply a

 

theorem homogeneous_induction {P : V → Prop} (h0 : P 0)
    (hh : ∀ d : ℕ, ∀ a ∈ A.grade d, P a)
    (hadd : ∀ a b : V, P a → P b → P (a + b)) (a : V) : P a := by
  let : DirectSum.Decomposition A.grade := A.grading_internal.chooseDecomposition
  exact DirectSum.Decomposition.inductionOn A.grade h0
    (fun {d} x => hh d x x.property) hadd a

 
theorem virasoro_commutator (m n : ℤ) (a : V) :
    A.virasoroMode m (A.virasoroMode n a) -
      A.virasoroMode n (A.virasoroMode m a) =
    ((m - n : ℤ) : ℂ) • A.virasoroMode (m + n) a +
      (if m + n = 0 then (A.centralCharge / 12) * ((m : ℂ)^3 - m) else 0) • a := by
  have h := congrArg (fun T : Module.End ℂ V => T a) (A.virasoro m n)
  simpa only [virasoroMode, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply] using h

 
theorem virasoro_vacuum (m : ℤ) (hm : -1 ≤ m) :
    A.virasoroMode m A.vacuum = 0 := by
  exact A.creation_truncation A.conformalVector (m + 1) (by omega)

 
theorem conformal_eq_virasoro_vacuum :
    A.conformalVector = A.virasoroMode (-2) A.vacuum := by
  exact (A.creation A.conformalVector).symm

 
theorem conformal_quasiPrimary : A.IsQuasiPrimary A.conformalVector := by
  have h := A.virasoro_commutator 1 (-2) A.vacuum
  have h₁ := A.virasoro_vacuum 1 (by omega)
  have h₂ := A.virasoro_vacuum (-1) (by omega)
  norm_num at h
  rw [h₁, map_zero, sub_zero, h₂, smul_zero] at h
  simpa only [IsQuasiPrimary, A.conformal_eq_virasoro_vacuum] using h

 
theorem virasoro_two_conformal :
    A.virasoroMode 2 A.conformalVector = (A.centralCharge / 2) • A.vacuum := by
  have h := A.virasoro_commutator 2 (-2) A.vacuum
  have h₂ := A.virasoro_vacuum 2 (by omega)
  have h₀ := A.virasoro_vacuum 0 (by omega)
  norm_num at h
  rw [h₂, map_zero, sub_zero, h₀, smul_zero, zero_add] at h
  rw [← A.conformal_eq_virasoro_vacuum] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

 
theorem physicalMode_conformal (m : ℤ) :
    A.physicalMode A.conformalVector 2 m = A.virasoroMode m := by
  unfold physicalMode virasoroMode
  congr 1
  omega

 
theorem virasoro_zero_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    A.virasoroMode 0 a = (d : ℂ) • a := A.conformal_energy d a ha

 
theorem gradeComponent_energy (d : ℕ) (a : V) :
    A.gradeComponent d (A.virasoroMode 0 a) = (d : ℂ) • A.gradeComponent d a := by
  apply A.homogeneous_induction (P := fun a =>
    A.gradeComponent d (A.virasoroMode 0 a) = (d : ℂ) • A.gradeComponent d a)
  · simp
  · intro e b hb
    rw [A.virasoro_zero_on_grade hb, map_smul]
    by_cases he : e = d
    · subst e
      rfl
    · rw [A.gradeComponent_of_mem_ne he hb]
      simp
  · intro b c hb hc
    simp only [map_add, smul_add, hb, hc]

 
theorem gradeComponent_eigenvalue {a : V} {z : ℂ}
    (ha : A.virasoroMode 0 a = z • a) (d : ℕ) (hd : (d : ℂ) ≠ z) :
    A.gradeComponent d a = 0 := by
  have h := congrArg (A.gradeComponent d) ha
  rw [A.gradeComponent_energy, map_smul] at h
  have h' : ((d : ℂ) - z) • A.gradeComponent d a = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hd)

 
theorem mem_grade_of_energy {d : ℕ} {a : V}
    (ha : A.virasoroMode 0 a = (d : ℂ) • a) : a ∈ A.grade d := by
  classical
  rw [← A.sum_gradeComponents a]
  apply Submodule.sum_mem
  intro e _
  by_cases he : e = d
  · subst e
    exact A.gradeComponent_mem d a
  · rw [A.gradeComponent_eigenvalue ha e (by exact_mod_cast he)]
    exact (A.grade d).zero_mem

 
theorem eq_zero_of_energy_not_grade {a : V} {z : ℂ}
    (ha : A.virasoroMode 0 a = z • a) (hz : ∀ d : ℕ, (d : ℂ) ≠ z) : a = 0 := by
  classical
  rw [← A.sum_gradeComponents a]
  apply Finset.sum_eq_zero
  intro d _
  exact A.gradeComponent_eigenvalue ha d (hz d)

 

theorem energy_mode_commutator_general (a : V) (n : ℤ) (b : V) :
    A.virasoroMode 0 (mode A.fields a n b) -
      mode A.fields a n (A.virasoroMode 0 b) =
        (-((n : ℂ) + 1)) • mode A.fields a n b +
          mode A.fields (A.virasoroMode 0 a) n b := by
  classical
  have h := A.toVertexAlgebra.mode_commutator A.conformalVector a b 1 n
  have hz (j : ℕ) (hj : 2 ≤ j) : Ring.choose (1 : ℂ) j = 0 := by
    rw [← Nat.cast_one, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 2) (by
    intro j hj
    by_contra hj'
    have hj'' : 2 ≤ j := by
      simp only [Finset.mem_coe, Finset.mem_range] at hj'
      omega
    exact hj (by simp [hz j hj'']))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one, Ring.choose_zero_right, Ring.choose_one_right,
    one_smul, Int.sub_zero] at h
  rw [A.conformal_translation, A.translation_covariance] at h
  simp only [LinearMap.smul_apply] at h
  have hi : 1 + n - 1 = n := by omega
  simp only [hi, Int.cast_one, one_smul, Int.cast_add] at h
  convert h using 1
  · rfl
  · simp only [virasoroMode, zero_add, add_comm]

 

theorem energy_mode_commutator {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    (n : ℤ) (b : V) :
    A.virasoroMode 0 (mode A.fields a n b) -
      mode A.fields a n (A.virasoroMode 0 b) =
        ((d : ℂ) - n - 1) • mode A.fields a n b := by
  rw [A.energy_mode_commutator_general, A.virasoro_zero_on_grade ha,
    mode_smul, LinearMap.smul_apply, ← add_smul]
  congr 1
  ring

 

theorem energy_preserves_c2 :
    A.toVertexAlgebra.c2 ≤ (A.toVertexAlgebra.c2).comap (A.virasoroMode 0) := by
  intro x hx
  change A.virasoroMode 0 x ∈ A.toVertexAlgebra.c2
  refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
    (fun z x _ hx => ?_) hx
  · obtain ⟨a, b, rfl⟩ := hx
    have he := A.energy_mode_commutator_general a (-2) b
    rw [sub_eq_iff_eq_add] at he
    rw [he]
    exact (A.toVertexAlgebra.c2).add_mem
      ((A.toVertexAlgebra.c2).add_mem
        ((A.toVertexAlgebra.c2).smul_mem _ (A.mode_neg_two_mem_c2 a b))
        (A.mode_neg_two_mem_c2 _ b)) (A.mode_neg_two_mem_c2 a _)
  · simp
  · simpa only [map_add] using (A.toVertexAlgebra.c2).add_mem hx hy
  · simpa only [map_smul] using (A.toVertexAlgebra.c2).smul_mem z hx

 
def c2Energy : Module.End ℂ (V ⧸ A.toVertexAlgebra.c2) :=
  (A.toVertexAlgebra.c2).mapQ A.toVertexAlgebra.c2
    (A.virasoroMode 0) A.energy_preserves_c2

 

theorem exists_c2_weight_cutoff (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ d : ℕ, D < d → A.grade d ≤ A.toVertexAlgebra.c2 := by
  let : FiniteDimensional ℂ (V ⧸ A.toVertexAlgebra.c2) := hc
  have hs : Set.Finite {d : ℕ | A.c2Energy.HasEigenvalue (d : ℂ)} :=
    A.c2Energy.finite_hasEigenvalue.preimage (by
      intro d _ e _ h
      exact_mod_cast h)
  obtain ⟨D, hD⟩ := hs.bddAbove
  refine ⟨max 2 D, le_max_left _ _, fun d hd a ha => ?_⟩
  by_contra hn
  have hq : (A.toVertexAlgebra.c2).mkQ a ≠ 0 := by
    simpa only [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hn
  have he : A.c2Energy.HasEigenvalue (d : ℂ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hq⟩
    rw [Module.End.mem_eigenspace_iff]
    change (A.toVertexAlgebra.c2).mkQ (A.virasoroMode 0 a) =
      (d : ℂ) • (A.toVertexAlgebra.c2).mkQ a
    rw [A.virasoro_zero_on_grade ha, map_smul]
  have hb : d ≤ D := hD he
  omega

 

theorem mode_energy_eigenvalue {d e : ℕ} {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (n : ℤ) :
    A.virasoroMode 0 (mode A.fields a n b) =
      ((e : ℂ) + d - n - 1) • mode A.fields a n b := by
  have h := A.energy_mode_commutator ha n b
  rw [A.virasoro_zero_on_grade hb, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← add_smul]
  congr 1
  ring

 

theorem mode_mem_grade {d e k : ℕ} {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (n : ℤ)
    (hk : (k : ℤ) = e + d - n - 1) : mode A.fields a n b ∈ A.grade k := by
  apply A.mem_grade_of_energy
  rw [A.mode_energy_eigenvalue ha hb]
  congr 1
  exact_mod_cast hk.symm

 

theorem mode_eq_zero_of_negative_energy {d e : ℕ} {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (n : ℤ)
    (hn : (e : ℤ) + d - n - 1 < 0) : mode A.fields a n b = 0 := by
  apply A.eq_zero_of_energy_not_grade (A.mode_energy_eigenvalue ha hb n)
  intro k h
  have hh : (k : ℤ) = (e : ℤ) + d - n - 1 := by exact_mod_cast h
  omega

 

theorem physical_normal_product_resplit (a b c : V) (d e : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    A.physicalMode (mode A.fields a (-1) b) (d + e) m c =
      (∑ᶠ j : ℕ, A.physicalMode a d (-1 - j)
        (A.physicalMode b e (m + 1 + j) c)) +
      (∑ᶠ j : ℕ, A.physicalMode b e (m - j)
        (A.physicalMode a d j c)) -
      ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℂ) • mode A.fields (mode A.fields a j b)
          (m + d + e - 2 - j) c := by
  have h := A.mode_normal_product_resplit a b c (m + d + e - 1) (d - 1)
  simp only [Nat.cast_sub hd, Nat.cast_one] at h
  simp_rw [A.mode_commutator_nat] at h
  have E₁ (j : ℕ) : (d : ℤ) - 1 - 1 - j = -1 - j + d - 1 := by omega
  have E₂ (j : ℕ) : m + d + e - 1 - ((d : ℤ) - 1) + j = m + 1 + j + e - 1 := by omega
  have E₃ (j : ℕ) : m + d + e - 1 - 1 - ((d : ℤ) - 1) - j = m - j + e - 1 := by omega
  have E₄ (j : ℕ) : (d : ℤ) - 1 + j = (j : ℤ) + d - 1 := by omega
  have E₅ (i j : ℕ) : (i : ℤ) + (m + d + e - 1 - 1 - i) - j = m + d + e - 2 - j := by omega
  simp_rw [E₁, E₂, E₃, E₄, E₅] at h
  simpa only [physicalMode, Nat.cast_add, ← add_assoc] using h

 

theorem physical_normal_product_on_grade {a b c : V} {d e h : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hc : c ∈ A.grade h)
    (hd : 1 ≤ d) (k : ℕ) :
    A.physicalMode (mode A.fields a (-1) b) (d + e) ((h : ℤ) - k) c =
      (∑ j ∈ Finset.range k, A.physicalMode a d (-1 - j)
        (A.physicalMode b e ((h : ℤ) - k + 1 + j) c)) +
      (∑ j ∈ Finset.range (h + 1), A.physicalMode b e ((h : ℤ) - k - j)
        (A.physicalMode a d j c)) -
      ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℂ) • mode A.fields (mode A.fields a j b)
          ((h : ℤ) - k + d + e - 2 - j) c := by
  classical
  rw [A.physical_normal_product_resplit a b c d e hd ((h : ℤ) - k)]
  have hL : Function.support (fun j : ℕ => A.physicalMode a d (-1 - j)
      (A.physicalMode b e ((h : ℤ) - k + 1 + j) c)) ⊆
      (Finset.range k : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra he
    apply hj
    change A.physicalMode a d (-1 - j) (mode A.fields b _ c) = 0
    rw [A.mode_eq_zero_of_negative_energy hb hc _ (by omega), map_zero]
  have hR : Function.support (fun j : ℕ => A.physicalMode b e ((h : ℤ) - k - j)
      (A.physicalMode a d j c)) ⊆ (Finset.range (h + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra he
    apply hj
    change A.physicalMode b e ((h : ℤ) - k - j) (mode A.fields a _ c) = 0
    rw [A.mode_eq_zero_of_negative_energy ha hc _ (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hR]

 

def homogeneousC2 (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ (e f : ℕ) (a b : V),
    a ∈ A.grade e ∧ b ∈ A.grade f ∧ e + f + 1 = d ∧
      x = mode A.fields a (-2) b}

 

theorem gradeComponent_c2Product_mem (d : ℕ) (a b : V) :
    A.gradeComponent d (mode A.fields a (-2) b) ∈ A.homogeneousC2 d := by
  revert b
  refine A.homogeneous_induction
    (P := fun a => ∀ b : V,
      A.gradeComponent d (mode A.fields a (-2) b) ∈ A.homogeneousC2 d) ?_ ?_ ?_ a
  · intro b
    simp
  · intro e a ha b
    refine A.homogeneous_induction
      (P := fun b => A.gradeComponent d (mode A.fields a (-2) b) ∈ A.homogeneousC2 d)
      ?_ ?_ ?_ b
    · simp
    · intro f b hb
      have hg : mode A.fields a (-2) b ∈ A.grade (e + f + 1) :=
        A.mode_mem_grade ha hb (-2) (by omega)
      by_cases he : e + f + 1 = d
      · rw [A.gradeComponent_of_mem (he ▸ hg)]
        exact Submodule.subset_span ⟨e, f, a, b, ha, hb, he, rfl⟩
      · rw [A.gradeComponent_of_mem_ne he hg]
        exact (A.homogeneousC2 d).zero_mem
    · intro b c hb hc
      simpa only [map_add] using (A.homogeneousC2 d).add_mem hb hc
  · intro a a' ha ha' b
    simpa only [mode_add, LinearMap.add_apply, map_add] using
      (A.homogeneousC2 d).add_mem (ha b) (ha' b)
end CFTTypeVOA
end Algebraic
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GradeComponentC
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
section Algebraic
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
namespace CFTTypeVOA
variable (A : CFTTypeVOA V)
theorem gradeComponent_c2_mem (d : ℕ) {a : V} (ha : a ∈ A.toVertexAlgebra.c2) :
    A.gradeComponent d a ∈ A.homogeneousC2 d := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    exact A.gradeComponent_c2Product_mem d a b
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add] using (A.homogeneousC2 d).add_mem hx hy
  | smul z x _ hx =>
    simpa only [map_smul] using (A.homogeneousC2 d).smul_mem z hx

 

theorem homogeneousC2_eq (d : ℕ) :
    A.homogeneousC2 d = A.toVertexAlgebra.c2 ⊓ A.grade d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨e, f, a, b, ha, hb, he, rfl⟩
    exact ⟨A.mode_neg_two_mem_c2 a b,
      A.mode_mem_grade ha hb (-2) (by omega)⟩
  · intro a ha
    simpa only [A.gradeComponent_of_mem ha.2] using A.gradeComponent_c2_mem d ha.1



theorem virasoro_mem_grade {e k : ℕ} {b : V} (hb : b ∈ A.grade e)
    (m : ℤ) (hk : (k : ℤ) = e - m) : A.virasoroMode m b ∈ A.grade k := by
  apply A.mode_mem_grade A.conformal_mem hb (m + 1)
  omega

 
theorem virasoro_eq_zero_of_lt {e : ℕ} {b : V} (hb : b ∈ A.grade e)
    (m : ℤ) (hm : (e : ℤ) < m) : A.virasoroMode m b = 0 := by
  apply A.mode_eq_zero_of_negative_energy A.conformal_mem hb (m + 1)
  omega

 

theorem virasoro_neg_one_eq_translation :
    A.virasoroMode (-1) = A.toVertexAlgebra.translation := by
  exact A.conformal_translation



theorem energyShift_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    A.energyShift a = (1 + (d : ℂ)) • a := by
  simp only [energyShift, LinearMap.add_apply, Module.End.one_apply,
    A.virasoro_zero_on_grade ha, add_smul, one_smul]

 
theorem energyShift_pow_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) (k : ℕ) :
    (A.energyShift ^ k) a = (1 + (d : ℂ)) ^ k • a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, A.energyShift_on_grade ha,
      map_smul, ih, smul_smul, pow_succ]
    congr 1
    ring

 
def IsPrimary (a : V) : Prop := ∀ n : ℕ, 0 < n → A.virasoroMode n a = 0



end CFTTypeVOA

end Algebraic



namespace CFTTypeVOA

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)



theorem energyShift_pow_norm_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) (k : ℕ) :
    ‖(A.energyShift ^ k) a‖ = (1 + (d : ℝ)) ^ k * ‖a‖ := by
  rw [A.energyShift_pow_on_grade ha, norm_smul, norm_pow]
  congr 2
  have h : (1 + (d : ℂ)) = ((1 + (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

 

def modeBlock (a : V) (d h k : ℕ) : A.grade h →L[ℂ] V := by
  let := A.grade_finite h
  exact LinearMap.toContinuousLinearMap
    ((A.physicalMode a d ((h : ℤ) - k)).domRestrict (A.grade h))

@[simp]
theorem modeBlock_apply (a : V) (d h k : ℕ) (c : A.grade h) :
    A.modeBlock a d h k c = A.physicalMode a d ((h : ℤ) - k) c := rfl

 

def BlockControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ h ≤ N, ∀ k ≤ N, ∀ c ∈ A.grade h,
    ‖A.physicalMode a d ((h : ℤ) - k) c‖ ≤ K * ‖c‖

theorem blockControl_mono {a : V} {d N : ℕ} {K L : ℝ}
    (H : A.BlockControl a d N K) (hKL : K ≤ L) : A.BlockControl a d N L := by
  intro h hh k hk c hc
  exact (H h hh k hk c hc).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))

theorem blockControl_zero (d N : ℕ) : A.BlockControl 0 d N 0 := by
  intro h hh k hk c hc
  simp [physicalMode]

theorem blockControl_add {a b : V} {d N : ℕ} {K L : ℝ}
    (ha : A.BlockControl a d N K) (hb : A.BlockControl b d N L) :
    A.BlockControl (a + b) d N (K + L) := by
  intro h hh k hk c hc
  change ‖(mode A.fields (a + b) _) c‖ ≤ _
  rw [mode_add, LinearMap.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (ha h hh k hk c hc) (hb h hh k hk c hc))

theorem blockControl_smul {a : V} {d N : ℕ} {K : ℝ}
    (ha : A.BlockControl a d N K) (z : ℂ) :
    A.BlockControl (z • a) d N (‖z‖ * K) := by
  intro h hh k hk c hc
  change ‖(mode A.fields (z • a) _) c‖ ≤ _
  rw [mode_smul, LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (ha h hh k hk c hc) (norm_nonneg _)

 

def correctionMass (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)

theorem correctionMass_nonneg (d : ℕ) : 0 ≤ correctionMass d := by
  unfold correctionMass
  positivity

 

theorem normalProduct_blockControl {a b : V} {d e N : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    {K L R : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : A.BlockControl a d N K) (Hb : A.BlockControl b e N L)
    (Hsing : ∀ j < d - 1, A.BlockControl (mode A.fields a j b) (d + e - j - 1) N R) :
    A.BlockControl (mode A.fields a (-1) b) (d + e) N
      (((2 : ℝ) * N + 1) * K * L + correctionMass d * R) := by
  classical
  intro h hh k hk c hc
  let f : ℕ → V := fun j => A.physicalMode a d (-1 - j)
    (A.physicalMode b e ((h : ℤ) - k + 1 + j) c)
  let g : ℕ → V := fun j => A.physicalMode b e ((h : ℤ) - k - j)
    (A.physicalMode a d j c)
  let r : ℕ → ℕ → V := fun i j => (i.choose j : ℂ) •
    mode A.fields (mode A.fields a j b) ((h : ℤ) - k + d + e - 2 - j) c
  have hf (j : ℕ) (hj : j ∈ Finset.range k) : ‖f j‖ ≤ K * L * ‖c‖ := by
    simp only [Finset.mem_range] at hj
    let l := k - 1 - j
    have hl : l ≤ N := by dsimp [l]; omega
    have hidx : (h : ℤ) - l = (h : ℤ) - k + 1 + j := by dsimp [l]; omega
    have hidx' : (l : ℤ) - k = -1 - j := by dsimp [l]; omega
    have hx : A.physicalMode b e ((h : ℤ) - k + 1 + j) c ∈ A.grade l :=
      A.mode_mem_grade hb hc _ (by dsimp [l]; omega)
    have H₁ := Ha l hl k hk _ hx
    have H₂ := Hb h hh l hl c hc
    rw [hidx'] at H₁
    rw [hidx] at H₂
    calc
      ‖f j‖ ≤ K * ‖A.physicalMode b e ((h : ℤ) - k + 1 + j) c‖ := H₁
      _ ≤ K * (L * ‖c‖) := mul_le_mul_of_nonneg_left H₂ hK
      _ = _ := by ring
  have hg (j : ℕ) (hj : j ∈ Finset.range (h + 1)) : ‖g j‖ ≤ K * L * ‖c‖ := by
    simp only [Finset.mem_range] at hj
    let l := h - j
    have hl : l ≤ N := by dsimp [l]; omega
    have hidx : (h : ℤ) - l = j := by dsimp [l]; omega
    have hidx' : (l : ℤ) - k = (h : ℤ) - k - j := by dsimp [l]; omega
    have hx : A.physicalMode a d j c ∈ A.grade l :=
      A.mode_mem_grade ha hc _ (by dsimp [l]; omega)
    have H₁ := Hb l hl k hk _ hx
    have H₂ := Ha h hh l hl c hc
    rw [hidx'] at H₁
    rw [hidx] at H₂
    calc
      ‖g j‖ ≤ L * ‖A.physicalMode a d j c‖ := H₁
      _ ≤ L * (K * ‖c‖) := mul_le_mul_of_nonneg_left H₂ hL
      _ = _ := by ring
  have hr (i : ℕ) (hi : i ∈ Finset.range (d - 1))
      (j : ℕ) (hj : j ∈ Finset.range (i + 1)) : ‖r i j‖ ≤ (i.choose j : ℝ) * R * ‖c‖ := by
    simp only [Finset.mem_range] at hi hj
    have hjs : j < d - 1 := by omega
    have H := Hsing j hjs h hh k hk c hc
    have he : (h : ℤ) - k + (d + e - j - 1 : ℕ) - 1 =
        (h : ℤ) - k + d + e - 2 - j := by omega
    simp only [physicalMode, he] at H
    dsimp only [r]
    rw [norm_smul, Complex.norm_natCast, mul_assoc]
    exact mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _)
  have hfs : ‖∑ j ∈ Finset.range k, f j‖ ≤ (k : ℝ) * (K * L * ‖c‖) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      norm_sum_le_of_le (Finset.range k) hf
  have hgs : ‖∑ j ∈ Finset.range (h + 1), g j‖ ≤ ((h : ℝ) + 1) * (K * L * ‖c‖) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
      norm_sum_le_of_le (Finset.range (h + 1)) hg
  have hrs : ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j‖ ≤
      correctionMass d * R * ‖c‖ := by
    have H := norm_sum_le_of_le (Finset.range (d - 1)) (fun i hi =>
      norm_sum_le_of_le (Finset.range (i + 1)) (hr i hi))
    simpa only [correctionMass, Finset.sum_mul] using H
  rw [A.physical_normal_product_on_grade ha hb hc hd k]
  change ‖(∑ j ∈ Finset.range k, f j) + (∑ j ∈ Finset.range (h + 1), g j) -
    (∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j)‖ ≤ _
  calc
    _ ≤ ‖∑ j ∈ Finset.range k, f j‖ + ‖∑ j ∈ Finset.range (h + 1), g j‖ +
        ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (k : ℝ) * (K * L * ‖c‖) + ((h : ℝ) + 1) * (K * L * ‖c‖) +
        correctionMass d * R * ‖c‖ := add_le_add (add_le_add hfs hgs) hrs
    _ = ((h : ℝ) + k + 1) * (K * L * ‖c‖) + correctionMass d * R * ‖c‖ := by ring
    _ ≤ ((2 : ℝ) * N + 1) * (K * L * ‖c‖) + correctionMass d * R * ‖c‖ := by
      have hcount : (h : ℝ) + k + 1 ≤ (2 : ℝ) * N + 1 := by
        exact_mod_cast (show h + k + 1 ≤ 2 * N + 1 by omega)
      gcongr
    _ = _ := by ring
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BlockGrowth
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
def BlockGrowth (B : ℕ → ℝ) (a : V) (d w : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N,
    A.BlockControl a d N (C * (1 + (N : ℝ)) ^ p * B N ^ w)

theorem blockGrowth_zero (B : ℕ → ℝ) (d w : ℕ) : A.BlockGrowth B 0 d w := by
  refine ⟨0, le_rfl, 0, ?_⟩
  intro N
  simpa only [zero_mul] using A.blockControl_zero d N

theorem blockGrowth_add {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N) {a b : V} {d w : ℕ}
    (ha : A.BlockGrowth B a d w) (hb : A.BlockGrowth B b d w) :
    A.BlockGrowth B (a + b) d w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  obtain ⟨D, hD, q, hq⟩ := hb
  refine ⟨C + D, add_nonneg hC hD, p + q, fun N => ?_⟩
  apply A.blockControl_mono (A.blockControl_add (hp N) (hq N))
  have hBN : 0 ≤ B N := (zero_le_one.trans (hB N))
  have hNp : (1 + (N : ℝ)) ^ p ≤ (1 + (N : ℝ)) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  have hNq : (1 + (N : ℝ)) ^ q ≤ (1 + (N : ℝ)) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  calc
    _ ≤ C * (1 + (N : ℝ)) ^ (p + q) * B N ^ w +
        D * (1 + (N : ℝ)) ^ (p + q) * B N ^ w := by gcongr
    _ = _ := by ring

theorem blockGrowth_smul {B : ℕ → ℝ} {a : V} {d w : ℕ}
    (ha : A.BlockGrowth B a d w) (z : ℂ) : A.BlockGrowth B (z • a) d w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg _) hC, p, fun N => ?_⟩
  simpa only [mul_assoc] using A.blockControl_smul (hp N) z

theorem blockGrowth_mono_weight {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d w w' : ℕ} (ha : A.BlockGrowth B a d w) (hw : w ≤ w') :
    A.BlockGrowth B a d w' := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨C, hC, p, fun N => ?_⟩
  apply A.blockControl_mono (hp N)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB N) hw) (by positivity)

 

theorem translation_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d w : ℕ} (ha : A.BlockGrowth B a d w) :
    A.BlockGrowth B (A.toVertexAlgebra.translation a) (d + 1) w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨((d : ℝ) + 2) * C, by positivity, p + 1, ?_⟩
  intro N h hh k hk c hc
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have he (m : ℤ) : A.physicalMode (A.toVertexAlgebra.translation a) (d + 1) m =
      (-(m + (d : ℤ) : ℤ) : ℂ) • A.physicalMode a d m := by
    simp only [physicalMode, Nat.cast_add, Nat.cast_one]
    rw [show m + ((d : ℤ) + 1) - 1 = m + d by omega, A.translation_covariance]
  rw [he, LinearMap.smul_apply, norm_smul]
  have hcoef : ‖(-((h : ℤ) - k + d) : ℤ)‖ ≤ ((d : ℝ) + 2) * (1 + (N : ℝ)) := by
    simp only [Int.norm_eq_abs, Int.cast_neg, Int.cast_add, Int.cast_sub, Int.cast_natCast, abs_neg]
    rw [abs_le]
    constructor <;> nlinarith [show (h : ℝ) ≤ N by exact_mod_cast hh,
      show (k : ℝ) ≤ N by exact_mod_cast hk, Nat.cast_nonneg (α := ℝ) h,
      Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) d,
      Nat.cast_nonneg (α := ℝ) N]
  have hcoef' : ‖(-(((h : ℤ) - k + d : ℤ) : ℂ))‖ ≤ ((d : ℝ) + 2) * (1 + (N : ℝ)) := by
    simpa only [norm_neg, Complex.norm_intCast, Int.norm_eq_abs, Int.cast_neg, abs_neg] using hcoef
  calc
    _ ≤ (((d : ℝ) + 2) * (1 + (N : ℝ))) *
        (C * (1 + (N : ℝ)) ^ p * B N ^ w * ‖c‖) := by
      exact mul_le_mul hcoef' (hp N h hh k hk c hc) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

 

theorem finite_blockGrowth_uniform {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {ι : Type*} (s : Finset ι) (a : ι → V) (d w : ι → ℕ)
    (hg : ∀ i ∈ s, A.BlockGrowth B (a i) (d i) (w i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i ∈ s, ∀ N,
      A.BlockControl (a i) (d i) N (C * (1 + (N : ℝ)) ^ p * B N ^ w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, p, hp⟩ := hg i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, q, hq⟩ := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, p + q, ?_⟩
    intro j hj N
    have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
    have hNp : (1 + (N : ℝ)) ^ p ≤ (1 + (N : ℝ)) ^ (p + q) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    have hNq : (1 + (N : ℝ)) ^ q ≤ (1 + (N : ℝ)) ^ (p + q) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply A.blockControl_mono (hp N)
      gcongr
      exact le_add_of_nonneg_right hD
    · apply A.blockControl_mono (hq j hj N)
      gcongr
      exact le_add_of_nonneg_left hC

 

theorem normalProduct_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (Ha : A.BlockGrowth B a d d) (Hb : A.BlockGrowth B b e e)
    (Hsing : ∀ j < d - 1,
      A.BlockGrowth B (mode A.fields a j b) (d + e - j - 1) (d + e - j - 1)) :
    A.BlockGrowth B (mode A.fields a (-1) b) (d + e) (d + e) := by
  classical
  obtain ⟨C, hC, p, hp⟩ := Ha
  obtain ⟨D, hD, q, hq⟩ := Hb
  have hsG : ∀ j ∈ Finset.range (d - 1),
      A.BlockGrowth B (mode A.fields a j b) (d + e - j - 1) (d + e) := by
    intro j hj
    exact A.blockGrowth_mono_weight hB (Hsing j (Finset.mem_range.mp hj)) (by omega)
  obtain ⟨R, hR, s, hs⟩ := A.finite_blockGrowth_uniform hB (Finset.range (d - 1))
    (fun j => mode A.fields a j b) (fun j => d + e - j - 1) (fun _ => d + e) hsG
  refine ⟨2 * C * D + correctionMass d * R,
    add_nonneg (by positivity) (mul_nonneg (correctionMass_nonneg d) hR), p + q + s + 1, ?_⟩
  intro N
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hmass := correctionMass_nonneg d
  apply A.blockControl_mono (A.normalProduct_blockControl ha hb hd
    (by positivity) (by positivity) (hp N) (hq N)
    (fun j hj => hs j (Finset.mem_range.mpr hj) N))
  have hpow₁ : (1 + (N : ℝ)) ^ (p + q + 1) ≤ (1 + (N : ℝ)) ^ (p + q + s + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  have hpow₂ : (1 + (N : ℝ)) ^ s ≤ (1 + (N : ℝ)) ^ (p + q + s + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  calc
    _ = ((2 : ℝ) * N + 1) * (C * D * (1 + (N : ℝ)) ^ (p + q) * B N ^ (d + e)) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B N ^ (d + e) := by
      simp only [pow_add]
      ring
    _ ≤ (2 * (1 + (N : ℝ))) * (C * D * (1 + (N : ℝ)) ^ (p + q) * B N ^ (d + e)) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B N ^ (d + e) := by
      gcongr
      linarith
    _ = 2 * C * D * (1 + (N : ℝ)) ^ (p + q + 1) * B N ^ (d + e) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B N ^ (d + e) := by
      rw [pow_succ]
      ring
    _ ≤ 2 * C * D * (1 + (N : ℝ)) ^ (p + q + s + 1) * B N ^ (d + e) +
        correctionMass d * R * (1 + (N : ℝ)) ^ (p + q + s + 1) * B N ^ (d + e) := by
      gcongr
    _ = _ := by ring

 

def blockGrowthSubmodule (B : ℕ → ℝ) (hB : ∀ N, 1 ≤ B N) (d w : ℕ) : Submodule ℂ V where
  carrier := {a | A.BlockGrowth B a d w}
  zero_mem' := A.blockGrowth_zero B d w
  add_mem' := A.blockGrowth_add hB
  smul_mem' z _ h := A.blockGrowth_smul h z

 
theorem vacuum_blockGrowth (B : ℕ → ℝ) : A.BlockGrowth B A.vacuum 0 0 := by
  refine ⟨1, zero_le_one, 0, fun N h hh k hk c hc => ?_⟩
  simp only [physicalMode, Nat.cast_zero, add_zero, A.vacuum_mode, pow_zero, mul_one, one_mul]
  split_ifs <;> simp

 

theorem homogeneousC2_le_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N) (w : ℕ)
    (hprev : ∀ d < w, ∀ a ∈ A.grade d, A.BlockGrowth B a d d) :
    A.homogeneousC2 w ≤ A.blockGrowthSubmodule B hB w w := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, e, a, b, ha, hb, hweight, rfl⟩
  change A.BlockGrowth B (mode A.fields a (-2) b) w w
  by_cases he : e = 0
  · subst e
    have hweight' : w = d + 1 := by omega
    rw [A.grade_zero] at hb
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul]
    have H := A.translation_blockGrowth hB (hprev d (by omega) a ha)
    have H' := A.blockGrowth_mono_weight hB H (show d ≤ w by omega)
    rw [hweight'] at H' ⊢
    exact A.blockGrowth_smul H' z
  · have hepos : 1 ≤ e := by omega
    have hTgrade : A.toVertexAlgebra.translation a ∈ A.grade (d + 1) := by
      rw [← A.virasoro_neg_one_eq_translation]
      exact A.virasoro_mem_grade ha (-1) (by omega)
    have hT := hprev (d + 1) (by omega) (A.toVertexAlgebra.translation a) hTgrade
    have hB' := hprev e (by omega) b hb
    have hsing : ∀ j < (d + 1) - 1,
        A.BlockGrowth B (mode A.fields (A.toVertexAlgebra.translation a) j b)
          (d + 1 + e - j - 1) (d + 1 + e - j - 1) := by
      intro j hj
      apply hprev _ (by omega)
      exact A.mode_mem_grade hTgrade hb j (by omega)
    have H := A.normalProduct_blockGrowth hB hTgrade hb (by omega) hT hB' hsing
    have heq : mode A.fields (A.toVertexAlgebra.translation a) (-1) b =
        mode A.fields a (-2) b := by
      rw [A.translation_covariance]
      norm_num
    rw [heq, show d + 1 + e = w by omega] at H
    exact H

 

theorem zeroMode_commutator {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (c : V) :
    A.virasoroMode 1 (A.physicalMode a d (-1) c) -
      A.physicalMode a d (-1) (A.virasoroMode 1 c) =
        (d : ℂ) • A.physicalMode a d 0 c := by
  have h := A.mode_commutator_nat A.conformalVector a c 2 ((d : ℤ) - 2)
  have hν0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a := by
    rw [A.conformal_translation]
  have hν1 : mode A.fields A.conformalVector 1 a = (d : ℂ) • a :=
    A.virasoro_zero_on_grade ha
  have hν2 : mode A.fields A.conformalVector 2 a = 0 := hq
  have ht := congrArg (fun f : Module.End ℂ V => f c) (A.translation_covariance a (d : ℤ))
  simp only [LinearMap.smul_apply] at ht
  norm_num [Finset.sum_range_succ, hν0, hν1, hν2, mode_zero, mode_smul] at h
  simp only [ht, Int.cast_natCast] at h
  change mode A.fields A.conformalVector 2 (mode A.fields a (-1 + (d : ℤ) - 1) c) -
      mode A.fields a (-1 + (d : ℤ) - 1) (mode A.fields A.conformalVector 2 c) =
        (d : ℂ) • mode A.fields a (0 + (d : ℤ) - 1) c
  rw [show -1 + (d : ℤ) - 1 = d - 2 by omega, zero_add]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  module

 
def selfCommutator (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ V :=
  A.physicalMode a d m * A.physicalMode a d (-m) -
    A.physicalMode a d (-m) * A.physicalMode a d m

@[simp]
theorem selfCommutator_apply (a : V) (d : ℕ) (m : ℤ) (c : V) :
    A.selfCommutator a d m c =
      A.physicalMode a d m (A.physicalMode a d (-m) c) -
        A.physicalMode a d (-m) (A.physicalMode a d m c) := rfl

 

theorem selfCommutator_eq_sum {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hd : 1 ≤ d) (m : ℕ) (c : V) :
    A.selfCommutator a d m c =
      ∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
        A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 c := by
  have hm : ((m + d - 1 : ℕ) : ℤ) = (m : ℤ) + d - 1 := by omega
  simp only [selfCommutator_apply, physicalMode]
  rw [← hm, A.mode_commutator]
  simp only [Int.cast_natCast, Ring.choose_natCast]
  have he : (∑ᶠ j : ℕ, ((m + d - 1).choose j : ℂ) •
      mode A.fields (mode A.fields a j a) ((m + d - 1 : ℕ) + (-(m : ℤ) + d - 1) - j) c) =
      ∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
        mode A.fields (mode A.fields a j a) ((m + d - 1 : ℕ) + (-(m : ℤ) + d - 1) - j) c := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hjn
    have hz := A.mode_eq_zero_of_negative_energy ha ha (j : ℤ) (by omega)
    apply hj
    simp only [hz, mode_zero, LinearMap.zero_apply, smul_zero]
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  congr 3
  omega



theorem selfCommutator_bound {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (H : ∀ j < 2 * d, A.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - j - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N m : ℕ, m ≤ N + 1 →
      ∀ h ≤ N, ∀ c ∈ A.grade h,
        ‖A.selfCommutator a d m c‖ ≤
          C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1) * ‖c‖ := by
  let s := Finset.range (2 * d)
  have H' : ∀ j ∈ s, A.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - 1) := by
    intro j hj
    exact A.blockGrowth_mono_weight hB (H j (Finset.mem_range.mp hj)) (by omega)
  obtain ⟨C, hC, p, hp⟩ := A.finite_blockGrowth_uniform hB s
    (fun j => mode A.fields a j a) (fun j => 2 * d - j - 1) (fun _ => 2 * d - 1) H'
  refine ⟨(2 * d : ℝ) * ((d : ℝ) + 1) ^ (2 * d) * C, by positivity, p + 2 * d, ?_⟩
  intro N m hm h hN c hc
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hbase : 1 ≤ ((d : ℝ) + 1) * (1 + (N : ℝ)) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hcoef (j : ℕ) (hj : j < 2 * d) :
      ((m + d - 1).choose j : ℝ) ≤ ((d : ℝ) + 1) ^ (2 * d) * (1 + (N : ℝ)) ^ (2 * d) := by
    have hn : (m + d - 1 : ℕ) ≤ (d + 1) * (N + 1) := by
      calc
        m + d - 1 ≤ m + d := Nat.sub_le _ _
        _ ≤ N + 1 + d := Nat.add_le_add_right hm d
        _ ≤ _ := by nlinarith
    calc
      _ ≤ ((m + d - 1 : ℕ) : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow (m + d - 1) j
      _ ≤ (((d : ℝ) + 1) * (1 + (N : ℝ))) ^ j := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast (show m + d - 1 ≤ (d + 1) * (1 + N) by simpa only [Nat.add_comm] using hn)
      _ ≤ (((d : ℝ) + 1) * (1 + (N : ℝ))) ^ (2 * d) :=
        pow_le_pow_right₀ hbase (by omega)
      _ = _ := mul_pow _ _ _
  rw [A.selfCommutator_eq_sum ha hd]
  calc
    _ ≤ ∑ j ∈ Finset.range (2 * d), ‖((m + d - 1).choose j : ℂ) •
        A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 c‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (2 * d),
        (((d : ℝ) + 1) ^ (2 * d) * (1 + (N : ℝ)) ^ (2 * d)) *
          (C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1) * ‖c‖) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Complex.norm_natCast]
      have hmode := hp j hj N h hN h hN c hc
      simp only [sub_self] at hmode
      exact mul_le_mul (hcoef j (Finset.mem_range.mp hj)) hmode (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rw [pow_add]; ring

 

def generatorMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D + 1), ∑ a ∈ S d,
    ∑ h ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹

theorem one_le_generatorMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ A.generatorMajorant D S N := by
  dsimp [generatorMajorant]
  have : 0 ≤ ∑ d ∈ Finset.range (D + 1), ∑ a ∈ S d,
      ∑ h ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹ := by
    positivity
  linarith

theorem root_modeBlock_le_generatorMajorant (D : ℕ) (S : ℕ → Finset V)
    {d h k N : ℕ} {a : V} (hd : d ≤ D) (ha : a ∈ S d)
    (hh : h ≤ N) (hk : k ≤ N) :
    ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹ ≤ A.generatorMajorant D S N := by
  have H (e : ℕ) (b : V) (i j : ℕ) :
      0 ≤ ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Real.rpow_nonneg (norm_nonneg (A.modeBlock b e i j)) _
  have Hk (e : ℕ) (b : V) (i : ℕ) : 0 ≤
      ∑ j ∈ Finset.range (N + 1), ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun j _ => H e b i j)
  have Hh (e : ℕ) (b : V) : 0 ≤
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun i _ => Hk e b i)
  have Ha (e : ℕ) : 0 ≤ ∑ b ∈ S e,
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ‖A.modeBlock b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun b _ => Hh e b)
  have h₁ := Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
    (fun j _ => H d a h j) (Finset.mem_range.mpr (by omega))
  have h₂ := Finset.single_le_sum (s := Finset.range (N + 1)) (a := h)
    (fun i _ => Hk d a i) (Finset.mem_range.mpr (by omega))
  have h₃ := Finset.single_le_sum (s := S d) (a := a) (fun b _ => Hh d b) ha
  have h₄ := Finset.single_le_sum (s := Finset.range (D + 1)) (a := d)
    (fun e _ => Ha e) (Finset.mem_range.mpr (by omega))
  exact (h₁.trans (h₂.trans (h₃.trans h₄))).trans (le_add_of_nonneg_left zero_le_one)

theorem generator_blockGrowth (D : ℕ) (S : ℕ → Finset V)
    {d : ℕ} {a : V} (hd : 0 < d) (hD : d ≤ D) (ha : a ∈ S d) :
    A.BlockGrowth (A.generatorMajorant D S) a d d := by
  refine ⟨1, zero_le_one, 0, fun N h hh k hk c hc => ?_⟩
  have hnorm := A.root_modeBlock_le_generatorMajorant D S hD ha hh hk
  have ht : 0 ≤ ‖A.modeBlock a d h k‖ ^ (d : ℝ)⁻¹ :=
    Real.rpow_nonneg (norm_nonneg (A.modeBlock a d h k)) _
  have hpow := pow_le_pow_left₀ ht hnorm d
  rw [Real.rpow_inv_natCast_pow (x := ‖A.modeBlock a d h k‖) (n := d)
    (norm_nonneg (A.modeBlock a d h k)) (by omega)] at hpow
  have h := (A.modeBlock a d h k).le_opNorm (⟨c, hc⟩ : A.grade h)
  simpa only [pow_zero, mul_one, one_mul, modeBlock_apply, ← Submodule.norm_coe] using
    h.trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg c))



namespace UnitaryStructure

variable {A} (U : A.UnitaryStructure)

 
def IsHermitian (d : ℕ) (a : V) : Prop := ((-1 : ℂ) ^ d) • U.pct a = a

 
theorem pct_virasoro (a : V) (n : ℤ) :
    U.pct (A.virasoroMode n a) = A.virasoroMode n (U.pct a) := by
  simpa [virasoroMode, U.pct_conformal] using U.pct_modes A.conformalVector a (n + 1)

 
theorem pct_quasiPrimary {a : V} (ha : A.IsQuasiPrimary a) :
    A.IsQuasiPrimary (U.pct a) := by
  change A.virasoroMode 1 (U.pct a) = 0
  rw [← U.pct_virasoro, ha, map_zero]

 

theorem physicalMode_adjoint {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (m : ℤ) (b c : V) :
    inner ℂ (A.physicalMode a d m b) c =
      inner ℂ b (A.physicalMode a d (-m) c) := by
  have hp : A.virasoroMode 1 (U.pct a) = 0 := U.pct_quasiPrimary hq
  have hpj (j : ℕ) (hj : j ≠ 0) :
      (A.virasoroMode 1 ^ j) (U.pct a) = 0 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, hp, map_zero]
  have hs :
      (∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
        mode A.fields ((A.virasoroMode 1 ^ j) (U.pct a))
          (2 * (d : ℤ) - j - (m + d - 1) - 2) c) =
      mode A.fields (U.pct a) (2 * (d : ℤ) - (m + d - 1) - 2) c := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hpj j hj]
    · simp
  have h := U.invariant d a ha (m + d - 1) b c
  rw [hs] at h
  have he :
      ((-1 : ℂ)^d) •
        mode A.fields (U.pct a) (2 * (d : ℤ) - (m + d - 1) - 2) c =
      mode A.fields a (2 * (d : ℤ) - (m + d - 1) - 2) c := by
    rw [← LinearMap.smul_apply, ← mode_smul, hh]
  rw [he] at h
  have hi : 2 * (d : ℤ) - (m + d - 1) - 2 = -m + d - 1 := by omega
  simpa only [physicalMode, hi] using h

include U

 

theorem mode_norm_sq_difference {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) (c : V) :
    ‖A.physicalMode a d (-m) c‖ ^ 2 - ‖A.physicalMode a d m c‖ ^ 2 =
      (inner ℂ c (A.selfCommutator a d m c)).re := by
  have hp := U.physicalMode_adjoint ha hq hh (-m) c (A.physicalMode a d (-m) c)
  simp only [neg_neg] at hp
  have hn := U.physicalMode_adjoint ha hq hh m c (A.physicalMode a d m c)
  rw [selfCommutator_apply, inner_sub_right, ← hp, ← hn, Complex.sub_re]
  exact (congrArg₂ (fun x y : ℝ => x - y)
    (inner_self_eq_norm_sq (𝕜 := ℂ) (A.physicalMode a d (-m) c))
    (inner_self_eq_norm_sq (𝕜 := ℂ) (A.physicalMode a d m c))).symm

 
theorem mode_norm_sq_le_adjoint {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) (c : V) :
    ‖A.physicalMode a d m c‖ ^ 2 ≤
      ‖c‖ * ‖A.physicalMode a d (-m) (A.physicalMode a d m c)‖ := by
  have h := congrArg Complex.re
    (U.physicalMode_adjoint ha hq hh m c (A.physicalMode a d m c))
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  exact h.trans_le ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LoweringNormSq
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U
theorem lowering_norm_sq_of_commutator {a : V} {d m N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ A.grade h, ‖A.selfCommutator a d m c‖ ≤ R * ‖c‖) :
    ∀ h ≤ N, ∀ c ∈ A.grade h,
      ‖A.physicalMode a d m c‖ ^ 2 ≤ (h : ℝ) * R * ‖c‖ ^ 2 := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro hN c hc
    by_cases hhm : h < m
    · have hz : A.physicalMode a d m c = 0 :=
        A.mode_eq_zero_of_negative_energy ha hc ((m : ℤ) + d - 1) (by omega)
      rw [hz, norm_zero, zero_pow (by omega)]
      positivity
    · let e := h - m
      have heh : e < h := by dsimp [e]; omega
      have heN : e ≤ N := by omega
      have hb : A.physicalMode a d m c ∈ A.grade e :=
        A.mode_mem_grade ha hc ((m : ℤ) + d - 1) (by dsimp [e]; omega)
      have hi := ih e heh heN _ hb
      have hcom : (inner ℂ (A.physicalMode a d m c)
          (A.selfCommutator a d m (A.physicalMode a d m c))).re ≤
          R * ‖A.physicalMode a d m c‖ ^ 2 := by
        calc
          _ ≤ ‖inner ℂ (A.physicalMode a d m c)
              (A.selfCommutator a d m (A.physicalMode a d m c))‖ := Complex.re_le_norm _
          _ ≤ ‖A.physicalMode a d m c‖ *
              ‖A.selfCommutator a d m (A.physicalMode a d m c)‖ := norm_inner_le_norm _ _
          _ ≤ ‖A.physicalMode a d m c‖ * (R * ‖A.physicalMode a d m c‖) := by
            gcongr
            exact H e heN _ hb
          _ = _ := by ring
      have hdiff := U.mode_norm_sq_difference ha hq hh (m : ℤ) (A.physicalMode a d m c)
      have hecast : (e : ℝ) + 1 ≤ h := by exact_mod_cast (by omega : e + 1 ≤ h)
      have hraise : ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖ ^ 2 ≤
          (h : ℝ) * R * ‖A.physicalMode a d m c‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hecast
          (mul_nonneg hR (sq_nonneg ‖A.physicalMode a d m c‖))
        nlinarith
      have hcs := U.mode_norm_sq_le_adjoint ha hq hh (m : ℤ) c
      by_cases hz : ‖A.physicalMode a d m c‖ = 0
      · rw [hz, zero_pow (by omega)]
        positivity
      · have hp : 0 < ‖A.physicalMode a d m c‖ ^ 2 := sq_pos_of_ne_zero hz
        apply (mul_le_mul_iff_of_pos_right hp).mp
        calc
          _ ≤ (‖c‖ * ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖) ^ 2 := by
            nlinarith [sq_nonneg (‖c‖ * ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖ -
              ‖A.physicalMode a d m c‖ ^ 2)]
          _ = ‖c‖ ^ 2 * ‖A.physicalMode a d (-(m : ℤ)) (A.physicalMode a d m c)‖ ^ 2 := mul_pow _ _ _
          _ ≤ ‖c‖ ^ 2 * ((h : ℝ) * R * ‖A.physicalMode a d m c‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hraise (sq_nonneg _)
          _ = _ := by ring

 

theorem raising_norm_sq_of_commutator {a : V} {d m N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ A.grade h, ‖A.selfCommutator a d m c‖ ≤ R * ‖c‖)
    {h : ℕ} (hN : h ≤ N) {c : V} (hc : c ∈ A.grade h) :
    ‖A.physicalMode a d (-(m : ℤ)) c‖ ^ 2 ≤ ((h : ℝ) + 1) * R * ‖c‖ ^ 2 := by
  have hi := U.lowering_norm_sq_of_commutator ha hq hh hm hR H h hN c hc
  have hdiff := U.mode_norm_sq_difference ha hq hh (m : ℤ) c
  have hcom : (inner ℂ c (A.selfCommutator a d m c)).re ≤ R * ‖c‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ c (A.selfCommutator a d m c)‖ := Complex.re_le_norm _
      _ ≤ ‖c‖ * ‖A.selfCommutator a d m c‖ := norm_inner_le_norm _ _
      _ ≤ ‖c‖ * (R * ‖c‖) := mul_le_mul_of_nonneg_left (H h hN c hc) (norm_nonneg _)
      _ = _ := by ring
  nlinarith

 
theorem virasoro_adjoint (m : ℤ) (a b : V) :
    inner ℂ (A.virasoroMode m a) b = inner ℂ a (A.virasoroMode (-m) b) := by
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [IsHermitian, U.pct_conformal]
  simpa only [A.physicalMode_conformal] using
    U.physicalMode_adjoint A.conformal_mem A.conformal_quasiPrimary hh m a b

 

theorem grades_orthogonal {d e : ℕ} (hde : d ≠ e) {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) : inner ℂ a b = 0 := by
  have h := U.virasoro_adjoint 0 a b
  simp only [neg_zero, A.virasoro_zero_on_grade ha, A.virasoro_zero_on_grade hb,
    inner_smul_left, inner_smul_right, map_natCast] at h
  have hd : (d : ℂ) - e ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hde)
  apply (mul_eq_zero.mp (show ((d : ℂ) - e) * inner ℂ a b = 0 from ?_)).resolve_left hd
  rw [sub_mul, h, sub_self]

 

theorem centralCharge_eq : A.centralCharge = 2 * (‖A.conformalVector‖ : ℂ)^2 := by
  have h := U.virasoro_adjoint (-2) A.vacuum A.conformalVector
  norm_num at h
  rw [← A.conformal_eq_virasoro_vacuum, A.virasoro_two_conformal,
    inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    U.vacuum_norm] at h
  norm_num at h
  linear_combination -2 * h

 
theorem centralCharge_nonneg : A.centralCharge.im = 0 ∧ 0 ≤ A.centralCharge.re := by
  rw [U.centralCharge_eq]
  constructor
  · simp [pow_two]
  · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, sub_zero]
    positivity

 
theorem grade_orthogonalFamily :
    OrthogonalFamily ℂ (fun d => A.grade d) (fun d => (A.grade d).subtypeₗᵢ) := by
  intro d e hde a b
  exact U.grades_orthogonal hde a.property b.property


theorem energy_norm_sq_eq_sum_grades (a : V) (k : ℕ) :
    ‖(A.energyShift ^ k) a‖ ^ 2 =
      ∑ d ∈ A.gradeSupport a, ((1 + (d : ℝ)) ^ k * ‖A.gradeComponent d a‖) ^ 2 := by
  have h := U.grade_orthogonalFamily.norm_sum
    (fun d => ⟨(A.energyShift ^ k) (A.gradeComponent d a), by
      rw [A.energyShift_pow_on_grade (A.gradeComponent_mem d a)]
      exact (A.grade d).smul_mem _ (A.gradeComponent_mem d a)⟩)
    (A.gradeSupport a)
  change ‖∑ d ∈ A.gradeSupport a, (A.energyShift ^ k) (A.gradeComponent d a)‖ ^ 2 =
    ∑ d ∈ A.gradeSupport a, ‖(A.energyShift ^ k) (A.gradeComponent d a)‖ ^ 2 at h
  rw [← map_sum, A.sum_gradeComponents] at h
  simpa only [A.energyShift_pow_norm_on_grade (A.gradeComponent_mem _ _)] using h

 

theorem virasoro_norm_sq_identity (n : ℤ) {d : ℕ} {a : V}
    (ha : a ∈ A.grade d) :
    ‖A.virasoroMode (-n) a‖ ^ 2 = ‖A.virasoroMode n a‖ ^ 2 +
      (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) * ‖a‖ ^ 2 := by
  have h := congrArg (fun b : V => inner ℂ a b) (A.virasoro_commutator n (-n) a)
  have hn := U.virasoro_adjoint (-n) a (A.virasoroMode (-n) a)
  simp only [neg_neg] at hn
  rw [inner_sub_right, ← hn, ← U.virasoro_adjoint n a (A.virasoroMode n a)] at h
  simp only [add_neg_cancel, A.virasoro_zero_on_grade ha,
    inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, pow_succ] at hr
  nlinarith [hr]

 
theorem virasoro_norm_sq_le_adjoint (n : ℤ) (a : V) :
    ‖A.virasoroMode n a‖ ^ 2 ≤ ‖a‖ * ‖A.virasoroMode (-n) (A.virasoroMode n a)‖ := by
  have h := congrArg Complex.re (U.virasoro_adjoint n a (A.virasoroMode n a))
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  calc
    _ = (inner ℂ a (A.virasoroMode (-n) (A.virasoroMode n a))).re := h
    _ ≤ ‖inner ℂ a (A.virasoroMode (-n) (A.virasoroMode n a))‖ := Complex.re_le_norm _
    _ ≤ _ := norm_inner_le_norm _ _

 

theorem virasoro_positive_norm_sq (n : ℕ) (hn : 0 < n) (d : ℕ)
    (a : V) (ha : a ∈ A.grade d) :
    ‖A.virasoroMode (n : ℤ) a‖ ^ 2 ≤
      (1 + A.centralCharge.re * n) * (d : ℝ)^2 * ‖a‖ ^ 2 := by
  induction d using Nat.strong_induction_on generalizing a with
  | h d ih =>
    by_cases hd : d < n
    · rw [A.virasoro_eq_zero_of_lt ha n (by exact_mod_cast hd), norm_zero, zero_pow (by omega)]
      have hc := U.centralCharge_nonneg.2
      positivity
    · let e := d - n
      have hen : e + n = d := Nat.sub_add_cancel (Nat.le_of_not_gt hd)
      have he : e < d := by dsimp [e]; omega
      have hb : A.virasoroMode (n : ℤ) a ∈ A.grade e :=
        A.virasoro_mem_grade ha n (by omega)
      have hi := ih e he (A.virasoroMode (n : ℤ) a) hb
      have hc := U.centralCharge_nonneg.2
      have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have her : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      have hdr : (d : ℝ) = e + n := by exact_mod_cast hen.symm
      have hq : A.centralCharge.re / 12 * ((n : ℝ)^3 - n) ≤
          A.centralCharge.re * (n : ℝ)^3 := by
        nlinarith [mul_nonneg hc (pow_nonneg hnr 3), mul_nonneg hc hnr]
      have hcoeff : (1 + A.centralCharge.re * n) * (e : ℝ)^2 +
          (2 * (n : ℝ) * e + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) ≤
          (1 + A.centralCharge.re * n) * (d : ℝ)^2 := by
        rw [hdr]
        nlinarith [sq_nonneg (n : ℝ), mul_nonneg (mul_nonneg hc (sq_nonneg (n : ℝ))) her]
      have hraise : ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖ ^ 2 ≤
          ((1 + A.centralCharge.re * n) * (d : ℝ)^2) * ‖A.virasoroMode n a‖ ^ 2 := by
        rw [U.virasoro_norm_sq_identity (n : ℤ) hb]
        push_cast
        calc
          _ ≤ ((1 + A.centralCharge.re * n) * (e : ℝ)^2) * ‖A.virasoroMode n a‖ ^ 2 +
              (2 * (n : ℝ) * e + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) *
                ‖A.virasoroMode n a‖ ^ 2 := add_le_add hi le_rfl
          _ = ((1 + A.centralCharge.re * n) * (e : ℝ)^2 +
              (2 * (n : ℝ) * e + A.centralCharge.re / 12 * ((n : ℝ)^3 - n))) *
                ‖A.virasoroMode n a‖ ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      have hcs := U.virasoro_norm_sq_le_adjoint (n : ℤ) a
      by_cases hz : ‖A.virasoroMode (n : ℤ) a‖ = 0
      · rw [hz, zero_pow (by omega)]
        positivity
      · have hp : 0 < ‖A.virasoroMode (n : ℤ) a‖ ^ 2 := sq_pos_of_ne_zero hz
        apply (mul_le_mul_iff_of_pos_right hp).mp
        calc
          _ ≤ (‖a‖ * ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖) ^ 2 := by
            nlinarith [sq_nonneg (‖a‖ * ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖ -
              ‖A.virasoroMode (n : ℤ) a‖ ^ 2)]
          _ = ‖a‖ ^ 2 * ‖A.virasoroMode (-(n : ℤ)) (A.virasoroMode n a)‖ ^ 2 := mul_pow _ _ _
          _ ≤ ‖a‖ ^ 2 * (((1 + A.centralCharge.re * n) * (d : ℝ)^2) *
              ‖A.virasoroMode n a‖ ^ 2) := mul_le_mul_of_nonneg_left hraise (sq_nonneg _)
          _ = _ := by ring

 
theorem virasoro_negative_norm_sq (n : ℕ) (hn : 0 < n) (d : ℕ)
    (a : V) (ha : a ∈ A.grade d) :
    ‖A.virasoroMode (-(n : ℤ)) a‖ ^ 2 ≤
      (1 + A.centralCharge.re * n) * ((d : ℝ) + n)^2 * ‖a‖ ^ 2 := by
  have hi := U.virasoro_positive_norm_sq n hn d a ha
  have hc := U.centralCharge_nonneg.2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hq : A.centralCharge.re / 12 * ((n : ℝ)^3 - n) ≤
      A.centralCharge.re * (n : ℝ)^3 := by
    nlinarith [mul_nonneg hc (pow_nonneg hn0 3), mul_nonneg hc hn0]
  have hcoeff : (1 + A.centralCharge.re * n) * (d : ℝ)^2 +
      (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) ≤
      (1 + A.centralCharge.re * n) * ((d : ℝ) + n)^2 := by
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg (mul_nonneg hc (sq_nonneg (n : ℝ))) hd0]
  rw [U.virasoro_norm_sq_identity (n : ℤ) ha]
  push_cast
  calc
    _ ≤ ((1 + A.centralCharge.re * n) * (d : ℝ)^2) * ‖a‖ ^ 2 +
        (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n)) * ‖a‖ ^ 2 :=
      add_le_add hi le_rfl
    _ = ((1 + A.centralCharge.re * n) * (d : ℝ)^2 +
        (2 * (n : ℝ) * d + A.centralCharge.re / 12 * ((n : ℝ)^3 - n))) * ‖a‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

 

theorem virasoro_level_coefficient_le (n d : ℕ) :
    (1 + A.centralCharge.re * n) * ((d : ℝ) + n)^2 ≤
      ((1 + A.centralCharge.re) * (1 + (n : ℝ))^2 * (1 + (d : ℝ)))^2 := by
  have hc := U.centralCharge_nonneg.2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc1 : 1 ≤ (1 + A.centralCharge.re) * (1 + (n : ℝ)) := by nlinarith
  have hk : 1 + A.centralCharge.re * n ≤
      ((1 + A.centralCharge.re) * (1 + (n : ℝ)))^2 := by
    have hle : 1 + A.centralCharge.re * n ≤
        (1 + A.centralCharge.re) * (1 + (n : ℝ)) := by nlinarith
    nlinarith [sq_nonneg ((1 + A.centralCharge.re) * (1 + (n : ℝ)) - 1)]
  have hd : (d : ℝ) + n ≤ (1 + (n : ℝ)) * (1 + (d : ℝ)) := by nlinarith
  calc
    _ ≤ ((1 + A.centralCharge.re) * (1 + (n : ℝ)))^2 *
        ((1 + (n : ℝ)) * (1 + (d : ℝ)))^2 := by gcongr
    _ = _ := by ring

 

theorem virasoro_norm_on_grade (n : ℤ) {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    ‖A.virasoroMode n a‖ ≤
      (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2 * (1 + (d : ℝ)) * ‖a‖ := by
  have hc := U.centralCharge_nonneg.2
  have hsuff (k : ℕ) (h : ‖A.virasoroMode n a‖ ^ 2 ≤
      (1 + A.centralCharge.re * k) * ((d : ℝ) + k)^2 * ‖a‖ ^ 2)
      (hk : |(n : ℝ)| = k) : ‖A.virasoroMode n a‖ ≤
      (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2 * (1 + (d : ℝ)) * ‖a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hk, mul_pow]
    exact h.trans (mul_le_mul_of_nonneg_right (U.virasoro_level_coefficient_le k d) (sq_nonneg _))
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      have he0 : Int.ofNat 0 = 0 := by decide
      rw [he0, Int.cast_zero]
      change ‖A.virasoroMode 0 a‖ ≤
        (1 + A.centralCharge.re) * (1 + |(0 : ℝ)|)^2 * (1 + (d : ℝ)) * ‖a‖
      rw [A.virasoro_zero_on_grade ha, norm_smul]
      simp only [norm_natCast, abs_zero, add_zero, one_pow, mul_one]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
      nlinarith [mul_nonneg hc (Nat.cast_nonneg d)]
    | succ k =>
      apply hsuff (k + 1) _ (by
        change |((k + 1 : ℕ) : ℝ)| = ((k + 1 : ℕ) : ℝ)
        exact abs_of_nonneg (Nat.cast_nonneg _))
      have h := U.virasoro_positive_norm_sq (k + 1) (by omega) d a ha
      apply h.trans
      gcongr
      exact le_add_of_nonneg_right (by positivity)
  | negSucc k =>
    have he : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := by omega
    apply hsuff (k + 1) _ (by
      rw [he, Int.cast_neg, Int.cast_natCast, abs_neg]
      exact abs_of_nonneg (Nat.cast_nonneg _))
    rw [he]
    exact U.virasoro_negative_norm_sq (k + 1) (by omega) d a ha

 

theorem mode_images_orthogonal {w d e : ℕ} {a b c : V}
    (ha : a ∈ A.grade w) (hb : b ∈ A.grade d) (hc : c ∈ A.grade e)
    (hde : d ≠ e) (n : ℤ) : inner ℂ (mode A.fields a n b) (mode A.fields a n c) = 0 := by
  have h := U.virasoro_adjoint 0 (mode A.fields a n b) (mode A.fields a n c)
  simp only [neg_zero, A.mode_energy_eigenvalue ha hb, A.mode_energy_eigenvalue ha hc,
    inner_smul_left, inner_smul_right, map_sub, map_add, map_natCast, map_intCast, map_one] at h
  have hd : ((d : ℂ) + w - n - 1) - ((e : ℂ) + w - n - 1) ≠ 0 := by
    intro hz
    have hcast : (d : ℂ) = e := by linear_combination hz
    exact hde (by exact_mod_cast hcast)
  apply (mul_eq_zero.mp (show (((d : ℂ) + w - n - 1) - ((e : ℂ) + w - n - 1)) *
      inner ℂ (mode A.fields a n b) (mode A.fields a n c) = 0 from ?_)).resolve_left hd
  rw [sub_mul, h, sub_self]

 

theorem mode_norm_sq_eq_sum_grades {w : ℕ} {a : V} (ha : a ∈ A.grade w)
    (n : ℤ) (b : V) :
    ‖mode A.fields a n b‖ ^ 2 =
      ∑ d ∈ A.gradeSupport b, ‖mode A.fields a n (A.gradeComponent d b)‖ ^ 2 := by
  classical
  let f := fun d => mode A.fields a n (A.gradeComponent d b)
  have hsum : ∑ d ∈ A.gradeSupport b, f d = mode A.fields a n b := by
    dsimp only [f]
    rw [← map_sum, A.sum_gradeComponents]
  have h : inner ℂ (∑ d ∈ A.gradeSupport b, f d) (∑ d ∈ A.gradeSupport b, f d) =
      ∑ d ∈ A.gradeSupport b, inner ℂ (f d) (f d) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro d hd
    rw [inner_sum]
    apply Finset.sum_eq_single d
    · intro e _ hed
      exact U.mode_images_orthogonal ha (A.gradeComponent_mem d b)
        (A.gradeComponent_mem e b) (Ne.symm hed) n
    · exact fun hnot => (hnot hd).elim
  rw [hsum] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

 

theorem zeroMode_norm_sq_of_commutator {a : V} {d N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hd : 1 ≤ d) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ A.grade h, ‖A.selfCommutator a d (1 : ℕ) c‖ ≤ R * ‖c‖)
    {h : ℕ} (hN : h ≤ N) {c : V} (hc : c ∈ A.grade h) :
    ‖A.physicalMode a d 0 c‖ ^ 2 ≤
      256 * (1 + A.centralCharge.re)^2 * (1 + (N : ℝ))^3 * R * ‖c‖^2 := by
  let G : ℝ := Real.sqrt ((1 + (N : ℝ)) * R)
  let K : ℝ := 8 * (1 + A.centralCharge.re) * (1 + (N : ℝ))
  have hccharge := U.centralCharge_nonneg.2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hraising {e : ℕ} (he : e ≤ N) {b : V} (hb : b ∈ A.grade e) :
      ‖A.physicalMode a d (-1) b‖ ≤ G * ‖b‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hG (norm_nonneg _))).mp
    have h := U.raising_norm_sq_of_commutator ha hq hh (by omega : 0 < 1) hR H he hb
    norm_num only [Nat.cast_one, neg_inj] at h
    rw [mul_pow, show G ^ 2 = (1 + (N : ℝ)) * R from Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ((e : ℝ) + 1) * R * ‖b‖ ^ 2 := h
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : e + 1 ≤ 1 + N)) hR)
        (sq_nonneg _)
  have hLbound {e : ℕ} (he : e ≤ N + 1) {b : V} (hb : b ∈ A.grade e) :
      ‖A.virasoroMode 1 b‖ ≤ K * ‖b‖ := by
    have h := U.virasoro_norm_on_grade 1 hb
    norm_num only [Int.cast_one, abs_one, one_add_one_eq_two, Nat.reducePow] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have her : (e : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast he
    dsimp [K]
    nlinarith [mul_nonneg (show 0 ≤ 1 + A.centralCharge.re by linarith) (by linarith : 0 ≤ 2 * (1 + (N : ℝ)) - (1 + e))]
  have hraisegrade : A.physicalMode a d (-1) c ∈ A.grade (h + 1) :=
    A.mode_mem_grade ha hc (-1 + (d : ℤ) - 1) (by omega)
  have hLgrade : A.virasoroMode 1 c ∈ A.grade (h - 1) := by
    by_cases hz : h = 0
    · have he := A.virasoro_eq_zero_of_lt hc 1 (by omega)
      rw [he]
      exact (A.grade (h - 1)).zero_mem
    · exact A.virasoro_mem_grade hc 1 (by omega)
  have hfirst : ‖A.virasoroMode 1 (A.physicalMode a d (-1) c)‖ ≤ K * G * ‖c‖ := by
    calc
      _ ≤ K * ‖A.physicalMode a d (-1) c‖ := hLbound (by omega) hraisegrade
      _ ≤ K * (G * ‖c‖) := mul_le_mul_of_nonneg_left (hraising hN hc) hK
      _ = _ := by ring
  have hsecond : ‖A.physicalMode a d (-1) (A.virasoroMode 1 c)‖ ≤ K * G * ‖c‖ := by
    calc
      _ ≤ G * ‖A.virasoroMode 1 c‖ := hraising (by omega) hLgrade
      _ ≤ G * (K * ‖c‖) := mul_le_mul_of_nonneg_left (hLbound (by omega) hc) hG
      _ = _ := by ring
  have he := congrArg norm (A.zeroMode_commutator ha hq c)
  rw [norm_smul, Complex.norm_natCast] at he
  have hlo : ‖A.physicalMode a d 0 c‖ ≤ 2 * K * G * ‖c‖ := by
    calc
      _ ≤ (d : ℝ) * ‖A.physicalMode a d 0 c‖ := by
        have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [norm_nonneg (A.physicalMode a d 0 c)]
      _ = _ := he.symm
      _ ≤ ‖A.virasoroMode 1 (A.physicalMode a d (-1) c)‖ +
          ‖A.physicalMode a d (-1) (A.virasoroMode 1 c)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  calc
    _ ≤ (2 * K * G * ‖c‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hlo 2
    _ = 4 * K^2 * G^2 * ‖c‖^2 := by ring
    _ = _ := by
      rw [show G^2 = (1 + (N : ℝ)) * R from Real.sq_sqrt (by positivity)]
      dsimp [K]
      ring

 

theorem modeBlock_norm_sq_bound {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (H : ∀ j < 2 * d, A.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - j - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N h k : ℕ, h ≤ N → k ≤ N →
      ‖A.modeBlock a d h k‖ ^ 2 ≤ C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1) := by
  obtain ⟨C, hC, p, hp⟩ := A.selfCommutator_bound hB ha hd H
  let F : ℝ := 256 * (1 + A.centralCharge.re)^2
  have hccharge := U.centralCharge_nonneg.2
  have hF : 1 ≤ F := by dsimp [F]; nlinarith [sq_nonneg A.centralCharge.re]
  refine ⟨F * C, by positivity, p + 3, ?_⟩
  intro N h k hN kN
  let R : ℝ := C * (1 + (N : ℝ)) ^ p * B N ^ (2 * d - 1)
  let Q : ℝ := F * (1 + (N : ℝ)) ^ 3 * R
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hQle : (1 + (N : ℝ)) * R ≤ Q := by
    dsimp [Q]
    have hpow : 1 + (N : ℝ) ≤ (1 + (N : ℝ)) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hN1 (by norm_num : 1 ≤ 3)
    have hmul : (1 + (N : ℝ)) ^ 3 ≤ F * (1 + (N : ℝ)) ^ 3 := by
      nlinarith [pow_nonneg (show 0 ≤ 1 + (N : ℝ) by positivity) 3]
    exact mul_le_mul_of_nonneg_right (hpow.trans hmul) hR
  have H' (m : ℕ) (hm : m ≤ N + 1) :
      ∀ e ≤ N, ∀ c ∈ A.grade e, ‖A.selfCommutator a d m c‖ ≤ R * ‖c‖ := hp N m hm
  have hsquare (c : A.grade h) : ‖A.modeBlock a d h k c‖^2 ≤ Q * ‖c‖^2 := by
    rw [modeBlock_apply]
    by_cases heq : h = k
    · subst k
      simpa only [sub_self, Q, F, ← Submodule.norm_coe] using
        U.zeroMode_norm_sq_of_commutator ha hq hh hd hR (H' 1 (by omega)) hN c.property
    · by_cases hhk : k < h
      · let m := h - k
        have hm : 0 < m := by dsimp [m]; omega
        have hmN : m ≤ N + 1 := by dsimp [m]; omega
        have he : (m : ℤ) = (h : ℤ) - k := by dsimp [m]; omega
        have hb := U.lowering_norm_sq_of_commutator ha hq hh hm hR (H' m hmN) h hN c c.property
        rw [he] at hb
        apply hb.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : h ≤ 1 + N)) hR).trans hQle
      · let m := k - h
        have hm : 0 < m := by dsimp [m]; omega
        have hmN : m ≤ N + 1 := by dsimp [m]; omega
        have he : -(m : ℤ) = (h : ℤ) - k := by dsimp [m]; omega
        have hb := U.raising_norm_sq_of_commutator ha hq hh hm hR (H' m hmN) hN c.property
        rw [he] at hb
        apply hb.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply le_trans _ hQle
        apply mul_le_mul_of_nonneg_right _ hR
        exact_mod_cast (by omega : h + 1 ≤ 1 + N)
  have hop : ‖A.modeBlock a d h k‖ ≤ Real.sqrt Q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro c
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hQ]
    exact hsquare c
  calc
    _ ≤ (Real.sqrt Q)^2 := pow_le_pow_left₀ (norm_nonneg (A.modeBlock a d h k)) hop 2
    _ = Q := Real.sq_sqrt hQ
    _ = _ := by dsimp [Q, R]; rw [pow_add]; ring
end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_VirasoroLinearEnergy
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U
theorem virasoro_linear_energy (n : ℤ) (a : V) :
    ‖A.virasoroMode n a‖ ≤
      (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2 * ‖A.energyShift a‖ := by
  have hc := U.centralCharge_nonneg.2
  let K : ℝ := (1 + A.centralCharge.re) * (1 + |(n : ℝ)|)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  change ‖A.virasoroMode n a‖ ^ 2 ≤ (K * ‖A.energyShift a‖)^2
  have hn := U.mode_norm_sq_eq_sum_grades A.conformal_mem (n + 1) a
  change ‖A.virasoroMode n a‖ ^ 2 =
    ∑ d ∈ A.gradeSupport a, ‖A.virasoroMode n (A.gradeComponent d a)‖ ^ 2 at hn
  have he := U.energy_norm_sq_eq_sum_grades a 1
  simp only [pow_one] at he
  calc
    _ = ∑ d ∈ A.gradeSupport a, ‖A.virasoroMode n (A.gradeComponent d a)‖ ^ 2 := hn
    _ ≤ ∑ d ∈ A.gradeSupport a, (K * (1 + (d : ℝ)) * ‖A.gradeComponent d a‖)^2 := by
      apply Finset.sum_le_sum
      intro d _
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (U.virasoro_norm_on_grade n (A.gradeComponent_mem d a))
    _ = K^2 * ∑ d ∈ A.gradeSupport a, ((1 + (d : ℝ)) * ‖A.gradeComponent d a‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [← he]; ring



theorem pct_mem_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    U.pct a ∈ A.grade d := by
  apply A.mem_grade_of_energy
  rw [← U.pct_virasoro, A.virasoro_zero_on_grade ha]
  simp

 

def hermitianConjugation (d : ℕ) : V →ₛₗ[starRingEnd ℂ] V :=
  ((-1 : ℂ) ^ d) • U.pct

theorem hermitianConjugation_involutive (d : ℕ) :
    Function.Involutive (U.hermitianConjugation d) := by
  intro a
  simp only [hermitianConjugation, LinearMap.smul_apply, map_smulₛₗ,
    map_pow, map_neg, map_one, U.pct_involutive a, smul_smul, ← mul_pow]
  simp

 

theorem exists_hermitian_quasiPrimary_spanning (d : ℕ) :
    ∃ S : Finset V,
      (∀ a ∈ S, a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      (∀ a ∈ A.grade d, A.IsQuasiPrimary a → a ∈ Submodule.span ℂ (S : Set V)) := by
  classical
  let E := A.grade d ⊓ (A.virasoroMode 1).ker
  let J := U.hermitianConjugation d
  let H := {a : V | a ∈ E ∧ J a = a}
  have hJin (a : V) (ha : a ∈ E) : J a ∈ E := by
    refine ⟨(A.grade d).smul_mem _ (U.pct_mem_grade ha.1), ?_⟩
    change A.virasoroMode 1 (((-1 : ℂ)^d) • U.pct a) = 0
    rw [map_smul, ← U.pct_virasoro, (LinearMap.mem_ker.mp ha.2), map_zero, smul_zero]
  have hJ (a : V) : J (J a) = a := U.hermitianConjugation_involutive d a
  have hfix (a : V) (ha : a ∈ E) : a + J a ∈ H := by
    refine ⟨E.add_mem ha (hJin a ha), ?_⟩
    rw [map_add, hJ, add_comm]
  have hspan : E ≤ Submodule.span ℂ H := by
    intro a ha
    have hx := Submodule.subset_span (R := ℂ) (hfix a ha)
    have hy := Submodule.subset_span (R := ℂ) (hfix (Complex.I • a) (E.smul_mem _ ha))
    have he : a = (2 : ℂ)⁻¹ • (a + J a) +
        (-Complex.I / 2 : ℂ) • (Complex.I • a + J (Complex.I • a)) := by
      rw [map_smulₛₗ, show starRingEnd ℂ Complex.I = -Complex.I from Complex.conj_I]
      simp only [smul_add, smul_smul]
      have hI : (-Complex.I / 2 : ℂ) * Complex.I = (2 : ℂ)⁻¹ := by
        rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
        norm_num
      rw [hI, mul_neg, hI]
      module
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)
  let := A.grade_finite d
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨T, hT⟩ := (Submodule.FG.of_finite (N := E))
  have hTspan : (T : Set V) ⊆ Submodule.span ℂ H := by
    intro a ha
    exact hspan (hT ▸ Submodule.subset_span ha)
  obtain ⟨S, hSH, hTS⟩ := Submodule.subset_span_finite_of_subset_span hTspan
  refine ⟨S, ?_, ?_⟩
  · intro a ha
    have h := hSH ha
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro a ha hqa
    have hle : E ≤ Submodule.span ℂ (S : Set V) := by
      rw [← hT]
      exact Submodule.span_le.mpr hTS
    exact hle ⟨ha, hqa⟩

 

theorem quasiPrimary_decomposition {d : ℕ} {a : V} (ha : a ∈ A.grade (d + 1)) :
    ∃ q ∈ A.grade (d + 1), A.IsQuasiPrimary q ∧
      ∃ b ∈ A.grade d, a = q + A.virasoroMode (-1) b := by
  let K := (A.grade d).map (A.virasoroMode (-1))
  let := A.grade_finite d
  have : FiniteDimensional ℂ K := Module.Finite.map _ _
  obtain ⟨y, hy, q, hq, hayq⟩ := K.exists_add_mem_mem_orthogonal a
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
  have hygrade := A.virasoro_mem_grade hb (-1) (k := d + 1) (by omega)
  have hqgrade : q ∈ A.grade (d + 1) := by
    have he : q = a - A.virasoroMode (-1) b := by rw [hayq]; abel
    rw [he]
    exact (A.grade (d + 1)).sub_mem ha hygrade
  have hLq : A.virasoroMode 1 q ∈ A.grade d :=
    A.virasoro_mem_grade hqgrade 1 (by omega)
  have hzero : A.virasoroMode 1 q = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have hmem : A.virasoroMode (-1) (A.virasoroMode 1 q) ∈ K :=
      Submodule.mem_map.mpr ⟨A.virasoroMode 1 q, hLq, rfl⟩
    have h := (K.mem_orthogonal q).mp hq _ hmem
    simpa only [U.virasoro_adjoint, neg_neg, Int.reduceNeg] using h
  exact ⟨q, hqgrade, hzero, b, hb, hayq.trans (add_comm _ _)⟩

 

theorem grade_blockGrowth {B : ℕ → ℝ} (hB : ∀ N, 1 ≤ B N) (D : ℕ)
    (hsmall : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      A.BlockGrowth B a d d)
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, ∀ a ∈ A.grade d, A.BlockGrowth B a d d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    by_cases hd0 : d = 0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact A.blockGrowth_smul (A.vacuum_blockGrowth B) z
    by_cases hdD : d ≤ D
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
      rw [hab, A.virasoro_neg_one_eq_translation]
      exact A.blockGrowth_add hB (hsmall _ (by omega) hdD q hq hqq)
        (A.blockGrowth_mono_weight hB (A.translation_blockGrowth hB (ih e (by omega) b hb))
          (by omega))
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha, ha⟩
      exact A.homogeneousC2_le_blockGrowth hB d ih hc

 

theorem exists_generatorMajorant (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      ∀ w, ∀ a ∈ A.grade w, A.BlockGrowth (A.generatorMajorant D S) a w w := by
  classical
  obtain ⟨D, hD, hcut⟩ := A.exists_c2_weight_cutoff hc
  choose R hR hspan using U.exists_hermitian_quasiPrimary_spanning
  let S : ℕ → Finset V := fun d => if 1 ≤ d ∧ d ≤ D then R d else ∅
  have hS (d : ℕ) (a : V) (ha : a ∈ S d) :
      1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a := by
    dsimp only [S] at ha
    split_ifs at ha with hd
    · exact ⟨hd.1, hd.2, hR d a ha⟩
    · simp at ha
  refine ⟨D, hD, S, ?_, hS, ?_⟩
  · intro d hd
    dsimp [S]
    rw [ite_eq_right]
    omega
  · apply U.grade_blockGrowth (A.one_le_generatorMajorant D S) D _ hcut
    intro d hd hdD a ha hq
    have he : S d = R d := by dsimp [S]; rw [ite_eq_left ⟨hd, hdD⟩]
    have hmem : a ∈ Submodule.span ℂ (S d : Set V) := by
      rw [he]
      exact hspan d a ha hq
    have hle : Submodule.span ℂ (S d : Set V) ≤
        A.blockGrowthSubmodule (A.generatorMajorant D S) (A.one_le_generatorMajorant D S) d d := by
      apply Submodule.span_le.mpr
      intro b hb
      exact A.generator_blockGrowth D S (by omega) hdD hb
    exact hle hmem

 

theorem generatorMajorant_polynomial (D : ℕ) (hD : 2 ≤ D) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
      A.IsQuasiPrimary a ∧ U.IsHermitian d a)
    (H : ∀ w, ∀ a ∈ A.grade w, A.BlockGrowth (A.generatorMajorant D S) a w w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N,
      A.generatorMajorant D S N ≤ C * (1 + (N : ℝ))^p := by
  classical
  let B := A.generatorMajorant D S
  have hB := A.one_le_generatorMajorant D S
  let G := (Finset.range (D + 1)).sigma S
  have HG (i : Σ _ : ℕ, V) (hi : i ∈ G) :
      1 ≤ i.1 ∧ i.1 ≤ D ∧ i.2 ∈ A.grade i.1 ∧
        A.IsQuasiPrimary i.2 ∧ U.IsHermitian i.1 i.2 :=
    hS i.1 i.2 (Finset.mem_sigma.mp hi).2
  have Hsq (i : Σ _ : ℕ, V) (hi : i ∈ G) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N (hk : ℕ × ℕ), hk.1 ≤ N ∧ hk.2 ≤ N →
        ‖A.modeBlock i.2 i.1 hk.1 hk.2‖^2 ≤
          C * (1 + (N : ℝ))^p * B N^(2 * i.1 - 1) := by
    obtain ⟨hd, _, ha, hq, hh⟩ := HG i hi
    obtain ⟨C, hC, p, hp⟩ := U.modeBlock_norm_sq_bound hB ha hd hq hh
      (fun j hj => H _ _ (A.mode_mem_grade ha ha j (by omega)))
    exact ⟨C, hC, p, fun N hk hh => hp N hk.1 hk.2 hh.1 hh.2⟩
  obtain ⟨C, hC, p, hp⟩ := finite_weighted_poly_uniform hB G
    (fun (i : Σ _ : ℕ, V) (_ : ℕ) (hk : ℕ × ℕ) => ‖A.modeBlock i.2 i.1 hk.1 hk.2‖^2)
    (fun i => 2 * i.1 - 1) (fun N (hk : ℕ × ℕ) => hk.1 ≤ N ∧ hk.2 ≤ N) Hsq
  let J : ℝ := (G.card : ℝ) + 1
  have hJ : 1 ≤ J := by dsimp [J]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  refine ⟨J^(2 * D) * (C + 1), by positivity, 4 * D + p, ?_⟩
  intro N
  have hBN : 0 ≤ B N := zero_le_one.trans (hB N)
  have hBN' : 0 ≤ A.generatorMajorant D S N := hBN
  let s := G ×ˢ (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
  let x : ((Σ _ : ℕ, V) × (ℕ × ℕ)) → ℝ :=
    fun i => ‖A.modeBlock i.1.2 i.1.1 i.2.1 i.2.2‖ ^ (i.1.1 : ℝ)⁻¹
  have hx (i) : 0 ≤ x i := by
    dsimp [x]
    exact Real.rpow_nonneg (norm_nonneg (A.modeBlock _ _ _ _)) _
  have hsum : 1 + ∑ i ∈ s, x i = B N := by
    simp only [s, x, G, B, generatorMajorant, Finset.sum_product, Finset.sum_sigma]
  let R := (C + 1) * (1 + (N : ℝ))^p
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hR : 1 ≤ R := by
    dsimp [R]
    nlinarith [one_le_pow₀ hN1 (n := p)]
  have hstep (i) (hi : i ∈ s) : (x i)^(2 * D) ≤ R * (B N)^(2 * D - 1) := by
    obtain ⟨hiG, hhk⟩ := Finset.mem_product.mp hi
    obtain ⟨hh, hk⟩ := Finset.mem_product.mp hhk
    have hhN : i.2.1 ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
    have hkN : i.2.2 ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    have hs := HG i.1 hiG
    have hroot : x i ≤ B N := A.root_modeBlock_le_generatorMajorant D S hs.2.1
      (Finset.mem_sigma.mp hiG).2 hhN hkN
    have hpow : (x i)^(2 * i.1.1) = ‖A.modeBlock i.1.2 i.1.1 i.2.1 i.2.2‖^2 := by
      rw [mul_comm 2 i.1.1, pow_mul]
      dsimp [x]
      rw [Real.rpow_inv_natCast_pow (norm_nonneg (A.modeBlock _ _ _ _)) (by omega)]
    have hsq := hp i.1 hiG N i.2 ⟨hhN, hkN⟩
    have hsq' : (x i)^(2 * i.1.1) ≤ R * (B N)^(2 * i.1.1 - 1) := by
      rw [hpow]
      apply hsq.trans
      dsimp [R]
      gcongr
      linarith
    have he : 2 * i.1.1 + (2 * D - 2 * i.1.1) = 2 * D := by omega
    have he' : (2 * i.1.1 - 1) + (2 * D - 2 * i.1.1) = 2 * D - 1 := by omega
    calc
      _ = (x i)^(2 * i.1.1) * (x i)^(2 * D - 2 * i.1.1) := by rw [← pow_add, he]
      _ ≤ (R * (B N)^(2 * i.1.1 - 1)) * (B N)^(2 * D - 2 * i.1.1) := by
        apply mul_le_mul hsq' (pow_le_pow_left₀ (hx i) hroot _) (pow_nonneg (hx i) _) (by positivity)
      _ = _ := by rw [mul_assoc, ← pow_add, he']
  have hcontract := finite_sum_power_contraction s x (2 * D) (by omega) R hR
    (fun i _ => hx i) (fun i hi => by rw [hsum]; exact hstep i hi)
  rw [hsum] at hcontract
  have hcard : (s.card : ℝ) + 1 ≤ J * (1 + (N : ℝ))^2 := by
    simp only [s, Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, J]
    nlinarith [Nat.cast_nonneg N (α := ℝ)]
  calc
    _ ≤ ((s.card : ℝ) + 1)^(2 * D) * R := hcontract
    _ ≤ (J * (1 + (N : ℝ))^2)^(2 * D) * R := by
      gcongr
    _ = _ := by
      dsimp [R]
      rw [mul_pow, ← pow_mul, ← mul_assoc, mul_right_comm _ _ (C + 1), mul_assoc,
        ← pow_add]
      congr 2
      omega

 

theorem energyBound_of_polynomial_blocks {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N,
      A.BlockControl a d N (C * (1 + (N : ℝ))^p)) : A.PolynomialEnergyBound a := by
  obtain ⟨C, hC, p, hp⟩ := H
  let K : ℝ := (C + 1) * ((d : ℝ) + 2)^p
  have hK : 0 < K := by dsimp [K]; positivity
  have hgrade (n : ℤ) (h : ℕ) (b : V) (hb : b ∈ A.grade h) :
      ‖mode A.fields a n b‖ ≤ K * (1 + |(n : ℝ)|)^p * (1 + (h : ℝ))^p * ‖b‖ := by
    by_cases hout : 0 ≤ (h : ℤ) + d - n - 1
    · let k := ((h : ℤ) + d - n - 1).toNat
      let N := h + d + 1 + n.natAbs
      have hk : (k : ℤ) = (h : ℤ) + d - n - 1 := Int.toNat_of_nonneg hout
      have hnabs : -n ≤ (n.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -n))
      have hhN : h ≤ N := by dsimp [N]; omega
      have hkN : k ≤ N := by dsimp [N]; omega
      have hindex : (h : ℤ) - k + d - 1 = n := by omega
      have hblock := hp N h hhN k hkN b hb
      simp only [physicalMode, hindex] at hblock
      have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      have hN : 1 + (N : ℝ) ≤ ((d : ℝ) + 2) * (1 + |(n : ℝ)|) * (1 + (h : ℝ)) := by
        dsimp [N]
        push_cast
        rw [habs]
        have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
        have hn0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
        nlinarith [mul_nonneg hd0 hn0, mul_nonneg hd0 hh0, mul_nonneg hn0 hh0,
          mul_nonneg (mul_nonneg hd0 hn0) hh0]
      apply hblock.trans
      have hc : C ≤ C + 1 := by linarith
      calc
        _ ≤ ((C + 1) * (((d : ℝ) + 2) * (1 + |(n : ℝ)|) * (1 + (h : ℝ)))^p) * ‖b‖ := by
          gcongr
        _ = _ := by dsimp [K]; simp only [mul_pow]; ring
    · rw [A.mode_eq_zero_of_negative_energy ha hb n (by omega), norm_zero]
      positivity
  refine ⟨K, hK, p, p, ?_⟩
  intro n b
  let L := K * (1 + |(n : ℝ)|)^p
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖mode A.fields a n b‖^2 ≤ (L * ‖(A.energyShift^p) b‖)^2
  rw [U.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ A.gradeSupport b, (L * (1 + (h : ℝ))^p * ‖A.gradeComponent h b‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact hgrade n h _ (A.gradeComponent_mem h b)
    _ = L^2 * ∑ h ∈ A.gradeSupport b, ((1 + (h : ℝ))^p * ‖A.gradeComponent h b‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← U.energy_norm_sq_eq_sum_grades]; ring
end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyShiftPow
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U
theorem energyShift_pow_norm_mono {k l : ℕ} (hkl : k ≤ l) (b : V) :
    ‖(A.energyShift^k) b‖ ≤ ‖(A.energyShift^l) b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [U.energy_norm_sq_eq_sum_grades, U.energy_norm_sq_eq_sum_grades]
  apply Finset.sum_le_sum
  intro d _
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg d)) hkl

theorem energyBound_add {a b : V} (ha : A.PolynomialEnergyBound a)
    (hb : A.PolynomialEnergyBound b) : A.PolynomialEnergyBound (a + b) := by
  obtain ⟨C, hC, p, k, hp⟩ := ha
  obtain ⟨D, hD, q, l, hq⟩ := hb
  refine ⟨C + D, add_pos hC hD, p + q, k + l, ?_⟩
  intro n c
  have hbase : 1 ≤ 1 + |(n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
  have hpp : (1 + |(n : ℝ)|)^p ≤ (1 + |(n : ℝ)|)^(p + q) :=
    pow_le_pow_right₀ hbase (by omega)
  have hqq : (1 + |(n : ℝ)|)^q ≤ (1 + |(n : ℝ)|)^(p + q) :=
    pow_le_pow_right₀ hbase (by omega)
  have hkk := U.energyShift_pow_norm_mono (show k ≤ k + l by omega) c
  have hll := U.energyShift_pow_norm_mono (show l ≤ k + l by omega) c
  rw [mode_add, LinearMap.add_apply]
  calc
    _ ≤ ‖mode A.fields a n c‖ + ‖mode A.fields b n c‖ := norm_add_le _ _
    _ ≤ C * (1 + |(n : ℝ)|)^p * ‖(A.energyShift^k) c‖ +
          D * (1 + |(n : ℝ)|)^q * ‖(A.energyShift^l) c‖ := add_le_add (hp n c) (hq n c)
    _ ≤ C * (1 + |(n : ℝ)|)^(p + q) * ‖(A.energyShift^(k + l)) c‖ +
          D * (1 + |(n : ℝ)|)^(p + q) * ‖(A.energyShift^(k + l)) c‖ := by gcongr
    _ = _ := by ring

 

theorem polynomialEnergyBounds (hc : A.toVertexAlgebra.C2Cofinite) : A.PolynomialEnergyBounds := by
  obtain ⟨D, hD, S, _, hS, H⟩ := U.exists_generatorMajorant hc
  obtain ⟨C, hC, p, hp⟩ := U.generatorMajorant_polynomial D hD S hS H
  have hB := A.one_le_generatorMajorant D S
  have hhom (d : ℕ) (a : V) (ha : a ∈ A.grade d) : A.PolynomialEnergyBound a := by
    obtain ⟨K, hK, q, hq⟩ := H d a ha
    apply U.energyBound_of_polynomial_blocks ha
    refine ⟨K * C^d, by positivity, q + p * d, ?_⟩
    intro N
    apply A.blockControl_mono (hq N)
    have hBN : 0 ≤ A.generatorMajorant D S N := zero_le_one.trans (hB N)
    calc
      _ ≤ K * (1 + (N : ℝ))^q * (C * (1 + (N : ℝ))^p)^d := by gcongr; exact hp N
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
  intro a
  exact A.homogeneous_induction (P := A.PolynomialEnergyBound)
    (hhom 0 0 (Submodule.zero_mem _)) hhom (fun _ _ => U.energyBound_add) a



end UnitaryStructure

end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyCutoff
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
def energyCutoff (N : ℕ) : Submodule ℂ V where
  carrier := {v | ∀ d, N < d → A.gradeComponent d v = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb d hd; simp only [map_add, ha d hd, hb d hd, add_zero]
  smul_mem' := by intro z a ha d hd; simp only [map_smul, ha d hd, smul_zero]


def cutoffProjection (N : ℕ) : Module.End ℂ V :=
  ∑ d ∈ Finset.range (N + 1), A.gradeComponent d

theorem cutoffProjection_apply (N : ℕ) (v : V) :
    A.cutoffProjection N v = ∑ d ∈ Finset.range (N + 1), A.gradeComponent d v := by
  simp [cutoffProjection]

theorem cutoffProjection_of_mem {N : ℕ} {v : V} (hv : v ∈ A.energyCutoff N) :
    A.cutoffProjection N v = v := by
  classical
  rw [cutoffProjection_apply]
  calc
    _ = ∑ d ∈ Finset.range (N + 1) ∪ A.gradeSupport v, A.gradeComponent d v := by
      apply Finset.sum_subset Finset.subset_union_left
      intro d _ hd
      exact hv d (by simp only [Finset.mem_range] at hd; omega)
    _ = ∑ d ∈ A.gradeSupport v, A.gradeComponent d v := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro d _ hd
      have hz : A.gradingEquiv v d = 0 := DFinsupp.notMem_support_iff.mp hd
      exact congrArg Subtype.val hz
    _ = v := A.sum_gradeComponents v

end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ConstrainedSquareBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 

instance energyCutoff_finite (N : ℕ) : FiniteDimensional ℂ (A.energyCutoff N) := by
  let := A.grade_finite
  apply Submodule.finiteDimensional_of_le (S₂ := (Finset.range (N + 1)).sup A.grade)
  intro v hv
  rw [← A.cutoffProjection_of_mem hv, cutoffProjection_apply]
  apply Submodule.sum_mem
  intro d hd
  exact Finset.le_sup (f := A.grade) hd (A.gradeComponent_mem d v)

 

def positiveColumn (a : V) (d N : ℕ) :
    A.energyCutoff N →L[ℂ] PiLp 2 (fun _ : Fin (N + 1) => V) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℂ (Fin (N + 1) → V)).symm.toLinearMap.comp
      (LinearMap.pi (fun m => (A.physicalMode a d m).comp (A.energyCutoff N).subtype)))

@[simp]
theorem positiveColumn_apply (a : V) (d N : ℕ) (v : A.energyCutoff N)
    (m : Fin (N + 1)) : (A.positiveColumn a d N v).ofLp m = A.physicalMode a d m v := rfl


end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 

def adjointPhysicalMode (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ V :=
  ((-1 : ℂ)^d) • ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
    A.physicalMode ((A.virasoroMode 1 ^ j) (U.pct a)) (d - j) (-m)

theorem adjointPhysicalMode_inner {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (m : ℤ) (v w : V) :
    inner ℂ (A.physicalMode a d m v) w = inner ℂ v (U.adjointPhysicalMode a d m w) := by
  have h := U.invariant d a ha (m + d - 1) v w
  refine h.trans ?_
  apply congrArg (fun x : V => inner ℂ v x)
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply]
  apply congrArg (fun x : V => ((-1 : ℂ)^d) • x)
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  dsimp only [physicalMode]
  congr 2
  have hj := Finset.mem_range.mp hj
  omega

end UnitaryStructure
end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertCore
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
namespace HilbertCore
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def space (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    Submodule ℂ (Completion V) :=
  LinearMap.range (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap

def equiv (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V ≃ₗ[ℂ] space V :=
  LinearEquiv.ofInjective (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap
    (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective

@[simp] theorem equiv_coe (v : V) : (equiv V v : Completion V) = (v : Completion V) := rfl
@[simp] theorem equiv_symm_coe (v : space V) :
    ((equiv V).symm v : Completion V) = (v : Completion V) :=
  LinearEquiv.ofInjective_symm_apply _ v

theorem dense : Dense (space V : Set (Completion V)) := by
  change Dense (Set.range (fun v : V => (v : Completion V)))
  exact Completion.denseRange_coe

 
def operator (T : V →ₗ[ℂ] Completion V) : Completion V →ₗ.[ℂ] Completion V where
  domain := space V
  toFun := T.comp (equiv V).symm.toLinearMap

@[simp] theorem operator_apply (T : V →ₗ[ℂ] Completion V) (v : V) :
    operator T (equiv V v) = T v := by simp [operator]

theorem formalAdjoint {T S : V →ₗ[ℂ] Completion V}
    (h : ∀ v w : V, inner ℂ (T v) (w : Completion V) =
      inner ℂ (v : Completion V) (S w)) :
    (operator T).IsFormalAdjoint (operator S) := by
  intro v w
  obtain ⟨v, rfl⟩ := (equiv V).surjective v
  obtain ⟨w, rfl⟩ := (equiv V).surjective w
  simpa using h v w

 

theorem closable {T S : V →ₗ[ℂ] Completion V}
    (h : ∀ v w : V, inner ℂ (T v) (w : Completion V) =
      inner ℂ (v : Completion V) (S w)) : (operator T).IsClosable := by
  have H := formalAdjoint h
  exact ((operator S).adjoint_isClosed dense).isClosable.leIsClosable (H.symm.le_adjoint dense)

end HilbertCore



namespace RapidCoefficients
variable {f g : ℤ → ℂ}

theorem conj (h : RapidCoefficients f) : RapidCoefficients (fun n => star (f n)) := by
  intro p
  simpa only [norm_star] using h p

theorem neg_index (h : RapidCoefficients f) : RapidCoefficients (fun n => f (-n)) := by
  intro p
  simpa only [Function.comp_def, Equiv.neg_apply, Int.cast_neg, abs_neg] using
    (Equiv.neg ℤ).summable_iff.mpr (h p)

theorem add (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    RapidCoefficients (fun n => f n + g n) := by
  intro p
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ ((hf p).add (hg p))
  intro n
  calc
    _ ≤ (‖f n‖+‖g n‖)*(1+|(n : ℝ)|)^p := mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = _ := by ring

theorem smul (hf : RapidCoefficients f) (z : ℂ) : RapidCoefficients (fun n => z * f n) := by
  intro p
  simpa only [norm_mul, mul_assoc] using (hf p).mul_left ‖z‖

theorem summable_norm_smul {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (hf : RapidCoefficients f)
    (T : ℤ → V →ₗ[ℂ] H) {C K : ℝ} {p : ℕ}
    (v : V) (hT : ∀ n, ‖T n v‖ ≤ C*(1+|(n : ℝ)|)^p*K) :
    Summable (fun n => ‖f n • T n v‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((hf p).mul_right (C*K))
  intro n
  rw [norm_smul]
  calc
    _ ≤ ‖f n‖*(C*(1+|(n : ℝ)|)^p*K) := mul_le_mul_of_nonneg_left (hT n) (norm_nonneg _)
    _ = _ := by ring

end RapidCoefficients

namespace SummableLinearFamily
variable {ι V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem adjoint_tsum {T S : ι → V →ₗ[ℂ] H} (hT : ∀ v, Summable (fun n => T n v))
    (hS : ∀ v, Summable (fun n => S n v)) (j : V →ₗ[ℂ] H)
    (Hadj : ∀ n v w, inner ℂ (T n v) (j w) = inner ℂ (j v) (S n w)) (v w : V) :
    inner ℂ (tsumMap T hT v) (j w) = inner ℂ (j v) (tsumMap S hS w) := by
  change inner ℂ (∑' n, T n v) (j w) = inner ℂ (j v) (∑' n, S n w)
  calc
    _ = ∑' n, inner ℂ (T n v) (j w) := ((innerSL ℂ).flip (j w)).map_tsum (hT v)
    _ = ∑' n, inner ℂ (j v) (S n w) := tsum_congr (fun n => Hadj n v w)
    _ = _ := ((innerSL ℂ (j v)).map_tsum (hS w)).symm

end SummableLinearFamily

namespace CFTTypeVOA
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 

theorem PolynomialEnergyBound.physical {a : V} (ha : A.PolynomialEnergyBound a) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ p k : ℕ, ∀ m v,
      ‖A.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^p*‖(A.energyShift^k) v‖ := by
  obtain ⟨C, hC, p, k, H⟩ := ha
  refine ⟨C*(1+|((d : ℝ)-1)|)^p, by positivity, p, k, ?_⟩
  intro m v
  apply (H (m+d-1) v).trans
  have he : 1+|((m+(d : ℤ)-1 : ℤ) : ℝ)| ≤ (1+|((d : ℝ)-1)|)*(1+|(m : ℝ)|) := by
    have ht := abs_add_le (m : ℝ) ((d : ℝ)-1)
    have hn := mul_nonneg (abs_nonneg ((d : ℝ)-1)) (abs_nonneg (m : ℝ))
    push_cast
    rw [add_sub_assoc]
    nlinarith
  calc
    _ ≤ C*((1+|((d : ℝ)-1)|)*(1+|(m : ℝ)|))^p*‖(A.energyShift^k) v‖ := by gcongr
    _ = _ := by rw [mul_pow]; ring

 
theorem summable_norm_physicalSmear {a : V} (ha : A.PolynomialEnergyBound a)
    (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : V) :
    Summable (fun m : ℤ => ‖f m • (A.physicalMode a d m v : Completion V)‖) := by
  obtain ⟨C, _, p, k, H⟩ := ha.physical A d
  apply hf.summable_norm_smul
    (fun m => (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp (A.physicalMode a d m))
    v (C := C) (K := ‖(A.energyShift^k) v‖) (p := p)
  intro m
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map] using H m v

 
def smearedMap (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) : V →ₗ[ℂ] Completion V :=
  SummableLinearFamily.tsumMap
    (fun m => f m • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      (A.physicalMode a d m))
    (fun v => (A.summable_norm_physicalSmear ha d hf v).of_norm)

@[simp] theorem smearedMap_apply (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) (v : V) :
    A.smearedMap a d ha f hf v = ∑' m : ℤ, f m • (A.physicalMode a d m v : Completion V) := rfl

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 

theorem summable_adjointPhysicalSmear (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : V) :
    Summable (fun m : ℤ => star (f m) • (U.adjointPhysicalMode a d m v : Completion V)) := by
  have hs (j : ℕ) : Summable (fun m : ℤ =>
      star (f m) • (A.physicalMode ((A.virasoroMode 1^j) (U.pct a)) (d-j) (-m) v : Completion V)) := by
    have h := (A.summable_norm_physicalSmear
      (U.polynomialEnergyBounds hc ((A.virasoroMode 1^j) (U.pct a))) (d-j)
      hf.conj.neg_index v).of_norm
    simpa only [Function.comp_def, Equiv.neg_apply, neg_neg] using
      (Equiv.neg ℤ).summable_iff.mpr h
  have hs' (j : ℕ) := (hs j).const_smul ((-1 : ℂ)^d * (j.factorial : ℂ)⁻¹)
  have H := summable_sum (s := Finset.range (d+1)) (fun j _ => hs' j)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext m
  change star (f m) • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (U.adjointPhysicalMode a d m v) = _
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

 
theorem smearedCore_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (HilbertCore.operator (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)).IsClosable := by
  let j : V →ₗ[ℂ] Completion V := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap
  let T (m : ℤ) : V →ₗ[ℂ] Completion V := f m • j.comp (A.physicalMode a d m)
  let S (m : ℤ) : V →ₗ[ℂ] Completion V := star (f m) • j.comp (U.adjointPhysicalMode a d m)
  have hT : ∀ v, Summable (fun m => T m v) := fun v =>
    (A.summable_norm_physicalSmear (U.polynomialEnergyBounds hc a) d hf v).of_norm
  have hS : ∀ v, Summable (fun m => S m v) := fun v => U.summable_adjointPhysicalSmear hc a d hf v
  have Hadj (m : ℤ) (x y : V) : inner ℂ (T m x) (j y) = inner ℂ (j x) (S m y) := by
    change inner ℂ (f m • (A.physicalMode a d m x : Completion V)) (y : Completion V) =
      inner ℂ (x : Completion V) (star (f m) • (U.adjointPhysicalMode a d m y : Completion V))
    simp only [inner_smul_left, inner_smul_right, Completion.inner_coe]
    rw [U.adjointPhysicalMode_inner ha]
    rfl
  exact HilbertCore.closable (SummableLinearFamily.adjoint_tsum hT hS j Hadj)

 

def closedSmearedOperator (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : ℤ → ℂ) (hf : RapidCoefficients f) :
    Completion V →ₗ.[ℂ] Completion V :=
  (HilbertCore.operator (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)).closure

end UnitaryStructure
end CFTTypeVOA

open scoped ContDiff



namespace SmoothCircleFunction

theorem period_pos : 0 < 2*Real.pi := by positivity

def coefficient (f : SmoothCircleFunction) (n : ℤ) : ℂ :=
  fourierCoeffOn period_pos f n

theorem periodic_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) (2*Real.pi) := by
  intro x
  have he : (fun y => f (y+2*Real.pi)) = f := funext f.periodic
  have h := congrFun (iteratedDeriv_comp_add_const k (f : ℝ → ℂ) (2*Real.pi)) x
  rw [he] at h
  exact h.symm

theorem continuous_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) :
    Continuous (iteratedDeriv k f) := f.smooth.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))

theorem differentiable_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k f) := f.smooth.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k)

 

theorem coefficient_deriv_step (f : SmoothCircleFunction) (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (Complex.I*(n : ℂ))*fourierCoeffOn period_pos (iteratedDeriv k f) n =
      fourierCoeffOn period_pos (iteratedDeriv (k+1) f) n := by
  have HD (x : ℝ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (f.differentiable_iteratedDeriv k x).hasDerivAt
  have H := fourierCoeffOn_of_hasDerivAt period_pos hn (fun x _ => HD x)
    ((f.continuous_iteratedDeriv (k+1)).intervalIntegrable 0 (2*Real.pi))
  have hp := f.periodic_iteratedDeriv k 0
  simp only [zero_add] at hp
  rw [hp, sub_self, mul_zero, zero_sub] at H
  rw [H]
  push_cast
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hn', hpi]
  ring

theorem coefficient_iteratedDeriv (f : SmoothCircleFunction) (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (Complex.I*(n : ℂ))^k*f.coefficient n =
      fourierCoeffOn period_pos (iteratedDeriv k f) n := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih]
    exact f.coefficient_deriv_step k hn

 

theorem coefficient_norm_le {g : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x ∈ Set.Icc 0 (2*Real.pi), ‖g x‖ ≤ C) (n : ℤ) :
    ‖fourierCoeffOn period_pos g n‖ ≤ C := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have H : ‖∫ x in (0 : ℝ)..2*Real.pi,
      fourier (-n) (x : AddCircle (2*Real.pi-0)) • g x‖ ≤ C*|2*Real.pi-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_smul, show ‖fourier (-n) (x : AddCircle (2*Real.pi-0))‖ = 1 from Circle.norm_coe _, one_mul]
    exact hC x (by
      rw [Set.uIoc_of_le period_pos.le] at hx
      exact ⟨hx.1.le, hx.2⟩)
  calc
    _ ≤ ‖(1 / (2*Real.pi-0) : ℝ)‖*(C*|2*Real.pi-0|) := mul_le_mul_of_nonneg_left H (norm_nonneg _)
    _ = C := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos period_pos]
      field_simp

 
theorem coefficient_polynomial_decay (f : SmoothCircleFunction) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 → |(n : ℝ)|^k * ‖f.coefficient n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f.continuous_iteratedDeriv k).continuousOn (s := Set.Icc 0 (2*Real.pi))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, period_pos.le⟩)
  refine ⟨C, hC0, ?_⟩
  intro n hn
  have H := congrArg norm (f.coefficient_iteratedDeriv k hn)
  have hn' : ‖(n : ℂ)‖ = |(n : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, hn'] at H
  rw [H]
  exact coefficient_norm_le hC n

 

theorem rapid_coefficients (f : SmoothCircleFunction) : RapidCoefficients f.coefficient := by
  intro p
  obtain ⟨C, hC, HC⟩ := f.coefficient_polynomial_decay (p+2)
  have hweight {x r : ℝ} (hx : 1 ≤ x) (hr : 0 ≤ r) (H : x^(p+2)*r ≤ C) :
      r*(1+x)^p ≤ (2^p*C)*(x^2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hx) _)).mpr
    calc
      _ ≤ r*(2*x)^p*x^2 := by gcongr; linarith
      _ = 2^p*(x^(p+2)*r) := by rw [pow_add, mul_pow]; ring
      _ ≤ 2^p*C := mul_le_mul_of_nonneg_left H (by positivity)
  have hs : Summable (fun n : ℕ => (2^p*C)*(((n+1 : ℕ) : ℝ)^2)⁻¹) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))).mul_left _
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro n
    have hn : ((n+1 : ℕ) : ℤ) ≠ 0 := by omega
    have hx : 1 ≤ |(((n+1 : ℕ) : ℤ) : ℝ)| := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.succ_pos n
    have H := hweight hx (norm_nonneg (f.coefficient ((n+1 : ℕ) : ℤ))) (HC _ hn)
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+1))] using H
  · apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro n
    have hn : -((n+1 : ℕ) : ℤ) ≠ 0 := by omega
    have hx : 1 ≤ |((-((n+1 : ℕ) : ℤ) : ℤ) : ℝ)| := by
      rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.succ_pos n
    have H := hweight hx (norm_nonneg (f.coefficient (-((n+1 : ℕ) : ℤ)))) (HC _ hn)
    simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+1))] using H

end SmoothCircleFunction

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def smoothSmearedField (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V :=
  HilbertCore.operator (A.smearedMap a d (U.polynomialEnergyBounds hc a)
    f.coefficient f.rapid_coefficients)

theorem smoothSmearedField_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    (U.smoothSmearedField hc a d f).IsClosable :=
  U.smearedCore_closable hc ha f.rapid_coefficients

 
def closedSmoothField (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V :=
  (U.smoothSmearedField hc a d f).closure

theorem closedSmoothField_isClosed (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    (U.closedSmoothField hc a d f).IsClosed :=
  (U.smoothSmearedField_closable hc ha f).closure_isClosed

end CFTTypeVOA.UnitaryStructure

section GraphData
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace ClosedGraphData

abbrev Double (H : Type u) := WithLp 2 (H × H)

 
def graph (T : H →ₗ.[ℂ] H) : Submodule ℂ (Double H) :=
  T.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toLinearEquiv.toLinearMap

omit [CompleteSpace H] in
theorem graph_closed {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    IsClosed (graph T : Set (Double H)) :=
  hT.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H H).continuous

 

def projection (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) : Double H →L[ℂ] Double H := by
  letI : IsClosed (graph T : Set (Double H)) := graph_closed hT
  exact (graph T).starProjection

def inclusion (i : Bool) : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (if i then ContinuousLinearMap.inr ℂ H H else ContinuousLinearMap.inl ℂ H H)

def coordinate (i : Bool) : Double H →L[ℂ] H :=
  (if i then ContinuousLinearMap.snd ℂ H H else ContinuousLinearMap.fst ℂ H H).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap

 
def entry (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) : H →L[ℂ] H :=
  (coordinate i).comp ((projection T hT).comp (inclusion j))

end ClosedGraphData
end GraphData
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphCommutants
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
open scoped ContDiff
section GraphData
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace LocalOperatorAlgebra
open scoped Pointwise
 

def generated (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) =
        (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    rw [Set.centralizer_centralizer_centralizer]

@[simp]
theorem coe_generated_commutant (s : Set (H →L[ℂ] H)) :
    ((generated s).commutant : Set (H →L[ℂ] H)) = (s ∪ star s).centralizer := by
  rw [VonNeumannAlgebra.coe_commutant]
  change Set.centralizer (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) = _
  rw [StarSubalgebra.coe_centralizer_centralizer,
    Set.centralizer_centralizer_centralizer]



end LocalOperatorAlgebra

end GraphData

namespace SmoothCircleFunction

 
def onCircle (f : SmoothCircleFunction) : AddCircle (2*Real.pi) → ℂ :=
  f.periodic.lift

@[simp]
theorem onCircle_coe (f : SmoothCircleFunction) (t : ℝ) :
    f.onCircle (t : AddCircle (2*Real.pi)) = f.toFun t := rfl

end SmoothCircleFunction



namespace ProperCircleArc

def carrier (I : ProperCircleArc) : Set (AddCircle (2*Real.pi)) :=
  (fun t : ℝ => (t : AddCircle (2*Real.pi))) '' Set.Ioo I.left I.right

 
def complement (I : ProperCircleArc) : ProperCircleArc where
  left := I.right
  right := I.left + 2*Real.pi
  nonempty' := I.nondense'
  nondense' := by linarith [I.nonempty']

end ProperCircleArc

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def localGraphData (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : Set (Completion V →L[ℂ] Completion V) :=
  {x | ∃ (a : V) (d : ℕ) (ha : a ∈ A.grade d) (f : SmoothCircleFunction),
      tsupport f.onCircle ⊆ O ∧ ∃ i j : Bool,
        x = ClosedGraphData.entry (U.closedSmoothField hc a d f)
          (U.closedSmoothField_isClosed hc ha f) i j}

 

def localAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : VonNeumannAlgebra (Completion V) :=
  LocalOperatorAlgebra.generated (U.localGraphData hc O)

def intervalAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (I : ProperCircleArc) : VonNeumannAlgebra (Completion V) :=
  U.localAlgebra hc I.carrier

 

def CKLWStrongLocal (hc : A.toVertexAlgebra.C2Cofinite) : Prop :=
  (∀ a : V, A.PolynomialEnergyBound a) ∧
    ∀ I : ProperCircleArc, U.intervalAlgebra hc I ≤
      (U.intervalAlgebra hc I.complement).commutant

end CFTTypeVOA.UnitaryStructure

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 
def gradeEmbedding (d : ℕ) : A.grade d →ₗᵢ[ℂ] Completion V :=
  (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).comp (A.grade d).subtypeₗᵢ

include U in
theorem completed_grades_orthogonal :
    OrthogonalFamily ℂ (fun d => A.grade d) (fun d => gradeEmbedding (A := A) d) := by
  intro d e hde a b
  change inner ℂ ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) a.val)
    ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) b.val) = 0
  rw [LinearIsometry.inner_map_map]
  exact U.grades_orthogonal hde a.property b.property

include U in
 

theorem completed_isHilbertSum :
    IsHilbertSum ℂ (fun d => A.grade d) (fun d => gradeEmbedding (A := A) d) := by
  classical
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  apply IsHilbertSum.mk U.completed_grades_orthogonal
  let S := ⨆ d, LinearMap.range (gradeEmbedding (A := A) d).toLinearMap
  have hcore : HilbertCore.space V ≤ S := by
    rintro _ ⟨a, rfl⟩
    rw [← A.sum_gradeComponents a, map_sum]
    apply Submodule.sum_mem
    intro d _
    apply Submodule.mem_iSup_of_mem d
    exact ⟨⟨A.gradeComponent d a, A.gradeComponent_mem d a⟩, rfl⟩
  have hd : Dense (S : Set (Completion V)) := HilbertCore.dense.mono hcore
  exact le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp hd).symm

 
def energyCoordinates : Completion V ≃ₗᵢ[ℂ] lp (fun d => A.grade d) 2 :=
  U.completed_isHilbertSum.linearIsometryEquiv

@[simp]
theorem energyCoordinates_grade {d : ℕ} (a : A.grade d) :
    U.energyCoordinates (a.val : Completion V) = lp.single 2 d a := by
  apply U.energyCoordinates.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (U.completed_isHilbertSum.linearIsometryEquiv_symm_apply_single a).symm



end CFTTypeVOA.UnitaryStructure

open scoped ENNReal
namespace HilbertScale
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

abbrev Space (G : ι → Type u) [∀ i, NormedAddCommGroup (G i)] := lp G 2

 
def domain (w : ι → ℂ) : Submodule ℂ (Space G) where
  carrier := {x | Memℓp (fun i => w i • x i) 2}
  zero_mem' := by
    change Memℓp (fun i => w i • (0 : G i)) 2
    simpa only [smul_zero] using (zero_mem_ℓp' (E := G) (p := 2))
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun i => w i • (x i + y i)) 2
    convert hx.add hy using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    exact smul_add _ _ _
  smul_mem' := by
    intro c x hx
    change Memℓp (fun i => w i • (c • x i)) 2
    convert hx.const_smul c using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    exact smul_comm _ _ _

 
def diagonal (w : ι → ℂ) : Space G →ₗ.[ℂ] Space G where
  domain := domain w
  toFun :=
    { toFun := fun x => ⟨fun i => w i • x.val i, x.property⟩
      map_add' := by
        intro x y; ext i
        change w i • (x.val i + y.val i) = w i • x.val i + w i • y.val i
        exact smul_add _ _ _
      map_smul' := by intro c x; ext i; simp [smul_smul, mul_comm] }

@[simp]
theorem diagonal_apply (w : ι → ℂ) (x : (diagonal (G := G) w).domain) (i : ι) :
    diagonal w x i = w i • x.val i := rfl

theorem mem_graph_iff (w : ι → ℂ) (x y : Space G) :
    (x,y) ∈ (diagonal w).graph ↔ ∀ i, y i = w i • x i := by
  constructor
  · intro hz i
    obtain ⟨z,hz,hzw⟩ := (diagonal w).mem_graph_iff.mp hz
    have h1 : (z : Space G) = x := hz
    have h2 : diagonal w z = y := hzw
    have hi := congrArg (fun v : Space G => v i) h2
    change w i • (z : Space G) i = y i at hi
    rw [h1] at hi
    exact hi.symm
  · intro h
    have hd : x ∈ domain w := by
      change Memℓp (fun i => w i • x i) 2
      convert lp.memℓp y using 1
      all_goals try with_reducible_and_instances rfl
      ext i; exact (h i).symm
    exact (diagonal w).mem_graph_iff.mpr ⟨⟨x,hd⟩,rfl,by ext i; exact (h i).symm⟩

theorem diagonal_closed (w : ι → ℂ) : (diagonal (G := G) w).IsClosed := by
  have heq : ((diagonal (G := G) w).graph : Set (Space G × Space G)) =
      ⋂ i, {z : Space G × Space G | z.2 i = w i • z.1 i} := by
    ext z; simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_graph_iff w z.1 z.2
  rw [LinearPMap.IsClosed, heq]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((lp.evalCLM ℂ G 2 i).continuous.comp continuous_snd)
    (((lp.evalCLM ℂ G 2 i).continuous.comp continuous_fst).const_smul (w i))

variable [DecidableEq ι]

theorem single_mem_domain (w : ι → ℂ) (i : ι) (v : G i) :
    lp.single 2 i v ∈ domain w := by
  change Memℓp _ 2
  have heq : (fun j => w j • lp.single 2 i v j) = (lp.single 2 i (w i • v) : ∀ j, G j) := by
    ext j; by_cases h : j = i
    · subst h; simp
    · simp [lp.single_apply, h]
  rw [heq]
  exact lp.memℓp _

theorem diagonal_single (w : ι → ℂ) (i : ι) (v : G i) :
    diagonal w ⟨lp.single 2 i v, single_mem_domain w i v⟩ = lp.single 2 i (w i • v) := by
  ext j; by_cases h : j = i
  · subst h; simp
  · simp [lp.single_apply, h]

variable [∀ i, CompleteSpace (G i)]


def finiteCore : Submodule ℂ (Space G) :=
  Submodule.span ℂ {x | ∃ i v, x = lp.single 2 i v}

omit [∀ i, CompleteSpace (G i)] in
theorem single_mem_finiteCore (i : ι) (v : G i) :
    lp.single 2 i v ∈ finiteCore (G := G) :=
  Submodule.subset_span ⟨i,v,rfl⟩

omit [∀ i, CompleteSpace (G i)] in
theorem finiteCore_le_domain (w : ι → ℂ) : finiteCore (G := G) ≤ domain w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,v,rfl⟩
  exact single_mem_domain w i v

omit [∀ i, CompleteSpace (G i)] in
 

theorem diagonal_hasCore (w : ι → ℂ) :
    (diagonal (G := G) w).HasCore finiteCore := by
  let T := (diagonal (G := G) w).domRestrict finiteCore
  have hT : T.IsClosable := (diagonal_closed w).isClosable.leIsClosable
    LinearPMap.domRestrict_le
  refine ⟨finiteCore_le_domain w, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hT.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) (diagonal_closed w)
  · intro z hz
    have hzy := (mem_graph_iff w z.1 z.2).mp hz
    have hs := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z.1).prodMk
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z.2)
    apply mem_closure_of_tendsto hs
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    apply T.mem_graph_iff.mpr
    have hdom : lp.single 2 i (z.1 i) ∈ T.domain :=
      ⟨single_mem_finiteCore _ _, single_mem_domain _ _ _⟩
    refine ⟨⟨_,hdom⟩,rfl,?_⟩
    change diagonal w ⟨lp.single 2 i (z.1 i),single_mem_domain _ _ _⟩ = _
    rw [diagonal_single, ← hzy i]



end HilbertScale

namespace OperatorTransport
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

 

def transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) : H →ₗ.[ℂ] H where
  domain := T.domain.comap E.toLinearEquiv.toLinearMap
  toFun :=
    { toFun := fun x => E.symm (T ⟨E x.val, x.property⟩)
      map_add' := by
        intro x y
        simp only [Submodule.coe_add,map_add]
        change E.symm (T (⟨E x.val,x.property⟩ + ⟨E y.val,y.property⟩)) = _
        rw [T.map_add,map_add]
      map_smul' := by
        intro c x
        simp only [Submodule.coe_smul,map_smul]
        change E.symm (T (c • (⟨E x.val,x.property⟩ : T.domain))) = _
        rw [T.map_smul,map_smul]
        rfl }

theorem mem_graph_iff (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (x y : H) :
    (x,y) ∈ (transport E T).graph ↔ (E x, E y) ∈ T.graph := by
  rw [(transport E T).mem_graph_iff, T.mem_graph_iff]
  constructor
  · rintro ⟨z,hz,hzy⟩
    dsimp only [Prod.fst,Prod.snd] at hz hzy ⊢
    have hmem : E z.val ∈ T.domain := z.property
    refine ⟨⟨E z.val,hmem⟩,congrArg E hz,?_⟩
    rw [← hzy]
    exact (E.apply_symm_apply _).symm
  · rintro ⟨z,hz,hzy⟩
    dsimp only [Prod.fst,Prod.snd] at hz hzy ⊢
    have hx : x ∈ (transport E T).domain := by
      change E x ∈ T.domain
      rw [← hz]; exact z.property
    refine ⟨⟨x,hx⟩,rfl,?_⟩
    change E.symm (T ⟨E x,hx⟩) = y
    have hz' : (⟨E x,hx⟩ : T.domain) = z := Subtype.ext hz.symm
    rw [hz',hzy,E.symm_apply_apply]
end OperatorTransport
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphEquiv
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
open scoped ContDiff
open scoped ENNReal
namespace OperatorTransport
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
def graphEquiv (E : H ≃ₗᵢ[ℂ] K) : (H × H) ≃L[ℂ] (K × K) :=
  E.toContinuousLinearEquiv.prodCongr E.toContinuousLinearEquiv

theorem graph_eq (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    (transport E T).graph = T.graph.comap (graphEquiv E).toLinearMap := by
  ext z
  exact mem_graph_iff E T z.1 z.2

theorem closed (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosed) :
    (transport E T).IsClosed := by
  rw [LinearPMap.IsClosed,graph_eq]
  exact hT.preimage (graphEquiv E).continuous

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem domRestrict (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (S : Submodule ℂ K) :
    (transport E T).domRestrict (S.comap E.toLinearEquiv.toLinearMap) =
      transport E (T.domRestrict S) := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rw [mem_graph_iff]
  simp only [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x,hx,hy⟩
    exact ⟨⟨E x.val,x.property⟩,congrArg E hx,by rw [← hy]; exact (E.apply_symm_apply _).symm⟩
  · rintro ⟨x,hx,hy⟩
    have hz : z.1 ∈ ((transport E T).domRestrict (S.comap E.toLinearEquiv.toLinearMap)).domain := by
      change E z.1 ∈ S ⊓ T.domain
      rw [← hx]; exact x.property
    refine ⟨⟨z.1,hz⟩,rfl,?_⟩
    change E.symm (T ⟨E z.1,hz.2⟩) = z.2
    have heq : (⟨E z.1,hz.2⟩ : T.domain) = ⟨x.val,x.property.2⟩ := Subtype.ext hx.symm
    rw [heq]
    change E.symm ((T.domRestrict S) x) = _
    rw [hy,E.symm_apply_apply]

omit [CompleteSpace H] [CompleteSpace K] in
theorem hasCore (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosed)
    {S : Submodule ℂ K} (hS : T.HasCore S) :
    (transport E T).HasCore (S.comap E.toLinearEquiv.toLinearMap) := by
  have hle : (transport E T).domRestrict (S.comap E.toLinearEquiv.toLinearMap) ≤
      transport E T := LinearPMap.domRestrict_le
  have hle' : T.domRestrict S ≤ T := LinearPMap.domRestrict_le
  have hc := (closed E hT).isClosable.leIsClosable hle
  have hc' := hT.isClosable.leIsClosable hle' 
  refine ⟨fun x hx => hS.le_domain hx,?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hc.graph_closure_eq_closure_graph,domRestrict,graph_eq,graph_eq]
  have hh : (T.domRestrict S).graph.topologicalClosure = T.graph := by
    rw [hc'.graph_closure_eq_closure_graph,hS.closure_eq]
  apply SetLike.coe_injective
  change closure ((graphEquiv E) ⁻¹' ((T.domRestrict S).graph : Set (K × K))) =
    (graphEquiv E) ⁻¹' (T.graph : Set (K × K))
  rw [← (graphEquiv E).preimage_closure]
  exact congrArg (fun s : Set (K × K) => (graphEquiv E) ⁻¹' s) (congrArg SetLike.coe hh)

end OperatorTransport

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

theorem finiteCore_comap_energyCoordinates :
    (HilbertScale.finiteCore (G := fun d => A.grade d)).comap
      U.energyCoordinates.toLinearEquiv.toLinearMap = HilbertCore.space V := by
  classical
  apply le_antisymm
  · intro x hx
    have h : ∀ z ∈ HilbertScale.finiteCore (G := fun d => A.grade d),
        U.energyCoordinates.symm z ∈ HilbertCore.space V := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨d,a,rfl⟩ := hz
        rw [← U.energyCoordinates_grade a,U.energyCoordinates.symm_apply_apply]
        exact ⟨a.val,rfl⟩
      | zero => simpa only [map_zero] using (HilbertCore.space V).zero_mem
      | add z w _ _ hz hw => simpa only [map_add] using (HilbertCore.space V).add_mem hz hw
      | smul c z _ hz => simpa only [map_smul] using (HilbertCore.space V).smul_mem c hz
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h (U.energyCoordinates x) hx
  · rintro x ⟨a,rfl⟩
    change U.energyCoordinates (a : Completion V) ∈ HilbertScale.finiteCore
    apply A.homogeneous_induction (P := fun a =>
      U.energyCoordinates (a : Completion V) ∈ HilbertScale.finiteCore)
    · change U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) 0) ∈ _
      rw [map_zero,map_zero]
      exact Submodule.zero_mem _
    · intro d b hb
      rw [U.energyCoordinates_grade ⟨b,hb⟩]
      exact HilbertScale.single_mem_finiteCore _ _
    · intro b c hb hc
      change U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (b+c)) ∈ _
      rw [map_add,map_add]
      exact Submodule.add_mem _ hb hc

 

def energyOperator (w : ℕ → ℝ) : Completion V →ₗ.[ℂ] Completion V :=
  OperatorTransport.transport U.energyCoordinates
    (HilbertScale.diagonal (fun d => (w d : ℂ)))

theorem energyOperator_closed (w : ℕ → ℝ) : (U.energyOperator w).IsClosed :=
  OperatorTransport.closed _ (HilbertScale.diagonal_closed _)



theorem energyOperator_hasCore (w : ℕ → ℝ) :
    (U.energyOperator w).HasCore (HilbertCore.space V) := by
  have h := OperatorTransport.hasCore U.energyCoordinates
    (HilbertScale.diagonal_closed (G := fun d => A.grade d) (fun d => (w d : ℂ)))
    (HilbertScale.diagonal_hasCore (fun d => (w d : ℂ)))
  rw [U.finiteCore_comap_energyCoordinates] at h
  exact h

theorem coe_mem_energyOperator (w : ℕ → ℝ) (a : V) :
    (a : Completion V) ∈ (U.energyOperator w).domain :=
  (U.energyOperator_hasCore w).le_domain ⟨a,rfl⟩


def energyPower (k : ℕ) : Completion V →ₗ.[ℂ] Completion V :=
  U.energyOperator (fun d => (1+(d : ℝ))^k)

theorem energyOperator_grade (w : ℕ → ℝ) {d : ℕ} (a : A.grade d) :
    U.energyOperator w ⟨(a.val : Completion V),U.coe_mem_energyOperator w a.val⟩ =
      (w d : ℂ) • (a.val : Completion V) := by
  have hg : ((a.val : Completion V), (w d : ℂ) • (a.val : Completion V)) ∈
      (U.energyOperator w).graph := by
    apply (OperatorTransport.mem_graph_iff _ _ _ _).mpr
    rw [map_smul,U.energyCoordinates_grade]
    apply (HilbertScale.diagonal (fun d => (w d : ℂ))).mem_graph_iff.mpr
    refine ⟨⟨_,HilbertScale.single_mem_domain _ _ _⟩,rfl,?_⟩
    rw [HilbertScale.diagonal_single]
    ext i
    simp only [lp.coeFn_smul,Pi.smul_apply]
    by_cases hi : i = d
    · subst i; simp
    · simp [lp.single_apply,hi]
  obtain ⟨x,hx,hy⟩ := (U.energyOperator w).mem_graph_iff.mp hg
  have heq : x = ⟨(a.val : Completion V),U.coe_mem_energyOperator w a.val⟩ :=
    Subtype.ext hx
  rwa [heq] at hy

 
theorem energyPower_coe (k : ℕ) (a : V) :
    U.energyPower k ⟨(a : Completion V),U.coe_mem_energyOperator _ a⟩ =
      ((A.energyShift^k) a : Completion V) := by
  apply A.homogeneous_induction (P := fun a =>
    U.energyPower k ⟨(a : Completion V),U.coe_mem_energyOperator _ a⟩ =
      ((A.energyShift^k) a : Completion V))
  · change (U.energyPower k).toFun 0 = ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V)
      ((A.energyShift^k) 0))
    rw [map_zero,map_zero,map_zero]
  · intro d b hb
    calc
      _ = (((1+(d : ℝ))^k : ℝ) : ℂ) • (b : Completion V) :=
        U.energyOperator_grade (fun d => (1+(d : ℝ))^k) ⟨b,hb⟩
      _ = ((A.energyShift^k) b : Completion V) := by
        rw [A.energyShift_pow_on_grade hb]
        change _ = (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (_ • b)
        rw [map_smul,Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
        rfl
  · intro b c hb hc
    have hbc : ((b+c : V) : Completion V) = (b : Completion V) + (c : Completion V) :=
      map_add (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) b c
    have hx : (⟨((b+c : V) : Completion V),U.coe_mem_energyOperator _ (b+c)⟩ :
        (U.energyPower k).domain) =
      ⟨(b : Completion V),U.coe_mem_energyOperator _ b⟩ +
      ⟨(c : Completion V),U.coe_mem_energyOperator _ c⟩ := Subtype.ext hbc
    rw [hx,(U.energyPower k).map_add,hb,hc]
    change _ = (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) ((A.energyShift^k) (b+c))
    rw [map_add,map_add]
    rfl

 

def smoothEnergySpace : Submodule ℂ (Completion V) := ⨅ k : ℕ, (U.energyPower k).domain

end CFTTypeVOA.UnitaryStructure

end StronglyRationalVOA

open scoped Topology
open Filter
namespace StronglyRationalVOA
namespace SymmetricOperator
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


variable [CompleteSpace H]



omit [CompleteSpace H] in
 

theorem formalAdjoint_closure {T S : H →ₗ.[ℂ] H}
    (hT : T.IsClosable) (hS : S.IsClosable) (hs : T.IsFormalAdjoint S) :
    T.closure.IsFormalAdjoint S.closure := by
  intro x y
  have hx : ((x : H),T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph_iff.mpr ⟨x,rfl,rfl⟩
  have hy : ((y : H),S.closure y) ∈ S.graph.topologicalClosure := by
    rw [hS.graph_closure_eq_closure_graph]
    exact S.closure.mem_graph_iff.mpr ⟨y,rfl,rfl⟩
  have hleft : ∀ q ∈ S.graph, ∀ p ∈ T.graph.topologicalClosure,
      inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
    intro q hq
    apply closure_minimal
    · intro p hp
      obtain ⟨a,ha,hTa⟩ := T.mem_graph_iff.mp hp
      obtain ⟨b,hb,hSb⟩ := S.mem_graph_iff.mp hq
      change inner ℂ p.2 q.1 = inner ℂ p.1 q.2
      rw [← ha,← hTa,← hb,← hSb]
      exact hs a b
    · exact isClosed_eq (continuous_snd.inner continuous_const)
        (continuous_fst.inner continuous_const)
  have hright : ∀ q ∈ S.graph.topologicalClosure,
      inner ℂ (T.closure x) q.1 = inner ℂ (x : H) q.2 := by
    apply closure_minimal
    · intro q hq; exact hleft q hq _ hx
    · exact isClosed_eq (continuous_const.inner continuous_fst)
        (continuous_const.inner continuous_snd)
  exact hright _ hy



end SymmetricOperator
end StronglyRationalVOA

namespace StronglyRationalVOA
namespace HilbertScale
open scoped ENNReal
universe u
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 
def boundedMultiplier (w : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    Space G →L[ℂ] Space G :=
  lp.mapCLM 2 (fun i => w i • ContinuousLinearMap.id ℂ (G i)) hC
    (fun i => (norm_smul_le _ _).trans ((mul_le_mul_of_nonneg_left
      ContinuousLinearMap.norm_id_le (norm_nonneg (w i))).trans (by simpa using hw i)))

omit [DecidableEq ι] in
@[simp] theorem boundedMultiplier_apply (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (x : Space G) (i : ι) :
    boundedMultiplier w hC hw x i = w i • x i := rfl

omit [DecidableEq ι] in
theorem boundedMultiplier_norm (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) : ‖boundedMultiplier (G := G) w hC hw‖ ≤ C :=
  lp.norm_mapCLM_le _ _ _ _
end HilbertScale
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BoundedMultiplierSingle
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
universe u
open scoped Topology
open Filter
namespace StronglyRationalVOA

namespace HilbertScale
open scoped ENNReal
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι] in
theorem boundedMultiplier_adjoint (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    (boundedMultiplier (G := G) w hC hw).adjoint =
      boundedMultiplier (fun i => star (w i)) hC (fun i => by simpa using hw i) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← (lp.hasSum_inner (boundedMultiplier w hC hw y) x).tsum_eq,
    ← (lp.hasSum_inner y (boundedMultiplier (fun i => star (w i)) hC
      (fun i => by simpa using hw i) x)).tsum_eq]
  apply tsum_congr
  intro i
  simp only [boundedMultiplier_apply,inner_smul_left,inner_smul_right,starRingEnd_apply]

omit [∀ (i : ι), CompleteSpace (G i)] in
theorem finiteCore_dense : Dense (finiteCore (G := G) : Set (Space G)) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  apply Filter.Eventually.of_forall
  intro s
  exact Submodule.sum_mem _ (fun i _ => single_mem_finiteCore i (x i))

end HilbertScale

end StronglyRationalVOA

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [instDec : DecidableEq ι]

def coreDiagonal (w : ι → ℂ) : finiteCore (G := G) →ₗ[ℂ] Space G :=
  (diagonal w).toFun.comp (Submodule.inclusion (finiteCore_le_domain w))

@[simp] theorem coreDiagonal_apply (w : ι → ℂ) (x : finiteCore (G := G)) (i : ι) :
    coreDiagonal w x i = w i • (x : Space G) i := rfl

@[simp] theorem coreDiagonal_single (w : ι → ℂ) (i : ι) (v : G i) :
    coreDiagonal w ⟨lp.single 2 i v,single_mem_finiteCore i v⟩ = lp.single 2 i (w i • v) :=
  diagonal_single w i v

theorem coreDiagonal_mem_finiteCore (w : ι → ℂ) (x : finiteCore (G := G)) :
    coreDiagonal w x ∈ finiteCore := by
  obtain ⟨x,hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,v,rfl⟩ := hx
    rw [coreDiagonal_single]
    exact single_mem_finiteCore i _
  | zero =>
    change coreDiagonal w 0 ∈ finiteCore (G := G)
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    change coreDiagonal w (⟨x,hx⟩+⟨y,hy⟩) ∈ finiteCore
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    change coreDiagonal w (c • ⟨x,hx⟩) ∈ finiteCore
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

def coreMultiplier (w : ι → ℂ) : finiteCore (G := G) →ₗ[ℂ] finiteCore (G := G) :=
  (coreDiagonal (G := G) w).codRestrict (finiteCore (G := G)) (coreDiagonal_mem_finiteCore w)

@[simp] theorem coreMultiplier_coe (w : ι → ℂ) (x : finiteCore (G := G)) :
    (coreMultiplier w x : Space G) = coreDiagonal w x := rfl

@[simp] theorem coreMultiplier_apply (w : ι → ℂ) (x : finiteCore (G := G)) (i : ι) :
    (coreMultiplier w x : Space G) i = w i • (x : Space G) i := rfl

theorem coreMultiplier_mul (w v : ι → ℂ) (x : finiteCore (G := G)) :
    coreMultiplier w (coreMultiplier v x) = coreMultiplier (fun i => w i*v i) x := by
  apply Subtype.ext
  apply lp.ext
  funext i
  simp only [coreMultiplier_apply,mul_smul]

theorem coreMultiplier_one (x : finiteCore (G := G)) :
    coreMultiplier (fun _ => 1) x = x := by
  apply Subtype.ext
  apply lp.ext
  funext i
  simp only [coreMultiplier_apply,one_smul]

variable [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι]

noncomputable def resolventWeight (h : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  ((n : ℝ)+1)/((n : ℝ)+1+h i)

noncomputable def complementWeight (h : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  h i/((n : ℝ)+1+h i)

theorem resolventWeight_nonneg (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    0 ≤ resolventWeight h n i := by
  unfold resolventWeight
  have := hh i
  positivity

theorem resolventWeight_le_one (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    resolventWeight h n i ≤ 1 := by
  unfold resolventWeight
  have := hh i
  apply (div_le_one (by positivity)).mpr
  linarith

theorem complementWeight_nonneg (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    0 ≤ complementWeight h n i := by
  unfold complementWeight
  have := hh i
  positivity

theorem complementWeight_le_one (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (i : ι) :
    complementWeight h n i ≤ 1 := by
  unfold complementWeight
  have := hh i
  apply (div_le_one (by positivity)).mpr
  have hh0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

omit [DecidableEq ι] in
def resolvent (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => (resolventWeight h n i : ℂ)) zero_le_one (fun i => by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (resolventWeight_nonneg h hh n i)]
    exact resolventWeight_le_one h hh n i)

omit [DecidableEq ι] in
def complement (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => (complementWeight h n i : ℂ)) zero_le_one (fun i => by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (complementWeight_nonneg h hh n i)]
    exact complementWeight_le_one h hh n i)

@[simp] theorem resolvent_apply (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : Space G) (i : ι) : resolvent h hh n x i = (resolventWeight h n i : ℂ) • x i := rfl

@[simp] theorem complement_apply (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : Space G) (i : ι) : complement h hh n x i = (complementWeight h n i : ℂ) • x i := rfl

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA
theorem inner_tsum_left {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {g : ι → H} (hg : Summable g) (y : H) :
    inner ℂ (∑' i, g i) y = ∑' i, inner ℂ (g i) y :=
  ((innerSL ℂ).flip y).map_tsum hg

theorem inner_tsum_right {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {g : ι → H} (hg : Summable g) (x : H) :
    inner ℂ x (∑' i, g i) = ∑' i, inner ℂ x (g i) :=
  (innerSL ℂ x).map_tsum hg

namespace CFTTypeVOA
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (A : CFTTypeVOA V)

 

theorem smearedMap_bound {a : V} {d k p : ℕ} (ha : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) {C : ℝ}
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖)
    (v : V) :
    ‖A.smearedMap a d ha f hf v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^k) v‖ := by
  rw [smearedMap_apply]
  apply (norm_tsum_le_tsum_norm (A.summable_norm_physicalSmear ha d hf v)).trans
  calc
    _ ≤ ∑' n : ℤ, (‖f n‖*(1+|(n : ℝ)|)^p)*(C*‖(A.energyShift^k) v‖) := by
      apply Summable.tsum_le_tsum _ (A.summable_norm_physicalSmear ha d hf v)
        ((hf p).mul_right _)
      intro n
      simp only [norm_smul,Completion.norm_coe]
      calc
        _ ≤ ‖f n‖*(C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖) :=
          mul_le_mul_of_nonneg_left (hb n v) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [tsum_mul_right]; ring

theorem energyShift_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (n : ℤ) (v : V) :
    A.energyShift (A.physicalMode a d n v)-A.physicalMode a d n (A.energyShift v) =
      (-(n : ℂ)) • A.physicalMode a d n v := by
  have h := A.energy_mode_commutator ha (n+d-1) v
  simp only [Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one] at h
  have he : (d : ℂ)-((n : ℂ)+d-1)-1 = -(n : ℂ) := by ring
  rw [he] at h
  simpa only [energyShift,LinearMap.add_apply,Module.End.one_apply,map_add,
    add_sub_add_left_eq_sub,physicalMode] using h

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

include U in
theorem energyShift_adjoint (x y : V) :
    inner ℂ (A.energyShift x) y = inner ℂ x (A.energyShift y) := by
  simp only [energyShift,LinearMap.add_apply,Module.End.one_apply,inner_add_left,
    inner_add_right,U.virasoro_adjoint,neg_zero]

 

theorem smearedMap_symmetric {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (he : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hreal : ∀ n, star (f n) = f (-n))
    (x y : V) :
    inner ℂ (A.smearedMap a d he f hf x) (y : Completion V) =
      inner ℂ (x : Completion V) (A.smearedMap a d he f hf y) := by
  rw [smearedMap_apply,smearedMap_apply,
    inner_tsum_left (A.summable_norm_physicalSmear he d hf x).of_norm,
    inner_tsum_right (A.summable_norm_physicalSmear he d hf y).of_norm]
  calc
    _ = ∑' n : ℤ, inner ℂ (x : Completion V)
        (f (-n) • (A.physicalMode a d (-n) y : Completion V)) := by
      apply tsum_congr
      intro n
      simp only [inner_smul_left,inner_smul_right,Completion.inner_coe,starRingEnd_apply,
        hreal,U.physicalMode_adjoint ha hq hh]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun n => inner ℂ (x : Completion V)
      (f n • (A.physicalMode a d n y : Completion V)))



end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

omit [∀ i, CompleteSpace (G i)] in
theorem coreMultiplier_cancel (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (x : finiteCore (G := G)) :
    coreMultiplier (fun i => (h i : ℂ)) (coreMultiplier (fun i => (h i : ℂ)⁻¹) x) = x := by
  rw [coreMultiplier_mul]
  have hw : (fun i => (h i : ℂ) * (h i : ℂ)⁻¹) = fun _ => 1 := by
    funext i
    apply mul_inv_cancel₀
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))
  rw [hw,coreMultiplier_one]

omit [∀ i, CompleteSpace (G i)] in
theorem coreMultiplier_inv_cancel (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (x : finiteCore (G := G)) :
    coreMultiplier (fun i => (h i : ℂ)⁻¹) (coreMultiplier (fun i => (h i : ℂ)) x) = x := by
  rw [coreMultiplier_mul]
  have hw : (fun i => (h i : ℂ)⁻¹ * (h i : ℂ)) = fun _ => 1 := by
    funext i
    apply inv_mul_cancel₀
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))
  rw [hw,coreMultiplier_one]

 
def energyNormalized (h : ι → ℝ) (M : finiteCore (G := G) →ₗ[ℂ] Space G) :
    finiteCore (G := G) →ₗ[ℂ] Space G :=
  M.comp (coreMultiplier (fun i => (h i : ℂ)⁻¹))

 

def energyExtension (h : ι → ℝ) (M : finiteCore (G := G) →ₗ[ℂ] Space G) :
    Space G →L[ℂ] Space G :=
  (energyNormalized h M).extendOfNorm (finiteCore (G := G)).subtype

omit [∀ i, CompleteSpace (G i)] in
theorem energyNormalized_bound (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (x : finiteCore (G := G)) : ‖energyNormalized h M x‖ ≤ C*‖(x : Space G)‖ := by
  have he : coreDiagonal (fun i => (h i : ℂ))
      (coreMultiplier (fun i => (h i : ℂ)⁻¹) x) = (x : Space G) :=
    congrArg Subtype.val (coreMultiplier_cancel h hh x)
  simpa only [energyNormalized,LinearMap.comp_apply,he] using
    hM (coreMultiplier (fun i => (h i : ℂ)⁻¹) x)

theorem energyExtension_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (x : finiteCore (G := G)) :
    energyExtension h M x = M (coreMultiplier (fun i => (h i : ℂ)⁻¹) x) := by
  exact (energyNormalized h M).extendOfNorm_eq
    (e := (finiteCore (G := G)).subtype) (by simpa [DenseRange] using (finiteCore_dense (G := G)))
    ⟨C,energyNormalized_bound h hh M hM⟩ x

theorem energyExtension_weighted (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (x : finiteCore (G := G)) :
    energyExtension h M (coreDiagonal (fun i => (h i : ℂ)) x) = M x := by
  change energyExtension h M ((coreMultiplier (fun i => (h i : ℂ)) x : finiteCore) : Space G) = _
  rw [energyExtension_core h hh M hM,coreMultiplier_inv_cancel h hh]

theorem energyExtension_norm (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖) :
    ‖energyExtension h M‖ ≤ C :=
  (energyNormalized h M).opNorm_extendOfNorm_le
    (e := (finiteCore (G := G)).subtype) (by simpa [DenseRange] using (finiteCore_dense (G := G)))
    hC (energyNormalized_bound h hh M hM)

end StronglyRationalVOA.HilbertScale

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ColumnControl
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
def ColumnControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ v ∈ A.energyCutoff N,
    (∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2) ≤ K * ‖v‖^2

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 
def AdjointColumnControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ v ∈ A.energyCutoff N,
    (∑ m ∈ Finset.range (N + 1), ‖U.adjointPhysicalMode a d (-(m : ℤ)) v‖^2) ≤ K * ‖v‖^2

end UnitaryStructure


end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 

def ColumnGrowth (X : ℕ → ℝ) (a : V) (d p q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N, A.ColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q)

 

def ZeroGrowth (X : ℕ → ℝ) (a : V) (d p q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N v, v ∈ A.energyCutoff N →
    ‖A.physicalMode a d 0 v‖^2 ≤ C * (N + 1 : ℝ)^p * X N^q * ‖v‖^2



def SharpDegreeGrowth (X : ℕ → ℝ) (a : V) (d w : ℕ) : Prop :=
  A.ColumnGrowth X a d (2*d-1) (2*w) ∧ A.ZeroGrowth X a d (max 1 (2*d-2)) (2*w)

def SharpGrowth (X : ℕ → ℝ) (a : V) (d : ℕ) : Prop :=
  A.SharpDegreeGrowth X a d d

end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertRegularization
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]


def coreOperator (M : finiteCore (G := G) →ₗ[ℂ] Space G) : Space G →ₗ.[ℂ] Space G where
  domain := finiteCore
  toFun := M

end StronglyRationalVOA.HilbertScale

open scoped Topology
open Filter

namespace StronglyRationalVOA.OperatorTransport
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem monotone (E : H ≃ₗᵢ[ℂ] K) : Monotone (transport E) := by
  intro S T hST
  apply LinearPMap.le_of_le_graph
  rw [graph_eq,graph_eq]
  exact Submodule.comap_mono (LinearPMap.le_graph_of_le hST)

theorem closable (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosable) :
    (transport E T).IsClosable :=
  (closed E hT.closure_isClosed).isClosable.leIsClosable (monotone E T.le_closure)

theorem closure (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosable) :
    (transport E T).closure = transport E T.closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (closable E hT).graph_closure_eq_closure_graph,graph_eq,graph_eq,
    ← hT.graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  change _root_.closure ((graphEquiv E) ⁻¹' (T.graph : Set (K × K))) =
    (graphEquiv E) ⁻¹' _root_.closure (T.graph : Set (K × K))
  exact ((graphEquiv E).preimage_closure _).symm

end StronglyRationalVOA.OperatorTransport

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

theorem coreEnergy_mem (a : V) :
    U.energyCoordinates (a : Completion V) ∈ HilbertScale.finiteCore := by
  have h : (a : Completion V) ∈ HilbertCore.space V := ⟨a,rfl⟩
  rwa [← U.finiteCore_comap_energyCoordinates] at h

 

def coreEnergyCoordinates : V ≃ₗ[ℂ] HilbertScale.finiteCore (G := fun d => A.grade d) :=
  LinearEquiv.ofBijective
    ((U.energyCoordinates.toLinearEquiv.toLinearMap.comp
      (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap).codRestrict _ U.coreEnergy_mem)
    (by
      constructor
      · intro x y h
        exact (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective
          (U.energyCoordinates.injective (congrArg Subtype.val h))
      · intro x
        have hx : U.energyCoordinates.symm x ∈ HilbertCore.space V := by
          rw [← U.finiteCore_comap_energyCoordinates]
          change U.energyCoordinates (U.energyCoordinates.symm x) ∈ HilbertScale.finiteCore
          rw [U.energyCoordinates.apply_symm_apply]
          exact x.property
        obtain ⟨v,hv⟩ := hx
        refine ⟨v,Subtype.ext ?_⟩
        change (v : Completion V) = U.energyCoordinates.symm x at hv
        change U.energyCoordinates (v : Completion V) = x
        rw [hv,U.energyCoordinates.apply_symm_apply])

@[simp] theorem coreEnergyCoordinates_coe (a : V) :
    (U.coreEnergyCoordinates a : HilbertScale.Space (fun d => A.grade d)) =
      U.energyCoordinates (a : Completion V) := rfl


def spectralCoreMap (T : V →ₗ[ℂ] Completion V) :
    HilbertScale.finiteCore (G := fun d => A.grade d) →ₗ[ℂ] HilbertScale.Space (fun d => A.grade d) :=
  U.energyCoordinates.toLinearEquiv.toLinearMap.comp (T.comp U.coreEnergyCoordinates.symm.toLinearMap)

@[simp] theorem spectralCoreMap_apply (T : V →ₗ[ℂ] Completion V) (a : V) :
    U.spectralCoreMap T (U.coreEnergyCoordinates a) = U.energyCoordinates (T a) := by
  simp [spectralCoreMap]

theorem spectralCoreOperator_transport (T : V →ₗ[ℂ] Completion V) :
    OperatorTransport.transport U.energyCoordinates (HilbertScale.coreOperator (U.spectralCoreMap T)) =
      HilbertCore.operator T := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rw [OperatorTransport.mem_graph_iff]
  constructor
  · intro h
    obtain ⟨x,hx,hy⟩ := (HilbertScale.coreOperator (U.spectralCoreMap T)).mem_graph_iff.mp h
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    have hv : (v : Completion V) = z.1 := U.energyCoordinates.injective hx
    have hw : T v = z.2 := by
      apply U.energyCoordinates.injective
      change U.spectralCoreMap T (U.coreEnergyCoordinates v) = _ at hy
      simpa only [U.spectralCoreMap_apply] using hy
    apply (HilbertCore.operator T).mem_graph_iff.mpr
    exact ⟨HilbertCore.equiv V v,hv,by simpa only [HilbertCore.operator_apply] using hw⟩
  · intro h
    obtain ⟨x,hx,hy⟩ := (HilbertCore.operator T).mem_graph_iff.mp h
    obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective x
    apply (HilbertScale.coreOperator (U.spectralCoreMap T)).mem_graph_iff.mpr
    refine ⟨U.coreEnergyCoordinates v,congrArg U.energyCoordinates hx,?_⟩
    change U.spectralCoreMap T (U.coreEnergyCoordinates v) = U.energyCoordinates z.2
    rw [U.spectralCoreMap_apply]
    exact congrArg U.energyCoordinates (by simpa only [HilbertCore.operator_apply] using hy)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

theorem physicalMode_sobolev_bound {a : V} {d k p : ℕ} (ha : a ∈ A.grade d)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖)
    (r : ℕ) (n : ℤ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)‖ ≤
      C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) v‖ := by
  induction r generalizing v with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero] using hb n v
  | succ r ih =>
    have he : A.energyShift (A.physicalMode a d n v) =
        (-(n : ℂ)) • A.physicalMode a d n v + A.physicalMode a d n (A.energyShift v) :=
      sub_eq_iff_eq_add.mp (A.energyShift_physical_commutator ha n v)
    rw [pow_succ,Module.End.mul_apply,he,map_add,map_smul]
    have hn : ‖-(n : ℂ)‖ = |(n : ℝ)| := by
      rw [norm_neg,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    have hp : (A.energyShift^(k+r)) (A.energyShift v) =
        (A.energyShift^(k+(r+1))) v := by
      rw [show k+(r+1)=k+r+1 by omega,pow_succ,Module.End.mul_apply]
    have hm := U.energyShift_pow_norm_mono (show k+r ≤ k+(r+1) by omega) v
    calc
      _ ≤ ‖(-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)‖ +
          ‖(A.energyShift^r) (A.physicalMode a d n (A.energyShift v))‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) v‖) +
          C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) (A.energyShift v)‖ := by
        rw [norm_smul,hn]
        exact add_le_add (mul_le_mul_of_nonneg_left (ih v) (abs_nonneg _)) (ih _)
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+(r+1))) v‖) +
          C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+(r+1))) v‖ := by
        rw [hp]
        gcongr
      _ = _ := by rw [show p+Nat.succ r=p+r+1 by omega,pow_succ]; ring

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SummableNormSobolev
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u v

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace Filter
open scoped Topology
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
theorem summable_norm_sobolevSmear {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (r : ℕ) (v : V) :
    Summable (fun n : ℤ => ‖f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)‖) := by
  obtain ⟨C,hC,p,k,hb⟩ := he.physical A d
  apply hf.summable_norm_smul
    (fun n => (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      ((A.energyShift^r).comp (A.physicalMode a d n))) v
      (C := C) (K := ‖(A.energyShift^(k+r)) v‖) (p := p+r)
  intro n
  simpa only [LinearMap.comp_apply,LinearIsometry.coe_toLinearMap,LinearIsometry.norm_map] using
    U.physicalMode_sobolev_bound ha hC.le hb r n v



end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 

theorem energyExtension_diagonal_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hc : (coreOperator M).IsClosable)
    (x : (diagonal (G := G) (fun i => (h i : ℂ))).domain) :
    (x.val,energyExtension h M (diagonal (fun i => (h i : ℂ)) x)) ∈
      (coreOperator M).closure.graph := by
  let D := diagonal (G := G) (fun i => (h i : ℂ))
  let E := energyExtension h M
  have hclosed : IsClosed {z : Space G × Space G |
      (z.1,E z.2) ∈ (coreOperator M).closure.graph} :=
    hc.closure_isClosed.preimage (continuous_fst.prodMk (E.continuous.comp continuous_snd))
  have hin : ((D.domRestrict finiteCore).graph : Set (Space G × Space G)) ⊆
      {z | (z.1,E z.2) ∈ (coreOperator M).closure.graph} := by
    intro z hz
    obtain ⟨a,ha,hTa⟩ := (D.domRestrict finiteCore).mem_graph_iff.mp hz
    have hv : a.val ∈ finiteCore (G := G) := a.property.1
    let v : finiteCore (G := G) := ⟨a.val,hv⟩
    have hD : D.domRestrict finiteCore a = coreDiagonal (fun i => (h i : ℂ)) v := rfl
    have hw : E z.2 = M v := by
      rw [← hTa,hD]
      exact energyExtension_weighted h hh M hM v
    change (z.1,E z.2) ∈ (coreOperator M).closure.graph
    rw [hw,← ha]
    exact LinearPMap.le_graph_of_le (coreOperator M).le_closure
      ((coreOperator M).mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
  have hDc : (D.domRestrict finiteCore).IsClosable :=
    (diagonal_closed _).isClosable.leIsClosable LinearPMap.domRestrict_le
  have hz : (x.val,D x) ∈ _root_.closure
      ((D.domRestrict finiteCore).graph : Set (Space G × Space G)) := by
    change (x.val,D x) ∈ (D.domRestrict finiteCore).graph.topologicalClosure
    rw [hDc.graph_closure_eq_closure_graph,(diagonal_hasCore _).closure_eq]
    exact D.mem_graph_iff.mpr ⟨x,rfl,rfl⟩
  exact closure_minimal hin hclosed hz

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.OperatorTransport
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

@[simp] theorem symm_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    transport E.symm (transport E T) = T := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rw [mem_graph_iff,mem_graph_iff,E.apply_symm_apply,E.apply_symm_apply]

theorem closable_iff (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    (transport E T).IsClosable ↔ T.IsClosable := by
  constructor
  · intro h
    simpa only [symm_transport] using closable E.symm h
  · exact closable E

end StronglyRationalVOA.OperatorTransport

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

local instance instFiniteDimensionalComplexSubtypeMemSubmoduleGrade : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

theorem coreEnergyCoordinates_energyPower (k : ℕ) (a : V) :
    HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ))
      (U.coreEnergyCoordinates a) = U.energyCoordinates ((A.energyShift^k) a : Completion V) := by
  have hg : ((a : Completion V),((A.energyShift^k) a : Completion V)) ∈ (U.energyPower k).graph :=
    (U.energyPower k).mem_graph_iff.mpr
      ⟨⟨_,U.coe_mem_energyOperator _ a⟩,rfl,U.energyPower_coe k a⟩
  have h := (OperatorTransport.mem_graph_iff U.energyCoordinates _ _ _).mp hg
  obtain ⟨x,hx,hy⟩ := (HilbertScale.diagonal _).mem_graph_iff.mp h
  have hx' : x = ⟨U.coreEnergyCoordinates a,HilbertScale.finiteCore_le_domain _
      (U.coreEnergyCoordinates a).property⟩ := Subtype.ext hx
  rw [hx'] at hy
  exact hy

 
def sobolevExtension (k : ℕ) (T : V →ₗ[ℂ] Completion V) :
    Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^k) (U.spectralCoreMap T)).comp
      U.energyCoordinates.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem sobolevExtension_apply (k : ℕ) (T : V →ₗ[ℂ] Completion V) (x : Completion V) :
    U.sobolevExtension k T x = U.energyCoordinates.symm
      (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^k) (U.spectralCoreMap T)
        (U.energyCoordinates x)) := rfl

theorem spectralCoreMap_bound (k : ℕ) (T : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hT : ∀ v, ‖T v‖ ≤ C*‖(A.energyShift^k) v‖) :
    ∀ x, ‖U.spectralCoreMap T x‖ ≤ C *
      ‖HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ)) x‖ := by
  intro x
  obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
  simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_energyPower,
    LinearIsometryEquiv.norm_map,Completion.norm_coe] using hT v

 

theorem sobolevExtension_energyGraph (k : ℕ) (T : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hT : ∀ v, ‖T v‖ ≤ C*‖(A.energyShift^k) v‖)
    (hc : (HilbertCore.operator T).IsClosable) (x : (U.energyPower k).domain) :
    (x.val,U.sobolevExtension k T (U.energyPower k x)) ∈ (HilbertCore.operator T).closure.graph := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have hc' : (HilbertScale.coreOperator (U.spectralCoreMap T)).IsClosable := by
    apply (OperatorTransport.closable_iff U.energyCoordinates _).mp
    rwa [U.spectralCoreOperator_transport]
  have hh (d : ℕ) : 1 ≤ (1+(d : ℝ))^k :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hx : U.energyCoordinates x.val ∈
      (HilbertScale.diagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ))).domain := x.property
  have h := HilbertScale.energyExtension_diagonal_graph _ hh _
    (U.spectralCoreMap_bound k T hT) hc' ⟨U.energyCoordinates x.val,hx⟩
  rw [← U.spectralCoreOperator_transport T,OperatorTransport.closure U.energyCoordinates hc',
    OperatorTransport.mem_graph_iff]
  have hDx : U.energyCoordinates (U.energyPower k x) =
      HilbertScale.diagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ))
        ⟨U.energyCoordinates x.val,hx⟩ := U.energyCoordinates.apply_symm_apply _
  simpa only [U.sobolevExtension_apply,U.energyCoordinates.apply_symm_apply,hDx] using h

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def weightedSmearedMap {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) :
    V →ₗ[ℂ] Completion V :=
  SummableLinearFamily.tsumMap
    (fun n => f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      ((A.energyShift^r).comp (A.physicalMode a d n)))
    (fun v => (U.summable_norm_sobolevSmear ha he hf r v).of_norm)

@[simp] theorem weightedSmearedMap_apply {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    U.weightedSmearedMap ha he hf r v =
      ∑' n : ℤ, f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V) := rfl

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 
def inverseEnergy (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => (h i : ℂ)⁻¹) zero_le_one (by
    intro i
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans (hh i))]
    exact inv_le_one_of_one_le₀ (hh i))

omit [DecidableEq ι] in
theorem inverseEnergy_apply (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) (i : ι) :
    inverseEnergy h hh x i = (h i : ℂ)⁻¹ • x i := rfl

theorem inverseEnergy_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : finiteCore (G := G)) :
    inverseEnergy h hh x = (coreMultiplier (fun i => (h i : ℂ)⁻¹) x : Space G) := by
  ext i
  rfl
end StronglyRationalVOA.HilbertScale

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_InverseEnergySelf
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]
omit [DecidableEq ι] in
theorem inverseEnergy_selfAdjoint (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) :
    IsSelfAdjoint (inverseEnergy (G := G) h hh) := by
  change (inverseEnergy (G := G) h hh).adjoint = inverseEnergy h hh
  unfold inverseEnergy
  rw [boundedMultiplier_adjoint]
  ext x i
  simp only [boundedMultiplier_apply,map_inv₀,Complex.star_def,Complex.conj_ofReal]

omit [DecidableEq ι] in
theorem inverseEnergy_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) :
    (inverseEnergy h hh x,x) ∈ (diagonal (fun i => (h i : ℂ))).graph := by
  apply (mem_graph_iff _ _ _).mpr
  intro i
  rw [inverseEnergy_apply,smul_smul,mul_inv_cancel₀,one_smul]
  exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))

omit [DecidableEq ι] in
theorem inverseEnergy_diagonal (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (x : (diagonal (G := G) (fun i => (h i : ℂ))).domain) :
    inverseEnergy h hh (diagonal (fun i => (h i : ℂ)) x) = (x : Space G) := by
  ext i
  rw [inverseEnergy_apply,diagonal_apply,smul_smul,inv_mul_cancel₀,one_smul]
  exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))



theorem energyExtension_defect (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G)) :
    energyExtension h M - (energyExtension h M).adjoint =
      (inverseEnergy h hh).comp (energyExtension h K) := by
  let E := energyExtension h M
  let F := (inverseEnergy h hh).comp (energyExtension h K)
  have hd : DenseRange ((finiteCore (G := G)).subtype) := by
    simpa [DenseRange] using (finiteCore_dense (G := G))
  have hp : ∀ x y : Space G, inner ℂ (E x) y-inner ℂ x (E y) = inner ℂ (F x) y := by
    intro x y
    refine hd.induction_on₂ ?_ ?_ x y
    · exact isClosed_eq
        (((E.continuous.comp continuous_fst).inner continuous_snd).sub
          (continuous_fst.inner (E.continuous.comp continuous_snd)))
        ((F.continuous.comp continuous_fst).inner continuous_snd)
    · intro x y
      let sx := coreMultiplier (fun i => (h i : ℂ)⁻¹) x
      let sy := coreMultiplier (fun i => (h i : ℂ)⁻¹) y
      have hcx : coreDiagonal (fun i => (h i : ℂ)) sx = (x : Space G) :=
        congrArg Subtype.val (coreMultiplier_cancel h hh x)
      have hcy : coreDiagonal (fun i => (h i : ℂ)) sy = (y : Space G) :=
        congrArg Subtype.val (coreMultiplier_cancel h hh y)
      have hS : (inverseEnergy (G := G) h hh).adjoint = inverseEnergy h hh :=
        inverseEnergy_selfAdjoint h hh
      change inner ℂ (energyExtension h M x) (y : Space G) -
        inner ℂ (x : Space G) (energyExtension h M y) =
        inner ℂ (inverseEnergy h hh (energyExtension h K x)) (y : Space G)
      rw [← hS,ContinuousLinearMap.adjoint_inner_left,
        energyExtension_core h hh M hM x,energyExtension_core h hh M hM y,
        energyExtension_core h hh K hK x,inverseEnergy_core]
      simpa only [hcx,hcy] using hk sx sy
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (E x-E.adjoint x) y = inner ℂ (F x) y
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
  exact hp x y

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


omit [CompleteSpace H] in
theorem formalAdjoint_graph_pairing {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T)
    {x y a b : H} (hxy : (x,y) ∈ T.graph) (hab : (a,b) ∈ T.graph) :
    inner ℂ y a = inner ℂ x b := by
  obtain ⟨u,hu,hTu⟩ := T.mem_graph_iff.mp hxy
  obtain ⟨v,hv,hTv⟩ := T.mem_graph_iff.mp hab
  dsimp only [Prod.fst,Prod.snd] at hu hv hTu hTv
  rw [← hu,← hv,← hTu,← hTv]
  exact hs u v



end StronglyRationalVOA.SymmetricOperator

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BoundedFlows
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.BoundedFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance boundedFlowRationalNormedAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) :=
  .restrictScalars ℚ ℂ (H →L[ℂ] H)

def flow (K : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H := NormedSpace.exp (t • K)

lemma flow_unitary {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H)) (t : ℝ) :
    flow K t ∈ unitary (H →L[ℂ] H) := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (t • K) = -(t • K)
  rw [star_smul,star_trivial,skewAdjoint.mem_iff.mp hK,smul_neg]

lemma flow_norm {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H)) (t : ℝ) (x : H) :
    ‖flow K t x‖ = ‖x‖ := ContinuousLinearMap.norm_map_of_mem_unitary (flow_unitary hK t) x

lemma flow_derivative (K : H →L[ℂ] H) (t : ℝ) (x : H) :
    HasDerivAt (fun s : ℝ => flow K s x) (flow K t (K x)) t := by
  exact ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const K t)

lemma flow_zero (K : H →L[ℂ] H) : flow K 0 = 1 := by simp [flow]

lemma flow_add (K : H →L[ℂ] H) (s t : ℝ) : flow K (s+t) = flow K s*flow K t := by
  simp only [flow,add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl K).smul_left s).smul_right t)

lemma flow_time_bound {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H))
    (s t : ℝ) (x : H) : ‖flow K t x-flow K s x‖ ≤ ‖K x‖*|t-s| := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => flow K t x) (f' := fun t : ℝ => flow K t (K x))
    (s := Set.univ) (x := s) (y := t)
    (fun t _ => (flow_derivative K t x).hasDerivWithinAt)
    (fun t _ => (flow_norm hK t (K x)).le) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs] using hb

lemma flow_initial_bound {K : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H))
    (t : ℝ) (x : H) : ‖flow K t x-x‖ ≤ |t| *‖K x‖ := by
  simpa only [flow_zero,one_apply_eq_self,sub_zero,mul_comm] using flow_time_bound hK 0 t x

lemma flow_difference {K L : H →L[ℂ] H} (hK : K ∈ skewAdjoint (H →L[ℂ] H))
    (hL : L ∈ skewAdjoint (H →L[ℂ] H)) (hKL : Commute K L) (t : ℝ) (x : H) :
    ‖flow K t x-flow L t x‖ ≤ |t| *‖(K-L) x‖ := by
  have hD : K-L ∈ skewAdjoint (H →L[ℂ] H) := by
    change star (K-L) = -(K-L)
    rw [star_sub,skewAdjoint.mem_iff.mp hK,skewAdjoint.mem_iff.mp hL]
    abel
  have hfactor : flow K t = flow L t*flow (K-L) t := by
    rw [flow,flow,flow,← NormedSpace.exp_add_of_commute]
    · congr 1
      module
    · exact ((hKL.symm.sub_right (Commute.refl L)).smul_left t).smul_right t
  rw [hfactor]
  change ‖flow L t (flow (K-L) t x)-flow L t x‖ ≤ _
  rw [← map_sub,flow_norm hL]
  exact flow_initial_bound hD t x

end StronglyRationalVOA.BoundedFlow

open scoped Topology
open Filter

open scoped Topology

open scoped Topology
open Filter

open scoped Topology

open scoped Topology
open Filter MeasureTheory

open scoped Topology
open Filter MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ApproximatingFlowDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory

open scoped Topology
open Filter

open scoped Topology
open Filter

namespace StronglyRationalVOA.HilbertScale
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι] in
lemma inverseEnergy_on_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    {x y : Space G} (hxy : (x,y) ∈ (diagonal (fun i => (h i : ℂ))).graph) :
    inverseEnergy h hh y = x := by
  obtain ⟨v,hv,hy⟩ := (diagonal (fun i => (h i : ℂ))).mem_graph_iff.mp hxy
  dsimp only [Prod.fst,Prod.snd] at hv hy
  rw [← hy,inverseEnergy_diagonal,hv]

end StronglyRationalVOA.HilbertScale

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

lemma physicalMode_power_commutator_bound {a : V} {d p : ℕ} (ha : a ∈ A.grade d)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    (r : ℕ) (n : ℤ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)-A.physicalMode a d n ((A.energyShift^r) v)‖ ≤
      (C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^r) v‖ := by
  induction r generalizing v with
  | zero => simp only [pow_zero,Module.End.one_apply,sub_self,norm_zero,Nat.cast_zero,mul_zero,zero_mul,le_refl]
  | succ r ih =>
    have he : (A.energyShift^(r+1)) (A.physicalMode a d n v)-
          A.physicalMode a d n ((A.energyShift^(r+1)) v) =
        (-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)+
          ((A.energyShift^r) (A.physicalMode a d n (A.energyShift v))-
            A.physicalMode a d n ((A.energyShift^r) (A.energyShift v))) := by
      have hc := congrArg (A.energyShift^r) (A.energyShift_physical_commutator ha n v)
      rw [map_sub,map_smul] at hc
      simp only [pow_succ,Module.End.mul_apply]
      rw [← hc]
      abel
    have hn : ‖-(n : ℂ)‖ = |(n : ℝ)| := by
      rw [norm_neg,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    have hpower : (A.energyShift^r) (A.energyShift v) = (A.energyShift^(r+1)) v := by
      rw [pow_succ,Module.End.mul_apply]
    have hs := U.physicalMode_sobolev_bound (k := 1) ha hC (by simpa only [pow_one] using hb) r n v
    rw [Nat.add_comm 1 r] at hs
    have hbase : 1 ≤ 1+|(n : ℝ)| := by have := abs_nonneg (n : ℝ); linarith
    have hbase0 : 0 ≤ 1+|(n : ℝ)| := zero_le_one.trans hbase
    rw [he]
    calc
      _ ≤ ‖(-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)‖+
        ‖(A.energyShift^r) (A.physicalMode a d n (A.energyShift v))-
          A.physicalMode a d n ((A.energyShift^r) (A.energyShift v))‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖)+
        (C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖ := by
          rw [norm_smul,hn]
          exact add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) (by simpa only [hpower] using ih (A.energyShift v))
      _ ≤ (1+|(n : ℝ)|)*(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖)+
        (1+|(n : ℝ)|)*((C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖) := by
          apply add_le_add
          · gcongr; linarith
          · exact le_mul_of_one_le_left (by positivity) hbase
      _ = _ := by rw [Nat.cast_succ,show p+Nat.succ r=p+r+1 by omega,pow_succ]; ring

include U in
lemma energyShift_pow_adjoint (r : ℕ) (x y : V) :
    inner ℂ ((A.energyShift^r) x) y = inner ℂ x ((A.energyShift^r) y) := by
  induction r generalizing x y with
  | zero => simp only [pow_zero,Module.End.one_apply]
  | succ r ih =>
    rw [pow_succ,Module.End.mul_apply,ih,U.energyShift_adjoint,← Module.End.mul_apply,← pow_succ']
    rfl

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def smearedPowerCommutator {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) :
    V →ₗ[ℂ] Completion V :=
  U.weightedSmearedMap ha he hf r - (A.smearedMap a d he f hf).comp (A.energyShift^r)

lemma smearedPowerCommutator_apply {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    U.smearedPowerCommutator ha he hf r v =
      ∑' n : ℤ, f n • (((A.energyShift^r) (A.physicalMode a d n v)-
        A.physicalMode a d n ((A.energyShift^r) v) : V) : Completion V) := by
  simp only [smearedPowerCommutator,LinearMap.sub_apply,LinearMap.comp_apply,
    weightedSmearedMap_apply,smearedMap_apply]
  rw [← (U.summable_norm_sobolevSmear ha he hf r v).of_norm.tsum_sub
    (A.summable_norm_physicalSmear he d hf ((A.energyShift^r) v)).of_norm]
  apply tsum_congr
  intro n
  change f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) _ -
    f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) _ =
      f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (_-_)
  rw [map_sub,smul_sub]

lemma smearedPowerCommutator_bound {a : V} {d p : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    ‖U.smearedPowerCommutator ha he hf r v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^(p+r))*(C*r))*‖(A.energyShift^r) v‖ := by
  let D (n : ℤ) : V →ₗ[ℂ] Completion V :=
    (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      ((A.energyShift^r).comp (A.physicalMode a d n) - (A.physicalMode a d n).comp (A.energyShift^r))
  have hd (n : ℤ) : ‖D n v‖ ≤ (C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^r) v‖ := by
    simpa only [D,LinearMap.comp_apply,LinearMap.sub_apply,LinearIsometry.coe_toLinearMap,
      LinearIsometry.norm_map] using U.physicalMode_power_commutator_bound ha hC hb r n v
  have hsum := hf.summable_norm_smul D v hd
  rw [U.smearedPowerCommutator_apply ha he hf r v]
  change ‖∑' n : ℤ, f n • D n v‖ ≤ _
  apply (norm_tsum_le_tsum_norm hsum).trans
  calc
    _ ≤ ∑' n : ℤ, (‖f n‖*(1+|(n : ℝ)|)^(p+r))*((C*r)*‖(A.energyShift^r) v‖) := by
      apply Summable.tsum_le_tsum _ hsum ((hf (p+r)).mul_right _)
      intro n
      rw [norm_smul]
      calc
        _ ≤ ‖f n‖*((C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^r) v‖) :=
          mul_le_mul_of_nonneg_left (hd n) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [tsum_mul_right]; ring

lemma weightedSmearedMap_inner {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (x y : V) :
    inner ℂ (U.weightedSmearedMap ha he hf r x) (y : Completion V) =
      inner ℂ (A.smearedMap a d he f hf x) ((A.energyShift^r) y : Completion V) := by
  rw [weightedSmearedMap_apply,smearedMap_apply,
    inner_tsum_left (U.summable_norm_sobolevSmear ha he hf r x).of_norm,
    inner_tsum_left (A.summable_norm_physicalSmear he d hf x).of_norm]
  apply tsum_congr
  intro n
  simp only [inner_smul_left,Completion.inner_coe,U.energyShift_pow_adjoint]

lemma smearedPowerCommutator_pairing {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (he : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hreal : ∀ n, star (f n) = f (-n))
    (r : ℕ) (x y : V) :
    inner ℂ (A.smearedMap a d he f hf x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (A.smearedMap a d he f hf y) =
    inner ℂ (U.smearedPowerCommutator ha he hf r x) (y : Completion V) := by
  simp only [smearedPowerCommutator,LinearMap.sub_apply,LinearMap.comp_apply,inner_sub_left]
  rw [U.weightedSmearedMap_inner,U.smearedMap_symmetric ha hq hh he hf hreal ((A.energyShift^r) x) y]

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology
open Filter MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RegularizerFactorAdd
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace

open scoped Topology
open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance regularizerFactorGradeFiniteDimensional :
    ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

 
def inverseSobolev (r : ℕ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.conjStarAlgEquiv
    (HilbertScale.inverseEnergy (fun d : ℕ => (1+(d : ℝ))^r)
      (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)))

lemma inverseSobolev_apply (r : ℕ) (x : Completion V) :
    U.inverseSobolev r x = U.energyCoordinates.symm
      (HilbertScale.inverseEnergy (fun d : ℕ => (1+(d : ℝ))^r)
        (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
        (U.energyCoordinates x)) := rfl

lemma inverseSobolev_selfAdjoint (r : ℕ) : IsSelfAdjoint (U.inverseSobolev r) := by
  have h := HilbertScale.inverseEnergy_selfAdjoint (G := fun d => A.grade d)
    (fun d : ℕ => (1+(d : ℝ))^r)
    (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
  change star (U.inverseSobolev r) = U.inverseSobolev r
  unfold inverseSobolev
  exact (U.energyCoordinates.symm.conjStarAlgEquiv.map_star' _).symm.trans
    (congrArg U.energyCoordinates.symm.conjStarAlgEquiv h)

lemma inverseSobolev_graph (r : ℕ) (x : Completion V) :
    (U.inverseSobolev r x,x) ∈ (U.energyPower r).graph := by
  change (_,_) ∈ (OperatorTransport.transport U.energyCoordinates
    (HilbertScale.diagonal (fun d : ℕ => (((1+(d : ℝ))^r : ℝ) : ℂ)))).graph
  rw [OperatorTransport.mem_graph_iff,inverseSobolev_apply,U.energyCoordinates.apply_symm_apply]
  exact HilbertScale.inverseEnergy_graph _ _ _

lemma inverseSobolev_on_graph (r : ℕ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.energyPower r).graph) : U.inverseSobolev r y = x := by
  have h := (OperatorTransport.mem_graph_iff U.energyCoordinates _ _ _).mp hxy
  rw [U.inverseSobolev_apply,HilbertScale.inverseEnergy_on_graph _ _ h,U.energyCoordinates.symm_apply_apply]

lemma inverseSobolev_dense (r : ℕ) : DenseRange (U.inverseSobolev r) := by
  apply (HilbertCore.dense (V := V)).mono
  rintro x ⟨v,rfl⟩
  refine ⟨((A.energyShift^r) v : Completion V),U.inverseSobolev_on_graph r ?_⟩
  exact (U.energyPower r).mem_graph_iff.mpr
    ⟨⟨_,U.coe_mem_energyOperator _ v⟩,rfl,U.energyPower_coe r v⟩

lemma sobolevExtension_eq_conj (r : ℕ) (M : V →ₗ[ℂ] Completion V) :
    U.sobolevExtension r M = U.energyCoordinates.symm.conjStarAlgEquiv
      (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^r) (U.spectralCoreMap M)) := by
  ext x
  rfl

lemma sobolevExtension_inverse_graph (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) (hc : (HilbertCore.operator M).IsClosable)
    (x : Completion V) :
    (U.inverseSobolev r x,U.sobolevExtension r M x) ∈ (HilbertCore.operator M).closure.graph := by
  obtain ⟨v,hv,hy⟩ := (U.energyPower r).mem_graph_iff.mp (U.inverseSobolev_graph r x)
  dsimp only [Prod.fst,Prod.snd] at hv hy
  have h := U.sobolevExtension_energyGraph r M hM hc v
  rwa [hv,hy] at h

lemma sobolevExtension_defect (r : ℕ) (M K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hK : ∀ v, ‖K v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hk : ∀ x y : V, inner ℂ (M x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (M y) = inner ℂ (K x) (y : Completion V)) :
    U.sobolevExtension r M-(U.sobolevExtension r M).adjoint =
      (U.inverseSobolev r).comp (U.sobolevExtension r K) := by
  have hk' : ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
      inner ℂ (U.spectralCoreMap M x)
          (HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^r : ℝ) : ℂ)) y)-
        inner ℂ (HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^r : ℝ) : ℂ)) x)
          (U.spectralCoreMap M y) = inner ℂ (U.spectralCoreMap K x) y := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,
      U.coreEnergyCoordinates_energyPower,U.energyCoordinates.inner_map_map] using hk v w
  have hb := HilbertScale.energyExtension_defect
    (fun d : ℕ => (1+(d : ℝ))^r)
    (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
    (U.spectralCoreMap M) (U.spectralCoreMap K)
    (U.spectralCoreMap_bound r M hM) (U.spectralCoreMap_bound r K hK) hk'
  change HilbertScale.energyExtension _ (U.spectralCoreMap M)-
    star (HilbertScale.energyExtension _ (U.spectralCoreMap M)) =
    HilbertScale.inverseEnergy _ _ * HilbertScale.energyExtension _ (U.spectralCoreMap K) at hb
  have h := congrArg U.energyCoordinates.symm.conjStarAlgEquiv hb
  change U.sobolevExtension r M-star (U.sobolevExtension r M) =
    U.inverseSobolev r*U.sobolevExtension r K
  have he : U.energyCoordinates.symm.conjStarAlgEquiv
      (star (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^r) (U.spectralCoreMap M))) =
    star (U.energyCoordinates.symm.conjStarAlgEquiv
      (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^r) (U.spectralCoreMap M))) :=
    U.energyCoordinates.symm.conjStarAlgEquiv.map_star' _
  rw [map_sub,he,map_mul] at h
  simpa only [U.sobolevExtension_eq_conj,inverseSobolev] using h



end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SymmetricWeakCommute
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



include U in
lemma stress_physical_bound (n : ℤ) (v : V) :
    ‖A.physicalMode A.conformalVector 2 n v‖ ≤
      (1+A.centralCharge.re)*(1+|(n : ℝ)|)^2*‖A.energyShift v‖ := by
  simpa only [physicalMode,virasoroMode,Nat.cast_ofNat,show n+(2 : ℤ)-1=n+1 by omega]
    using U.virasoro_linear_energy n v

lemma stress_hermitian : U.IsHermitian 2 A.conformalVector := by
  simp [IsHermitian,U.pct_conformal]

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Set
open scoped ContDiff

open MeasureTheory Set Filter
open scoped Topology Interval
namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

 
def term (K : ℝ → A) : ℕ → ℝ → A
  | 0, _ => 1
  | n+1, t => ∫ s in 0..t, K s*term K n s
end StronglyRationalVOA.TimeOrdered

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressEvolution
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval

open MeasureTheory Set Filter
open scoped Topology Interval

open Set Filter
open scoped Topology
namespace StronglyRationalVOA.HilbertScale
variable {G : ℕ → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

def energyCutoff (n : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => if i ≤ n then 1 else 0) zero_le_one (by intro i; split_ifs <;> simp)

lemma energyCutoff_apply (n : ℕ) (x : Space G) (i : ℕ) :
    energyCutoff n x i = if i ≤ n then x i else 0 := by
  simp only [energyCutoff,boundedMultiplier_apply]
  split_ifs <;> simp
end StronglyRationalVOA.HilbertScale

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyCutoffNorm
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
namespace StronglyRationalVOA.HilbertScale
variable {G : ℕ → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
lemma energyCutoff_norm (n : ℕ) : ‖energyCutoff (G := G) n‖ ≤ 1 := boundedMultiplier_norm _ _ _

lemma energyCutoff_selfAdjoint (n : ℕ) : IsSelfAdjoint (energyCutoff (G := G) n) := by
  change (energyCutoff (G := G) n).adjoint=energyCutoff n
  unfold energyCutoff
  rw [boundedMultiplier_adjoint]
  ext x i
  simp only [boundedMultiplier_apply]
  split_ifs <;> simp

lemma energyCutoff_commute_multiplier (n : ℕ) (w : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    Commute (energyCutoff (G := G) n) (boundedMultiplier w hC hw) := by
  change _ * _ = _ * _
  ext x i
  change energyCutoff n (boundedMultiplier w hC hw x) i = boundedMultiplier w hC hw (energyCutoff n x) i
  simp only [energyCutoff_apply,boundedMultiplier_apply]
  split_ifs <;> simp

lemma energyCutoff_inverseEnergy (n r : ℕ) :
    Commute (energyCutoff (G := G) n)
      (inverseEnergy (fun i : ℕ => (1+(i:ℝ))^r) (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i)))) :=
  energyCutoff_commute_multiplier _ _ _ _

def truncatedEnergyPower (n r : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => if i ≤ n then (1+(i:ℂ))^r else 0)
    (show 0 ≤ (1+(n:ℝ))^r by positivity) (by
      intro i
      split_ifs with hi
      · rw [norm_pow]
        have hn : ‖(1:ℂ)+(i:ℂ)‖ = 1+(i:ℝ) := by
          rw [show (1:ℂ)+(i:ℂ) = ((1+(i:ℝ) : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        rw [hn]
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hi 1) _
      · simpa using (show 0 ≤ (1+(n:ℝ))^r by positivity))

lemma truncatedEnergyPower_apply (n r : ℕ) (x : Space G) (i : ℕ) :
    truncatedEnergyPower n r x i = if i ≤ n then (1+(i:ℂ))^r • x i else 0 := by
  simp only [truncatedEnergyPower,boundedMultiplier_apply]
  split_ifs <;> simp

lemma inverseEnergy_truncated (n r : ℕ) :
    inverseEnergy (G := G) (fun i : ℕ => (1+(i:ℝ))^r) (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i)))*
      truncatedEnergyPower n r = energyCutoff n := by
  ext x i
  change inverseEnergy (fun i : ℕ => (1+(i:ℝ))^r) (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i))) (truncatedEnergyPower n r x) i = energyCutoff n x i
  rw [inverseEnergy_apply,truncatedEnergyPower_apply,energyCutoff_apply]
  split_ifs
  · rw [smul_smul]
    have he : (((1+(i:ℝ))^r : ℝ) : ℂ) = (1+(i:ℂ))^r := by push_cast; rfl
    rw [he,inv_mul_cancel₀,one_smul]
    apply pow_ne_zero
    have hp : (0:ℝ)<1+(i:ℝ) := by positivity
    exact_mod_cast ne_of_gt hp
  · rw [smul_zero]

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cutoff_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T)
    (P R : H →L[ℂ] H) (hP : IsSelfAdjoint P) (hg : ∀ x, (P x,R x) ∈ T.graph) :
    IsSelfAdjoint (P*R) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (P (R x)) y=inner ℂ x (P (R y))
  have hPa : P.adjoint=P := hP
  calc
    _ = inner ℂ (R x) (P y) := by rw [← P.adjoint_inner_right,hPa]
    _ = inner ℂ (P x) (R y) := formalAdjoint_graph_pairing hs (hg x) (hg y)
    _ = _ := by rw [← P.adjoint_inner_right,hPa]

omit [CompleteSpace H] in
lemma cutoff_normalized (T : H →ₗ.[ℂ] H)
    (P R S E : H →L[ℂ] H) (hg : ∀ x, (P x,R x) ∈ T.graph)
    (he : ∀ x, (S x,E x) ∈ T.graph) (hPS : Commute P S) :
    (P*R)*S=P*E*P := by
  ext x
  change P (R (S x))=P (E (P x))
  congr 1
  apply T.mem_graph_snd_inj (hg (S x)) (he (P x))
  exact congrArg (fun A : H →L[ℂ] H => A x) hPS.eq

 
lemma cutoff_commutator (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T)
    (P R S E F : H →L[ℂ] H) (hP : IsSelfAdjoint P) (hS : IsSelfAdjoint S)
    (hg : ∀ x, (P x,R x) ∈ T.graph) (he : ∀ x, (S x,E x) ∈ T.graph)
    (hPS : Commute P S) (hdef : E-E.adjoint = S*F) :
    S*(Complex.I • (P*R))-(Complex.I • (P*R))*S =
      (Complex.I • (P*F.adjoint*P))*S := by
  have hT := cutoff_selfAdjoint T hs P R hP hg
  have hn := cutoff_normalized T P R S E hg he hPS
  have ha : S*(P*R)=P*E.adjoint*P := by
    calc
      _ = star ((P*R)*S) := by rw [star_mul,show star S=S from hS,show star (P*R)=P*R from hT]
      _ = star (P*E*P) := congrArg star hn
      _ = _ := by rw [star_mul,star_mul,show star P=P from hP]; simp only [ContinuousLinearMap.star_eq_adjoint,mul_assoc]
  have hde : E.adjoint-E=F.adjoint*S := by
    have h := congrArg star hdef
    simpa only [star_sub,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint,star_mul,show star S=S from hS] using h
  calc
    _ = Complex.I • (S*(P*R)-(P*R)*S) := by rw [mul_smul_comm,smul_mul_assoc,smul_sub]
    _ = Complex.I • (P*(E.adjoint-E)*P) := by rw [ha,hn]; congr 1; noncomm_ring
    _ = Complex.I • ((P*F.adjoint*P)*S) := by rw [hde]; congr 1; rw [mul_assoc,mul_assoc,← hPS.eq]; simp only [mul_assoc]
    _ = _ := by rw [smul_mul_assoc]

end StronglyRationalVOA.SymmetricOperator

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance instFiniteDimensionalComplexSubtypeMemSubmoduleGrade_1 : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

lemma sobolevExtension_norm (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) : ‖U.sobolevExtension r M‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  rw [U.sobolevExtension_apply,LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    (HilbertScale.energyExtension _ (U.spectralCoreMap M)).le_of_opNorm_le
      (HilbertScale.energyExtension_norm _ (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i))) _ hC (U.spectralCoreMap_bound r M hM)) (U.energyCoordinates x)

def inverseCoreEnergy (r : ℕ) : V →ₗ[ℂ] V :=
  U.coreEnergyCoordinates.symm.toLinearMap.comp
    ((HilbertScale.coreMultiplier (fun d : ℕ => ((((1+(d:ℝ))^r : ℝ) : ℂ)⁻¹))).comp
      U.coreEnergyCoordinates.toLinearMap)

lemma inverseCoreEnergy_coe (r : ℕ) (v : V) :
    (U.inverseCoreEnergy r v : Completion V) = U.inverseSobolev r v := by
  apply U.energyCoordinates.injective
  rw [U.inverseSobolev_apply,U.energyCoordinates.apply_symm_apply]
  change (U.coreEnergyCoordinates (U.inverseCoreEnergy r v) : HilbertScale.Space (fun d => A.grade d)) = _
  simp only [inverseCoreEnergy,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  exact (HilbertScale.inverseEnergy_core _ _ (U.coreEnergyCoordinates v)).symm

lemma energyShift_inverseCoreEnergy (r : ℕ) (v : V) :
    (A.energyShift^r) (U.inverseCoreEnergy r v)=v := by
  have h := U.inverseSobolev_graph r (v : Completion V)
  rw [← U.inverseCoreEnergy_coe] at h
  have hg : ((U.inverseCoreEnergy r v : V) : Completion V) =
    ((U.inverseCoreEnergy r v : V) : Completion V) := rfl
  have he : ((U.inverseCoreEnergy r v : Completion V),((A.energyShift^r) (U.inverseCoreEnergy r v) : Completion V)) ∈ (U.energyPower r).graph := (U.energyPower r).mem_graph_iff.mpr
    ⟨⟨_,U.coe_mem_energyOperator _ _⟩,rfl,U.energyPower_coe r (U.inverseCoreEnergy r v)⟩
  exact (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective
    ((U.energyPower r).mem_graph_snd_inj he h hg)

lemma sobolevExtension_coe (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) (v : V) :
    U.sobolevExtension r M (v : Completion V)=M (U.inverseCoreEnergy r v) := by
  rw [U.sobolevExtension_apply,← U.coreEnergyCoordinates_coe,
    HilbertScale.energyExtension_core _ (fun i => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg i))) _ (U.spectralCoreMap_bound r M hM)]
  change U.energyCoordinates.symm (U.energyCoordinates (M (U.inverseCoreEnergy r v))) = _
  exact U.energyCoordinates.symm_apply_apply _

lemma sobolevExtension_sub_norm (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D E : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖) (hE : 0 ≤ E)
    (hMN : ∀ v, ‖M v-N v‖ ≤ E*‖(A.energyShift^r) v‖) :
    ‖U.sobolevExtension r M-U.sobolevExtension r N‖ ≤ E := by
  apply ContinuousLinearMap.opNorm_le_bound _ hE
  intro x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => ‖(U.sobolevExtension r M-U.sobolevExtension r N) x‖ ≤ E*‖x‖) x
    (isClosed_le (by fun_prop) (by fun_prop))
  intro v
  change ‖U.sobolevExtension r M (v : Completion V)-U.sobolevExtension r N (v : Completion V)‖ ≤ _
  rw [U.sobolevExtension_coe r M hM,U.sobolevExtension_coe r N hN,Completion.norm_coe]
  simpa only [U.energyShift_inverseCoreEnergy] using hMN (U.inverseCoreEnergy r v)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance instFiniteDimensionalComplexSubtypeMemSubmoduleGrade_2 : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

def energyCutoff (n : ℕ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.conjStarAlgEquiv (HilbertScale.energyCutoff n)

def truncatedEnergyPower (n r : ℕ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.conjStarAlgEquiv (HilbertScale.truncatedEnergyPower n r)

lemma energyCutoff_norm (n : ℕ) : ‖U.energyCutoff n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖U.energyCoordinates.symm (HilbertScale.energyCutoff n (U.energyCoordinates x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    (HilbertScale.energyCutoff (G := fun d => A.grade d) n).le_of_opNorm_le (HilbertScale.energyCutoff_norm n) (U.energyCoordinates x)

lemma energyCutoff_selfAdjoint (n : ℕ) : IsSelfAdjoint (U.energyCutoff n) := by
  change star (U.energyCutoff n)=U.energyCutoff n
  unfold energyCutoff
  exact (U.energyCoordinates.symm.conjStarAlgEquiv.map_star' _).symm.trans
    (congrArg U.energyCoordinates.symm.conjStarAlgEquiv (HilbertScale.energyCutoff_selfAdjoint n))

lemma energyCutoff_inverseSobolev (n r : ℕ) : Commute (U.energyCutoff n) (U.inverseSobolev r) := by
  exact (HilbertScale.energyCutoff_inverseEnergy n r).map U.energyCoordinates.symm.conjStarAlgEquiv

lemma inverseSobolev_truncated (n r : ℕ) :
    U.inverseSobolev r*U.truncatedEnergyPower n r=U.energyCutoff n := by
  change U.energyCoordinates.symm.conjStarAlgEquiv _ * U.energyCoordinates.symm.conjStarAlgEquiv _ = _
  rw [← map_mul,HilbertScale.inverseEnergy_truncated]
  rfl

lemma energyCutoff_graph (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hc : (HilbertCore.operator M).IsClosable) (n : ℕ) (x : Completion V) :
    (U.energyCutoff n x,(U.sobolevExtension r M*U.truncatedEnergyPower n r) x) ∈
      (HilbertCore.operator M).closure.graph := by
  have h := U.sobolevExtension_inverse_graph r M hM hc (U.truncatedEnergyPower n r x)
  change ((U.inverseSobolev r*U.truncatedEnergyPower n r) x,_) ∈ _ at h
  rwa [U.inverseSobolev_truncated] at h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
namespace RapidCoefficients
variable {f g : ℤ → ℂ}
lemma neg (hf : RapidCoefficients f) : RapidCoefficients (fun n => -f n) := by
  simpa only [neg_one_mul] using hf.smul (-1)
lemma sub (hf : RapidCoefficients f) (hg : RapidCoefficients g) : RapidCoefficients (fun n => f n-g n) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
end RapidCoefficients

def coefficientSeminorm (f : ℤ → ℂ) (r : ℕ) : ℝ := ∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^r
lemma coefficientSeminorm_nonneg (f : ℤ → ℂ) (r : ℕ) : 0 ≤ coefficientSeminorm f r :=
  tsum_nonneg (fun n => by positivity)

namespace CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_sub {a : V} (he : A.PolynomialEnergyBound a) (d : ℕ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    A.smearedMap a d he f hf-A.smearedMap a d he g hg =
      A.smearedMap a d he (fun n => f n-g n) (hf.sub hg) := by
  ext v
  simp only [LinearMap.sub_apply,smearedMap_apply,sub_smul]
  exact ((A.summable_norm_physicalSmear he d hf v).of_norm.tsum_sub
    (A.summable_norm_physicalSmear he d hg v).of_norm).symm

lemma smearedMap_difference_bound {a : V} (he : A.PolynomialEnergyBound a) {d p k : ℕ}
    {C : ℝ} (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (v : V) :
    ‖A.smearedMap a d he f hf v-A.smearedMap a d he g hg v‖ ≤
      (coefficientSeminorm (fun n => f n-g n) p*C)*‖(A.energyShift^k) v‖ := by
  change ‖(A.smearedMap a d he f hf-A.smearedMap a d he g hg) v‖ ≤ _
  rw [A.smearedMap_sub he d hf hg]
  exact A.smearedMap_bound he (hf.sub hg) hb v
end CFTTypeVOA
end StronglyRationalVOA

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

def stressCore (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    V →ₗ[ℂ] Completion V := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc _) f hf

def stressNormalized (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (r : ℕ) : Completion V →L[ℂ] Completion V :=
  U.sobolevExtension r (U.stressCore hc hf)

lemma stressCore_bound (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) (v : V) :
    ‖U.stressCore hc hf v‖ ≤
      (coefficientSeminorm f 2*(1+A.centralCharge.re))*‖(A.energyShift^r) v‖ := by
  have h := A.smearedMap_bound (U.polynomialEnergyBounds hc A.conformalVector) hf
    (k := 1) (by simpa only [pow_one] using U.stress_physical_bound) v
  exact h.trans (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hr v)
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])))

lemma stressNormalized_norm (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) :
    ‖U.stressNormalized hc hf r‖ ≤ coefficientSeminorm f 2*(1+A.centralCharge.re) := by
  apply U.sobolevExtension_norm
    r (U.stressCore hc hf) (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg]))
  exact U.stressCore_bound hc hf hr

lemma stressNormalized_graph (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) (x : Completion V) :
    (U.inverseSobolev r x,U.stressNormalized hc hf r x) ∈
      (U.closedSmearedOperator hc A.conformalVector 2 f hf).graph := by
  exact U.sobolevExtension_inverse_graph r _ (U.stressCore_bound hc hf hr)
    (U.smearedCore_closable hc A.conformal_mem hf) x

lemma stressNormalized_difference (hc : A.toVertexAlgebra.C2Cofinite) {f g : ℤ → ℂ}
    (hf : RapidCoefficients f) (hg : RapidCoefficients g) {r : ℕ} (hr : 1 ≤ r) :
    ‖U.stressNormalized hc hf r-U.stressNormalized hc hg r‖ ≤
      coefficientSeminorm (fun n => f n-g n) 2*(1+A.centralCharge.re) := by
  apply U.sobolevExtension_sub_norm r _ _ (U.stressCore_bound hc hf hr) (U.stressCore_bound hc hg hr)
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg]))
  intro v
  have h := A.smearedMap_difference_bound (U.polynomialEnergyBounds hc A.conformalVector)
    (k := 1) (by simpa only [pow_one] using U.stress_physical_bound) hf hg v
  exact h.trans (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hr v)
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])))

lemma stressNormalized_continuous (hc : A.toVertexAlgebra.C2Cofinite)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t))
    (hl : ∀ t, Tendsto (fun s => coefficientSeminorm (fun n => f s n-f t n) 2) (𝓝 t) (𝓝 0))
    {r : ℕ} (hr : 1 ≤ r) : Continuous (fun t => U.stressNormalized hc (hf t) r) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun s => U.stressNormalized_difference hc (hf s) (hf t) hr)
  simpa only [zero_mul] using (hl t).mul_const (1+A.centralCharge.re)

lemma stressNormalized_defect (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hreal : ∀ n, star (f n)=f (-n)) {r : ℕ} (hr : 1 ≤ r) :
    ∃ F : Completion V →L[ℂ] Completion V,
      U.stressNormalized hc hf r-(U.stressNormalized hc hf r).adjoint=U.inverseSobolev r*F ∧
      ‖F‖ ≤ coefficientSeminorm f (2+r)*((1+A.centralCharge.re)*r) := by
  let K := U.smearedPowerCommutator A.conformal_mem (U.polynomialEnergyBounds hc A.conformalVector) hf r
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hK (v : V) : ‖K v‖ ≤ (coefficientSeminorm f (2+r)*((1+A.centralCharge.re)*r))*‖(A.energyShift^r) v‖ :=
    U.smearedPowerCommutator_bound A.conformal_mem (U.polynomialEnergyBounds hc _) hC U.stress_physical_bound hf r v
  refine ⟨U.sobolevExtension r K,?_,U.sobolevExtension_norm r K
    (mul_nonneg (coefficientSeminorm_nonneg _ _) (mul_nonneg hC (Nat.cast_nonneg r))) hK⟩
  exact U.sobolevExtension_defect r _ K (U.stressCore_bound hc hf hr) hK
    (U.smearedPowerCommutator_pairing A.conformal_mem A.conformal_quasiPrimary U.stress_hermitian
      (U.polynomialEnergyBounds hc _) hf hreal r)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance instFiniteDimensionalComplexSubtypeMemSubmoduleGrade_3 : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

lemma truncatedEnergyPower_norm (n r : ℕ) : ‖U.truncatedEnergyPower n r‖ ≤ (1+(n:ℝ))^r := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖U.energyCoordinates.symm (HilbertScale.truncatedEnergyPower n r (U.energyCoordinates x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h : ‖HilbertScale.truncatedEnergyPower (G := fun d => A.grade d) n r‖ ≤ (1+(n:ℝ))^r :=
    HilbertScale.boundedMultiplier_norm _ _ _
  simpa only [LinearIsometryEquiv.norm_map] using ContinuousLinearMap.le_of_opNorm_le _ h (U.energyCoordinates x)

 

def stressCutoff (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) : Completion V →L[ℂ] Completion V :=
  Complex.I • (U.energyCutoff n*(U.stressNormalized hc hf 1*U.truncatedEnergyPower n 1))

lemma stressCutoff_norm (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ‖U.stressCutoff hc n hf‖ ≤ (coefficientSeminorm f 2*(1+A.centralCharge.re))*(1+(n:ℝ)) := by
  rw [stressCutoff,norm_smul,Complex.norm_I,one_mul]
  calc
    _ ≤ ‖U.energyCutoff n‖*(‖U.stressNormalized hc hf 1‖*‖U.truncatedEnergyPower n 1‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*((coefficientSeminorm f 2*(1+A.centralCharge.re))*(1+(n:ℝ))^1) := by
      gcongr
      · exact U.energyCutoff_norm n
      · exact mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])
      · exact U.stressNormalized_norm hc hf le_rfl
      · exact U.truncatedEnergyPower_norm n 1
    _ = _ := by rw [pow_one,one_mul]

lemma stressCore_formalAdjoint (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hr : ∀ n, star (f n)=f (-n)) :
    (U.closedSmearedOperator hc A.conformalVector 2 f hf).IsFormalAdjoint
      (U.closedSmearedOperator hc A.conformalVector 2 f hf) := by
  exact SymmetricOperator.formalAdjoint_closure (U.smearedCore_closable hc A.conformal_mem hf)
    (U.smearedCore_closable hc A.conformal_mem hf)
    (HilbertCore.formalAdjoint (U.smearedMap_symmetric A.conformal_mem A.conformal_quasiPrimary
      U.stress_hermitian (U.polynomialEnergyBounds hc _) hf hr))

lemma stressCutoff_skew (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hr : ∀ m, star (f m)=f (-m)) :
    star (U.stressCutoff hc n hf) = -U.stressCutoff hc n hf := by
  have hs := SymmetricOperator.cutoff_selfAdjoint
    (U.closedSmearedOperator hc A.conformalVector 2 f hf) (U.stressCore_formalAdjoint hc hf hr)
    (U.energyCutoff n) (U.stressNormalized hc hf 1*U.truncatedEnergyPower n 1)
    (U.energyCutoff_selfAdjoint n)
    (U.energyCutoff_graph 1 (U.stressCore hc hf) (U.stressCore_bound hc hf le_rfl)
      (U.smearedCore_closable hc A.conformal_mem hf) n)
  rw [stressCutoff,star_smul,show star (_ : Completion V →L[ℂ] Completion V)=_ from hs]
  simp only [Complex.star_def,Complex.conj_I,neg_smul]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressCutoff_continuous (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t))
    (hl : ∀ t, Tendsto (fun s => coefficientSeminorm (fun m => f s m-f t m) 2) (𝓝 t) (𝓝 0)) :
    Continuous (fun t => U.stressCutoff hc n (hf t)) := by
  unfold stressCutoff
  exact (continuous_const (y := Complex.I)).smul (continuous_const.mul
    ((U.stressNormalized_continuous hc hf hl le_rfl).mul continuous_const))

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

structure StressPath where
  coefficients : ℝ → ℤ → ℂ
  rapid : ∀ t, RapidCoefficients (coefficients t)
  real : ∀ t n, star (coefficients t n)=coefficients t (-n)
  continuous : ∀ t, Tendsto (fun s => coefficientSeminorm
    (fun n => coefficients s n-coefficients t n) 2) (𝓝 t) (𝓝 0)
  bound : ℕ → ℝ
  bound_nonneg : ∀ r, 0 ≤ bound r
  seminorm_bound : ∀ t r, coefficientSeminorm (coefficients t) r ≤ bound r

lemma stressPath_cutoff_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) :
    ‖U.stressCutoff hc n (f.rapid t)‖ ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) := by
  exact (U.stressCutoff_norm hc n (f.rapid t)).trans (by
    gcongr
    · linarith [U.centralCharge_nonneg]
    · exact f.seminorm_bound t 2)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter Set
open scoped Topology

open UniformSpace Filter Set MeasureTheory
open scoped Topology

end

end OAI
end


