-- Prove2me | Definitions.Def_OAIE3v2B080
-- name    : OAIE3v2B080
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:19:26.723817+00:00
-- url     : https://prove2.me/theorems/75489922-402c-427d-b278-525866498751
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 81 of 311
-- statement:
--   Definitions bundle 81 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B043`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B046`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B050`, `OAIE3v2B058`, `OAIE3v2B059`, `OAIE3v2B060`, `OAIE3v2B061` of this split.
--
--   Modules: `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/CommonCorrectionBudget.lean`, `Dynamics/FilteredSectionSingleDenominatorBudget.lean`, `Dynamics/FlatPatchReset.lean`, `Dynamics/PointwiseSymbolBudget.lean`, `Estimates/ActiveProfileNoise.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/DependentPatchValue.lean`, `Estimates/JointRationalSpaceGenerators.lean`, `Estimates/RegularCylinderDecomposition.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Fourier/TorusCellBudget.lean`, `Fourier/UniformScaledRetainedCharacters.lean`, `Geometry/SupportedTriangularSum.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/StablePrimeUpperComparison.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Linear/ExternalFamilyPrecenterProjectionData.lean`, `Linear/JointRationalSpaceDefiningMatrix.lean`, `Linear/PeriodicKernelPartition.lean`, `Polynomial/BoundedRealPolynomialBasis.lean`, `Polynomial/LowestPolynomialLayer.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialShearObservableNet.lean`, `Polynomial/PolynomialSymbolicShearWeightedDegree.lean`, `Polynomial/RealPolynomialMassBox.lean`, `Probability/SpatialProductDensity.lean`, `Sampling/FixedPatchShearFiberCandidateScore.lean`, `Sampling/PatchKernelGridBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B043
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B046
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B058
import Definitions.Def_OAIE3v2B059
import Definitions.Def_OAIE3v2B060
import Definitions.Def_OAIE3v2B061

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3

theorem bounded_depth_budget {p : ℝ} (hp : 0 ≤ p) (a : ℕ) (q : ℕ → ℝ)
    (hq : ∀ d, 0 ≤ q d) (hzero : q 0 ≤ p)
    (hstep : ∀ d, q (d + 1) ≤ (q d + 2) ^ a) (d : ℕ) :
    q d ≤ (p + 2) ^ budgetDepthExponent a d := by
  induction d with
  | zero => simpa only [budgetDepthExponent, pow_one] using hzero.trans (by linarith : p ≤ p + 2)
  | succ d ih => exact polynomial_budget_comp hp (hq d) _ a ih (hstep d)

end Erdos3

end

section

namespace Erdos3

theorem iteratedPowerBudget_le_power (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    iteratedPowerBudget a p n ≤ (p + 2) ^ budgetDepthExponent a n :=
  bounded_depth_budget hp a (iteratedPowerBudget a p)
    (iteratedPowerBudget_nonneg a hp) le_rfl (fun _ => le_rfl) n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem contributing_unique {b c : Fin d → ℤ}
    (hb : Φ.value (A.residual b) ≠ 0) (hc : Φ.value (A.residual c) ≠ 0) : b = c :=
  A.integer_unique (by norm_num) (Φ.support _ hb) (Φ.support _ hc)

theorem patchValue_eq_of_nonzero {b : Fin d → ℤ} (hb : Φ.value (A.residual b) ≠ 0) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.contributing_unique Φ hc hb)

theorem patchValue_mem_Icc : A.patchValue Φ ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    rw [A.patchValue_eq_of_nonzero Φ hb]
    exact ⟨Φ.nonneg _, Φ.le_one _⟩
  · have hz : ∀ b : Fin d → ℤ, Φ.value (A.residual b) = 0 := by simpa using h
    rw [A.patchValue_eq_zero Φ hz]
    exact ⟨le_rfl, zero_le_one⟩

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {d : ℕ}

theorem patchValue_dist_of_residuals_close (A B : TriangularSlots d) (Φ : PatchKernel d)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε < 1 / 4)
    (hclose : ∀ b, Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0 →
      dist (A.residual b) (B.residual b) ≤ ε) :
    dist (A.patchValue Φ) (B.patchValue Φ) ≤ Φ.lip * ε := by
  have hbound (b) (hb : Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0) :
      ∀ i, |A.residual b i| ≤ 1 / 4 + ε := by
    intro i
    rcases hb with hb | hb
    · exact (Φ.support _ hb i).trans (by linarith)
    · have hd := (dist_le_pi_dist (A.residual b) (B.residual b) i).trans
        (hclose b (Or.inr hb))
      rw [Real.dist_eq] at hd
      have htriangle : |A.residual b i| ≤
          |A.residual b i - B.residual b i| + |B.residual b i| := by
        simpa only [sub_add_cancel] using
          abs_add_le (A.residual b i - B.residual b i) (B.residual b i)
      linarith [Φ.support _ hb i]
  by_cases h : ∃ b, Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    have hunique (c) (hc : Φ.value (A.residual c) ≠ 0 ∨ Φ.value (B.residual c) ≠ 0) : c = b :=
      A.integer_unique (by linarith : (1 / 4 + ε) + (1 / 4 + ε) < 1) (hbound c hc) (hbound b hb)
    have hA : A.patchValue Φ = Φ.value (A.residual b) := by
      apply tsum_eq_single b
      intro c hcb
      by_contra hc
      exact hcb (hunique c (Or.inl hc))
    have hB : B.patchValue Φ = Φ.value (B.residual b) := by
      apply tsum_eq_single b
      intro c hcb
      by_contra hc
      exact hcb (hunique c (Or.inr hc))
    rw [hA, hB]
    exact (Φ.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (hclose b hb) Φ.lip.coe_nonneg)
  · have hA (b) : Φ.value (A.residual b) = 0 := by
      by_contra hb
      exact h ⟨b, Or.inl hb⟩
    have hB (b) : Φ.value (B.residual b) = 0 := by
      by_contra hb
      exact h ⟨b, Or.inr hb⟩
    rw [A.patchValue_eq_zero Φ hA, B.patchValue_eq_zero Φ hB, dist_self]
    exact mul_nonneg Φ.lip.coe_nonneg hε

end Erdos3.TriangularSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

namespace SlotAffine

variable [Fintype τ] {h : ℕ}

theorem zero : SlotAffine (σ := σ) (τ := τ) (R := R) h 0 := by
  refine ⟨0, 0, (weightedSupportLE _ _).zero_mem, ?_⟩
  intro t x
  simp

theorem of_monomial {α : (σ ⊕ τ) →₀ ℕ} (c : R) (hh : 0 < h)
    (hα : Finsupp.weight (lowestSlotWeight h) α ≤ h) :
    SlotAffine h (monomial α c) := by
  classical
  by_cases hslots : ∀ j : τ, α (Sum.inr j) = 0
  · let C₀ : MvPolynomial σ R :=
      aeval (Sum.elim X (fun _ : τ => 0)) (monomial α c)
    have hC : C₀ ∈ weightedSupportLE (fun _ : σ => 1) h := by
      apply weightedSupportLE_aeval (lowestSlotWeight h) (fun _ : σ => 1)
      · intro v
        cases v with
        | inl a => exact weightedSupportLE_X _ a
        | inr j => exact (weightedSupportLE _ _).zero_mem
      · exact weightedSupportLE_mono hα (weightedSupportLE_monomial _ _ _)
    refine ⟨C₀, 0, hC, ?_⟩
    intro t x
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, C₀,
      MvPolynomial.comp_aeval_apply]
    simp only [aeval_monomial]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    cases v with
    | inl a => simp
    | inr j => simp [hslots j]
  · push Not at hslots
    obtain ⟨j, hj⟩ := hslots
    rw [exponent_eq_single_of_lowest_slot hh hα hj]
    refine ⟨0, Pi.single j c, (weightedSupportLE _ _).zero_mem, ?_⟩
    intro t x
    simp [aeval_monomial, Pi.single_apply]

end SlotAffine

theorem slotAffine_of_weightedSupport [Fintype τ] {h : ℕ} (hh : 0 < h)
    {p : MvPolynomial (σ ⊕ τ) R}
    (hp : p ∈ weightedSupportLE (lowestSlotWeight h) h) : SlotAffine h p := by
  classical
  have hsum (s : Finset ((σ ⊕ τ) →₀ ℕ))
      (hs : ∀ α ∈ s, Finsupp.weight (lowestSlotWeight h) α ≤ h) :
      SlotAffine h (∑ α ∈ s, monomial α (p.coeff α)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (SlotAffine.zero (σ := σ) (τ := τ) (R := R) (h := h))
    | @insert α s hnot ih =>
      rw [Finset.sum_insert hnot]
      exact (SlotAffine.of_monomial _ hh (hs α (Finset.mem_insert_self _ _))).add
        (ih (fun β hβ => hs β (Finset.mem_insert_of_mem hβ)))
  simpa only [p.support_sum_monomial_coeff] using hsum p.support hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedIntegerExponent_card_le (K : Type*) [Fintype K] (h : ℕ) :
    Fintype.card (BoundedIntegerExponent K h) ≤ (Fintype.card K + 1) ^ h := by
  classical
  let f : BoundedIntegerExponent K h → List.Vector (Option K) h :=
    fun e => paddedExponentWord e.val h e.property
  have hf : Function.Injective f := by
    intro e d hed
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg (fun v : List.Vector (Option K) h =>
      (v.val : Multiset (Option K)).count (some k)) hed
    simpa only [f, paddedExponentWord_count] using hc
  simpa using Fintype.card_le_of_injective f hf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SpatialProductDensity
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

instance pairSource_probability : IsProbabilityMeasure (pairSource ι) := by
  unfold pairSource
  infer_instance

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem roundedIntegerPolynomial_remainder_bound (P : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    |(P - MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P)).coeff a| ≤ 1 / 2 := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_map, roundedIntegerPolynomial_coeff]
  exact abs_sub_round (P.coeff a)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} {d : ℕ}

theorem slotPolynomialInput_update (t : σ → R) (b : Fin d → R) (i : Fin d) (c : R) :
    slotPolynomialInput t (Function.update b i c) i = slotPolynomialInput t b i := by
  funext v
  cases v with
  | inl a => rfl
  | inr j =>
      apply Function.update_of_ne
      intro h
      have hv := congrArg Fin.val h
      have hj := j.isLt
      simp only [earlierSlot] at hv
      omega

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem patchVariableWeight_split {d : ℕ} (w : Fin d → ℕ) (i : Fin d) :
    patchVariableWeight (σ := σ) w i = patchSlotWeight w i + patchParameterWeight i := by
  funext a
  cases a <;> simp [patchVariableWeight, patchSlotWeight, patchParameterWeight]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

theorem slotPrefixLift_eval (k i : Fin d) (hki : k.val ≤ i.val)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (t : σ → ℝ) (b : Fin d → ℝ) :
    aeval (slotPolynomialInput t b i) (slotPrefixLift k i R) =
      aeval (slotPolynomialInput t b k) R := by
  rw [slotPrefixLift, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f R)
  funext v
  cases v with
  | inl a => simp only [PolynomialSlots.placementSubstitution, Sum.elim_inl,
      aeval_X, slotPolynomialInput]
  | inr j =>
      have hj : (id (earlierSlot k j)).val < i.val := lt_of_lt_of_le j.isLt hki
      simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dif_pos hj,
        aeval_X, slotPolynomialInput]
      rfl

theorem slotPrefixLift_self (k : Fin d) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) :
    slotPrefixLift k k R = R := by
  have hsub : PolynomialSlots.placementSubstitution (σ := σ) id k k = X := by
    funext v
    cases v with
    | inl a => rfl
    | inr j =>
        have hj : (id (earlierSlot k j)).val < k.val := j.isLt
        simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dif_pos hj]
        rfl
  rw [slotPrefixLift, hsub, MvPolynomial.aeval_X_left_apply]

theorem slotShearSubstitution_before (k i : Fin d) (hik : i.val ≤ k.val)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) : slotShearSubstitution k R i = X := by
  funext v
  cases v with
  | inl a => rfl
  | inr j =>
      have h : earlierSlot i j ≠ k := by
        intro h
        have hv := congrArg Fin.val h
        have hj := j.isLt
        simp only [earlierSlot] at hv
        omega
      simp only [slotShearSubstitution, Sum.elim_inr, if_neg h, add_zero]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

theorem slotPolynomialLift_eval (i : Fin d) (P : MvPolynomial (σ ⊕ Fin i.val) R)
    (t : σ → R) (b : Fin d → R) :
    aeval (Sum.elim t b) (slotPolynomialLift i P) = aeval (slotPolynomialInput t b i) P := by
  rw [slotPolynomialLift, MvPolynomial.aeval_rename]
  apply congrArg (fun f => aeval f P)
  funext a
  cases a <;> rfl

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialMassBox
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

theorem lipschitzOn_realPolynomial_mass_box {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℝ)
    (C B : ℝ≥0) {s : ℕ} (hB : 1 ≤ B) (hC : realPolynomialMass P ≤ C)
    (hdegree : P.totalDegree ≤ s) :
    LipschitzOnWith (C * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)))
      (fun v : σ → ℝ => aeval v P) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  rw [Real.dist_eq]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hdiff (i : σ) : |v i - w i| ≤ dist v w := by
    simpa only [Real.dist_eq] using dist_le_pi_dist v w i
  have h := abs_aeval_sub_aeval_mass_box_bound P v w hBr dist_nonneg hv hw hdiff hdegree
  apply h.trans
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (pow_nonneg B.coe_nonneg _)) dist_nonneg

theorem lipschitzOn_realPolynomialVector_mass_box {σ τ : Type*} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ ℝ) (C B : ℝ≥0) {s : ℕ} (hB : 1 ≤ B)
    (hC : ∀ j, realPolynomialMass (P j) ≤ C) (hdegree : ∀ j, (P j).totalDegree ≤ s) :
    LipschitzOnWith (C * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)))
      (fun v : σ → ℝ => fun j => aeval v (P j)) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).mpr
  intro j
  exact (lipschitzOn_realPolynomial_mass_box (P j) C B hB (hC j) (hdegree j)).dist_le_mul v hv w hw

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem residualCoordinate_eval (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (b : Fin d → ℝ) (i : Fin d) :
    aeval (Sum.elim t b) (A.residualCoordinate i) =
      b i - (A.slots t).center b i := by
  rw [residualCoordinate, map_sub, aeval_X, slotPolynomialLift_eval]
  rfl

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

theorem patchParameterSpecialization_eval (t : σ → ℝ) (b : Fin d → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    aeval b (patchParameterSpecialization t P) = aeval (Sum.elim t b) P := by
  rw [patchParameterSpecialization, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f P)
  funext a
  cases a with
  | inl j => simp only [Sum.elim_inl, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  | inr j => simp only [Sum.elim_inr, aeval_X]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_common_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + (s + 2)) ^ (s + 2) * (p + 1) + (p + 2) ^ a + p + 2
      let t := ((q + 2) ^ 10 + 2) ^ 4
      separationBudget t + (t + 2) ^ 36 + ((t + 2) ^ 18 + t) ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) * (Polynomial.X + 1) +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let J : Polynomial ℕ := ((P + 2) ^ 10 + 2) ^ 4
  let B : Polynomial ℕ := (J + 2) ^ 48 + (J + 2) ^ 24 + J + 1 +
    (J + 2) ^ 36 + ((J + 2) ^ 18 + J)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, J, P, separationBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FilteredSectionSingleDenominatorBudget
namespace OAI

section

namespace Erdos3

theorem filtered_section_coefficient_loss_le_exp (n m H a : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    Real.exp ((p + 2) ^ a) +
      (((m : ℝ) + 1) * ((rationalKernelHeight m H : ℝ) + 1)) *
        ((((n : ℝ) + 1) * ((H : ℝ) + 1)) * Real.exp ((p + 2) ^ a) +
          Real.exp ((p + 2) ^ a)) ≤ Real.exp ((p + 2) ^ (a + 12)) := by
  let q := (p + 2) ^ (a + 9)
  let E := Real.exp q
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  have hq : 1 ≤ q := one_le_pow₀ hbase
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by dsimp [q]; positivity)
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have hpow (b : ℕ) (hb : b ≤ a + 9) : (p + 2) ^ b ≤ q := pow_le_pow_right₀ hbase hb
  have hA : Real.exp ((p + 2) ^ a) ≤ E := Real.exp_le_exp.mpr (hpow a (by omega))
  have hD : ((n : ℝ) + 1) * ((H : ℝ) + 1) ≤ E := by
    calc
      _ ≤ ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        gcongr
        exact hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide)))
      _ ≤ Real.exp ((p + 2) ^ 3) := matrix_weighted_factor_le_exp_power n hp hn 1 (by decide)
      _ ≤ E := Real.exp_le_exp.mpr (hpow 3 (by omega))
  have hS : ((m : ℝ) + 1) * ((rationalKernelHeight m H : ℝ) + 1) ≤ E := by
    calc
      _ ≤ ((m : ℝ) + 1) * (Real.exp ((p + 2) ^ 7) + 1) := by
        gcongr
        exact rationalKernelHeight_le_budget m H hp hm hH
      _ ≤ Real.exp ((p + 2) ^ 9) := matrix_weighted_factor_le_exp_power m hp hm 7 (by decide)
      _ ≤ E := Real.exp_le_exp.mpr (hpow 9 (by omega))
  have hE2 : E ≤ E * E := by nlinarith
  have hE3 : E * E ≤ E * E * E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (mul_nonneg hE0 hE0)
  calc
    _ ≤ E + E * (E * E + E) := by gcongr
    _ ≤ 3 * E ^ 3 := by nlinarith
    _ ≤ Real.exp 2 * (Real.exp q) ^ 3 := by
      change 3 * (Real.exp q) ^ 3 ≤ _
      exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by positivity)
    _ = Real.exp (2 + 3 * q) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    _ ≤ Real.exp ((p + 2) ^ (a + 12)) := by
      apply Real.exp_le_exp.mpr
      have hcube : (8 : ℝ) ≤ (p + 2) ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ p + 2) 3
        norm_num at h ⊢
        exact h
      calc
        2 + 3 * q ≤ 8 * q := by linarith
        _ ≤ (p + 2) ^ 3 * q := mul_le_mul_of_nonneg_right hcube (by linarith)
        _ = (p + 2) ^ (a + 12) := by
          dsimp [q]
          rw [← pow_add]
          congr 1
          omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FlatPatchReset
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

namespace PatchKernel

variable {d : ℕ} (Φ : PatchKernel d)

noncomputable def periodicValue (x : Fin d → ℝ) : ℝ := (constantSlots x).patchValue Φ

theorem periodicValue_mem_Icc (x : Fin d → ℝ) : Φ.periodicValue x ∈ Set.Icc (0 : ℝ) 1 :=
  (constantSlots x).patchValue_mem_Icc Φ

theorem kernel_le_periodicValue (x : Fin d → ℝ) (b : Fin d → ℤ) :
    Φ.value (fun i => (b i : ℝ) - x i) ≤ Φ.periodicValue x := by
  by_cases hb : Φ.value (fun i => (b i : ℝ) - x i) = 0
  · rw [hb]
    exact (Φ.periodicValue_mem_Icc x).1
  · exact le_of_eq ((constantSlots x).patchValue_eq_of_nonzero Φ hb).symm

theorem periodicValue_sub_le (x y : Fin d → ℝ) :
    Φ.periodicValue x - Φ.periodicValue y ≤ Φ.lip * dist x y := by
  by_cases hx : ∃ b : Fin d → ℤ, Φ.value (fun i => (b i : ℝ) - x i) ≠ 0
  · obtain ⟨b, hb⟩ := hx
    have heq := (constantSlots x).patchValue_eq_of_nonzero Φ hb
    have hle := Φ.kernel_le_periodicValue y b
    have hdist := Φ.lipschitz.dist_le_mul
      ((fun i => (b i : ℝ)) - x) ((fun i => (b i : ℝ)) - y)
    rw [dist_sub_left, Real.dist_eq] at hdist
    have habs := (le_abs_self
      (Φ.value (fun i => (b i : ℝ) - x i) - Φ.value (fun i => (b i : ℝ) - y i))).trans hdist
    change Φ.periodicValue x = Φ.value (fun i => (b i : ℝ) - x i) at heq
    linarith
  · have hz : Φ.periodicValue x = 0 := by
      apply (constantSlots x).patchValue_eq_zero Φ
      intro b
      exact not_ne_iff.mp (fun hb => hx ⟨b, hb⟩)
    have hy := (Φ.periodicValue_mem_Icc y).1
    have hnonneg : 0 ≤ (Φ.lip : ℝ) * dist x y := mul_nonneg Φ.lip.coe_nonneg dist_nonneg
    linarith

theorem periodicValue_lipschitz : LipschitzWith Φ.lip Φ.periodicValue := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have hxy := Φ.periodicValue_sub_le x y
  have hyx := Φ.periodicValue_sub_le y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

end PatchKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
namespace OAI

section

namespace Erdos3

theorem symbol_spanning_parameter_power_bound (s k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + (s + 3)) ^ (s + 3) + 2) ^ k ≤
      (p + 2) ^ (((s + 4) * (s + 3) + 2) * k) := by
  apply polynomial_budget_comp hp (by positivity) ((s + 4) * (s + 3)) k _ le_rfl
  simpa only [Nat.cast_add, Nat.cast_ofNat] using shifted_self_power_le_base_power hp (s + 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

noncomputable def localizedMajorArcLengthBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  localizationLengthBudget U (localizationThreshold U ζ (n + 1))
    (localizedMajorArcBudget n U ζ + 1)

theorem localizedMajorArcBudget_pos (n : ℕ) {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) :
    0 < localizedMajorArcBudget n U ζ :=
  multiaffineBiasBudget_pos n (localizationThreshold_pos hU hζ (n + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

theorem regularizedTentPartition_zero (c : I → X) (r : ℝ) (i : I) (x : X)
    (hx : 2 * r ≤ dist x (c i)) : regularizedTentPartition c r i x = 0 := by
  simp only [regularizedTentPartition, metricTent_zero_of_far (c i) x hx, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

theorem regularizedTentPartition_approx (c : I → X) {r : ℝ} (hr : 0 < r)
    (f : X → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (hcover : ∀ x, f x ≠ 0 → ∃ i, dist x (c i) ≤ r) (x : X) :
    |f x - ∑ i, regularizedTentPartition c r i x * f (c i)| ≤ 2 * L * r := by
  let w : I → ℝ := fun i => regularizedTentPartition c r i x
  have hw (i) : 0 ≤ w i := (regularizedTentPartition_range c hr i x).1
  have hsum : (∑ i, w i) ≤ 1 := regularizedTentPartition_sum_le c hr x
  have hidentity : f x = (∑ i, w i) * f x := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero]
    · rw [show (∑ i, w i) = 1 from regularizedTentPartition_sum c hr x (hcover x hx), one_mul]
  have hdiff : f x - ∑ i, w i * f (c i) = ∑ i, w i * (f x - f (c i)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hidentity]
  change |f x - ∑ i, w i * f (c i)| ≤ _
  rw [hdiff]
  calc
    _ ≤ ∑ i, |w i * (f x - f (c i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * (2 * L * r) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      by_cases hi : w i = 0
      · simp only [hi, zero_mul, le_refl]
      · have hnear : dist x (c i) < 2 * r := by
          by_contra! hfar
          exact hi (regularizedTentPartition_zero c r i x hfar)
        apply mul_le_mul_of_nonneg_left _ (hw i)
        calc
          |f x - f (c i)| ≤ (L : ℝ) * dist x (c i) := hf.dist_le_mul x (c i)
          _ ≤ (L : ℝ) * (2 * r) := mul_le_mul_of_nonneg_left hnear.le L.coe_nonneg
          _ = _ := by ring
    _ = (∑ i, w i) * (2 * L * r) := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * L * r := mul_le_of_le_one_left (by positivity) hsum

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PeriodicKernelPartition
namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ} {ι : Type*} [Fintype ι]

noncomputable def translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ := ∑ i, Φ.periodicValue (x - c i)

theorem translateSum_nonneg (Φ : PatchKernel d) (c : ι → Fin d → ℝ) (x : Fin d → ℝ) :
    0 ≤ Φ.translateSum c x := Finset.sum_nonneg (fun i _ => (Φ.periodicValue_mem_Icc (x - c i)).1)

theorem periodicValue_le_translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (i : ι) (x : Fin d → ℝ) : Φ.periodicValue (x - c i) ≤ Φ.translateSum c x := by
  exact Finset.single_le_sum (f := fun j => Φ.periodicValue (x - c j))
    (fun j _ => (Φ.periodicValue_mem_Icc (x - c j)).1) (Finset.mem_univ i)

theorem abs_translateSum_sub_le (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x y : Fin d → ℝ) :
    |Φ.translateSum c x - Φ.translateSum c y| ≤ Fintype.card ι * Φ.lip * dist x y := by
  unfold translateSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Φ.periodicValue (x - c i) - Φ.periodicValue (y - c i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (Φ.lip : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.dist_eq, dist_sub_right] using Φ.periodicValue_lipschitz.dist_le_mul
        (x - c i) (y - c i)
    _ = _ := by simp [mul_assoc]

theorem kernel_le_translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (i : ι) (x : Fin d → ℝ) : Φ.value x ≤ Φ.translateSum c (c i - x) := by
  have hk := Φ.kernel_le_periodicValue (-x) 0
  have hs := Φ.periodicValue_le_translateSum c i (c i - x)
  have heq : c i - x - c i = -x := by abel
  rw [heq] at hs
  simpa only [Pi.zero_apply, Int.cast_zero, Pi.neg_apply, zero_sub, neg_neg] using hk.trans hs

noncomputable def normalizedTranslate (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hcover : ∀ x, (δ : ℝ) ≤ Φ.translateSum c x) (i : ι) :
    PatchKernel d where
  value x := Φ.value x / Φ.translateSum c (c i - x)
  nonneg x := div_nonneg (Φ.nonneg x) (Φ.translateSum_nonneg c _)
  le_one x := by
    apply (div_le_one ((show (0 : ℝ) < δ from hδ).trans_le (hcover (c i - x)))).mpr
    exact Φ.kernel_le_translateSum c i x
  support x hx := Φ.support x (fun h => hx (by simp only [h, zero_div]))
  lip := Φ.lip / δ + Fintype.card ι * Φ.lip / (δ * δ)
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hnum := Φ.lipschitz.dist_le_mul x y
    have hden := Φ.abs_translateSum_sub_le c (c i - x) (c i - y)
    rw [dist_sub_left] at hden
    have h := abs_div_sub_div_bound (show (0 : ℝ) < δ from hδ) (hcover _) (hcover _)
      (mul_nonneg Φ.lip.coe_nonneg dist_nonneg) zero_le_one
      (by positivity : 0 ≤ (Fintype.card ι : ℝ) * Φ.lip * dist x y)
      hnum (by rw [abs_of_nonneg (Φ.nonneg _)]; exact Φ.le_one _) hden
    apply h.trans_eq
    push_cast
    ring

end Erdos3.PatchKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCellBudget
namespace OAI

section

namespace Erdos3

namespace PatchKernel

variable {d : ℕ}

noncomputable def integerLift (Φ : PatchKernel d) (x : Fin d → ℝ) : Fin d → ℤ := by
  classical
  exact if h : ∃ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) ≠ 0 then h.choose else 0

end PatchKernel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def emptyScalarCubeResidueEquiv (L : ℕ) (m : Option Empty → ℕ)
    (r : ∀ i, ZMod (m i)) :
    ↥((integerScalarCubeSet Empty L) ∩ scalarCubeResidueSet Empty L m r) ≃
      ↥(coefficientResidueSet L (m none) (r none)) where
  toFun x := by
    have hx := Finset.mem_inter.mp x.property
    have h0 := ((mem_integerScalarCubeSet L x.val).mp hx.1) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
    exact ⟨x.val none, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr h0,
      (mem_scalarCubeResidueSet L m r x.val).mp hx.2 none⟩⟩
  invFun z := by
    have hz := Finset.mem_filter.mp z.property
    have hb := Finset.mem_Ico.mp hz.1
    let x : IntegerScalarCubeBox Empty L := fun _ =>
      ⟨z.val, Finset.mem_Ico.mpr ⟨by omega, hb.2⟩⟩
    refine ⟨x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply (mem_integerScalarCubeSet L x).mpr
      intro t
      have ht : t = ∅ := Subsingleton.elim _ _
      simpa only [ht, integerScalarCubeValue, Finset.sum_empty, add_zero] using hb
    · apply (mem_scalarCubeResidueSet L m r x).mpr
      intro i
      cases i with
      | none => exact hz.2
      | some a => exact a.elim
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i with
    | none => rfl
    | some a => exact a.elim
  right_inv z := by apply Subtype.ext; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

instance standardEuclideanLattice_full : IsZLattice ℝ (standardEuclideanLattice ι) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointRationalSpaceGenerators
namespace OAI

section

namespace Erdos3

open scoped Matrix

def jointSpaceGeneratorHeight (ambient columns rows H R : ℕ) : ℕ :=
  imageDefiningHeight (ambient + rows) (ambient + rows)
    (max (imageDefiningHeight columns ambient H) R)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix NNReal

variable {J R I : Type*} [Fintype J] [Fintype R]

noncomputable def rationalKernelAxisBound (Q : Matrix R J ℚ) (H : ℕ) : ℝ :=
  (matrixDenominator Q : ℝ) * (((Fintype.card J : ℝ) + 1) * ((H : ℝ) + 1))

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem rationalRangeLattice_full
    {J C : Type*} [Fintype J] [Fintype C]
    (B : Matrix J C ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin = W)
    {H : ℕ} (hB : ∀ i j, RationalHeightLE (B i j) H) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice J) (euclideanSubspace W)) := by
  obtain ⟨v, hv, hmem, _⟩ := exists_bounded_integral_span_of_rational_range B W hW hB
  constructor
  apply top_unique
  rw [← hv]
  apply span_mono
  rintro _ ⟨j, rfl⟩
  exact hmem j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier MeasureTheory
open scoped TensorProduct

variable {L ι : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [T2Space (ℝ ⊗[ℚ] L)]

abbrev KernelProjectionParameters (K : Submodule ℚ L) :=
  CircleAverageTuple (List.finRange (finrank ℚ K))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

abbrev PrincipalAxisTuples (P : D → Prop) (L : PrincipalTupleIndex B h → ℕ) :=
  PrincipalIntegerTuples (fun d : {d // P d} => B d.val) (fun d => h d.val) α
    (principalAxisLength P L)

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

abbrev PrincipalAxisParameter (P : D → Prop) :=
  JointBlockParameter (fun d : {d // P d} => B d.val) (fun d => h d.val) α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

abbrev PartitionedProfileNoiseIndex {D : Type*} (G Z α : Type*) (B : D → Type*)
    (h : D → ℕ) (P : D → Prop) :=
  (Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) ⊕
    (Σ d, SamplerCoefficientSlot G B h d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

noncomputable def cut (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) : ℝ := by
  classical
  exact if c.Contains (F z) then w z else 0

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

instance containsDecidable (c : ProductCylinder X) (x : ∀ i, X i) : Decidable (c.Contains x) := by
  unfold Contains
  infer_instance

end Erdos3.ProductCylinder

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedTriangularSum
namespace OAI

section

namespace Erdos3.TriangularSlots

open scoped BigOperators

variable {d : ℕ} (A : TriangularSlots d)

theorem tsum_eq_at_of_residual_bound (f : (Fin d → ℝ) → ℝ) {R : ℝ}
    (hgap : R + R < 1) (hsupport : ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ R)
    (b : Fin d → ℤ) (hb : ∀ i, |A.residual b i| ≤ R) :
    (∑' z, f (A.residual z)) = f (A.residual b) := by
  apply tsum_eq_single b
  intro z hzb
  by_contra hz
  exact hzb (A.integer_unique hgap (hsupport _ hz) hb)

theorem tsum_approx_finite_family {I : Type*} [Fintype I]
    (f : (Fin d → ℝ) → ℝ) (g : I → (Fin d → ℝ) → ℝ) (c : I → ℝ)
    {R ε : ℝ} (hgap : R + R < 1) (hε : 0 ≤ ε)
    (hf : ∀ x, f x ≠ 0 → ∀ j, |x j| ≤ R)
    (hg : ∀ i x, g i x ≠ 0 → ∀ j, |x j| ≤ R)
    (happrox : ∀ x, |f x - ∑ i, c i * g i x| ≤ ε) :
    |(∑' z, f (A.residual z)) - ∑ i, c i * ∑' z, g i (A.residual z)| ≤ ε := by
  classical
  by_cases h : ∃ z : Fin d → ℤ, f (A.residual z) ≠ 0 ∨ ∃ i, g i (A.residual z) ≠ 0
  · obtain ⟨z, hz⟩ := h
    have hb : ∀ j, |A.residual z j| ≤ R := by
      rcases hz with hz | ⟨i, hi⟩
      · exact hf _ hz
      · exact hg i _ hi
    rw [A.tsum_eq_at_of_residual_bound f hgap hf z hb]
    simp_rw [A.tsum_eq_at_of_residual_bound _ hgap (hg _) z hb]
    exact happrox _
  · have hfzero (z : Fin d → ℤ) : f (A.residual z) = 0 := by
      by_contra hz
      exact h ⟨z, Or.inl hz⟩
    have hgzero (i : I) (z : Fin d → ℤ) : g i (A.residual z) = 0 := by
      by_contra hz
      exact h ⟨z, Or.inr ⟨i, hz⟩⟩
    simp only [hfzero, hgzero, tsum_zero, mul_zero, Finset.sum_const_zero, sub_self, abs_zero]
    exact hε

end Erdos3.TriangularSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateMean {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℂ :=
  𝔼 z : primeCoordinateCell lo N q I x, f z.val

noncomputable def PrimeCoordinateStable {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → (primeCoordinateCell lo N q (I ∪ J) y).Nonempty →
    ‖primeCoordinateMean f lo N q I x - primeCoordinateMean f lo N q (I ∪ J) y‖ ≤ δ

universe u v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev ResiduePrimeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :=
  {z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a //
    ∀ i ∈ I, (fun j => ((z j).val : ZMod (q i))) = x i}

noncomputable def residuePrimeCoordinateMean {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℂ := by
  classical
  exact 𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StablePrimeUpperComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def PrimeRefinementUpperBound {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (h g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (level ε δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y) →
    (residuePrimeCoordinateMean h lo N M a q (I ∪ J) y).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q I x).re + ε + level * δ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

theorem exists_controlledProjectionBudget_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → controlledProjectionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ :=
    Polynomial.X + (Polynomial.X + (Polynomial.X + 3) ^ 7 + 2) ^ 4 + 1
  let P : Polynomial ℕ :=
    ((Polynomial.X + 2) ^ 10 + 2) ^ 36 +
      (((Polynomial.X + 2) ^ 10 + 2) ^ 18 + Polynomial.X) +
      ((Q + Q * ((Q + 2) ^ 7 + Q)) + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Q, controlledProjectionBudget, preimageBasisBudget, sparseGeneratorBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem exists_controlledProjectionUniformBudget_power (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      controlledProjectionBudget (controlledProjectionDimensionInput s p) ≤ (p + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_controlledProjectionBudget_power
  let P : Polynomial ℕ :=
    (2 * ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)) ^ 2 +
      Polynomial.X + 1 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  apply (ha _ (controlledProjectionDimensionInput_nonneg s hp)).trans
  simpa [P, controlledProjectionDimensionInput, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointRationalSpaceDefiningMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem jointSpaceDefiningHeight_le_exp (ambient columns H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    ((max (imageDefiningHeight columns ambient H) R : ℕ) : ℝ) ≤
      Real.exp ((p+2)^10) := by
  rw [Nat.cast_max]
  exact max_le (imageDefiningHeight_le_exp columns ambient H hp hc ha hH)
    (hR.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 10))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {D : ℕ} {R : Type*} [CommRing R]

theorem earlierSlotMatrix_strict (m : (i : Fin D) → Fin i.val → R)
    (i j : Fin D) (hij : i ≤ j) : earlierSlotMatrix m i j = 0 := by
  classical
  have hne (k : Fin i.val) : earlierSlot i k ≠ j := by
    intro heq
    have hval := congrArg Fin.val heq
    have hi := k.isLt
    change k.val = j.val at hval
    change i.val ≤ j.val at hij
    omega
  simp [earlierSlotMatrix, hne]

theorem earlierSlotMatrix_mulVec (m : (i : Fin D) → Fin i.val → R)
    (x : Fin D → R) (i : Fin D) :
    (earlierSlotMatrix m).mulVec x i = ∑ k : Fin i.val, m i k * x (earlierSlot i k) := by
  classical
  simp only [earlierSlotMatrix, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_mul, zero_mul]
  simp

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin (D + E) → ℕ}

theorem lowest_prefix_slotAffine (A : PolynomialSlots σ (D + E) w)
    {h : ℕ} (hh : 0 < h) (hw : ∀ i : Fin D, w (i.castAdd E) = h) (i : Fin D) :
    SlotAffine h (A.center (i.castAdd E)) := by
  apply slotAffine_of_weightedSupport hh
  have hweight : patchVariableWeight w (i.castAdd E) =
      lowestSlotWeight (σ := σ) (τ := Fin i.val) h := by
    funext v
    cases v with
    | inl a => rfl
    | inr j =>
      exact hw ⟨j.val, lt_trans j.isLt i.isLt⟩
  rw [← hweight, ← hw i]
  exact A.degree (i.castAdd E)

theorem exists_lowest_affine_prefix (A : PolynomialSlots σ (D + E) w)
    {h : ℕ} (hh : 0 < h) (hw : ∀ i : Fin D, w (i.castAdd E) = h) :
    ∃ (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
      (P : Fin D → MvPolynomial σ ℝ),
      (∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) h) ∧
      ∀ t : σ → ℝ, (A.slots t).takePrefix =
        TriangularSlots.affineBlock M hM (fun i => aeval t (P i)) := by
  classical
  have hrows := A.lowest_prefix_slotAffine hh hw
  choose C₀ m hC hrow using hrows
  let M := earlierSlotMatrix m
  have hM : ∀ i j, i ≤ j → M i j = 0 := earlierSlotMatrix_strict m
  have hcenter (t : σ → ℝ) (x : Fin D → ℝ) (i : Fin D) :
      (A.slots t).takePrefix.center x i = aeval t (C₀ i) + M.mulVec x i := by
    change aeval (Sum.elim t (fun j =>
      Fin.append x 0 (earlierSlot (i.castAdd E) j))) (A.center (i.castAdd E)) = _
    have hargs : (fun j : Fin i.val => Fin.append x 0 (earlierSlot (i.castAdd E) j)) =
        (fun j => x (earlierSlot i j)) := by
      funext j
      change Fin.append x 0 ((earlierSlot i j).castAdd E) = _
      exact Fin.append_left _ _ _
    calc
      _ = aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center (i.castAdd E)) :=
        congrArg (fun f : Fin i.val → ℝ => aeval (Sum.elim t f) (A.center (i.castAdd E))) hargs
      _ = aeval t (C₀ i) + ∑ j, m i j * x (earlierSlot i j) := hrow i t _
      _ = _ := congrArg (fun z => aeval t (C₀ i) + z) (earlierSlotMatrix_mulVec m x i).symm
  obtain ⟨P, hP, hsolve⟩ := polynomial_affine_origin M hM C₀ hC
  refine ⟨M, hM, P, hP, ?_⟩
  intro t
  apply TriangularSlots.ext
  intro x i
  rw [hcenter]
  change aeval t (C₀ i) + M.mulVec x i =
    aeval t (P i) + M.mulVec (x - fun j => aeval t (P j)) i
  rw [Matrix.mulVec_sub]
  have hs := hsolve t
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hs
  have hi := congrFun hs i
  simp only [Pi.sub_apply] at hi ⊢
  linarith

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E h : ℕ}

theorem nonempty_lowestLayerModel (A : PolynomialPatch σ s (D + E))
    (hh : 0 < h) (hw : ∀ i : Fin D, A.weight (i.castAdd E) = h) :
    Nonempty (A.LowestLayerModel h) := by
  obtain ⟨M, hM, P, hP, heq⟩ := A.form.exists_lowest_affine_prefix hh hw
  exact ⟨⟨M, hM, P, hP, hw, heq⟩⟩

noncomputable def lowestLayerModel (A : PolynomialPatch σ s (D + E))
    (hh : 0 < h) (hw : ∀ i : Fin D, A.weight (i.castAdd E) = h) :
    A.LowestLayerModel h := Classical.choice (A.nonempty_lowestLayerModel hh hw)

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearObservableNet
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem patchTopCoefficientIndex_card (d s : ℕ) :
    Fintype.card (PatchTopCoefficientIndex d s) ≤ d * (d + 1) ^ s := by
  simpa only [PatchTopCoefficientIndex, Fintype.card_prod, Fintype.card_fin] using
    Nat.mul_le_mul_left d (boundedIntegerExponent_card_le (Fin d) s)

theorem patchTopCoefficientCode_card (d s N : ℕ) :
    Fintype.card (PatchTopCoefficientIndex d s → Fin (N + 1)) ≤
      (N + 1) ^ (d * (d + 1) ^ s) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by omega) (patchTopCoefficientIndex_card d s)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PatchKernelGridBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem gridPatchKernel_original_support {d N : ℕ} (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : Fin d → ℝ)
    (hx : regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x ≠ 0)
    (j : Fin d) : |x j| ≤ 3 / 8 := by
  have hnear : dist x (uniformBoxGrid (1 / 4) N i) < 2 * (patchKernelGridRadius N : ℝ) := by
    by_contra! hfar
    exact hx (regularizedTentPartition_zero _ _ _ _ hfar)
  have hcoord := dist_le_pi_dist x (uniformBoxGrid (1 / 4) N i) j
  rw [Real.dist_eq] at hcoord
  have hcenter := uniformBoxGrid_mem (by norm_num : (0 : ℝ) ≤ 1 / 4) (by omega : 0 < N) i j
  have htriangle : |x j| ≤ |x j - uniformBoxGrid (1 / 4) N i j| +
      |uniformBoxGrid (1 / 4) N i j| := by
    simpa only [sub_add_cancel] using
      abs_add_le (x j - uniformBoxGrid (1 / 4) N i j) (uniformBoxGrid (1 / 4) N i j)
  linarith [patchKernelGridRadius_small hN]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPatchShearFiberCandidateScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialSlots

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ} {w : Fin d → ℕ}

noncomputable def coordinateFiberForm (A : PolynomialSlots I d w)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) : PolynomialSlots {i // keep i} d w :=
  A.reparam (coordinateFiberParameters keep fixed) (coordinateFiberParameters_degree keep fixed)

end PolynomialSlots

end Erdos3

end

end OAI
end


