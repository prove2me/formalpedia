-- Prove2me | Definitions.Def_OAIE3v2B097
-- name    : OAIE3v2B097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:30.832982+00:00
-- url     : https://prove2.me/theorems/7bd2a478-5f2d-4f2f-8e01-d365ee2e685d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 99 of 311
-- statement:
--   Definitions bundle 99 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B072`, `OAIE3v2B073`, `OAIE3v2B074`, `OAIE3v2B077`, `OAIE3v2B078`, `OAIE3v2B079`, `OAIE3v2B080`, `OAIE3v2B081`, `OAIE3v2B082`, `OAIE3v2B083` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateCoveredBudget.lean`, `Dynamics/PreparedFiniteForwardActualNativeBudget.lean`, `Dynamics/PreparedFiniteScheduleGeometryBudget.lean`, `Estimates/ActiveProfileNoise.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedTailProfileIdentity.lean`, `Estimates/CoefficientDeckImageCongruence.lean`, `Estimates/JointRationalSpaceGenerators.lean`, `Estimates/MixedCoefficientCounting.lean`, `Estimates/MixedCoveredRowReindex.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/PositiveRetainedDenominatorLog.lean`, `Estimates/PreparedUniformEarlyRadiusWithCutoff.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/UniformScaledRetainedLogBounds.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Fourier/UniformSpectrumLogBounds.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/EmptyLayerChartBounds.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/RelativePatchFiniteCoordinateReduction.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/AllocatedSupportedSlicedResidue.lean`, `Lattices/CertifiedFullChartAffineTerminal.lean`, `Lattices/CoefficientDeckResidueMask.lean`, `Lattices/FullTaggedAffineComplementAgreement.lean`, `Lattices/IntegerBoxObservedMean.lean`, `Lattices/LatticeSheetHaar.lean`, `Lattices/LieSubalgebraLatticeInnerGrid.lean`, `Lattices/NormalizedResidueBlockCells.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Linear/AllocatedCanonicalProjectionBudget.lean`, `Linear/NormalizedBasisBounds.lean`, `Linear/WeightedDualVector.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/PreparedUniformDegreePrecisionBudget.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/OrthonormalMixedLaw.lean`, `Probability/RelativeFullSliceLaw.lean`, `Probability/SpatialProductDensity.lean`, `Sampling/AllocatedSlicedGridResourceBudget.lean`, `Sampling/AllocatedSupportedSlicedFullGridSite.lean`, `Sampling/ForecastGoodPathMeanNorm.lean`, `Sampling/NativeMarkedFreezingSliceScore.lean`, `Sampling/NormalizedRealBoxHalfGrid.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B072
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B077
import Definitions.Def_OAIE3v2B078
import Definitions.Def_OAIE3v2B079
import Definitions.Def_OAIE3v2B080
import Definitions.Def_OAIE3v2B081
import Definitions.Def_OAIE3v2B082
import Definitions.Def_OAIE3v2B083

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem short_progression_cell_mass_le {N : ℕ} (P : FiniteProgressionPartition N)
    {L : ℝ} (hL : 0 ≤ L) :
    (𝔼 n : Fin N, if ((P.length (P.cell n) : ℕ) : ℝ) < L then 1 else 0) ≤
      (Fintype.card P.Label : ℝ) * L / N := by
  classical
  let b : Fin N → ℝ := fun n => if (P.length (P.cell n) : ℝ) < L then 1 else 0
  have hcell (a : P.Label) : (∑ n ∈ partitionCell P.cell a, b n) ≤ L := by
    have heq : (∑ n ∈ partitionCell P.cell a, b n) =
        if (P.length a : ℝ) < L then (P.length a : ℝ) else 0 := by
      calc
        _ = ∑ _n ∈ partitionCell P.cell a, if (P.length a : ℝ) < L then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [b, (mem_partitionCell _ _ _).mp hn]
        _ = _ := by split_ifs <;> simp [P.card_cell]
    rw [heq]
    split_ifs with h
    · exact h.le
    · exact hL
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset P.Label)) => hcell a)
  rw [sum_partitionCell] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)

theorem short_box_side_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i) :
    (𝔼 x : (∀ i, Fin (N i)), if (∀ i, L i ≤ ((P i).length ((P i).cell (x i)) : ℝ)) then 0 else 1) ≤
      ∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i := by
  classical
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hpoint (x : ∀ i, Fin (N i)) :
      (if (∀ i, L i ≤ ((P i).length ((P i).cell (x i)) : ℝ)) then (0 : ℝ) else 1) ≤
        ∑ i, if ((P i).length ((P i).cell (x i)) : ℝ) < L i then 1 else 0 := by
    split_ifs with h
    · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => if ((P j).length ((P j).cell (x j)) : ℝ) < L j then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [hi, ite_true] using hs
  apply (Finset.expect_le_expect (fun x _ => hpoint x)).trans
  rw [Finset.expect_sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [expect_coordinate (X := fun j => Fin (N j)) i
    (fun n : Fin (N i) => if ((P i).length ((P i).cell n) : ℝ) < L i then (1 : ℝ) else 0)]
  exact short_progression_cell_mass_le (P i) (hL i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
namespace OAI

section

namespace Erdos3

theorem exists_normalizedRealBoxGrid_half_cell {σ : Type*}
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {N : ℕ} (hN : 0 < N)
    (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) :
    ∃ j : σ → Fin (N + 1), ∀ i,
      |v i - normalizedRealBoxGrid T N j i| ≤ T i / N := by
  classical
  have hnorm (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i)]
    exact (div_le_one (hT i)).mpr (hv i)
  choose j hj using fun i => exists_uniformIntervalGrid_half_approx
    (by norm_num : (0 : ℝ) < 1) hN (v i / T i) (hnorm i)
  refine ⟨j, fun i => ?_⟩
  have heq : v i - normalizedRealBoxGrid T N j i =
      T i * (v i / T i - uniformIntervalGrid 1 N (j i)) := by
    dsimp only [normalizedRealBoxGrid, uniformBoxGrid]
    field_simp [(hT i).ne']
  rw [heq, abs_mul, abs_of_pos (hT i)]
  exact (mul_le_mul_of_nonneg_left (hj i) (hT i).le).trans_eq (by ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

theorem ofBlocks_point (H : ι → ℕ) (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label)
    (j : ∀ i, Fin ((ofBlocks H hq hH a).length i)) :
    (ofBlocks H hq hH a).point j =
      BoxProgressionPartition.point (fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)) a j := by
  funext i
  apply Fin.ext
  rfl

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3

theorem exists_normalized_cell_of_coordinate_intervals {ι : Type*}
    (T lo hi : ι → ℝ) (hT : ∀ i, 0 < T i) {Q : ℕ} (hQ : 0 < Q)
    (hlo : ∀ i, |lo i| ≤ T i) (hhi : ∀ i, |hi i| ≤ T i)
    (hwidth : ∀ i, hi i - lo i ≤ 2 * T i / Q) :
    ∃ a : ι → Fin (Q + 1), ∀ v : ι → ℝ,
      (∀ i, lo i ≤ v i ∧ v i ≤ hi i) →
      ∀ i, |v i - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q) := by
  let mid := fun i => (lo i + hi i) / 2
  have hm (i) : |mid i| ≤ T i := by
    apply abs_le.mpr
    have hl := abs_le.mp (hlo i)
    have hh := abs_le.mp (hhi i)
    dsimp only [mid]
    constructor <;> linarith
  obtain ⟨a, ha⟩ := exists_normalizedRealBoxGrid_half_cell T hT hQ mid hm
  refine ⟨a, ?_⟩
  intro v hv i
  have hd : |v i - mid i| ≤ T i / Q := by
    apply abs_le.mpr
    have hw := hwidth i
    rw [mul_div_assoc] at hw
    have hh := hv i
    dsimp only [mid]
    constructor <;> linarith
  calc
    _ ≤ |v i - mid i| + |mid i - normalizedRealBoxGrid T Q a i| := abs_sub_le _ _ _
    _ ≤ T i / Q + T i / Q := add_le_add hd (ha i)
    _ = T i * (2 / Q) := by ring

namespace ResidueBoxSlice

theorem exists_affine_normalized_cell {ι : Type*} {N : ι → ℕ} {q Q : ℕ}
    (A : ResidueBoxSlice N q) (hlen : ∀ i, 0 < A.length i)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) (hQ : 0 < Q)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hwidth : ∀ i, step * q * A.length i ≤ 2 * T i / Q) :
    ∃ a : ι → Fin (Q + 1), ∀ j : ∀ i, Fin (A.length i), ∀ i,
      |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q a i| ≤
        T i * (2 / Q) := by
  let lo := fun i => origin i + step * A.start i
  let hi := fun i => origin i + step * (A.start i + q * (A.length i - 1) : ℕ)
  have hlo (i) : |lo i| ≤ T i := by
    apply hparent i (A.start i)
    simpa only [Nat.mul_zero, Nat.add_zero] using A.inside i 0 (hlen i)
  have hhi (i) : |hi i| ≤ T i :=
    hparent i _ (A.inside i _ (Nat.sub_lt (hlen i) (by decide)))
  have hw (i) : hi i - lo i ≤ 2 * T i / Q := by
    have hs : step * (q : ℝ) * (A.length i - 1 : ℕ) ≤ step * q * A.length i :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le _ _)) (by positivity)
    dsimp only [hi, lo]
    push_cast
    nlinarith [hwidth i]
  obtain ⟨a, ha⟩ := exists_normalized_cell_of_coordinate_intervals T lo hi hT hQ hlo hhi hw
  refine ⟨a, fun j => ha (fun i => origin i + step * (A.point j i).val) ?_⟩
  intro i
  have hj : (j i).val ≤ A.length i - 1 := by have := (j i).isLt; omega
  have hs := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj : ((j i).val : ℝ) ≤ _)
    (show 0 ≤ step * (q : ℝ) by positivity)
  dsimp only [lo, hi, point]
  push_cast
  constructor
  · have hn : 0 ≤ step * (q : ℝ) * ((j i).val : ℝ) := by positivity
    nlinarith
  · nlinarith

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

noncomputable def ofPhysicalResidueEquiv :
    (∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) ≃
      IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a :=
  Equiv.piCongrRight fun i =>
    physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem modeling_dual_zero_weight (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ}
    (htau : 0 < tau) (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0 := by
  intro x hx
  have h := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
  rw [p.mean_single_norm, hx, mul_zero] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (f (Pi.single x 1))]

theorem weightedDualVector_cap (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ}
    (hK : 0 ≤ K) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, ‖weightedDualVector p f x‖ ≤ K / tau := by
  intro x
  rw [weightedDualVector_norm]
  rcases (p.nonneg x).eq_or_lt with hx | hx
  · rw [← hx, div_zero]
    exact div_nonneg hK htau.le
  · have h := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
    rw [p.mean_single_norm] at h
    apply (div_le_iff₀ hx).mpr
    have h' : ‖f (Pi.single x 1)‖ ≤ (K * p.weight x) / tau :=
      (le_div_iff₀ htau).mpr (by nlinarith only [h])
    calc
      _ ≤ (K * p.weight x) / tau := h'
      _ = _ := by ring

theorem weightedDualVector_detectable (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (b : Ω → ℂ) {M tau : ℝ}
    (hM : 0 < M) (htau : 0 < tau) (hb : ∀ x, ‖b x‖ ≤ M)
    (hfb : 1 < (f b).re) (hdual : ∀ v, tau * ‖f v‖ ≤ X v)
    (hzero : ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0) :
    tau / M ^ 2 < X (weightedDualVector p f) := by
  have hbMean : p.mean (fun x => ‖b x‖ ^ 2) ≤ M ^ 2 :=
    (p.mean_mono (fun x => pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)).trans_eq
      (p.mean_const (M ^ 2))
  have hself : ‖f (weightedDualVector p f)‖ =
      p.mean (fun x => ‖weightedDualVector p f x‖ ^ 2) := by
    rw [functional_eq_weighted_inner p f hzero, p.correlation_self,
      Complex.norm_real, Real.norm_of_nonneg (p.mean_nonneg (fun x => sq_nonneg _))]
  have hcs := p.norm_correlation_sq_le b (weightedDualVector p f)
  rw [← functional_eq_weighted_inner p f hzero, ← hself] at hcs
  have hupper := mul_le_mul_of_nonneg_right hbMean
    (norm_nonneg (f (weightedDualVector p f)))
  have hnorm : 1 < ‖f b‖ := hfb.trans_le (Complex.re_le_norm _)
  have hlarge : 1 < M ^ 2 * ‖f (weightedDualVector p f)‖ := by
    nlinarith only [hcs, hupper, hnorm]
  have hscaled := mul_lt_mul_of_pos_left hlarge htau
  have hdom := mul_le_mul_of_nonneg_left (hdual (weightedDualVector p f)) (sq_nonneg M)
  apply (div_lt_iff₀ (pow_pos hM 2)).mpr
  nlinarith only [hscaled, hdom]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NormalizedBasisBounds
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators Matrix

theorem basis_coordinates_norm_le_of_covolume {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (o : OrthonormalBasis (Fin n) ℝ E) (b : Basis (Fin n) ℝ E)
    {H κ : ℝ} (hH : 0 ≤ H) (hκ : 0 < κ) (hb : ∀ i, ‖b i‖ ≤ H)
    (hcovol : κ ≤ ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖b.equivFun x‖ ≤ ((n : ℝ) * n.factorial * H ^ (n - 1) / κ) * ‖x‖ := by
  classical
  let A := o.toBasis.toMatrix b
  have hdet : κ ≤ |A.det| := by
    simpa only [covolume_basis_eq_orthonormal_det o b, Basis.det_apply] using hcovol
  have hentry : ∀ i j, |A i j| ≤ H := fun i j =>
    (orthonormal_basis_coordinate_abs_le o (b j) i).trans (hb j)
  have hinv : ∀ i j, |A⁻¹ i j| ≤ (n.factorial : ℝ) * H ^ (n - 1) / κ := by
    intro i j
    simpa only [Fintype.card_fin] using matrix_inverse_entry_abs_le A hentry hκ hdet i j
  have hM : A *ᵥ (b.equivFun x) = o.toBasis.equivFun x :=
    basis_coordinate_matrix_mulVec b o.toBasis.equivFun.toLinearMap x
  have hback : A⁻¹ *ᵥ (o.toBasis.equivFun x) = b.equivFun x := by
    rw [← hM, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (abs_pos.mp (hκ.trans_le hdet))),
      Matrix.one_mulVec]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [← hback, Real.norm_eq_abs]
  change |∑ j, A⁻¹ i j * o.toBasis.equivFun x j| ≤ _
  calc
    _ ≤ ∑ j, |A⁻¹ i j * o.toBasis.equivFun x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ((n.factorial : ℝ) * H ^ (n - 1) / κ) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hinv i j) (orthonormal_basis_coordinate_abs_le o x j)
        (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem normalizedAxisBasis_coordinates_bound (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖(normalizedAxisBasis b).equivFun x‖ ≤
      ((n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖ := by
  have h := basis_coordinates_norm_le_of_covolume o (normalizedAxisBasis b)
    (by positivity : 0 ≤ B + 1) (one_div_pos.mpr hD)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2)
    (normalizedAxisBasis_covolume_lower o b hD hprod) x
  simpa only [one_div, div_inv_eq_mul] using h

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

instance fourSource_probability : IsProbabilityMeasure (fourSource ι) := by
  unfold fourSource
  infer_instance

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialShearBoundedCoordinates (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) :
    PolynomialShearLieAlgebra w R →ₗ[R] (σ → weightedSupportLE (R := R) w s) where
  toFun D i := ⟨D.val (X i), weightedSupportLE_mono (hw i)
    (weightedSupportDrop_le (D.property i))⟩
  map_add' D E := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' c D := by
    funext i
    apply Subtype.ext
    rfl

theorem polynomialShearBoundedCoordinates_injective (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) :
    Function.Injective (polynomialShearBoundedCoordinates (R := R) w s hw) := by
  intro D E h
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  exact congrArg (fun f : σ → weightedSupportLE (R := R) w s => (f i : MvPolynomial σ R)) h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {I J : Type*} [Fintype J]

theorem samplingRankProjection_mem (a : J → ℤ) (e : J → ℝ)
    (W : Submodule ℝ (J → ℝ)) (he : e ∈ W) (hae : integerRowLinear a e = 1)
    {v : J → ℝ} (hv : v ∈ W) :
    samplingRankProjection a e v ∈ W ⊓ LinearMap.ker (integerRowLinear a) := by
  constructor
  · exact W.sub_mem hv (W.smul_mem _ he)
  · change integerRowLinear a (samplingRankProjection a e v) = 0
    rw [samplingRankProjection_apply, map_sub, map_smul, hae]
    simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped Matrix BigOperators

namespace VectorPolynomial

theorem jointRationalSpace_appendRankCutRow {ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) (a : ι → ℤ) :
    jointRationalSpace B (appendRankCutRow A a) =
      jointRationalSpace B A ⊓ LinearMap.ker (integerRowLinear a) := by
  ext v
  constructor
  · rintro ⟨hB, hA⟩
    change Matrix.of (fun r i => ((appendRankCutRow A a) r i : ℝ)) *ᵥ v = 0 at hA
    refine ⟨⟨hB, ?_⟩, ?_⟩
    · change Matrix.of (fun r i => (A r i : ℝ)) *ᵥ v = 0
      ext r
      exact congrFun hA (some r)
    · change integerRowLinear a v = 0
      have hn := congrFun hA none
      simpa only [appendRankCutRow, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Option.elim_none, Rat.cast_intCast, Pi.zero_apply, integerRowLinear_apply] using hn
  · rintro ⟨⟨hB, hA⟩, ha⟩
    refine ⟨hB, ?_⟩
    change Matrix.of (fun r i => ((appendRankCutRow A a) r i : ℝ)) *ᵥ v = 0
    change Matrix.of (fun r i => (A r i : ℝ)) *ᵥ v = 0 at hA
    change integerRowLinear a v = 0 at ha
    ext r
    cases r with
    | none =>
      simpa only [appendRankCutRow, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Option.elim_none, Rat.cast_intCast, Pi.zero_apply, integerRowLinear_apply] using ha
    | some r => exact congrFun hA r

open scoped TensorProduct

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyLayerChartBounds
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

theorem normalizedOrthogonalChart_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    (o : OrthonormalBasis (Fin n) ℝ Wᗮ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖normalizedOrthogonalChart W b x‖ ≤
      (1 + (n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖ := by
  apply orthogonalBasisChart_norm_le W (normalizedAxisBasis b) (by positivity)
  exact normalizedAxisBasis_coordinates_bound o b hB hD hb hprod

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_quotient_haar_translated_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : E) {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) A) :
    μ ((fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  have hBm : MeasurableSet ((fun x : E => x - v) '' A) :=
    hAm.image_of_continuousOn_injOn (continuous_id.sub continuous_const).continuousOn
      (fun _ _ _ _ he => sub_left_inj.mp he)
  have hB : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
      ((fun x : E => x - v) '' A) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    exact congrArg (fun z => z - v) (hA hx hy he)
  have hset : ((fun x : E => x - v) '' A) = (fun x => x + v) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, sub_add_cancel] using hy
    · intro hx
      exact ⟨x + v, hx, add_sub_cancel_right x v⟩
  have he := lattice_quotient_haar_image Λ b μ hBm hB
  rw [image_image] at he
  rw [he, hset, measure_preimage_add_right]

theorem lattice_quotient_haar_countable_sheets {T : Type*} [Countable T]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) (A : T → Set E) (hAm : ∀ t, MeasurableSet (A t))
    (hA : ∀ t, InjOn (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) (A t))
    (hdisj : Pairwise (fun s t => Disjoint
      ((fun x => (QuotientAddGroup.mk (x - v s) : E ⧸ Λ.toAddSubgroup)) '' A s)
      ((fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t))) :
    μ (⋃ t, (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t) =
      (∑' t, volume (A t)) / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  rw [measure_iUnion hdisj (fun t => (hAm t).image_of_continuousOn_injOn
    (continuous_quotient_mk'.comp (continuous_id.sub continuous_const)).continuousOn (hA t))]
  simp_rw [lattice_quotient_haar_translated_image Λ b μ _ (hAm _) (hA _)]
  simpa only [div_eq_mul_inv] using ENNReal.tsum_mul_right

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

theorem jointSpaceGeneratorHeight_le_exp (ambient columns rows H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p) (hr : (rows : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    (jointSpaceGeneratorHeight ambient columns rows H R : ℝ) ≤ Real.exp ((p + 2) ^ 120) := by
  have hfirst := imageDefiningHeight_le_exp columns ambient H hp hc ha hH
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have hmax : ((max (imageDefiningHeight columns ambient H) R : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    rw [Nat.cast_max]
    exact max_le hfirst (hR.trans (Real.exp_le_exp.mpr hpp))
  have hsum : ((ambient + rows : ℕ) : ℝ) ≤ (p + 2) ^ 10 := by
    have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ 10 := pow_le_pow_right₀ (by linarith) (by decide)
    push_cast
    nlinarith
  have hsecond := imageDefiningHeight_le_exp (ambient + rows) (ambient + rows)
    (max (imageDefiningHeight columns ambient H) R) (by positivity) hsum hsum hmax
  exact hsecond.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 10))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

theorem affineProbabilityProfile_contDiff (c w : ℝ) :
    ContDiff ℝ ∞ (affineProbabilityProfile c w) := by
  change ContDiff ℝ ∞ (fun x => w⁻¹ * smoothProbabilityProfile ((x-c)/w))
  exact contDiff_const.mul
    (smoothProbabilityProfile_contDiff.comp ((contDiff_id.sub contDiff_const).div_const w))

theorem affineProbabilityProfile_compact (c : ℝ) {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (affineProbabilityProfile c w) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) (|c|+w))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact le_of_not_gt (fun h => hx (affineProbabilityProfile_zero_outside c hw x h))

theorem affineProbabilityProfile_integrable (c : ℝ) {w : ℝ} (hw : 0 < w) :
    Integrable (affineProbabilityProfile c w) :=
  (affineProbabilityProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProbabilityProfile_compact c hw)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_contDiff {I : Type*} [Fintype I] (c w : I → ℝ) :
    ContDiff ℝ ∞ (affineProductProfile c w) := by
  unfold affineProductProfile
  apply contDiff_prod
  intro i _
  exact (affineProbabilityProfile_contDiff (c i) (w i)).comp
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).contDiff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem mixedCoefficientLaw_density {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    mixedCoefficientLaw c w p =
      realDensityMeasure
        ((volume : Measure (I → ℝ)).prod (Measure.pi (fun _ : J => (Measure.count : Measure ℤ))))
        (mixedCoefficientDensity c w p) := by
  have hc : Measure.pi (fun i => affineCoefficientMeasure (c i) (w i)) =
      realDensityMeasure volume (affineProductProfile c w) :=
    independentCoordinateDensity_measure (fun i => affineProbabilityProfile (c i) (w i))
      (fun i => affineProbabilityProfile_integrable (c i) (hw i))
      (fun i => affineProbabilityProfile_nonneg (c i) (hw i))
      (fun i => affineProbabilityProfile_integral (c i) (hw i))
  rw [mixedCoefficientLaw, hc, independentIntegerLaw_density]
  exact binaryDensity_measure _ _ _ _ (affineProductProfile_contDiff c w).continuous.measurable
    (measurable_of_countable _) (affineProductProfile_nonneg c w hw)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoefficientCounting
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem mixedCoefficientLaw_count_density {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    mixedCoefficientLaw c w p =
      realDensityMeasure ((volume : Measure (I → ℝ)).prod (Measure.count : Measure (J → ℤ)))
        (mixedCoefficientDensity c w p) := by
  simpa only [integerCoordinate_count] using mixedCoefficientLaw_density c w hw p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.OrthonormalMixedLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] [Fintype J]

theorem orthonormalMixedChart_measurePreserving (b : OrthonormalBasis I ℝ E) :
    MeasurePreserving (orthonormalMixedChart (J := J) b)
      ((volume : Measure (I → ℝ)).prod Measure.count) (volume.prod Measure.count) :=
  (orthonormalChart_measurePreserving b).prod (MeasurePreserving.id Measure.count)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

theorem translatedQuotientChart_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    μ (translatedQuotientChart Λ v '' S) =
      (volume.prod (Measure.count : Measure T)) S / ENNReal.ofReal (ZLattice.covolume Λ) := by
  rw [translatedQuotientChart_image, Measure.prod_apply_symm hS, lintegral_count]
  apply lattice_quotient_haar_countable_sheets Λ b μ v
  · intro t
    exact hS.preimage (measurable_id.prodMk measurable_const)
  · intro t x hx y hy he
    exact congrArg Prod.fst (hinj hx hy he)
  · intro s t hst
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact hst (congrArg Prod.snd (hinj hx hy he.symm))

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

theorem affineProbabilityProfile_abs_le (c : ℝ) {w x : ℝ} (hw : 0 < w)
    (hx : affineProbabilityProfile c w x ≠ 0) : |x| ≤ |c| + w := by
  have hb := affineProbabilityProfile_support c hw hx
  have ht := abs_add_le (x - c) c
  rw [sub_add_cancel] at ht
  linarith

theorem mixedCoefficient_small_support {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (hcw : ∀ i, |c i| + w i ≤ R) (p : Fin n → PMF ℤ)
    (hp : ∀ i k, k ∈ (p i).support → |(k : ℝ) / basisAxisScale b i| ≤ R)
    (x : (I → ℝ) × (Fin n → ℤ)) (hx : mixedCoefficientDensity c w p x ≠ 0) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  have hs := (mixedCoefficientDensity_support c w p x).mp hx
  exact normalizedMixedPoint_small W b o hC hR hchart hsmall x
    (fun i => (affineProbabilityProfile_abs_le _ (hw i) (hs.1 i)).trans (hcw i))
    (fun i => hp i _ (hs.2 i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

theorem polynomial_degree (S : ResidueBoxSlice N q) (i : I) :
    (S.polynomial i).totalDegree ≤ 1 := by
  dsimp only [polynomial]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, zero_le]
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeFullSliceLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

noncomputable def fullSliceInverseParameters (S : ResidueBoxSlice N q) (i : X) : MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • (MvPolynomial.X i - MvPolynomial.C (S.start i : ℝ))

omit [Fintype X] [DecidableEq X] in
theorem fullSliceInverseParameters_degree (S : ResidueBoxSlice N q) (i : X) :
    S.fullSliceInverseParameters i ∈ weightedSupportLE (fun _ => 1) 1 :=
  (weightedSupportLE _ _).smul_mem _ ((weightedSupportLE _ _).sub_mem
    (weightedSupportLE_X _ _) (weightedSupportLE_C _ _ _))

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem exists_allocatedFourierLogBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → allocatedFourierLogBudget m P ≤ (P+a)^a := by
  let e := coefficientAmbientBudgetExponent m
  let scalar : Polynomial ℕ := 7 * (Polynomial.C (layerTailDegree m+1) * (4 * (Polynomial.X+8)) + 8)
  let common : Polynomial ℕ := Polynomial.X + Polynomial.X * scalar + 1
  let width : Polynomial ℕ := Polynomial.C (m+4) * (Polynomial.X+8)
  let mixed : Polynomial ℕ := (2*Polynomial.X+1)*(width+common)+3*Polynomial.X+1
  let ambient : Polynomial ℕ := Polynomial.X + Polynomial.X*(2*mixed+4*Polynomial.X+9)+1
  let budget : Polynomial ℕ := (Polynomial.X+ambient+Polynomial.C e)^e
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget budget
  refine ⟨a, ha, ?_⟩
  intro P hP
  simpa [budget, ambient, mixed, width, common, scalar, e, allocatedFourierLogBudget,
    allocatedAmbientLog, allocatedMixedLog, allocatedWidthLog, allocatedCommonLog,
    allocatedScalarLog, integerInterpolationLogEnvelope, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedFourierOutputBudget (m : ℕ) (P : ℝ) : ℝ :=
  let Q := allocatedFourierLogBudget m P
  2*Q*(2*Q+2)^4+Q+(2*Q+2)^4

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open BooleanCubeKernel
open scoped BigOperators Classical

variable {K : Type*} {P : K → ℕ} {q r : ℕ}

def composeSlice (S : ResidueBoxSlice P q) (T : ResidueBoxSlice S.length r) :
    ResidueBoxSlice P (q * r) where
  start k := S.start k + q * T.start k
  length := T.length
  inside k j hj := by
    have h := S.inside k _ (T.inside k j hj)
    convert h using 1; ring

theorem composeSlice_point (S : ResidueBoxSlice P q) (T : ResidueBoxSlice S.length r)
    (u : ∀ k, Fin (T.length k)) : (S.composeSlice T).point u = S.point (T.point u) := by
  funext k
  apply Fin.ext
  change S.start k + q * T.start k + (q * r) * (u k).val =
    S.start k + q * (T.start k + r * (u k).val)
  ring

def parameterCell (Q : ∀ k, FiniteProgressionPartition (P k))
    (hstep : ∀ k c, (Q k).step c = r) (c : ∀ k, (Q k).Label) : ResidueBoxSlice P r where
  start k := (Q k).start (c k)
  length k := (Q k).length (c k)
  inside k j hj := by simpa only [hstep] using (Q k).point_lt (c k) hj

theorem stride_mul_length_le_twice (S : ResidueBoxSlice P q) (k : K)
    (hlen : 2 ≤ S.length k) : q * S.length k ≤ 2 * P k := by
  have hlast := S.inside k (S.length k - 1) (by omega)
  have hlen' : S.length k ≤ 2 * (S.length k - 1) := by omega
  have hmul := Nat.mul_le_mul_left q hlen'
  nlinarith

theorem composeSlice_length_lower (S : ResidueBoxSlice P q)
    (T : ResidueBoxSlice S.length r) {cost loss : ℝ}
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hT : ∀ k, (S.length k : ℝ) * Real.exp (-loss) ≤ T.length k) (k : K) :
    Real.exp (-(cost + loss)) * (P k : ℝ) ≤ (S.composeSlice T).length k := by
  calc
    _ = (Real.exp (-cost) * (P k : ℝ)) * Real.exp (-loss) := by
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (S.length k : ℝ) * Real.exp (-loss) :=
      mul_le_mul_of_nonneg_right (hS k) (Real.exp_nonneg _)
    _ ≤ _ := hT k

theorem length_large_of_cost (S : ResidueBoxSlice P q) {cost target : ℝ}
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + target) ≤ (P k : ℝ)) (k : K) :
    Real.exp target ≤ (S.length k : ℝ) := by
  calc
    _ = Real.exp (-cost) * Real.exp (cost + target) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-cost) * (P k : ℝ) :=
      mul_le_mul_of_nonneg_left (hP k) (Real.exp_nonneg _)
    _ ≤ _ := hS k

theorem stride_le_twice_exp_cost (S : ResidueBoxSlice P q) {cost : ℝ}
    (k : K) (hlen : 2 ≤ S.length k)
    (hS : Real.exp (-cost) * (P k : ℝ) ≤ S.length k) :
    (q : ℝ) ≤ 2 * Real.exp cost := by
  have hP : (0 : ℝ) < P k := by
    have h := S.inside k 0 (by omega)
    exact_mod_cast (show 0 < P k by omega)
  have hspan : (q : ℝ) * S.length k ≤ 2 * (P k : ℝ) := by
    exact_mod_cast S.stride_mul_length_le_twice k hlen
  have hmul := (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg q)).trans hspan
  have hq : (q : ℝ) * Real.exp (-cost) ≤ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hq (Real.exp_nonneg cost)
  simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] using h

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def coefficientDeckJetMap (d : ℕ) :
    CoefficientDeckResidues (K := K) B d →+ (∀ j, O j → B j → ZMod d) where
  toFun r j t := ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e
  map_zero' := by
    funext j t i
    simp
  map_add' r s := by
    funext j t
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

end Erdos3.VectorPolynomial

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

def principalAxisRestrict (P : D → Prop) {L : PrincipalTupleIndex B h → ℕ}
    (y : PrincipalIntegerTuples B h α L) : PrincipalAxisTuples (α := α) P L :=
  fun j => y ⟨j.1.val, j.2⟩

def principalAxisJoin (P : D → Prop) [DecidablePred P] {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    PrincipalIntegerTuples B h α L :=
  fun j => if hp : P j.1 then u ⟨⟨j.1, hp⟩, j.2⟩ else v ⟨⟨j.1, hp⟩, j.2⟩

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

def partitionedPrincipalInput (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) :
    SamplerTupleIndex G B h → Option α →
      (Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) ⊕
        PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d)
  | .inl g, a => .inl (.inl (extra g a))
  | .inr ⟨d, b, v⟩, a =>
      if hp : P d then .inl (.inr ⟨⟨d, hp⟩, b, v, a⟩) else .inr ⟨⟨d, hp⟩, b, v, a⟩

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

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def partitionedProfilePrincipal (γ : D → ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (d : {d // ¬P d}) (b : B d.val) : ℝ :=
  3 * γ d.val / 2 + γ d.val / 2 * y (.inr ⟨d.val, principalCoefficientSlot h d.val b⟩)

noncomputable def partitionedProfileConstant (ρ : D → ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (d : {d // ¬P d}) : ℝ :=
  ρ d.val * y (.inr ⟨d.val, constantCoefficientSlot _ _⟩)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
  (sets : ∀ d, O d → Finset α)

noncomputable def partitionedIdealMap
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (Σ d, O d) → ℝ :=
  booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) y) +
    jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
      (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def profileNoiseWithActive {D G Z α : Type*} {B : D → Type*}
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    PartitionedProfileNoiseIndex G Z α B h P → ℝ
  | .inl j => z (.inl j)
  | .inr ⟨d, e⟩ => if hp : P d then z (.inr ⟨d, e⟩) else r ⟨⟨d, hp⟩, e⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoveredRowReindex
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetArrayScale : ℝ :=
  ∏ j, (ZLattice.covolume
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))⁻¹ ^ Fintype.card (O j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastGoodPathMeanNorm
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem forecastBoundedSignalTransfer
    {Sample Term : Type*} [Fintype Sample] [Fintype Term]
    (μ : FiniteProbabilityWeights Sample)
    (target signal : Sample → ℂ) (coefficient : Term → ℂ)
    (atom : Term → Sample → ℂ) {M ε δ B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (happrox : ∀ x, ‖target x - ∑ t, coefficient t * atom t x‖ ≤ δ)
    (hmass : (∑ t, ‖coefficient t‖) ≤ M)
    (hsignal : ∀ x, ‖signal x‖ ≤ B)
    (hatom : ∀ t, ‖μ.complexMean (fun x => signal x * atom t x)‖ ≤ ε) :
    ‖μ.complexMean (fun x => signal x * target x)‖ ≤ M * ε + B * δ := by
  let model := fun x => ∑ t, coefficient t * atom t x
  have hmodel : μ.complexMean (fun x => signal x * model x) =
      ∑ t, coefficient t * μ.complexMean (fun x => signal x * atom t x) := by
    unfold FiniteProbabilityWeights.complexMean
    simp only [model, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hmodelBound : ‖μ.complexMean (fun x => signal x * model x)‖ ≤ M * ε := by
    rw [hmodel]
    calc
      _ ≤ ∑ t, ‖coefficient t * μ.complexMean (fun x => signal x * atom t x)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ t, ‖coefficient t‖ * ε := by
        apply Finset.sum_le_sum
        intro t _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hatom t) (norm_nonneg _)
      _ = (∑ t, ‖coefficient t‖) * ε := (Finset.sum_mul ..).symm
      _ ≤ M * ε := mul_le_mul_of_nonneg_right hmass hε
  have herror : ‖μ.complexMean (fun x => signal x * target x) -
      μ.complexMean (fun x => signal x * model x)‖ ≤ B * δ := by
    apply (μ.norm_complexMean_sub_le _ _ (fun _ => B * δ) ?_).trans_eq (μ.mean_const (B * δ))
    intro x _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hsignal x) (happrox x) (norm_nonneg _) hB
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (μ.complexMean (fun x => signal x * target x))
    (μ.complexMean (fun x => signal x * model x)) 0
  simp only [sub_zero] at htriangle
  exact (htriangle.trans (add_le_add herror hmodelBound)).trans_eq (add_comm (B * δ) (M * ε))

theorem exists_forecast_detecting_atom
    {Sample Term : Type*} [Fintype Sample] [Fintype Term]
    (μ : FiniteProbabilityWeights Sample) (target signal : Sample → ℂ)
    (coefficient : Term → ℂ) (atom : Term → Sample → ℂ)
    {a B M : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hsignal : ∀ x, ‖signal x‖ ≤ B)
    (happrox : ∀ x, ‖target x - ∑ t, coefficient t * atom t x‖ ≤ a / (2 * (B + 1)))
    (hmass : (∑ t, ‖coefficient t‖) ≤ M)
    (hlarge : a ≤ ‖μ.complexMean (fun x => signal x * target x)‖) :
    ∃ t, a / (4 * (M + 1)) ≤ ‖μ.complexMean (fun x => signal x * atom t x)‖ := by
  by_contra! hn
  have hu := forecastBoundedSignalTransfer μ target signal coefficient atom
    (show 0 ≤ a / (4 * (M + 1)) by positivity) hB happrox hmass hsignal
    (fun t => (hn t).le)
  have hm : M * (a / (4 * (M + 1))) ≤ a / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 4 * (M + 1))]
    nlinarith
  have hb : B * (a / (2 * (B + 1))) ≤ a / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * (B + 1))]
    nlinarith
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LieSubalgebraLatticeInnerGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators Matrix TensorProduct

theorem integralVector_mulVec_of_column_denominators
    {ι κ : Type*} [Fintype κ] (B : Matrix ι κ ℚ) (q : ℕ)
    (hB : ∀ j, B.col j ∈ denominatorGrid q) (z : κ → ℤ) :
    IntegralVector (B *ᵥ ((q : ℚ) • (fun j => (z j : ℚ)))) := by
  classical
  choose c hc using hB
  refine ⟨fun i => ∑ j, c j i * z j, fun i => ?_⟩
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  have h : (q : ℚ) * B i j = (c j i : ℚ) := hc j i
  rw [← h]
  ring

theorem scaledIntegerGrid_mulVec_of_column_denominators
    {ι κ : Type*} [Fintype κ] (B : Matrix ι κ ℚ) (l q : ℕ)
    (hB : ∀ j, B.col j ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ B.mulVec ⁻¹' scaledIntegerGrid l := by
  rintro x ⟨z, rfl⟩
  have h := scaled_grid_mulVec B l _ (integralVector_mulVec_of_column_denominators B q hB z)
  simpa only [Set.mem_preimage, smul_smul, Nat.cast_mul] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem gowersNorm_two_fourier (f : G → ℂ) :
    gowersNorm 2 f ^ 4 = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 4 := by
  let C := finiteConvolution f (fun x => star (f (-x)))
  calc
    _ = 𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x‖ ^ 2 := by
      simpa only [gowersNorm_one, Nat.zero_add, show 2 ^ 2 = 4 by norm_num,
        show 2 ^ 1 = 2 by norm_num] using gowersNorm_derivative 0 f
    _ = 𝔼 h, ‖C h‖ ^ 2 := by
      apply Fintype.expect_equiv (Equiv.neg G)
      intro h
      simp only [C, finiteConvolution, Equiv.neg_apply, neg_sub,
        sub_neg_eq_add, multiplicativeDerivative]
    _ = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff C χ‖ ^ 2 := (finiteFourier_parseval C).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      simp only [C, finiteFourierCoeff_convolution, finiteFourierCoeff_reflected_conjugate,
        norm_mul, norm_star]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerProgressionSupport_subset_of_fin (L H step : ℕ) (start : ℤ)
    (hinside : ∀ t : Fin H, 0 ≤ start + (step : ℤ) * t.val ∧
      start + (step : ℤ) * t.val < L) :
    integerProgressionSupport start (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ) :=
  (integerProgressionSupport_subset_iff_fin L H step start).mpr hinside

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_fourierCoeff_le_gowers_two {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (χ : AddChar G ℂ) : ‖finiteFourierCoeff f χ‖ ≤ gowersNorm 2 f := by
  classical
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (gowersNorm_nonneg 1 f)
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [gowersNorm_two_fourier]
  exact Finset.single_le_sum (fun ψ _ => pow_nonneg (norm_nonneg _) 4) (Finset.mem_univ χ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
  (sets : ∀ d, O d → Finset α)

noncomputable def partitionedSlicedRegularizedIdeal
    (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) : ((Σ d, O d) → ℝ) → ℝ :=
  regularizedImageDensity (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
    (fun x => partitionedIdealMap h P sets z (fun i => center i + width i * x i)) ρ

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

noncomputable def activeSlicedProfileIdeal (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) : ((Σ d, O d) → ℝ) → ℝ :=
  partitionedSlicedRegularizedIdeal h P sets ρ center width
    (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumLogBounds
namespace OAI

section

namespace Erdos3

def majorArcErrorLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcBiasLog n p + (n + 1 : ℕ) * majorArcLocalizationLog n p

def majorArcCoverLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (majorArcBiasLog n p + (n + 1 : ℕ) * p) + v + majorArcErrorLog n p + 2

theorem majorArcBaseLogs_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ majorArcBiasLog n p ∧ 0 ≤ majorArcLocalizationLog n p ∧
      0 ≤ majorArcLengthLog n p ∧ 0 ≤ majorArcErrorLog n p := by
  unfold majorArcLengthLog majorArcErrorLog majorArcBiasLog majorArcLocalizationLog
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem majorArcCoverLog_nonneg (n j : ℕ) {p v : ℝ} (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ majorArcCoverLog n j p v := by
  obtain ⟨hb, _, _, he⟩ := majorArcBaseLogs_nonneg n hp
  unfold majorArcCoverLog
  positivity

end Erdos3

end

section

namespace Erdos3

def majorArcSpectrumLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (195 + 4 * majorArcCoverLog n j p v)

def uniformBlockAccuracyLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w : A) : A :=
  1 + majorArcSpectrumLog n j p v + (majorArcSpectrumExponent n j : ℕ) +
    (w + t * ((majorArcLengthExponent n : ℕ) + majorArcLengthLog n p)) + 2

def uniformSpectrumSizeLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w : A) : A :=
  majorArcSpectrumLog n j p v + (w + t * majorArcLengthLog n p) + 1 +
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) : ℕ) *
      uniformBlockAccuracyLog n j t p v w

theorem uniformSpectrumLogs_nonneg (n j t : ℕ) {p v w : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ majorArcSpectrumLog n j p v ∧ 0 ≤ uniformBlockAccuracyLog n j t p v w ∧
      0 ≤ uniformSpectrumSizeLog n j t p v w := by
  have hC := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hS : 0 ≤ majorArcSpectrumLog n j p v := by
    unfold majorArcSpectrumLog
    positivity
  have hA : 0 ≤ uniformBlockAccuracyLog n j t p v w := by
    unfold uniformBlockAccuracyLog
    positivity
  refine ⟨hS, hA, ?_⟩
  unfold uniformSpectrumSizeLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformScaledRetainedLogBounds
namespace OAI

section

namespace Erdos3

def uniformRetainedBiasLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  uniformBlockAccuracyLog n j t p v w + E

def uniformSpectrumCardLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  uniformSpectrumSizeLog n j t p v w +
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) : ℕ) * E

def uniformRetainedFrequencyLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  1 + majorArcCoverLog n j p v + (majorArcCoverExponent n j : ℕ) *
    uniformRetainedBiasLog n j t p v w E

def uniformRetainedDenominatorLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  j * (3 + majorArcCoverLog n j p v) + (majorArcCoverExponent n j * j : ℕ) *
      uniformRetainedBiasLog n j t p v w E +
    (w + t * majorArcLengthLog n p + (majorArcLengthExponent n * t : ℕ) *
      uniformRetainedBiasLog n j t p v w E) + 2

theorem uniformRetainedLogs_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ uniformRetainedBiasLog n j t p v w E ∧
      0 ≤ uniformSpectrumCardLog n j t p v w E ∧
      0 ≤ uniformRetainedFrequencyLog n j t p v w E ∧
      0 ≤ uniformRetainedDenominatorLog n j t p v w E := by
  obtain ⟨_, hA, hS⟩ := uniformSpectrumLogs_nonneg n j t hp hv hw
  have hC := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hB : 0 ≤ uniformRetainedBiasLog n j t p v w E := by
    unfold uniformRetainedBiasLog
    positivity
  refine ⟨hB, ?_, ?_, ?_⟩
  · unfold uniformSpectrumCardLog
    positivity
  · unfold uniformRetainedFrequencyLog
    positivity
  · unfold uniformRetainedDenominatorLog
    positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveRetainedDenominatorLog
namespace OAI

section

namespace Erdos3

def positiveModerateCoverLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  majorArcLengthLog (n + 1) p + 1 + majorArcCoverLog n j p (v + 4) +
    majorArcCoverLog (n + 1) j p v + 1

def positiveModerateSpectrumLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (195 + 4 * positiveModerateCoverLog n j p v)

def positiveModerateAccuracyLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w : A) : A :=
  1 + positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℕ) +
    (w + t * ((positiveModerateLengthExponent n : ℕ) + positiveModerateLengthLog n p)) + 2

theorem positiveModerateLogs_nonneg (n j t : ℕ) {p v w : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ positiveModerateLengthLog n p ∧ 0 ≤ positiveModerateCoverLog n j p v ∧
      0 ≤ positiveModerateSpectrumLog n j p v ∧ 0 ≤ positiveModerateAccuracyLog n j t p v w := by
  have hn := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hn1 := (majorArcBaseLogs_nonneg (n + 1) hp).2.2.1
  have hc := majorArcCoverLog_nonneg n j hp (by positivity : 0 ≤ v + 4)
  have hc1 := majorArcCoverLog_nonneg (n + 1) j hp hv
  have hL : 0 ≤ positiveModerateLengthLog n p := by unfold positiveModerateLengthLog; positivity
  have hC : 0 ≤ positiveModerateCoverLog n j p v := by unfold positiveModerateCoverLog; positivity
  have hS : 0 ≤ positiveModerateSpectrumLog n j p v := by unfold positiveModerateSpectrumLog; positivity
  refine ⟨hL, hC, hS, ?_⟩
  unfold positiveModerateAccuracyLog
  positivity

end Erdos3

end

section

namespace Erdos3

def positiveRetainedBiasLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateAccuracyLog n j t p v w + E

def positiveSpectrumCardLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℕ) *
      positiveRetainedBiasLog n j t p v w E +
    (w + t * positiveModerateLengthLog n p + (positiveModerateLengthExponent n * t : ℕ) *
      positiveRetainedBiasLog n j t p v w E) + 1

def positiveRetainedFrequencyLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateCoverLog n j p v + (positiveModerateCoverExponent n j : ℕ) *
    positiveRetainedBiasLog n j t p v w E + 1

theorem positiveRetainedLogs_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedBiasLog n j t p v w E ∧
      0 ≤ positiveSpectrumCardLog n j t p v w E ∧
      0 ≤ positiveRetainedFrequencyLog n j t p v w E := by
  obtain ⟨hL, hC, hS, hA⟩ := positiveModerateLogs_nonneg n j t hp hv hw
  have hB : 0 ≤ positiveRetainedBiasLog n j t p v w E := by
    unfold positiveRetainedBiasLog
    positivity
  refine ⟨hB, ?_, ?_⟩
  · unfold positiveSpectrumCardLog
    positivity
  · unfold positiveRetainedFrequencyLog
    positivity

end Erdos3

end

section

namespace Erdos3

def positiveRetainedDenominatorLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  j * (positiveRetainedFrequencyLog n j t p v w E + 1) +
    (w + t * positiveModerateLengthLog n p + (positiveModerateLengthExponent n * t : ℕ) *
      positiveRetainedBiasLog n j t p v w E)

def positiveRetainedComplexityLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  positiveSpectrumCardLog n j t p v w E + positiveRetainedFrequencyLog n j t p v w E +
    positiveRetainedDenominatorLog n j t p v w E

theorem positiveRetainedDenominatorLog_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedDenominatorLog n j t p v w E := by
  obtain ⟨hB, _, hF⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hL := (positiveModerateLogs_nonneg n j t hp hv hw).1
  unfold positiveRetainedDenominatorLog
  positivity

theorem positiveRetainedComplexityLog_bounds (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveSpectrumCardLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveRetainedFrequencyLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveRetainedDenominatorLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E := by
  obtain ⟨_, hC, hF⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hD := positiveRetainedDenominatorLog_nonneg n j t hp hv hw hE
  unfold positiveRetainedComplexityLog
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCommonProductRadiusLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      allocatedCommonProductRadiusLog m p g ≤ (p + g + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p g hp hg
  apply (allocatedCommonProductRadiusLog_mono m hp hg (le_add_of_nonneg_right hg)
    (le_add_of_nonneg_left hp)).trans
  simpa [poly, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
    allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hb (p + g) (add_nonneg hp hg)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedFullGridSite
namespace OAI

section

namespace Erdos3
open scoped NNReal

def slicedGridSiteLog {A : Type*} [Semiring A]
    (n d ta ti : ℕ) (D p E : A) : A :=
  positiveRetainedComplexityLog n d ta p p p E +
  uniformSpectrumCardLog n d ti p p p E + uniformRetainedFrequencyLog n d ti p p p E +
  uniformRetainedDenominatorLog n d ti p p p E +
  positiveSpectrumCardLog n d ta p p p 0 + uniformSpectrumSizeLog n d ti p p p +
  (D + 2) * p + E + 2 * D + 20

theorem slicedGridSiteLog_bounds (n d ta ti : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Q := slicedGridSiteLog n d ta ti D p E
    0 ≤ Q ∧ p ≤ Q ∧ E ≤ Q ∧
      positiveRetainedComplexityLog n d ta p p p E + 2 * D + 13 ≤ Q ∧
      uniformSpectrumCardLog n d ti p p p E ≤ Q ∧
      uniformRetainedFrequencyLog n d ti p p p E + 2 * D + 13 ≤ Q ∧
      uniformRetainedDenominatorLog n d ti p p p E ≤ Q ∧
      positiveSpectrumCardLog n d ta p p p 0 + 2 + E ≤ Q ∧
      uniformSpectrumSizeLog n d ti p p p + 2 + E ≤ Q ∧
      D * p ≤ Q ∧ 2 * D + (D + 2) * p + 1 ≤ Q := by
  have ha := (positiveRetainedComplexityLog_bounds n d ta hp hp hp hE).1
  obtain ⟨_, hc, hf, ht⟩ := uniformRetainedLogs_nonneg n d ti hp hp hp hE
  have hca := (positiveRetainedLogs_nonneg n d ta hp hp hp (le_refl (0 : ℝ))).2.1
  have hci := (uniformSpectrumLogs_nonneg n d ti hp hp hp).2.2
  have hDp := mul_nonneg hD hp
  dsimp only
  unfold slicedGridSiteLog
  constructor; · positivity
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor <;> nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

@[gcongr] theorem majorArcBiasLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcBiasLog n p ≤ majorArcBiasLog n p₂ := by
  unfold majorArcBiasLog
  gcongr

@[gcongr] theorem majorArcLengthLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcLengthLog n p ≤ majorArcLengthLog n p₂ := by
  unfold majorArcLengthLog
  gcongr

@[gcongr] theorem majorArcErrorLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcErrorLog n p ≤ majorArcErrorLog n p₂ := by
  unfold majorArcErrorLog
  gcongr

@[gcongr] theorem majorArcCoverLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    majorArcCoverLog n j p v ≤ majorArcCoverLog n j p₂ v₂ := by
  unfold majorArcCoverLog
  gcongr

@[gcongr] theorem positiveModerateLengthLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    positiveModerateLengthLog n p ≤ positiveModerateLengthLog n p₂ := by
  unfold positiveModerateLengthLog
  gcongr

@[gcongr] theorem positiveModerateCoverLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    positiveModerateCoverLog n j p v ≤ positiveModerateCoverLog n j p₂ v₂ := by
  unfold positiveModerateCoverLog
  gcongr

@[gcongr] theorem positiveModerateSpectrumLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    positiveModerateSpectrumLog n j p v ≤ positiveModerateSpectrumLog n j p₂ v₂ := by
  unfold positiveModerateSpectrumLog
  gcongr

@[gcongr] theorem positiveModerateAccuracyLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    positiveModerateAccuracyLog n j t p v w ≤ positiveModerateAccuracyLog n j t p₂ v₂ w₂ := by
  unfold positiveModerateAccuracyLog
  gcongr

@[gcongr] theorem positiveRetainedBiasLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedBiasLog n j t p v w E ≤ positiveRetainedBiasLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedBiasLog
  gcongr

@[gcongr] theorem positiveSpectrumCardLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveSpectrumCardLog n j t p v w E ≤ positiveSpectrumCardLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveSpectrumCardLog
  gcongr

@[gcongr] theorem positiveRetainedFrequencyLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedFrequencyLog n j t p v w E ≤ positiveRetainedFrequencyLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedFrequencyLog
  gcongr

@[gcongr] theorem positiveRetainedDenominatorLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedDenominatorLog n j t p v w E ≤ positiveRetainedDenominatorLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedDenominatorLog
  gcongr

@[gcongr] theorem positiveRetainedComplexityLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedComplexityLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedComplexityLog
  gcongr

@[gcongr] theorem majorArcSpectrumLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    majorArcSpectrumLog n j p v ≤ majorArcSpectrumLog n j p₂ v₂ := by
  unfold majorArcSpectrumLog
  gcongr

@[gcongr] theorem uniformBlockAccuracyLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    uniformBlockAccuracyLog n j t p v w ≤ uniformBlockAccuracyLog n j t p₂ v₂ w₂ := by
  unfold uniformBlockAccuracyLog
  gcongr

@[gcongr] theorem uniformSpectrumSizeLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    uniformSpectrumSizeLog n j t p v w ≤ uniformSpectrumSizeLog n j t p₂ v₂ w₂ := by
  unfold uniformSpectrumSizeLog
  gcongr

@[gcongr] theorem uniformRetainedBiasLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedBiasLog n j t p v w E ≤ uniformRetainedBiasLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedBiasLog
  gcongr

@[gcongr] theorem uniformSpectrumCardLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformSpectrumCardLog n j t p v w E ≤ uniformSpectrumCardLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformSpectrumCardLog
  gcongr

@[gcongr] theorem uniformRetainedFrequencyLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedFrequencyLog n j t p v w E ≤ uniformRetainedFrequencyLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedFrequencyLog
  gcongr

@[gcongr] theorem uniformRetainedDenominatorLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedDenominatorLog n j t p v w E ≤ uniformRetainedDenominatorLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedDenominatorLog
  gcongr

theorem slicedGridSiteLog_mono (n d ta ti : ℕ) {D p E D' p' E' : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (_hE : 0 ≤ E)
    (hDD : D ≤ D') (hpp : p ≤ p') (hEE : E ≤ E') :
    slicedGridSiteLog n d ta ti D p E ≤ slicedGridSiteLog n d ta ti D' p' E' := by
  unfold slicedGridSiteLog
  gcongr
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def allocatedSlicedGridResourceLog {A : Type*} [Semiring A]
    (m dim : ℕ) (D p v E : A) : A :=
  let L := fun (j : Fin m) (e : A) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p e
  let Cp := ∑ j, (L j 0 + D * (v + 1))
  let E' := uniformProductAccuracyLog D Cp E + D * (v + 1) + 1
  ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j E') + (D + 1) * (v + 1))

theorem allocatedSlicedGridResourceLog_nonneg (m dim : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedSlicedGridResourceLog m dim D p v E := by
  unfold allocatedSlicedGridResourceLog
  dsimp only
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · apply siteExponentialOutputLog_nonneg
    apply (slicedGridSiteLog_bounds _ _ _ _ hD hp ?_).1
    apply add_nonneg _ zero_le_one
    apply add_nonneg _ (by positivity)
    apply uniformProductAccuracyLog_nonneg hD _ hE
    exact Finset.sum_nonneg (fun i _ =>
      add_nonneg (slicedGridSiteLog_bounds _ _ _ _ hD hp (le_refl 0)).1 (by positivity))
  · positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientDeckResidueMask
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

def coefficientSamplerChartResidues (q : ℕ)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) E q) :
    CoefficientChartResidues K n E q :=
  fun j e => Sum.elim (fun i => ((x j).2 i e : ZMod q)) (r j e)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedResidueBlockCells
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

theorem exists_affine_normalized_cell_of_width {ι : Type*} {N : ι → ℕ} {q Q : ℕ}
    (A : ResidueBoxSlice N q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) (hQ : 0 < Q)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hwidth : ∀ i, step * q * A.length i ≤ 2 * T i / Q) :
    ∃ z : ι → Fin (Q + 1), ∀ j : ∀ i, Fin (A.length i), ∀ i,
      |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q z i| ≤
        T i * (2 / Q) := by
  classical
  by_cases hlen : ∀ i, 0 < A.length i
  · exact A.exists_affine_normalized_cell hlen origin step hstep T hT hQ hparent hwidth
  · push Not at hlen
    obtain ⟨i, hi⟩ := hlen
    refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, ?_⟩
    intro j
    have hj := (j i).isLt
    omega

end ResidueBoxSlice

theorem normalized_residue_block_cell {ι : Type*} (N : ι → ℕ) (q Q : ℕ)
    (H : ι → ℕ) (hq : 0 < q) (hQ : 0 < Q) (hH : ∀ i, 0 < H i)
    (hwidth : ∀ i, (q : ℝ) * H i ≤ (N i : ℝ) / Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label) :
    ∃ z : ι → Fin (Q + 1),
      ∀ j : ∀ i, Fin ((ResidueBoxSlice.ofBlocks H hq hH a).length i), ∀ i,
      |origin i + step * ((ResidueBoxSlice.ofBlocks H hq hH a).point j i).val -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
  apply ResidueBoxSlice.exists_affine_normalized_cell_of_width _ origin step hstep T hT hQ hparent
  intro i
  have hlen : ((ResidueBoxSlice.ofBlocks H hq hH a).length i : ℝ) ≤ H i := by
    exact_mod_cast truncatedProgressionLength_le (N i) (progressionBlockStart (a i)) q (H i)
  calc
    _ ≤ step * q * H i := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = step * ((q : ℝ) * H i) := by ring
    _ ≤ step * ((N i : ℝ) / Q) := mul_le_mul_of_nonneg_left (hwidth i) hstep
    _ = (step * N i) / Q := by ring
    _ ≤ 2 * T i / Q := div_le_div_of_nonneg_right (hparentwidth i) (Nat.cast_nonneg _)

theorem exists_normalized_residue_block_cells {ι : Type*} (N : ι → ℕ) (q Q : ℕ)
    (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i) :
    ∃ (H : ι → ℕ) (hH : ∀ i, 0 < H i),
      (∀ i, q * H i ≤ N i) ∧
      (∀ i, (q : ℝ) * H i ≤ (N i : ℝ) / Q) ∧
      (∀ i, (N i : ℝ) / (2 * q * Q) ≤ H i) ∧
      ∀ a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label,
        ∃ z : ι → Fin (Q + 1),
          ∀ j : ∀ i, Fin ((ResidueBoxSlice.ofBlocks H hq hH a).length i), ∀ i,
          |origin i + step * ((ResidueBoxSlice.ofBlocks H hq hH a).point j i).val -
            normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hρ : (0 : ℝ) < 1 / Q := by positivity
  have hρ1 : (1 : ℝ) / Q ≤ 1 := (div_le_one hQr).mpr (by exact_mod_cast hQ)
  obtain ⟨H, hH, hfit, hwidth, hlower⟩ := exists_box_block_mesh N q hq hρ hρ1 hlarge
  have hwidth' (i) : (q : ℝ) * H i ≤ (N i : ℝ) / Q := by
    calc
      _ ≤ (1 / (Q : ℝ)) * N i := hwidth i
      _ = _ := by ring
  refine ⟨H, hH, hfit, hwidth', ?_, ?_⟩
  · intro i
    have he : (1 / (Q : ℝ)) * N i / (2 * q) = (N i : ℝ) / (2 * q * Q) := by ring
    rw [← he]
    exact hlower i
  · exact normalized_residue_block_cell N q Q H hq hQ hH hwidth'
      origin step hstep T hT hparent hparentwidth

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeMarkedFreezingSliceScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

theorem exists_long_frozen_box {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i)
    (score W : (∀ i, Fin (N i)) → ℝ) (V : (∀ i, (P i).Label) → (∀ i, Fin (N i)) → ℝ)
    {C τ ε S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hscoreBound : ∀ x, |score x| ≤ 1) (hW : ∀ x, score x * W x ≤ C)
    (hclose : ∀ x, dist (W x) (V (cell P x) x) ≤ ε)
    (hscore : S ≤ 𝔼 x, score x * W x)
    (hbudget : τ + ε + C * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S) :
    ∃ a : ∀ i, (P i).Label, (∀ i, L i ≤ ((P i).length (a i) : ℝ)) ∧
      τ < 𝔼 j : (∀ i, Fin ((P i).length (a i))), score (point P a j) * V a (point P a j) := by
  classical
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  obtain ⟨a, ha, hs⟩ := exists_good_frozen_partition_score (cell P)
    (fun a => ∀ i, L i ≤ ((P i).length (a i) : ℝ)) score W V hC hτ hε hscoreBound hW
    (short_box_side_mass_le P hN L hL) hclose hscore hbudget
  exact ⟨a, ha, by simpa only [expect_cell] using hs⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open BoxProgressionPartition

theorem exists_long_residue_cell_frozen_score
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i)
    (score W : (∀ i, Fin (N i)) → ℝ)
    (V : (ι → ZMod q) → (ι → Fin (Q + 1)) → (∀ i, Fin (N i)) → ℝ)
    {B τ ε θ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hscoreBound : ∀ x, |score x| ≤ 1) (hcap : ∀ x, score x * W x ≤ B)
    (hclose : ∀ r z x, (∀ i, ((x i).val : ZMod q) = r i) →
      (∀ i, |origin i + step * (x i).val - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) →
      dist (W x) (V r z x) ≤ ε)
    (hscore : S ≤ 𝔼 x, score x * W x) (hbudget : τ + ε + B * θ < S) :
    ∃ A : ResidueBoxSlice N q, (∀ i, 0 < A.length i) ∧
      (∀ i, θ * N i / (4 * q * Q * (Fintype.card ι + 1 : ℝ)) ≤ A.length i) ∧
      ∃ r : ι → ZMod q, ∃ z : ι → Fin (Q + 1),
        (∀ j : ∀ i, Fin (A.length i), ∀ i, ((A.point j i).val : ZMod q) = r i) ∧
        (∀ j : ∀ i, Fin (A.length i), ∀ i,
          |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) ∧
        τ < 𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * V r z (A.point j) := by
  classical
  obtain ⟨H, hH, hfit, hwidth, hHlower, hcells⟩ :=
    exists_normalized_residue_block_cells N q Q hq hQ origin step hstep T hT hparent
      hparentwidth hlarge
  let P := fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)
  choose z hz using hcells
  let r := fun a : ∀ i, (P i).Label => fun i => ((P i).start (a i) : ZMod q)
  let Vcell := fun a : ∀ i, (P i).Label => V (r a) (z a)
  let L := fun i => θ * H i / (2 * (Fintype.card ι + 1 : ℝ))
  have hL (i) : 0 < L i :=
    (residueBlock_long_side_budget hθ (hN i) hq hQ (hHlower i) (Fintype.card ι)).2
  have hres (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) (i) :
      ((point P a j i).val : ZMod q) = r a i := by
    rw [point_val]
    change (((P i).start (a i) + q * (j i).val : ℕ) : ZMod q) = _
    simp [r]
  have hcellclose (x : ∀ i, Fin (N i)) : dist (W x) (Vcell (cell P x) x) ≤ ε := by
    let a := cell P x
    let j := fun i => (P i).offset (x i)
    have hid : point P a j = x := by
      funext i
      exact (P i).point_cell_offset (x i)
    apply hclose (r a) (z a) x
    · intro i
      rw [← hid]
      exact hres a j i
    · have hp : (ResidueBoxSlice.ofBlocks H hq hH a).point j = x :=
        (ResidueBoxSlice.ofBlocks_point H hq hH a j).trans hid
      simpa only [hp] using hz a j
  have hshort : (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) ≤ θ :=
    boxBlock_short_side_budget N H q hN hH hfit hθ.le
  have hbudget' : τ + ε + B * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S :=
    by linarith [mul_le_mul_of_nonneg_left hshort hB]
  obtain ⟨a, ha, hs⟩ := exists_long_frozen_box P hN L (fun i => (hL i).le)
    score W Vcell hB hτ hε hscoreBound hcap hcellclose hscore hbudget'
  let A := ResidueBoxSlice.ofBlocks H hq hH a
  have hlength (i) : 0 < A.length i := by
    have hpos : (0 : ℝ) < (P i).length (a i) := (hL i).trans_le (ha i)
    exact_mod_cast hpos
  refine ⟨A, hlength, ?_, r a, z a, ?_, hz a, ?_⟩
  · intro i
    exact (residueBlock_long_side_budget hθ (hN i) hq hQ (hHlower i)
      (Fintype.card ι)).1.trans (ha i)
  · intro j i
    rw [ResidueBoxSlice.ofBlocks_point]
    exact hres a j i
  · simpa only [A, ResidueBoxSlice.ofBlocks_point] using hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateCoveredBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_candidateCoveredParameters_bound (A B R Q : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      candidateCoveredOuterParameter A p ≤ (p + C) ^ C ∧
      candidateCoveredGeometryParameter A B R p ≤ (p + C) ^ C ∧
      candidateCoveredDiagramParameter A B R Q p ≤ (p + C) ^ C ∧
      p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredRightParameter A B p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredDictionaryParameter A B R p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredGeometryParameter A B R p ≤ finiteFreezingRecursiveParameter C p ∧
      candidateCoveredDiagramParameter A B R Q p ≤ finiteFreezingRecursiveParameter C p := by
  let outer : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let right : Polynomial ℕ := (outer + Polynomial.C B) ^ B
  let dict : Polynomial ℕ := (right + Polynomial.C R) ^ R
  let geo : Polynomial ℕ := Polynomial.X + outer + right + dict + 1
  let total : Polynomial ℕ := geo + (geo + Polynomial.C Q) ^ Q + outer
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hgeometry := candidateCoveredGeometryParameter_bounds A B R hp
  have ho : 0 ≤ candidateCoveredOuterParameter A p := by
    unfold candidateCoveredOuterParameter
    positivity
  have hg : 0 ≤ candidateCoveredGeometryParameter A B R p := by linarith [hgeometry.1]
  have hc : 0 ≤ candidateCoveredDiagramParameter A B R Q p := by
    unfold candidateCoveredDiagramParameter
    positivity
  have htotal : candidateCoveredGeometryParameter A B R p +
      candidateCoveredDiagramParameter A B R Q p + candidateCoveredOuterParameter A p ≤
        (p + C) ^ C := by
    simpa [total, geo, dict, right, outer, candidateCoveredGeometryParameter,
      candidateCoveredDiagramParameter, candidateCoveredDictionaryParameter,
      candidateCoveredRightParameter, candidateCoveredOuterParameter,
      Polynomial.eval₂_pow] using hbound p hp
  have hoBound : candidateCoveredOuterParameter A p ≤ (p + C) ^ C := by linarith
  have hgBound : candidateCoveredGeometryParameter A B R p ≤ (p + C) ^ C := by linarith
  have hcBound : candidateCoveredDiagramParameter A B R Q p ≤ (p + C) ^ C := by linarith
  have hrec : (p + C) ^ C ≤ finiteFreezingRecursiveParameter C p := by
    unfold finiteFreezingRecursiveParameter
    have : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
    linarith
  exact ⟨hoBound, hgBound, hcBound, hgeometry.2.1, hgeometry.2.2.2.1,
    hgeometry.2.2.2.2, hgBound.trans hrec, hcBound.trans hrec⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteScheduleGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem exists_canonicalSliceEarlyScale_budget (m s Cdetect : ℕ) (A T : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type*} [Fintype G] {count nX : ℕ}
      {P D p q a target Qstride pRadius : ℝ},
      0 ≤ P → D ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → q ∈ Set.Icc 0 P →
      a ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      pRadius ∈ Set.Icc 0 P → (count : ℝ) ≤ P → (nX : ℝ) ≤ P →
      (Fintype.card G : ℝ) ≤ P →
      let gainLog := slicedDetectionGainLog s Cdetect count p q a
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
      let F := p + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (A : ℝ) (T : ℝ) E F
      let Pscale := pRadius + Ptail
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
      let budget := (P + C) ^ C
      P ≤ budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
      Tmod ∈ Set.Icc 0 budget ∧ Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget := by
  obtain ⟨Adet, _, hdet⟩ := exists_slicedDetection_uniform_budget s Cdetect
  let Ac : ℕ := ⌈(A : ℝ)⌉₊
  let Tc : ℕ := ⌈(T : ℝ)⌉₊
  let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
  let X : Polynomial ℕ := Polynomial.X
  let detPoly := (4 * X + Polynomial.C Adet) ^ Adet
  let errorPoly := X + X * (Polynomial.C (m * 2 ^ (m + 1)) * detPoly) + 5
  let inputPoly := affineProfileInputEnvelope X (Polynomial.C Ac) (Polynomial.C Tc) errorPoly (X + 2)
  let rhoPoly := 2 * inputPoly + 2
  let tailPoly := affineProfileToleranceEnvelope m X (X * (X + 1) + X * X + X + 1)
    (Polynomial.C Ac) (Polynomial.C Tc) errorPoly (X + 2)
  let modPoly := Polynomial.C (m + 1) * detPoly + X * X
  let scalePoly := (X + (X + tailPoly) + rhoPoly + detPoly + X + (X + 2) + modPoly + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (X + detPoly + rhoPoly + tailPoly + modPoly + (X + tailPoly) + scalePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P D p q a target Qstride pRadius hP hD hp hq ha ht hQs hRadius hc hnX hG
    gainLog Pk F Tmod E Prho Ptail Pscale K' scaleLog budget
  let detBound := (4 * P + Adet) ^ Adet
  let errorBound := P + P * ((m * 2 ^ (m + 1) : ℕ) * detBound) + 5
  let inputBound := affineProfileInputEnvelope P (Ac : ℝ) (Tc : ℝ) errorBound (P + 2)
  let rhoBound := 2 * inputBound + 2
  let tailBound := affineProfileToleranceEnvelope m P (P * (P + 1) + P * P + P + 1)
    (Ac : ℝ) (Tc : ℝ) errorBound (P + 2)
  let modBound := ((m + 1 : ℕ) : ℝ) * detBound + P * P
  let scaleBound := (P + (P + tailBound) + rhoBound + detBound + P + (P + 2) + modBound + K) ^ K
  have hD0 := hD.1
  have hp0 := hp.1
  have hq0 := hq.1
  have ha0 := ha.1
  have ht0 := ht.1
  have hQs0 := hQs.1
  have hRadius0 := hRadius.1
  have hgain0 : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect count hp0 hq0 ha0
  have hk0 : 0 ≤ Pk := by dsimp only [Pk]; rw [scalarKernelLogarithmicBudget_eq]; positivity
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hinput0 : 0 ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F :=
    jointAffineSourceEnvelope_nonneg hD0
      (by dsimp [affineProfileCoefficientEnvelope]; positivity) (by positivity) hF0
  have hrho0 : 0 ≤ Prho := by dsimp only [Prho]; positivity
  have htail0 : 0 ≤ Ptail := by dsimp only [Ptail, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]; positivity
  have hmod0 : 0 ≤ Tmod := by dsimp only [Tmod]; positivity
  have hscaleP0 : 0 ≤ Pscale := add_nonneg hRadius0 htail0
  have hscale0 : 0 ≤ scaleLog := by dsimp only [scaleLog]; positivity
  have hdet := hdet (G := G) hP hp0 hq0 ha0 hc hG
  have hdetPow : (P + p + q + a + Adet) ^ Adet ≤ detBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hp.2, hq.2, ha.2]
  have hgain : gainLog ≤ detBound := hdet.1.trans hdetPow
  have hk : Pk ≤ detBound := hdet.2.trans hdetPow
  have hAc : (A : ℝ) ≤ Ac := Nat.le_ceil _
  have hTc : (T : ℝ) ≤ Tc := Nat.le_ceil _
  have hdet0 : 0 ≤ detBound := by dsimp only [detBound]; positivity
  have herror0 : 0 ≤ errorBound := by dsimp only [errorBound]; positivity
  have hinputBound0 : 0 ≤ inputBound := jointAffineSourceEnvelope_nonneg hP
    (by dsimp [affineProfileCoefficientEnvelope]; positivity) (by positivity) (by positivity)
  have hrhoBound0 : 0 ≤ rhoBound := by dsimp only [rhoBound]; positivity
  have htailBound0 : 0 ≤ tailBound := by dsimp only [tailBound, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]; positivity
  have hmodBound0 : 0 ≤ modBound := by dsimp only [modBound]; positivity
  have hscaleBound0 : 0 ≤ scaleBound := by dsimp only [scaleBound]; positivity
  have hE : E ≤ errorBound := by dsimp only [E, errorBound]; gcongr; exact ht.2; exact hD.2
  have hF : F ≤ P + 2 := by dsimp only [F]; linarith only [hp.2]
  have hinput : affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F ≤ inputBound :=
    canonical_profileInput_mono hD0 A.coe_nonneg T.coe_nonneg hE0 hF0 hD.2 hAc hTc hE hF
  have hrho : Prho ≤ rhoBound := by dsimp only [Prho, rhoBound]; gcongr
  have htail : Ptail ≤ tailBound := by
    dsimp only [Ptail, tailBound, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]
    gcongr
    all_goals first | exact hinput | exact hD.2
  have hmod : Tmod ≤ modBound := by dsimp only [Tmod, modBound]; gcongr; exact hQs.2
  have hscaleP : Pscale ≤ P + tailBound := add_le_add hRadius.2 htail
  have hscale : scaleLog ≤ scaleBound := by
    dsimp only [scaleLog, scaleBound]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    all_goals first | exact hD.2 | exact ht.2
  have hsum : P + detBound + rhoBound + tailBound + modBound + (P + tailBound) + scaleBound ≤ budget := by
    simpa [X, detPoly, errorPoly, inputPoly, rhoPoly, tailPoly, modPoly, scalePoly,
      detBound, errorBound, inputBound, rhoBound, tailBound, modBound, scaleBound,
      affineProfileInputEnvelope, affineProfileCoefficientEnvelope, affineProfileToleranceEnvelope,
      jointAffineSourceEnvelope, jointAffineInverseEnvelope, jointAffineDerivativeEnvelope,
      jointAffineWeightEnvelope, affineInverseAxisEnvelope, affineDerivativeAxisEnvelope,
      affineWeightAxisEnvelope, affineMinorLogEnvelope, affineMinorVariableEnvelope,
      affineMinorDegreeEnvelope, affineMinorConstantEnvelope, Polynomial.eval₂_pow] using hbound P hP
  refine ⟨?_, ⟨hgain0, ?_⟩, ⟨hk0, ?_⟩, ⟨hrho0, ?_⟩, ⟨htail0, ?_⟩,
    ⟨hmod0, ?_⟩, ⟨hscaleP0, ?_⟩, ⟨hscale0, ?_⟩⟩ <;>
    linarith only [hsum, hP, hgain, hk, hrho, htail, hmod, hscaleP, hscale,
      hdet0, hrhoBound0, htailBound0, hmodBound0, hscaleBound0]

theorem exists_primitiveCanonicalSliceEarlyScale_budget (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type*} [Fintype G] {count nX : ℕ}
      {P pnum p q a target Qstride pRadius : ℝ},
      0 ≤ P → pnum ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → q ∈ Set.Icc 0 P →
      a ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      pRadius ∈ Set.Icc 0 P → (count : ℝ) ≤ P → (nX : ℝ) ≤ P →
      (Fintype.card G : ℝ) ≤ P →
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect count p q a
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
      let F := p + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let Pscale := pRadius + Ptail
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
      let budget := (P + C) ^ C
      P ≤ budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
      Tmod ∈ Set.Icc 0 budget ∧ Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget := by
  obtain ⟨Aearly, _, hearly⟩ := exists_canonicalSliceEarlyScale_budget m s Cdetect
    canonicalSublevelCutoffLip canonicalTransitionLip
  let X : Polynomial ℕ := Polynomial.X
  let poly := (allocatedComparisonDimension m X + Polynomial.C Aearly) ^ Aearly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P pnum p q a target Qstride pRadius hP hnum hp hq ha ht hQs hRadius hc hnX hG
    D gainLog Pk F Tmod E Prho Ptail Pscale K scaleLog budget
  let R := allocatedComparisonDimension m P
  have hR0 : 0 ≤ R := (allocatedComparisonDimension_bounds m hP).1
  have hPR : P ≤ R := (allocatedComparisonDimension_bounds m hP).2.2.1
  have hnum0 := hnum.1
  have hD0 : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum0).1
  have hDR : D ≤ R := by
    dsimp only [D, R, allocatedComparisonDimension]
    gcongr <;> exact hnum.2
  have hlift {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 R :=
    ⟨hx.1, hx.2.trans hPR⟩
  have hbudget : (R + Aearly) ^ Aearly ≤ budget := by
    simpa [poly, X, R, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound P hP
  obtain ⟨hbase, hgain, hk, hrho, htail, hmod, hscaleP, hscale⟩ :=
    hearly (G := G) hR0 ⟨hD0, hDR⟩ (hlift hp) (hlift hq) (hlift ha) (hlift ht)
      (hlift hQs) (hlift hRadius) (hc.trans hPR) (hnX.trans hPR) (hG.trans hPR)
  have hbudgetLift {x : ℝ} (hx : x ∈ Set.Icc 0 ((R + Aearly) ^ Aearly)) :
      x ∈ Set.Icc 0 budget := ⟨hx.1, hx.2.trans hbudget⟩
  exact ⟨hPR.trans (hbase.trans hbudget), ⟨hD0, hDR.trans (hbase.trans hbudget)⟩,
    hbudgetLift hgain, hbudgetLift hk, hbudgetLift hrho, hbudgetLift htail,
    hbudgetLift hmod, hbudgetLift hscaleP, hbudgetLift hscale⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleEarlyBudget
    (m nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
      {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Qstride : ℝ}
      (pDetect aDetect target : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      (∀ k, pDetect k ∈ Set.Icc 0 P) → (∀ k, aDetect k ∈ Set.Icc 0 P) →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : K =>
        slicedDetectionGainLog (degree s) (Cdetect s) count (pDetect s) (pDetect s) (aDetect s)
      let Pk := fun s : K =>
        scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
      let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : K => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
      let Ptail := fun s : K => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget := by
  let Index := Fin (m + 1) × Fin (Cmax + 1)
  let Cs := fun i : Index => Classical.choose
    (exists_primitiveCanonicalSliceEarlyScale_budget m i.1.val i.2.val)
  obtain ⟨A, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := X + (2 * X + Polynomial.C A) ^ A +
    ∑ s : Index, (X + Polynomial.C (Cs s)) ^ (Cs s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro K _ degree Cdetect G _ count nX P Bstruct pnum Qstride pDetect aDetect target
    _hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG
    pRadius D gainLog Pk Tmod E Prho Ptail budget
  let piece := fun s : Index => (P + Cs s) ^ Cs s
  have hpiece (s) : 0 ≤ piece s := by dsimp only [piece]; positivity
  have hradiusBound : 0 ≤ (2 * P + A) ^ A := by positivity
  have hsum0 : 0 ≤ ∑ s, piece s := Finset.sum_nonneg (fun s _ => hpiece s)
  have htotal : P + (2 * P + A) ^ A + ∑ s, piece s ≤ budget := by
    simpa [poly, X, piece, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum] using hbound P hP
  have hbase : P ≤ budget := by linarith only [htotal, hradiusBound, hsum0]
  have hradiusCap : (2 * P + A) ^ A ≤ budget := by linarith only [htotal, hP, hsum0]
  have hpieceCap (s) : piece s ≤ budget := by
    have hi : piece s ≤ ∑ i, piece i :=
      Finset.single_le_sum (fun i _ => hpiece i) (Finset.mem_univ s)
    linarith only [htotal, hi, hP, hradiusBound]
  have hradius : pRadius ∈ Set.Icc 0 budget := by
    refine ⟨(allocatedCommonProductRadius_bounds m hB.1 hB.1).1, ?_⟩
    apply (hRadius hB.1 hB.1).trans
    apply le_trans _ hradiusCap
    exact pow_le_pow_left₀ (by linarith only [hB.1, (show (0 : ℝ) ≤ A from Nat.cast_nonneg A)]) (by linarith only [hB.2]) A
  let index : K → Index := fun s =>
    (⟨degree s, Nat.lt_succ_of_le (hdegree s)⟩,
      ⟨Cdetect s, Nat.lt_succ_of_le (hCdetect s)⟩)
  have hdata (s : K) :
      D ∈ Set.Icc 0 budget ∧ gainLog s ∈ Set.Icc 0 budget ∧
      Pk s ∈ Set.Icc 0 budget ∧ Prho s ∈ Set.Icc 0 budget ∧
      Ptail s ∈ Set.Icc 0 budget ∧ Tmod s ∈ Set.Icc 0 budget := by
    obtain ⟨_, hD, hg, hk, hρ, ht, hmod, _, _⟩ :=
      (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget
        m (degree s) (Cdetect s))).2
        (G := G) hP hnum (hp s) (hp s) (ha s) (htarget s) hQ
        (show (0 : ℝ) ∈ Set.Icc 0 P from ⟨le_rfl, hP⟩) hcount hnX hG
    have lift {x : ℝ} (hx : x ∈ Set.Icc 0 (piece (index s))) : x ∈ Set.Icc 0 budget :=
      ⟨hx.1, hx.2.trans (hpieceCap (index s))⟩
    exact ⟨lift hD, lift hg, lift hk, lift hρ, lift ht, lift hmod⟩
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨_, hD, _⟩ :=
    (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget m 0 0)).2
      (G := G) hP hnum hzero hzero hzero hzero hQ hzero hcount hnX hG
  have hDCap : D ∈ Set.Icc 0 budget :=
    ⟨hD.1, hD.2.trans (hpieceCap (⟨0, Nat.succ_pos m⟩, ⟨0, Nat.succ_pos Cmax⟩))⟩
  exact ⟨hbase, hradius, hDCap, fun s => (hdata s).2⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_allocatedCanonicalProjection_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P coverLog : ℝ, 0 ≤ P → 0 ≤ coverLog →
      allocatedCanonicalProjectionLog m dim P coverLog ≤ (P + coverLog + A) ^ A := by
  obtain ⟨a, ha, hfourier⟩ := exists_allocatedFourierLogBudget_bound m
  let polynomial : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X +
      Polynomial.C (canonicalProjectionRowCost m dim)
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget polynomial
  refine ⟨A, hA, ?_⟩
  intro P coverLog hP hcoverLog
  have hpow : (P + a) ^ a ≤ (P + coverLog + a) ^ a := by
    gcongr
    linarith only [hcoverLog]
  have hpoly := hbound (P + coverLog) (add_nonneg hP hcoverLog)
  have hle : allocatedCanonicalProjectionLog m dim P coverLog ≤
      (P + coverLog + a) ^ a + (P + coverLog) + canonicalProjectionRowCost m dim := by
    unfold allocatedCanonicalProjectionLog
    linarith only [hfourier P hP, hpow, hP]
  apply hle.trans
  simpa [polynomial, Polynomial.eval₂_pow] using hpoly

theorem exists_allocatedCanonicalProjection_composed_budget (m dim Acover : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      let coverLog := (P + (dim + 2 : ℕ) + Acover) ^ Acover
      let Aproj := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
      coverLog ≤ (P + C) ^ C ∧
        (P + coverLog + Aproj) ^ Aproj ≤ (P + C) ^ C := by
  let Aproj := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
  let coverPolynomial : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (dim + 2) + Polynomial.C Acover) ^ Acover
  let densityPolynomial : Polynomial ℕ :=
    (Polynomial.X + coverPolynomial + Polynomial.C Aproj) ^ Aproj
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (coverPolynomial + densityPolynomial)
  refine ⟨C, hC, ?_⟩
  intro P hP coverLog Aprojection
  have hsum : coverLog + (P + coverLog + Aprojection) ^ Aprojection ≤ (P + C) ^ C := by
    simpa [coverPolynomial, densityPolynomial, Polynomial.eval₂_pow, coverLog,
      Aprojection, Aproj] using hbound P hP
  have hcover : 0 ≤ coverLog := by dsimp [coverLog]; positivity
  have hdensity : 0 ≤ (P + coverLog + Aprojection) ^ Aprojection := by positivity
  exact ⟨(le_add_of_nonneg_right hdensity).trans hsum,
    (le_add_of_nonneg_left hcover).trans hsum⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreePrecisionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreeEarlyBudget
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum pDetect aDetect Qstride : ℝ}
      (target : Fin (m + 1) → ℝ),
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : Fin (m + 1) =>
        slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect aDetect
      let Pk := fun s : Fin (m + 1) =>
        scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
      let Tmod := fun s : Fin (m + 1) => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : Fin (m + 1) => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : Fin (m + 1) => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2) + 2
      let Ptail := fun s : Fin (m + 1) => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget := by
  let Cs := fun s : Fin (m + 1) =>
    Classical.choose (exists_primitiveCanonicalSliceEarlyScale_budget m s.val (Cdetect s))
  obtain ⟨A, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := X + (2 * X + Polynomial.C A) ^ A +
    ∑ s : Fin (m + 1), (X + Polynomial.C (Cs s)) ^ (Cs s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P Bstruct pnum pDetect aDetect Qstride target
    hP hB hnum hp ha hQ htarget hcount hnX hG
    pRadius D gainLog Pk Tmod E Prho Ptail budget
  let piece := fun s : Fin (m + 1) => (P + Cs s) ^ Cs s
  have hpiece (s) : 0 ≤ piece s := by dsimp only [piece]; positivity
  have hradiusBound : 0 ≤ (2 * P + A) ^ A := by positivity
  have hsum0 : 0 ≤ ∑ s, piece s := Finset.sum_nonneg (fun s _ => hpiece s)
  have htotal : P + (2 * P + A) ^ A + ∑ s, piece s ≤ budget := by
    simpa [poly, X, piece, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum] using hbound P hP
  have hbase : P ≤ budget := by linarith only [htotal, hradiusBound, hsum0]
  have hradiusCap : (2 * P + A) ^ A ≤ budget := by linarith only [htotal, hP, hsum0]
  have hpieceCap (s) : piece s ≤ budget := by
    have hi : piece s ≤ ∑ i, piece i :=
      Finset.single_le_sum (fun i _ => hpiece i) (Finset.mem_univ s)
    linarith only [htotal, hi, hP, hradiusBound]
  have hradius : pRadius ∈ Set.Icc 0 budget := by
    refine ⟨(allocatedCommonProductRadius_bounds m hB.1 hB.1).1, ?_⟩
    apply (hRadius hB.1 hB.1).trans
    apply le_trans _ hradiusCap
    exact pow_le_pow_left₀ (by linarith only [hB.1, (show (0 : ℝ) ≤ A from Nat.cast_nonneg A)]) (by linarith only [hB.2]) A
  have hdata (s : Fin (m + 1)) :
      D ∈ Set.Icc 0 budget ∧ gainLog s ∈ Set.Icc 0 budget ∧
      Pk s ∈ Set.Icc 0 budget ∧ Prho s ∈ Set.Icc 0 budget ∧
      Ptail s ∈ Set.Icc 0 budget ∧ Tmod s ∈ Set.Icc 0 budget := by
    obtain ⟨_, hD, hg, hk, hρ, ht, hmod, _, _⟩ :=
      (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget m s.val (Cdetect s))).2
        (G := G) hP hnum hp hp ha (htarget s) hQ
        (show (0 : ℝ) ∈ Set.Icc 0 P from ⟨le_rfl, hP⟩) hcount hnX hG
    have lift {x : ℝ} (hx : x ∈ Set.Icc 0 (piece s)) : x ∈ Set.Icc 0 budget :=
      ⟨hx.1, hx.2.trans (hpieceCap s)⟩
    exact ⟨lift hD, lift hg, lift hk, lift hρ, lift ht, lift hmod⟩
  exact ⟨hbase, hradius, (hdata ⟨0, Nat.succ_pos m⟩).1, fun s => (hdata s).2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreePrecisionBudget
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P pDetect aDetect Qstride : ℝ},
      0 ≤ P → pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let gainLog := fun s : Fin (m + 1) =>
        slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect aDetect
      let Pk := fun s : Fin (m + 1) =>
        scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
      let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ s, Pk s
      let target := fun s : Fin (m + 1) =>
        gainLog s + 40 + coefficientErrorSpatialLog Pphysical
      let budget := (P + C) ^ C
      P ≤ budget ∧ Pphysical ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          target s ∈ Set.Icc 0 budget := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedUniformDegreeEarlyBudget m Cdetect
  let X : Polynomial ℕ := Polynomial.X
  let earlyPoly := (X + Polynomial.C A) ^ A
  let physicalPoly := Polynomial.C (m + 2) + 3 * X + Polynomial.C (m + 1) * earlyPoly
  let precisionPoly := earlyPoly + 40 + coefficientErrorSpatialLog physicalPoly
  obtain ⟨C, hC, hBound⟩ :=
    exists_natPolynomial_eval_budget (earlyPoly + physicalPoly + precisionPoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P pDetect aDetect Qstride hP hp ha hQ hcount hnX hG
    gainLog Pk Pphysical target budget
  let early := (P + A) ^ A
  let physical : ℝ := ((m + 2 : ℕ) : ℝ) + 3 * P + ((m + 1 : ℕ) : ℝ) * early
  let precision := early + 40 + coefficientErrorSpatialLog physical
  have hearly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hphysical0 : 0 ≤ physical := by dsimp only [physical]; positivity
  have hprecision0 : 0 ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysical0
    dsimp only [precision]
    positivity
  have htotal : early + physical + precision ≤ budget := by
    simpa [X, earlyPoly, physicalPoly, precisionPoly, early, physical, precision,
      coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
      Polynomial.eval₂_pow] using hBound P hP
  have hearlyCap : early ≤ budget := by linarith only [htotal, hphysical0, hprecision0]
  have hphysicalCap : physical ≤ budget := by linarith only [htotal, hearly0, hprecision0]
  have hprecisionCap : precision ≤ budget := by linarith only [htotal, hearly0, hphysical0]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨hPEarly, _, _, hDegrees⟩ :=
    hEarly (G := G) (fun _ => 0) hP hzero hzero hp ha hQ
      (fun _ => hzero) hcount hnX hG
  have hg (s) : gainLog s ∈ Set.Icc 0 early := (hDegrees s).1
  have hk (s) : Pk s ∈ Set.Icc 0 early := (hDegrees s).2.1
  have hsum0 : 0 ≤ ∑ s, Pk s := Finset.sum_nonneg (fun s _ => (hk s).1)
  have hsum : ∑ s, Pk s ≤ ((m + 1 : ℕ) : ℝ) * early := by
    calc
      _ ≤ ∑ _s : Fin (m + 1), early := Finset.sum_le_sum (fun s _ => (hk s).2)
      _ = _ := by simp
  have hactual0 : 0 ≤ Pphysical := by
    have hstride0 := hQ.1
    dsimp only [Pphysical]
    positivity
  have hactual : Pphysical ≤ physical := by
    dsimp only [Pphysical, physical]
    linarith only [hcount, hnX, hQ.2, hsum]
  have hspatial : coefficientErrorSpatialLog Pphysical ≤ coefficientErrorSpatialLog physical := by
    unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  refine ⟨hPEarly.trans hearlyCap, ⟨hactual0, hactual.trans hphysicalCap⟩, ?_⟩
  intro s
  refine ⟨⟨(hg s).1, (hg s).2.trans hearlyCap⟩,
    ⟨(hk s).1, (hk s).2.trans hearlyCap⟩, ?_⟩
  constructor
  · have := (hg s).1
    have := coefficientErrorSpatialLog_nonneg hactual0
    dsimp only [target]
    positivity
  · apply le_trans _ hprecisionCap
    dsimp only [target, precision]
    linarith only [(hg s).2, hspatial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardActualNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleLocalPrecisionBudget
    (m Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ (degree : ℕ), degree ≤ m →
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P pDetect aDetect Qstride : ℝ},
      0 ≤ P → pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let budget := (P + C) ^ C
      P ≤ budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
        Pphysical ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hUniform⟩ :=
    exists_preparedUniformDegreePrecisionBudget m (fun _ => Cdetect)
  refine ⟨C, hC, ?_⟩
  intro degree hdegree G _ count nX P pDetect aDetect Qstride
    hP hp ha hQ hcount hnX hG gainLog Pk Pphysical target budget
  let s : Fin (m + 1) := ⟨degree, Nat.lt_succ_of_le hdegree⟩
  let allGain := fun t : Fin (m + 1) =>
    slicedDetectionGainLog t.val Cdetect count pDetect pDetect aDetect
  let allKernel := fun t : Fin (m + 1) =>
    scalarKernelLogarithmicBudget (Fin (t.val + 1)) G (allGain t + pDetect + 4)
  let allPhysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ t, allKernel t
  have hAll := hUniform (G := G) hP hp ha hQ hcount hnX hG
  change P ≤ budget ∧ allPhysical ∈ Set.Icc 0 budget ∧
    ∀ t, allGain t ∈ Set.Icc 0 budget ∧ allKernel t ∈ Set.Icc 0 budget ∧
      allGain t + 40 + coefficientErrorSpatialLog allPhysical ∈ Set.Icc 0 budget at hAll
  have hgain : gainLog ∈ Set.Icc 0 budget := (hAll.2.2 s).1
  have hkernel : Pk ∈ Set.Icc 0 budget := (hAll.2.2 s).2.1
  have hsingle : allKernel s ≤ ∑ t, allKernel t :=
    Finset.single_le_sum (fun t _ => (hAll.2.2 t).2.1.1) (Finset.mem_univ s)
  have hphysical0 : 0 ≤ Pphysical := by
    have hkernel0 := hkernel.1
    have hstride0 := hQ.1
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    positivity
  have hphysical : Pphysical ≤ allPhysical := by
    change ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + allKernel s ≤
      ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ t, allKernel t
    exact add_le_add le_rfl hsingle
  have hspatial : coefficientErrorSpatialLog Pphysical ≤
      coefficientErrorSpatialLog allPhysical := by
    have hallPhysical0 := hAll.2.1.1
    unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  refine ⟨hAll.1, hgain, hkernel, ⟨hphysical0, hphysical.trans hAll.2.1.2⟩, ?_⟩
  constructor
  · have hgain0 := hgain.1
    have hspatial0 := coefficientErrorSpatialLog_nonneg hphysical0
    dsimp only [target]
    positivity
  · apply le_trans _ (hAll.2.2 s).2.2.2
    change gainLog + 40 + coefficientErrorSpatialLog Pphysical ≤
      gainLog + 40 + coefficientErrorSpatialLog allPhysical
    exact add_le_add le_rfl hspatial

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X Y : Type*} {N : X → ℕ} {q : ℕ}

def coordinateReturn (e : X ≃ Y) (S : ResidueBoxSlice (coordinateReindexedSides e N) q) :
    ResidueBoxSlice N q where
  start i := S.start (e i)
  length i := S.length (e i)
  inside i j hj := by
    simpa only [coordinateReindexedSides, Equiv.symm_apply_apply] using S.inside (e i) j hj

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def ResiduePrimeCoordinateStable {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y) →
    ‖residuePrimeCoordinateMean f lo N M a q I x -
      residuePrimeCoordinateMean f lo N M a q (I ∪ J) y‖ ≤ δ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedLinearMapChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => ∑ a : J j,
      (P j (Pi.single a 1) i) • MvPolynomial.X (Sum.inr ⟨j, a⟩)

noncomputable def fullTaggedAffineMapChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => C (c j i - P j (c j) i) +
      fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩)

theorem fullTaggedLinearMapChart_eval_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (x : X ⊕ (Σ j, J j) → ℝ)
    (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩)) =
      P j (fun a => x (Sum.inr ⟨j, a⟩)) i := by
  have hsum : ∑ a : J j, x (Sum.inr ⟨j, a⟩) • Pi.single a (1 : ℝ) =
      (fun a => x (Sum.inr ⟨j, a⟩)) := by
    ext a
    simp [Pi.smul_apply, Pi.single_apply]
  rw [fullTaggedLinearMapChart]
  simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, eval_X]
  rw [← hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem fullTaggedAffineMapChart_eval_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ) (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedAffineMapChart J P c (Sum.inr ⟨j, i⟩)) =
      c j i + P j ((fun a => x (Sum.inr ⟨j, a⟩)) - c j) i := by
  rw [fullTaggedAffineMapChart, map_add, eval_C, fullTaggedLinearMapChart_eval_tag,
    map_sub, Pi.sub_apply]
  ring

theorem fullTaggedAffineMapChart_eval_eq
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j y, y ∈ U j → P j y = y)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, (fun a => x (Sum.inr ⟨j, a⟩)) - c j ∈ U j) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  funext v
  cases v with
  | inl a => exact MvPolynomial.eval_X _
  | inr v =>
    rw [fullTaggedAffineMapChart_eval_tag, hP _ _ (hx _), Pi.sub_apply]
    ring

theorem fullTaggedAffineMapChart_eval_eq_of_quotient
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j y, y ∈ U j → P j y = y)
    {D : Fin m → Type*} [∀ j, AddCommGroup (D j)] [∀ j, Module ℝ (D j)]
    (Q : ∀ j, (J j → ℝ) →ₗ[ℝ] D j) (hQ : ∀ j, LinearMap.ker (Q j) = U j)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, Q j (fun a => x (Sum.inr ⟨j, a⟩)) = Q j (c j)) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  apply fullTaggedAffineMapChart_eval_eq J P c U hP x
  intro j
  rw [← hQ j, LinearMap.mem_ker, map_sub, hx j, sub_self]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FullTaggedAffineComplementAgreement
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedAffineMapChart_eval_eq_of_complement
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hvalue : ∀ j, ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (fun a => x (Sum.inr ⟨j, a⟩)) = c j)
    (hconstant : ∀ j, ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  have hfixed : ∀ j y, y ∈ LinearMap.ker
      ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) → P j y = y := by
    intro j y hy
    change y - P j y = 0 at hy
    exact (sub_eq_zero.mp hy).symm
  apply fullTaggedAffineMapChart_eval_eq_of_quotient J P c
    (fun j => LinearMap.ker ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j)) hfixed
    (fun j => (LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (fun _ => rfl) x
  intro j
  rw [hvalue j, hconstant j]

theorem fullTaggedAffineMatrixChart_eval_eq_of_complement
    (P : ∀ j, Matrix (J j) (J j) ℚ) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hvalue : ∀ j, rationalTagProjectionComplement (P j)
      (fun a => x (Sum.inr ⟨j, a⟩)) = c j)
    (hconstant : ∀ j, rationalTagProjectionComplement (P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v)) = x := by
  exact fullTaggedAffineMapChart_eval_eq_of_complement J
    (fullTaggedRealMatrixProjection J P) c x hvalue hconstant

theorem fullTaggedAffineMatrixChart_eval_eq_of_anchor
    (P : ∀ j, Matrix (J j) (J j) ℚ) (c anchor : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hdisplacement : ∀ j, rationalTagProjectionComplement (P j)
      ((fun a => x (Sum.inr ⟨j, a⟩)) - anchor j) = 0)
    (hanchor : ∀ j, rationalTagProjectionComplement (P j) (anchor j) = c j)
    (hconstant : ∀ j, rationalTagProjectionComplement (P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v)) = x := by
  apply fullTaggedAffineMatrixChart_eval_eq_of_complement J P c x ?_ hconstant
  intro j
  have h := hdisplacement j
  rw [map_sub, sub_eq_zero, hanchor j] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
end


