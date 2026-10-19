-- Prove2me | Definitions.Def_OAIE3v2B060
-- name    : OAIE3v2B060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:14:46.188078+00:00
-- url     : https://prove2.me/theorems/af32204d-8c73-4088-992f-66c95bbc3587
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 61 of 311
-- statement:
--   Definitions bundle 61 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B006`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013`, `OAIE3v2B015`, `OAIE3v2B018`, `OAIE3v2B021`, `OAIE3v2B028`, `OAIE3v2B029`, `OAIE3v2B030` of this split.
--
--   Modules: `Dynamics/AllocatedMarkedCoveredLowerDiagramBudget.lean`, `Dynamics/ImageCoverBudget.lean`, `Dynamics/LieSubalgebraRepresentativeBudget.lean`, `Dynamics/ProjectedAxisBudgets.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AuxiliaryIntervalCells.lean`, `Estimates/BoundedCoefficientEvaluation.lean`, `Estimates/CommonIntegralModelEquivalences.lean`, `Estimates/ConstantObservableMemberNets.lean`, `Estimates/CopiedLayerSpace.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/McShaneEnvelope.lean`, `Estimates/PinnedSectionMeans.lean`, `Estimates/PositiveReconstruction.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/FrequencyProjectionBudget.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Geometry/CommonStrideCoordinates.lean`, `Geometry/QuantitativeProjectedChart.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Lattices/BoxResiduePartition.lean`, `Lattices/EuclideanShortLatticeBasis.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/BasisAxisNormalization.lean`, `Linear/NativeChartKernel.lean`, `Linear/OrthogonalBasisChart.lean`, `Linear/PreparedDeterminingMatrixBudget.lean`, `Linear/RankPreparationProjectedAxisBudget.lean`, `Model.lean`, `Polynomial/LowestPolynomialLayer.lean`, `Polynomial/PolynomialKernelValues.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Probability/PairedProductDensity.lean`, `Sampling/NormalizedRealBoxHalfGrid.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B021
import Definitions.Def_OAIE3v2B028
import Definitions.Def_OAIE3v2B029
import Definitions.Def_OAIE3v2B030

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedMarkedCoveredLowerDiagramBudget
namespace OAI

section

namespace Erdos3

theorem exists_allocatedMarkedCoveredLowerDiagramBudget (A B T : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 1 ≤ p →
      let nativeCost := (p + A) ^ A
      let inputCost := p + nativeCost
      let recoveryCost := (inputCost + B) ^ B
      let lowerInput := inputCost + recoveryCost
      let finalLower := (lowerInput + T) ^ T
      1 ≤ inputCost ∧ p ≤ inputCost ∧ nativeCost ≤ inputCost ∧
        inputCost ≤ lowerInput ∧ recoveryCost ≤ lowerInput ∧
        lowerInput ≤ (p + C) ^ C ∧ finalLower ≤ (p + C) ^ C := by
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let I : Polynomial ℕ := Polynomial.X + N
  let R : Polynomial ℕ := (I + Polynomial.C B) ^ B
  let U : Polynomial ℕ := I + R
  let F : Polynomial ℕ := (U + Polynomial.C T) ^ T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + F)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let nativeCost := (p + A) ^ A
  let inputCost := p + nativeCost
  let recoveryCost := (inputCost + B) ^ B
  let lowerInput := inputCost + recoveryCost
  let finalLower := (lowerInput + T) ^ T
  have hnative : 0 ≤ nativeCost := by dsimp [nativeCost]; positivity
  have hinput : 0 ≤ inputCost := add_nonneg hp0 hnative
  have hrecovery : 0 ≤ recoveryCost := by dsimp [recoveryCost]; positivity
  have hlower : 0 ≤ lowerInput := add_nonneg hinput hrecovery
  have hfinal : 0 ≤ finalLower := by dsimp [finalLower]; positivity
  have hsum : lowerInput + finalLower ≤ (p + C) ^ C := by
    simpa only [N, I, R, U, F, nativeCost, inputCost, recoveryCost, lowerInput, finalLower,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Nat.coe_castRingHom] using hbudget p hp0
  exact ⟨hp.trans (le_add_of_nonneg_right hnative), le_add_of_nonneg_right hnative,
    le_add_of_nonneg_left hp0, le_add_of_nonneg_right hrecovery,
    le_add_of_nonneg_left hinput, (le_add_of_nonneg_right hfinal).trans hsum,
    (le_add_of_nonneg_left hlower).trans hsum⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
namespace OAI

section

namespace Erdos3

theorem exists_uniformIntervalGrid_half_approx {B : ℝ} (hB : 0 < B)
    {N : ℕ} (hN : 0 < N) (x : ℝ) (hx : |x| ≤ B) :
    ∃ k : Fin (N + 1), |x - uniformIntervalGrid B N k| ≤ B / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let δ : ℝ := 2 * B / N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  let q : ℝ := (x + B) / δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hqN : q ≤ N := by
    apply (div_le_iff₀ hδ).mpr
    linarith [(abs_le.mp hx).2]
  let k : Fin (N + 1) := ⟨⌊q + 1 / 2⌋₊, (Nat.floor_lt (by positivity)).mpr (by
    push_cast
    linarith)⟩
  have hk : |q - (k.val : ℝ)| ≤ 1 / 2 := by
    apply abs_le.mpr
    have hlo := Nat.floor_le (show 0 ≤ q + 1 / 2 by positivity)
    have hhi := Nat.lt_floor_add_one (q + 1 / 2)
    change -(1 / 2) ≤ q - (⌊q + 1 / 2⌋₊ : ℝ) ∧ _
    constructor <;> linarith
  refine ⟨k, ?_⟩
  have heq : x - uniformIntervalGrid B N k = δ * (q - k.val) := by
    have hδq : δ * q = x + B := by dsimp [q]; field_simp
    change x - (-B + δ * k.val) = _
    rw [mul_sub, hδq]
    ring
  rw [heq, abs_mul, abs_of_pos hδ]
  exact (mul_le_mul_of_nonneg_left hk hδ.le).trans_eq (by dsimp [δ]; ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Model
namespace OAI

namespace Erdos3

noncomputable def extremalNumber (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card

end Erdos3

open scoped BigOperators

namespace Erdos3

def QuantitativeDensityBound (k : ℕ) : Prop :=
  ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ N : ℕ, 3 ≤ N →
      (extremalNumber k N : ℝ) ≤
        C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))

def QuantitativeDensityTheorem : Prop :=
  ∀ k : ℕ, 3 ≤ k → QuantitativeDensityBound k


end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

instance unitScalarMeasure_probability : IsProbabilityMeasure unitScalarMeasure := by
  constructor
  simp [unitScalarMeasure]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem ReflectsPairSums.mono {φ : A →+ B} {Q R : Set A}
    (hφ : ReflectsPairSums φ Q) (hRQ : R ⊆ Q) : ReflectsPairSums φ R := by
  intro a ha b hb c hc d hd he
  exact hφ a (hRQ ha) b (hRQ hb) c (hRQ hc) d (hRQ hd) he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

def compatibleAuxResidueOfPoint (M d : ℕ) (hd : 0 < d) (u x : ℤ)
    (hx : x ≡ u [ZMOD (M : ℤ)]) : CompatibleAuxResidue M d u :=
  ⟨integerResidueLabel d hd x, x, hx, (integerResidueLabel_eq_iff d hd x _).mp rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

noncomputable def intervalResidueCell (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (r v : ℤ) :
    ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N))) → P.Label :=
  fun x => P.cell (integerIntervalEquivFin a N ⟨x.val, (Finset.mem_filter.mp x.property).1⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {X D E : Type*}

noncomputable def integralBasisPolynomialCoordinates
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U) : E → MvPolynomial X ℝ :=
  fun e => coordinate (b.coord e).toAddMonoidHom (restrictCoefficients U p hmem)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ImageCoverBudget
namespace OAI

section

namespace Erdos3

theorem imageLatticeBound_le_exp (K d n H l m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    ((K * H ^ (n ^ 3) * (m * (l * rationalKernelHeight n H ^ (d * n))) : ℕ) : ℝ) ≤
      Real.exp (imageLatticeLogBudget K p) := by
  have hK : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have hpow : ((H ^ (n ^ 3) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _).trans
    rw [← Real.exp_nat_mul, Nat.cast_pow]
    apply Real.exp_le_exp.mpr
    calc
      (n : ℝ) ^ 3 * p ≤ (p + 2) ^ 3 * (p + 2) := by gcongr <;> linarith
      _ = _ := by ring
  have hkernel := rationalKernelHeight_le_budget n H hp hn hH
  have hpowK : ((rationalKernelHeight n H ^ (d * n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hkernel _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul]
    apply Real.exp_le_exp.mpr
    calc
      (d : ℝ) * n * (p + 2) ^ 7 ≤ (p + 2) * (p + 2) * (p + 2) ^ 7 := by gcongr <;> linarith
      _ = _ := by ring
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ Real.exp K * Real.exp ((p + 2) ^ 4) *
        (Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 9))) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; unfold imageLatticeLogBudget; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

def lieSubalgebraRepresentativeHeight (d r H : ℕ) : ℕ :=
  rationalLieStructureHeight d (max H (rationalSolveHeight r H))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisAxisNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem basisAxisScale_mul_norm (b : Basis I ℝ E) (i : I) :
    1 ≤ (basisAxisScale b i : ℝ) * ‖b i‖ ∧
      (basisAxisScale b i : ℝ) * ‖b i‖ < ‖b i‖ + 1 := by
  have hpos : 0 < ‖b i‖ := norm_pos_iff.mpr (b.ne_zero i)
  have hlo := mul_le_mul_of_nonneg_right (Nat.le_ceil ‖b i‖⁻¹) hpos.le
  have hhi := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (inv_nonneg.mpr hpos.le)) hpos
  constructor
  · simpa only [basisAxisScale, inv_mul_cancel₀ hpos.ne'] using hlo
  · have he : (‖b i‖⁻¹ + 1) * ‖b i‖ = ‖b i‖ + 1 := by
      rw [add_mul, inv_mul_cancel₀ hpos.ne', one_mul, add_comm]
    simpa only [basisAxisScale, he] using hhi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrthogonalBasisChart
namespace OAI

section

namespace Erdos3

open Module

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonalBasisChart_symm_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    (p : W × (Fin n → ℝ)) :
    (orthogonalBasisChart W b).symm p = p.1.val + (b.equivFun.symm p.2).val := rfl

theorem orthogonalBasisChart_symm_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖b.equivFun.symm x‖ ≤ C * ‖x‖)
    (p : W × (Fin n → ℝ)) :
    ‖(orthogonalBasisChart W b).symm p‖ ≤ (1 + C) * ‖p‖ := by
  rw [orthogonalBasisChart_symm_apply]
  calc
    _ ≤ ‖p.1‖ + ‖b.equivFun.symm p.2‖ := norm_add_le _ _
    _ ≤ ‖p.1‖ + C * ‖p.2‖ := by gcongr; exact hb _
    _ ≤ ‖p‖ + C * ‖p‖ := by gcongr; exact norm_fst_le p; exact norm_snd_le p
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

namespace VectorPolynomial

theorem appendRankCutRow_height {ι ρ : Type*} (A : Matrix ρ ι ℚ) (a : ι → ℤ)
    {R : ℕ} (hR : 1 ≤ R) (hA : ∀ r i, RationalHeightLE (A r i) R)
    (ha : ∀ i, |(a i : ℝ)| ≤ R) :
    ∀ r i, RationalHeightLE (appendRankCutRow A a r i) R := by
  intro r i
  cases r with
  | none =>
    change RationalHeightLE (a i : ℚ) R
    have habs : (a i).natAbs ≤ R := by
      exact_mod_cast (show ((a i).natAbs : ℝ) ≤ R by
        simpa only [Nat.cast_natAbs, Int.cast_abs] using ha i)
    exact ⟨by simpa only [Rat.num_intCast] using habs, by simpa only [Rat.den_intCast] using hR⟩
  | some r => exact hA r i

open scoped TensorProduct

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonalLatticeImage_le_dual_section (Λ : Submodule ℤ E)
    (W : Submodule ℝ E) :
    orthogonalLatticeImage Λ W ≤ euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_euclideanDualLattice _ _).mpr
  intro y hy
  have hy' : (y : E) ∈ euclideanDualLattice Λ := hy
  obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ y.val).mp hy' x hx
  refine ⟨n, ?_⟩
  change inner ℝ (W.orthogonalProjectionOnto x) y = (n : ℝ)
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, real_inner_comm]
  exact hn

theorem orthogonalLatticeImage_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E) [DiscreteTopology (orthogonalLatticeImage Λ W)] :
    IsZLattice ℝ (orthogonalLatticeImage Λ W) := by
  constructor
  change span ℝ (W.orthogonalProjectionOnto.toLinearMap '' (Λ : Set E)) = ⊤
  rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro w
  refine ⟨w.val, ?_⟩
  apply Subtype.ext
  exact W.starProjection_eq_self_iff.mpr w.property

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

theorem standardEuclideanLattice_self_dual :
    euclideanDualLattice (standardEuclideanLattice ι) = standardEuclideanLattice ι := by
  ext x
  rw [mem_euclideanDualLattice, mem_standardEuclideanLattice]
  constructor
  · intro hx i
    have hi : EuclideanSpace.basisFun ι ℝ i ∈ standardEuclideanLattice ι :=
      Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hx _ hi
    exact ⟨n, by simpa only [EuclideanSpace.inner_basisFun_real] using hn.symm⟩
  · intro hx y hy
    choose a ha using hx
    choose b hb using (mem_standardEuclideanLattice ι y).mp hy
    refine ⟨∑ i, a i * b i, ?_⟩
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp only [Int.cast_sum, Int.cast_mul, ha, hb]
    apply Finset.sum_congr rfl
    intro i _
    ring

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalLatticeKernelEquiv (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    latticeSection Λ Wᗮ ≃ₗ[ℤ] LinearMap.ker (orthogonalLatticeProjection Λ W) where
  toFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext
    (W.orthogonalProjectionOnto_eq_zero_iff.mpr x.val.property)⟩
  invFun x := ⟨⟨x.val.val, W.orthogonalProjectionOnto_eq_zero_iff.mp
    (congrArg Subtype.val (show orthogonalLatticeProjection Λ W x.val = 0 from x.property))⟩,
    x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_orthogonal_lattice_split_basis {I J : Type*}
    (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bK : Basis I ℤ (latticeSection Λ Wᗮ)) (bP : Basis J ℤ (orthogonalLatticeImage Λ W)) :
    ∃ b : Basis (I ⊕ J) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, W.orthogonalProjectionOnto (b (Sum.inr j) : E) = (bP j).val) := by
  let : Free ℤ (orthogonalLatticeImage Λ W) := Free.of_basis bP
  obtain ⟨b, hK, hP⟩ := exists_basis_of_surjection (orthogonalLatticeProjection Λ W)
    (orthogonalLatticeProjection_surjective Λ W) (bK.map (orthogonalLatticeKernelEquiv Λ W)) bP
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hK]
    rfl
  · intro j
    exact congrArg Subtype.val (hP j)

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integerBasisOfReal_apply (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (i : I) : (integerBasisOfReal Λ b hb i).val = b i := by
  simp only [integerBasisOfReal, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.restrictScalars_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanShortLatticeBasis
namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem orthonormalChart_symm_norm_le (b : OrthonormalBasis I ℝ E) (x : E) :
    ‖(orthonormalChart b).symm x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  have h := PiLp.norm_apply_le (b.repr x) i
  simpa [orthonormalChart] using h

noncomputable def orthonormalCoordinateLattice (Λ : Submodule ℤ E)
    (b : OrthonormalBasis I ℝ E) : Submodule ℤ (I → ℝ) :=
  ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap

instance orthonormalCoordinateLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (b : OrthonormalBasis I ℝ E) : DiscreteTopology (orthonormalCoordinateLattice Λ b) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap))

instance orthonormalCoordinateLattice_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : OrthonormalBasis I ℝ E) :
    IsZLattice ℝ (orthonormalCoordinateLattice Λ b) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap))

variable [MeasurableSpace E] [BorelSpace E]

theorem orthonormalChart_measurePreserving (b : OrthonormalBasis I ℝ E) :
    MeasurePreserving (orthonormalChart b) :=
  b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp I)

theorem orthonormalCoordinateLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : OrthonormalBasis I ℝ E) :
    ZLattice.covolume (orthonormalCoordinateLattice Λ b) = ZLattice.covolume Λ :=
  ZLattice.covolume_comap Λ volume volume (orthonormalChart_measurePreserving b)

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

variable {J : Type*} [Fintype J]

theorem projectedIntegerGenerator_mem (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) :
    projectedIntegerGenerator W i ∈ projectedIntegerLattice W := by
  refine ⟨EuclideanSpace.basisFun J ℝ i, ?_, rfl⟩
  exact subset_span (Set.mem_range_self i)

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem exists_bounded_integral_span_of_rational_range
    {J C : Type*} [Fintype J] [Fintype C]
    (B : Matrix J C ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin = W)
    {H : ℕ} (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ v : C → euclideanSubspace W,
      span ℝ (Set.range v) = ⊤ ∧
      (∀ j, v j ∈ latticeSection (standardEuclideanLattice J) (euclideanSubspace W)) ∧
      ∀ j, ‖v j‖ ≤ (Fintype.card J : ℝ) * H ^ (Fintype.card J * Fintype.card C) := by
  classical
  obtain ⟨D, hD, _, z, hz, hzH⟩ :=
    exists_bounded_integer_array (fun ij : J × C => B ij.1 ij.2) (fun ij => hB ij.1 ij.2)
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hzr (i : J) (j : C) : (z (i, j) : ℝ) = (D : ℝ) * (B i j : ℝ) := by
    exact_mod_cast hz (i, j)
  have hcol (j : C) : (fun i => (B i j : ℝ)) ∈ W := by
    rw [← hW, Matrix.range_mulVecLin]
    exact subset_span ⟨j, rfl⟩
  have hmem (j : C) : WithLp.toLp 2 (fun i => (z (i, j) : ℝ)) ∈ euclideanSubspace W := by
    change (fun i => (z (i, j) : ℝ)) ∈ W
    have he : (fun i => (z (i, j) : ℝ)) = (D : ℝ) • (fun i => (B i j : ℝ)) :=
      funext (fun i => hzr i j)
    rw [he]
    exact W.smul_mem (D : ℝ) (hcol j)
  let v : C → euclideanSubspace W := fun j => ⟨WithLp.toLp 2 (fun i => (z (i, j) : ℝ)), hmem j⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    have hx : WithLp.ofLp x.val ∈ W := x.property
    obtain ⟨y, hy⟩ := hW.ge hx
    have heq : x = ∑ j, (y j / D) • v j := by
      apply Subtype.ext
      ext i
      have hi := congrFun hy i
      change (∑ j, (B i j : ℝ) * y j) = x.val i at hi
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum,
        WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hi]
      apply Finset.sum_congr rfl
      intro j _
      rw [hzr]
      field_simp
    rw [heq]
    exact sum_mem (fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩))
  · intro j
    change (v j).val ∈ standardEuclideanLattice J
    exact (mem_standardEuclideanLattice J _).mpr (fun i => ⟨z (i, j), rfl⟩)
  · intro j
    calc
      ‖v j‖ ≤ ∑ i, |(z (i, j) : ℝ)| := euclidean_norm_le_sum_abs (v j).val
      _ ≤ ∑ _ : J, (H : ℝ) ^ (Fintype.card J * Fintype.card C) := by
        apply Finset.sum_le_sum
        intro i _
        have hb := hzH (i, j)
        rw [Fintype.card_prod] at hb
        have hr : |z (i, j)| ≤ (H ^ (Fintype.card J * Fintype.card C) : ℕ) := by
          simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hb)
        exact_mod_cast hr
      _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProjectedAxisBudgets
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory BohrLattice.MinkowskiSecondBox
open scoped BigOperators

noncomputable def projectedAxisNormBudget (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * n.factorial * minkowskiSecondConstant n

noncomputable def projectedAxisDefectBudget (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ n * minkowskiSecondConstant n

theorem projectedAxisNormBudget_pos (n : ℕ) : 0 < projectedAxisNormBudget n := by
  unfold projectedAxisNormBudget minkowskiSecondConstant
  positivity

theorem projectedAxisDefectBudget_pos (n : ℕ) : 0 < projectedAxisDefectBudget n := by
  unfold projectedAxisDefectBudget minkowskiSecondConstant
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

theorem shifted_power_le_fixed_base {p : ℝ} (hp : 0 ≤ p) (C : ℕ) (hC : 2 ≤ C) :
    (p + C) ^ C ≤ (p + 2) ^ ((C + 1) * C) := by
  have hbase : 0 ≤ p + 2 := by linarith
  have hpTerm : p ≤ (p + 2) ^ C := le_power_budget hp (by omega)
  have htwo : (C : ℝ) ≤ (2 : ℝ) ^ C := by
    exact_mod_cast (show C < 2 ^ C from Nat.lt_two_pow_self).le
  have hCTerm : (C : ℝ) ≤ (p + 2) ^ C :=
    htwo.trans (pow_le_pow_left₀ (by norm_num) (by linarith) C)
  have hsum : p + C ≤ (p + 2) ^ (C + 1) := by
    calc
      _ ≤ 2 * (p + 2) ^ C := by linarith
      _ ≤ (p + 2) * (p + 2) ^ C :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hbase _)
      _ = _ := (pow_succ' _ _).symm
  calc
    _ ≤ ((p + 2) ^ (C + 1)) ^ C := pow_le_pow_left₀ (by positivity) hsum C
    _ = _ := (pow_mul _ _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module

theorem coefficientTorus_compact_of_basis {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) :
    CompactSpace (CoefficientTorus (K := K) U) := by
  classical
  apply compact_quotient_of_integral_basis (coefficientIntegerLattice U)
    (Pi.basis (fun s : CoefficientSlot K m => b s.1))
  rintro ⟨s, i⟩ t a
  simp only [Pi.basis_apply]
  by_cases hts : t = s
  · subst t
    simpa only [Pi.single_eq_same] using hb s.1 i a
  · exact ⟨0, by simp [Pi.single_eq_of_ne hts]⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeProjectedChart
namespace OAI

section

namespace Erdos3

theorem projectedAxisNormBudget_le_exp (n : ℕ) :
    projectedAxisNormBudget n ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hf := factorial_le_exp_sq n
  have hm := BohrProgression.minkowskiSecondConstant_le_exp n
  have hm0 := BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_nonneg n
  unfold projectedAxisNormBudget
  calc
    _ ≤ Real.exp n * Real.exp ((n : ℝ) ^ 2) * Real.exp (2 * (n : ℝ) ^ 2) := by
      gcongr
    _ = Real.exp ((n : ℝ) + (n : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedAxisDefectBudget_le_exp (n : ℕ) :
    projectedAxisDefectBudget n ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hm := BohrProgression.minkowskiSecondConstant_le_exp n
  have hm0 := BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_nonneg n
  unfold projectedAxisDefectBudget
  calc
    _ ≤ (Real.exp n) ^ n * Real.exp (2 * (n : ℝ) ^ 2) := by gcongr
    _ = Real.exp ((n : ℝ) * n + 2 * (n : ℝ) ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedAxisNormBudget_add_one_le_exp (n : ℕ) :
    projectedAxisNormBudget n + 1 ≤ Real.exp (5 * ((n : ℝ) + 1) ^ 2) := by
  have h := one_add_le_exp_succ (by positivity : 0 ≤ 4 * ((n : ℝ) + 1) ^ 2)
    (projectedAxisNormBudget_le_exp n)
  calc
    _ ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2 + 1) := by simpa only [add_comm] using h
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedChart_forwardBudget_le_exp (n : ℕ) :
    1 + (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ (n - 1) *
      projectedAxisDefectBudget n ≤ Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hf := factorial_le_exp_sq n
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hd := projectedAxisDefectBudget_le_exp n
  have hd0 := (projectedAxisDefectBudget_pos n).le
  have hb0 := (projectedAxisNormBudget_pos n).le
  have hp : (projectedAxisNormBudget n + 1) ^ (n - 1) ≤
      (projectedAxisNormBudget n + 1) ^ n :=
    pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have hterm : (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ (n - 1) *
      projectedAxisDefectBudget n ≤
      Real.exp ((n : ℝ) + (n : ℝ) ^ 2 + n * (5 * ((n : ℝ) + 1) ^ 2) +
        4 * ((n : ℝ) + 1) ^ 2) := by
    calc
      _ ≤ (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ n *
          projectedAxisDefectBudget n := by gcongr
      _ ≤ Real.exp n * Real.exp ((n : ℝ) ^ 2) *
          (Real.exp (5 * ((n : ℝ) + 1) ^ 2)) ^ n *
          Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply (one_add_le_exp_succ (by positivity) hterm).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

theorem projectedChart_inverseBudget_le_exp (n : ℕ) :
    1 + (n : ℝ) * (projectedAxisNormBudget n + 1) ≤
      Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hb0 := (projectedAxisNormBudget_pos n).le
  have hterm : (n : ℝ) * (projectedAxisNormBudget n + 1) ≤
      Real.exp ((n : ℝ) + 5 * ((n : ℝ) + 1) ^ 2) := by
    calc
      _ ≤ Real.exp n * Real.exp (5 * ((n : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  apply (one_add_le_exp_succ (by positivity) hterm).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

theorem projectedChart_volumeBudget_le_exp (n : ℕ) :
    (n.factorial : ℝ) * (projectedAxisNormBudget n + 1) ^ n ≤
      Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hf := factorial_le_exp_sq n
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hb0 := (projectedAxisNormBudget_pos n).le
  calc
    _ ≤ Real.exp ((n : ℝ) ^ 2) * (Real.exp (5 * ((n : ℝ) + 1) ^ 2)) ^ n := by gcongr
    _ = Real.exp ((n : ℝ) ^ 2 + n * (5 * ((n : ℝ) + 1) ^ 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn0 := Nat.cast_nonneg (α := ℝ) n
      have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
      nlinarith

theorem projectedChart_defectBudget_le_exp (n : ℕ) :
    projectedAxisDefectBudget n ≤ Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  apply (projectedAxisDefectBudget_le_exp n).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeChartKernel
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MetricSpace X]

noncomputable def chartCoordinateKernel (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) : (ι → ℝ) → ℝ := chartCutoff phi.symm F

omit [Fintype ι] in
theorem chartCoordinateKernel_of_mem (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {v : ι → ℝ} (hv : v ∈ phi.source) :
    chartCoordinateKernel phi F v = F (phi v) := by
  classical
  change (if v ∈ phi.source then F (phi v) else 0) = _
  rw [if_pos hv]

omit [Fintype ι] in
theorem chartCoordinateKernel_of_not_mem (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {v : ι → ℝ} (hv : v ∉ phi.source) :
    chartCoordinateKernel phi F v = 0 := by
  classical
  change (if v ∈ phi.source then F (phi v) else 0) = _
  rw [if_neg hv]

omit [Fintype ι] in
theorem chartCoordinateKernel_range (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (v : ι → ℝ) :
    0 ≤ chartCoordinateKernel phi F v ∧ chartCoordinateKernel phi F v ≤ 1 :=
  chartCutoff_range phi.symm F hF v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerAffineMap_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (a s x : I → ℤ) :
    integerAffineMap (fun i j => if i = j then s i else 0) a x = fun i => a i + s i * x i := by
  funext i
  simp [integerAffineMap, ite_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_complex_partition_approximation {I X : Type*} [Fintype I]
    [PseudoMetricSpace X] (w : I → X → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    {rho : ℝ} (hdiam : ∀ i x y, 0 < w i x → 0 < w i y → dist x y ≤ rho)
    (F : X → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) {K : ℝ≥0} (hLip : LipschitzWith K F) :
    ∃ c : I → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
      ∀ x, ‖F x - ∑ i, (w i x : ℂ) * c i‖ ≤ (K : ℝ) * rho := by
  classical
  have hchoose (i : I) : ∃ c : ℂ, ‖c‖ ≤ 1 ∧
      ∀ x, 0 < w i x → ‖F x - c‖ ≤ (K : ℝ) * rho := by
    by_cases hi : ∃ y, 0 < w i y
    · obtain ⟨y, hy⟩ := hi
      refine ⟨F y, hF y, fun x hx => ?_⟩
      have h := hLip.dist_le_mul x y
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hdiam i x y hx hy) K.coe_nonneg)
    · refine ⟨0, by norm_num, fun x hx => False.elim (hi ⟨x, hx⟩)⟩
  choose c hc herr using hchoose
  exact ⟨c, hc, fun x => norm_sub_positive_sum_le (fun i => w i x) c (F x) _
    (fun i => hw i x) (hsum x) (fun i => herr i x)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.McShaneEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

omit [Nonempty X] in
theorem mcShaneEnvelope_le (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) (x : X) :
    mcShaneEnvelope φ L f y ≤ f x + L * dist y (φ x) :=
  ciInf_le (mcShaneEnvelope_bddBelow φ L f hf y) x

theorem mcShaneEnvelope_lipschitz (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    LipschitzWith L (mcShaneEnvelope φ L f) := by
  apply LipschitzWith.of_le_add_mul
  intro y z
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro x
  rw [sub_le_iff_le_add]
  calc
    mcShaneEnvelope φ L f y ≤ f x + L * dist y (φ x) := mcShaneEnvelope_le φ L f hf y x
    _ ≤ f x + L * dist z (φ x) + L * dist y z := by
      have h := mul_le_mul_of_nonneg_left (dist_triangle y z (φ x)) L.coe_nonneg
      linarith

theorem mcShaneEnvelope_eq (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hLip : ∀ x z, |f x - f z| ≤ L * dist (φ x) (φ z)) (x : X) :
    mcShaneEnvelope φ L f (φ x) = f x := by
  apply le_antisymm
  · simpa only [dist_self, mul_zero, add_zero] using mcShaneEnvelope_le φ L f hf (φ x) x
  · apply le_ciInf
    intro z
    have h := (le_abs_self (f x - f z)).trans (hLip x z)
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveReconstruction
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem positiveClip_unit_interval (z : ℂ) :
    (positiveClip z).im = 0 ∧ 0 ≤ (positiveClip z).re ∧ (positiveClip z).re ≤ 1 := by
  refine ⟨rfl, le_max_left _ _, ?_⟩
  exact max_le (by norm_num) (min_le_left _ _)

theorem positiveClip_eq_self (z : ℂ) (hz : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) :
    positiveClip z = z := by
  apply Complex.ext
  · change max 0 (min 1 z.re) = z.re
    rw [min_eq_right hz.2.2, max_eq_right hz.2.1]
  · exact hz.1.symm

theorem positiveClip_lipschitz : LipschitzWith 1 positiveClip := by
  change LipschitzWith 1 (fun z : ℂ => ((max 0 (min 1 z.re) : ℝ) : ℂ))
  have h : LipschitzWith 1 (fun z : ℂ => max 0 (min 1 z.re)) :=
    ((RCLike.lipschitzWith_re (K := ℂ)).const_min 1).const_max 0
  simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp h

theorem norm_positiveClip_le_one (z : ℂ) : ‖positiveClip z‖ ≤ 1 := by
  change ‖((max 0 (min 1 z.re) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact (positiveClip_unit_interval z).2.2

theorem exists_positive_lipschitz_reconstruction {X Y : Type*} [PseudoMetricSpace Y]
    (f : X → ℂ) (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (φ : X → Y) (v : Y → ℂ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (heval : ∀ x, v (φ x) = f x) :
    ∃ u : Y → ℂ, LipschitzWith K u ∧
      (∀ y, (u y).im = 0 ∧ 0 ≤ (u y).re ∧ (u y).re ≤ 1) ∧
      (∀ y, ‖u y‖ ≤ 1) ∧ ∀ x, u (φ x) = f x := by
  refine ⟨fun y => positiveClip (v y), ?_, fun y => positiveClip_unit_interval (v y),
    fun y => norm_positiveClip_le_one (v y), ?_⟩
  · simpa only [one_mul, Function.comp_def] using positiveClip_lipschitz.comp hv
  · intro x
    change positiveClip (v (φ x)) = f x
    rw [heval, positiveClip_eq_self _ (hf x)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem mem_restrictedFrequencySpan_coannihilator (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) (v : P) :
    v ∈ (restrictedFrequencySpan P eta js).dualCoannihilator ↔
      (v : V) ∈ finiteFrequencyKernel P eta js := by
  change v ∈ ((Submodule.span ℚ ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})).dualCoannihilator : Set P) ↔ _
  rw [Submodule.coe_dualCoannihilator_span, mem_finiteFrequencyKernel]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_image, LinearMap.comp_apply,
    Submodule.subtype_apply, v.property, true_and]

end Erdos3

end

section

namespace Erdos3

open Module

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

theorem finiteFrequencyKernel_eq_map_coannihilator (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    finiteFrequencyKernel P eta js =
      (restrictedFrequencySpan P eta js).dualCoannihilator.map P.subtype := by
  ext v
  constructor
  · intro hv
    let x : P := ⟨v, finiteFrequencyKernel_le P eta js hv⟩
    exact ⟨x, (mem_restrictedFrequencySpan_coannihilator P eta js x).mpr hv, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_restrictedFrequencySpan_coannihilator P eta js x).mp hx

theorem finiteFrequencyKernel_eq_of_span_eq (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) (xi : I → V →ₗ[ℚ] ℚ) (is : List I)
    (hspan : restrictedFrequencySpan P eta js = restrictedFrequencySpan P xi is) :
    finiteFrequencyKernel P eta js = finiteFrequencyKernel P xi is := by
  rw [finiteFrequencyKernel_eq_map_coannihilator, finiteFrequencyKernel_eq_map_coannihilator, hspan]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

omit [Nonempty X] in
theorem positiveImageExtension_unit_interval (f : X → ℂ) (y : Y) :
    (positiveImageExtension φ L f y).im = 0 ∧
      0 ≤ (positiveImageExtension φ L f y).re ∧ (positiveImageExtension φ L f y).re ≤ 1 :=
  positiveClip_unit_interval _

omit [Nonempty X] in
theorem positiveImageExtension_norm_le_one (f : X → ℂ) (y : Y) :
    ‖positiveImageExtension φ L f y‖ ≤ 1 := norm_positiveClip_le_one _

theorem positiveImageExtension_eq (f : X → ℂ)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (hLip : ∀ x z, ‖f x - f z‖ ≤ L * dist (φ x) (φ z)) (x : X) :
    positiveImageExtension φ L f (φ x) = f x := by
  have hreal : ∀ x z, |(f x).re - (f z).re| ≤ L * dist (φ x) (φ z) :=
    fun x z => (Complex.abs_re_le_norm (f x - f z)).trans (hLip x z)
  have heq : ((f x).re : ℂ) = f x := Complex.ext rfl (hf x).1.symm
  unfold positiveImageExtension
  rw [mcShaneEnvelope_eq φ L _ (fun x => (hf x).2.1) hreal, heq,
    positiveClip_eq_self _ (hf x)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (L : ℝ≥0)

theorem positiveImageSlice_eq (f : X → ℂ)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (hLip : ∀ x z, ‖f x - f z‖ ≤ L * dist (φ x) (φ z)) (x : X) :
    positiveImageSlice φ L f (φ x).2 (φ x).1 = f x :=
  positiveImageExtension_eq φ L f hf hLip x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

noncomputable def bounded (b : ℕ) : Finset (ProductCylinder X) := by
  classical
  exact Finset.univ.filter (fun c => c.1.card ≤ b)

end ProductCylinder

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AuxiliaryIntervalCells
namespace OAI

section

namespace Erdos3

noncomputable def intervalAuxiliaryCell (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N)))) :
    P.Label × CompatibleAuxResidue M d u :=
  (intervalResidueCell a P r b x,
    compatibleAuxResidueOfPoint M d hd u x.val (hbase x.val (Finset.mem_filter.mp x.property).2))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyProjectionBudget
namespace OAI

section

namespace Erdos3

theorem frequency_code_count_bound {p v : ℝ} {D M : ℕ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hD : (D : ℝ) ≤ p) (hM : (M : ℝ) ≤ Real.exp v) :
    ((M : ℝ) + 1) ^ D ≤ Real.exp (p * (v + 1)) := by
  have parameterNonneg := hp
  have hbase : (M : ℝ) + 1 ≤ Real.exp (v + 1) := by
    simpa only [add_zero] using add_le_exp_add_one hv (le_refl (0 : ℝ)) hM
      (by simp : (1 : ℝ) ≤ Real.exp 0)
  calc
    _ ≤ (Real.exp (v + 1)) ^ D := pow_le_pow_left₀ (by positivity) hbase D
    _ = Real.exp ((D : ℝ) * (v + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (by linarith [parameterNonneg]))

theorem mass_div_frequency_count {mass p v R : ℝ} {D M : ℕ}
    (hmass : 0 ≤ mass) (hp : 0 ≤ p) (hv : 0 ≤ v) (hD : (D : ℝ) ≤ p)
    (hM : (M : ℝ) ≤ Real.exp v) (hR : p * (v + 1) ≤ R) :
    mass * Real.exp (-R) ≤ mass / ((M : ℝ) + 1) ^ D := by
  have hden := (frequency_code_count_bound hp hv hD hM).trans (Real.exp_le_exp.mpr hR)
  have hi : Real.exp (-R) ≤ 1 / ((M : ℝ) + 1) ^ D := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hden
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hi hmass

end Erdos3

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

def principalAxisLength (P : D → Prop) (L : PrincipalTupleIndex B h → ℕ) :
    PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) → ℕ :=
  fun j => L ⟨j.1.val, j.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem bounded_coefficients_evaluation_error {J : Type*} [Fintype J]
    (P Q : MvPolynomial J ℝ) {s : ℕ} (hP : P.totalDegree ≤ s) (hQ : Q.totalDegree ≤ s)
    {η B : ℝ} (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hcoeff : ∀ e : BoundedIntegerExponent J s, |P.coeff e.val - Q.coeff e.val| ≤ η)
    (x : J → ℝ) (hx : ∀ j, |x j| ≤ B) :
    |aeval x P - aeval x Q| ≤ ((s + 1) * (Fintype.card J + 1) ^ s : ℕ) * η * B ^ s := by
  have hdeg : (P - Q).totalDegree ≤ s := (totalDegree_sub P Q).trans (max_le hP hQ)
  have hmass : realPolynomialMass (P - Q) ≤ ((s + 1) * (Fintype.card J + 1) ^ s : ℕ) * η := by
    calc
      _ ≤ ∑ _e ∈ (P - Q).support, η := by
        apply Finset.sum_le_sum
        intro e he
        simpa only [coeff_sub] using hcoeff ⟨e, (le_totalDegree he).trans hdeg⟩
      _ = ((P - Q).support.card : ℝ) * η := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (polynomial_support_card_le _ hdeg)) hη
  rw [← map_sub]
  exact (abs_aeval_le_mass_box (P - Q) x hB hx hdeg).trans
    (mul_le_mul_of_nonneg_right hmass (pow_nonneg (zero_le_one.trans hB) s))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
namespace OAI

section

namespace Erdos3

open Module

theorem exists_common_bounded_moduli {G κ : Type*} [Fintype κ]
    (S : Finset G) (hS : S.Nonempty) (moduli : G → κ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hmoduli : ∀ a ∈ S, ∀ i, (moduli a i : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset G, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, moduli a = moduli a₀) ∧
      Real.exp (-((p + 1) * Fintype.card κ)) * S.card ≤ (T.card : ℝ) := by
  classical
  let N := ⌊Real.exp p⌋₊
  let tag : G → κ → Fin (N + 1) := fun a i =>
    ⟨min (moduli a i) N, (min_le_right _ _).trans_lt (Nat.lt_succ_self _)⟩
  have htag : ∀ a ∈ S, ∀ i, (tag a i).val = moduli a i := by
    intro a ha i
    exact min_eq_left (Nat.le_floor (hmoduli a ha i))
  have hbase : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
    have h1 : 1 ≤ Real.exp p := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Nat.cast_add, Nat.cast_one]
    calc
      (N : ℝ) + 1 ≤ Real.exp p + Real.exp p :=
        add_le_add (Nat.floor_le (Real.exp_pos p).le) h1
      _ = Real.exp p * 2 := by ring
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos p).le
      _ = _ := (Real.exp_add p 1).symm
  have hcount : ((Set.univ : Set (κ → Fin (N + 1))).ncard : ℝ) ≤
      Real.exp ((p + 1) * Fintype.card κ) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (p + 1) ^ Fintype.card κ := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, T, hTS, hT, hconstant, hlarge⟩ := exists_exponential_constant_fiber
    S hS tag Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcount
  obtain ⟨a₀, ha₀⟩ := hT
  refine ⟨a₀, hTS ha₀, T, hTS, ha₀, ?_, hlarge⟩
  intro a ha
  funext i
  have h := congrArg (fun f : κ → Fin (N + 1) => (f i).val)
    ((hconstant a ha).trans (hconstant a₀ ha₀).symm)
  simpa only [htag a (hTS ha) i, htag a₀ (hTS ha₀) i] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantObservableMemberNets
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem constantObservable_integerBox_memberNets
    {X Y : Type*} [Fintype X] (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (F : Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(fun (_ : X → ℤ) => F) x y - (fun (_ : X → ℤ) => F) (oc i).val y‖ ≤ η := by
  have hzero : (0 : X → ℤ) ∈ integerBox N := by
    apply (mem_integerBox N 0).mpr
    intro x
    exact ⟨le_rfl, by change (0 : ℤ) < N x; exact_mod_cast hN x⟩
  exact constantObservable_memberNets (integerBox N) ⟨0, hzero⟩ F hp e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CopiedLayerSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem jointRationalSpace_copiedLayer {J K C V : Type*}
    [Fintype J] [Fintype K] [Fintype C]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) (e : K → ℚ) :
    jointRationalSpace (copiedLayerMatrix B e) (copiedLayerRows A) =
      copiedLayerSpace (jointRationalSpace B A) (Submodule.span ℝ {fun k => (e k : ℝ)}) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz⟩, hA⟩
    change Matrix.of (fun j c => (copiedLayerMatrix B e j c : ℝ)) *ᵥ z = x at hz
    rw [copiedLayerMatrix_real_mulVec] at hz
    change Matrix.of (fun r j => (copiedLayerRows A r j : ℝ)) *ᵥ x = 0 at hA
    rw [copiedLayerRows_real_mulVec] at hA
    refine ⟨⟨⟨fun c => z (some c), ?_⟩, hA⟩, ?_⟩
    · ext j
      exact congrFun hz (.inl j)
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨z none, ?_⟩
      ext k
      exact congrFun hz (.inr k)
  · rintro ⟨⟨⟨z, hz⟩, hA⟩, he⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he
    refine ⟨⟨Option.elim' t z, ?_⟩, ?_⟩
    · change Matrix.of (fun j c => (copiedLayerMatrix B e j c : ℝ)) *ᵥ Option.elim' t z = x
      rw [copiedLayerMatrix_real_mulVec]
      ext j
      cases j with
      | inl j => exact congrFun hz j
      | inr k => exact congrFun ht k
    · change Matrix.of (fun r j => (copiedLayerRows A r j : ℝ)) *ᵥ x = 0
      rw [copiedLayerRows_real_mulVec]
      exact hA

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def preparationHeight (p : ℝ) (depth : ℕ) : ℕ :=
  ⌊Real.exp ((p + 2) ^ budgetDepthExponent 38 depth)⌋₊

theorem preparationExponent_pos (depth : ℕ) : 1 ≤ budgetDepthExponent 38 depth := by
  induction depth with
  | zero => rfl
  | succ d ih => simp only [budgetDepthExponent]; omega

theorem preparationExponent_mono : Monotone (budgetDepthExponent 38) := by
  apply monotone_nat_of_le_succ
  intro d
  simp only [budgetDepthExponent]
  omega

theorem preparationHeight_pos {p : ℝ} (hp : 0 ≤ p) (depth : ℕ) :
    1 ≤ preparationHeight p depth := by
  apply Nat.le_floor
  norm_cast
  exact Real.one_le_exp (by positivity)

theorem preparationHeight_le_exp (p : ℝ) (depth : ℕ) :
    (preparationHeight p depth : ℝ) ≤ Real.exp ((p + 2) ^ budgetDepthExponent 38 depth) :=
  Nat.floor_le (Real.exp_nonneg _)

theorem preparationHeight_mono {p : ℝ} (hp : 0 ≤ p) : Monotone (preparationHeight p) := by
  intro d e hde
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_right₀ (by linarith) (preparationExponent_mono hde)

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

variable {σ : Type*}

theorem polynomialMatrixAction_degree (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) {h : ℕ}
    (hC : ∀ i, C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h) :
    ∀ i, polynomialMatrixAction M C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h := by
  intro i
  exact (weightedSupportLE _ _).sum_mem
    (fun j _ => (weightedSupportLE _ _).smul_mem _ (hC j))

theorem polynomial_affine_origin (M : Matrix (Fin D) (Fin D) R)
    (hM : ∀ i j, i ≤ j → M i j = 0)
    (C₀ : Fin D → MvPolynomial σ R) {h : ℕ}
    (hC : ∀ i, C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h) :
    ∃ P : Fin D → MvPolynomial σ R,
      (∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) h) ∧
      ∀ t : σ → R, (1 - M).mulVec (fun i => aeval t (P i)) =
        (fun i => aeval t (C₀ i)) := by
  refine ⟨polynomialMatrixAction (1 - M)⁻¹ C₀,
    polynomialMatrixAction_degree _ C₀ hC, ?_⟩
  intro t
  rw [polynomialMatrixAction_eval, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (by rw [det_one_sub_strictLower M hM]; exact isUnit_one),
    Matrix.one_mulVec]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget
namespace OAI

section

namespace Erdos3

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox
open scoped BigOperators

def preparedIntegralBasisExponent (m : ℕ) : ℕ :=
  (budgetDepthExponent 38 m + 2) * 124

end Erdos3

end

end OAI
end


