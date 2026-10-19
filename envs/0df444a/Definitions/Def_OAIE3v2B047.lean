-- Prove2me | Definitions.Def_OAIE3v2B047
-- name    : OAIE3v2B047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:00.809772+00:00
-- url     : https://prove2.me/theorems/c9e21acb-af16-48c1-bd38-8c0f1a948483
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 48 of 311
-- statement:
--   Definitions bundle 48 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B012`, `OAIE3v2B013`, `OAIE3v2B014`, `OAIE3v2B015` of this split.
--
--   Modules: `Dynamics/NativeHorizontalLiftBudget.lean`, `Dynamics/SpectralLogBudget.lean`, `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/DenseCyclicFreimanModel.lean`, `Estimates/FiniteFiberTest.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/FreePrimitiveCriterion.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/PreparedFiniteScheduleUniversalMaskProductiveGood.lean`, `Estimates/ProgressionPartitionComposition.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RealProjectedCoefficientLift.lean`, `Estimates/ReplicatedLieAction.lean`, `FixedDensity/AdaptiveCoarseTargetRegularity.lean`, `FixedDensity/BooleanCutReduction.lean`, `FixedDensity/Energy.lean`, `FixedDensity/OrderedCounting.lean`, `FixedDensity/OrderedPattern.lean`, `FixedDensity/OrderedRemoval.lean`, `FixedDensity/SimplexTelescoping.lean`, `FixedDensity/SourceFullCoarseTargetRegularity.lean`, `FixedDensity/StrongOrderedComplexRegularity.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/NaturalFrequencyMultiples.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/LieStructureTransport.lean`, `Geometry/LieTreeSupport.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerVectorFreimanEmbedding.lean`, `Lattices/NativeProperAffineRecovery.lean`, `Linear/BoundedAdaptedBasis.lean`, `Linear/LieWordProjection.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Nilpotent/BCHDenominatorBudget.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/WordTruncationBracket.lean`, `Polynomial/LieCoordinatePolynomials.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Probability/FiniteExcessMassCap.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Sampling/RealGridRationalLift.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
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
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B014
import Definitions.Def_OAIE3v2B015

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3

variable {X : Type*}

section Lie
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dynkinProjection_wordTruncation (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (p : WordPolynomial X) :
    dynkinProjection f (wordTruncation s p) = dynkinProjection f p := by
  apply dynkinProjection_eq_of_low_coeff_eq f hnil
  intro w hw
  simp only [wordTruncation_coeff, hw, ite_true]

end Lie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LieWordProjection
namespace OAI

section

namespace Erdos3

variable {X : Type*}

noncomputable def lieWordSubalgebra : LieSubalgebra ℚ (WordPolynomial X) :=
  LieSubalgebra.lieSpan ℚ (WordPolynomial X)
    (Set.range (fun x : X => MonoidAlgebra.single (FreeSemigroup.of x) (1 : ℚ)))

theorem commutatorTree_mem_lieWordSubalgebra (t : FreeMagma X) :
    commutatorTree t ∈ lieWordSubalgebra := by
  induction t using FreeMagma.rec with
  | of x => exact LieSubalgebra.subset_lieSpan ⟨x, rfl⟩
  | mul u v hu hv => exact lieWordSubalgebra.lie_mem hu hv

theorem freeLieWordExpansion_range :
    (freeLieWordExpansion (X := X)).range = lieWordSubalgebra := by
  apply le_antisymm
  · intro p hp
    obtain ⟨x, rfl⟩ := (LieHom.mem_range _ _).mp hp
    apply freeLie_linear_induction (fun x => freeLieWordExpansion x ∈ lieWordSubalgebra)
    · simpa only [map_zero] using lieWordSubalgebra.zero_mem
    · intro x y hx hy
      rw [map_add]
      exact lieWordSubalgebra.add_mem hx hy
    · intro r x hx
      rw [map_smul]
      exact lieWordSubalgebra.smul_mem r hx
    · intro t
      rw [freeLieWordExpansion_tree]
      exact commutatorTree_mem_lieWordSubalgebra t
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro p ⟨x, rfl⟩
    exact (LieHom.mem_range _ _).mpr ⟨FreeLieAlgebra.of ℚ x, freeLieWordExpansion_of x⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem freeWordCoefficients_embedding (p : WordPolynomial X) (w : FreeSemigroup X) :
    freeWordCoefficients (wordPolynomialEmbedding p) w.toFreeMonoid = p.coeff w := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
      (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid p))).coeff w.toFreeMonoid = _
  rw [AlgEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply FreeSemigroup.toFreeMonoid_injective p.coeff w

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem wordTruncation_homogeneous (s : ℕ) {n : ℕ} {p : WordPolynomial X}
    (hp : WordHomogeneous n p) :
    wordTruncation s p = if n ≤ s then p else 0 := by
  classical
  ext w
  rw [wordTruncation_coeff]
  by_cases hw : p.coeff w = 0
  · simp only [hw]
    split_ifs <;> simp [hw]
  · rw [hp w hw]
    split_ifs <;> rfl

noncomputable def freeLieTruncation (s : ℕ) : FreeLieAlgebra ℚ X →ₗ[ℚ] FreeLieAlgebra ℚ X :=
  (dynkinProjection (FreeLieAlgebra.of ℚ)).comp
    ((wordTruncation s).comp freeLieWordExpansion.toLinearMap)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

namespace FreeCoefficientBound

variable {s D E M N : ℕ} {p q : FreeAlgebra ℚ X}

theorem mono (hp : FreeCoefficientBound s D M p) (hMN : M ≤ N) :
    FreeCoefficientBound s D N p := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  exact ⟨a, ha, hb.trans hMN⟩

theorem zero (s D M : ℕ) : FreeCoefficientBound (X := X) s D M 0 := by
  intro w _
  refine ⟨0, ?_, Nat.zero_le _⟩
  simp

theorem add_same (hp : FreeCoefficientBound s D M p) (hq : FreeCoefficientBound s D N q) :
    FreeCoefficientBound s D (M + N) (p + q) := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  obtain ⟨b, he, hf⟩ := hq w hw
  refine ⟨a + b, ?_, (Int.natAbs_add_le _ _).trans (Nat.add_le_add hb hf)⟩
  simp only [Int.cast_add, map_add, Finsupp.add_apply, mul_add, ha, he]

theorem enlarge_denominator (hp : FreeCoefficientBound s D M p) (E : ℕ) :
    FreeCoefficientBound s (E * D) (E * M) p := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  refine ⟨(E : ℤ) * a, ?_, ?_⟩
  · push_cast
    rw [ha, mul_assoc]
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul_left E hb

theorem sum_finset {ι : Type*} (t : Finset ι) (f : ι → FreeAlgebra ℚ X)
    (hf : ∀ i ∈ t, FreeCoefficientBound s D M (f i)) :
    FreeCoefficientBound s D (t.card * M) (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using zero s D 0
  | @insert i t hi ih =>
    have h := (hf i (Finset.mem_insert_self _ _)).add_same
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.add_mul, one_mul, Nat.add_comm] using h

theorem rationalHeight (hp : FreeCoefficientBound s D M p) (hD : 0 < D)
    (w : FreeMonoid X) (hw : w.length ≤ s) :
    RationalHeightLE (freeWordCoefficients p w) (max D M) := by
  obtain ⟨a, ha, hb⟩ := hp w hw
  have heq : freeWordCoefficients p w = (a : ℚ) / (D : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hD.ne')).mpr
    simpa only [Int.cast_natCast, mul_comm] using ha.symm
  rw [heq]
  apply rationalHeightLE_fraction a (D : ℤ) (by exact_mod_cast hD.ne')
  · exact hb.trans (le_max_right _ _)
  · simpa only [Int.natAbs_natCast] using le_max_left D M

end FreeCoefficientBound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem progressionBlockLabel_eq_iff {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) (n : Fin N) :
    progressionBlockLabel q H hq n = i ↔
      ∃ j < truncatedProgressionLength N (progressionBlockStart i) q H,
        n.val = progressionBlockStart i + q * j := by
  constructor
  · intro hi
    have heq := progressionBlock_reconstruct (H := H) hq n
    rw [hi] at heq
    exact ⟨n.val / q % H,
      (lt_truncatedProgressionLength_iff hq).mpr
        ⟨Nat.mod_lt _ hH, lt_of_eq_of_lt heq n.isLt⟩,
      heq.symm⟩
  · rintro ⟨j, hj, hn⟩
    have hj' := (lt_truncatedProgressionLength_iff hq).mp hj
    have heq := progressionBlockLabel_of_point hq hH i hj'.1 hj'.2
    have hfin : n = ⟨progressionBlockStart i + q * j, hj'.2⟩ := Fin.ext hn
    rwa [← hfin] at heq

noncomputable def progressionBlockEquiv {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) :
    Fin (truncatedProgressionLength N (progressionBlockStart i) q H) ≃
      ↥(partitionCell (progressionBlockLabel q H hq) i) := by
  let point (j : Fin (truncatedProgressionLength N (progressionBlockStart i) q H)) :
      ↥(partitionCell (progressionBlockLabel q H hq) i) :=
    ⟨⟨progressionBlockStart i + q * j.val,
        ((lt_truncatedProgressionLength_iff hq).mp j.isLt).2⟩,
      (mem_partitionCell _ _ _).mpr
        (progressionBlockLabel_of_point hq hH i
          ((lt_truncatedProgressionLength_iff hq).mp j.isLt).1 _)⟩
  apply Equiv.ofBijective point
  constructor
  · intro j k hjk
    apply Fin.ext
    have heq : progressionBlockStart i + q * j.val =
        progressionBlockStart i + q * k.val := congrArg (fun n => n.val.val) hjk
    exact mul_left_cancel₀ hq.ne' (Nat.add_left_cancel heq)
  · intro n
    obtain ⟨j, hj, hn⟩ := (progressionBlockLabel_eq_iff hq hH i n.val).mp
      ((mem_partitionCell _ _ _).mp n.property)
    exact ⟨⟨j, hj⟩, Subtype.ext (Fin.ext hn.symm)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

theorem point_lt (i : P.Label) {j : ℕ} (hj : j < P.length i) :
    P.start i + P.step i * j < N := by
  simpa only [P.point_val] using (P.point i ⟨j, hj⟩).isLt

def whole (N : ℕ) : FiniteProgressionPartition N where
  Label := Unit
  labelFintype := inferInstance
  start := fun _ => 0
  step := fun _ => 1
  length := fun _ => N
  step_pos := fun _ => by decide
  equiv := {
    toFun := fun x => x.2
    invFun := fun n => ⟨(), n⟩
    left_inv := fun ⟨i, j⟩ => by cases i; rfl
    right_inv := fun _ => rfl }
  equiv_val := fun _ _ => by simp

noncomputable def blocks (N q H : ℕ) (hq : 0 < q) (hH : 0 < H) :
    FiniteProgressionPartition N where
  Label := Fin q × Fin (N / q / H + 1)
  labelFintype := inferInstance
  start := progressionBlockStart
  step := fun _ => q
  length := fun i => truncatedProgressionLength N (progressionBlockStart i) q H
  step_pos := fun _ => hq
  equiv := (Equiv.sigmaCongrRight (fun i => (progressionBlockEquiv hq hH i).trans
    (Equiv.subtypeEquivRight (fun n => mem_partitionCell (progressionBlockLabel q H hq) i n)))).trans
    (Equiv.sigmaFiberEquiv (progressionBlockLabel q H hq))
  equiv_val := fun _ _ => rfl

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3

theorem mergedInterval_length_bounds {N H k : ℕ} (hH : 0 < H) (hk : k < N / H) :
    H ≤ mergedIntervalLength N H k ∧ mergedIntervalLength N H k < 2 * H := by
  by_cases hlast : k + 1 = N / H
  · have hstart := mergedInterval_start_le hk
    have hcancel := Nat.sub_add_cancel hstart
    have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
    have hdiv := Nat.mod_add_div N H
    have hrem := Nat.mod_lt N hH
    rw [← hlast] at hq hdiv
    simp only [mergedIntervalLength, hlast, ite_true]
    constructor <;> nlinarith
  · simp only [mergedIntervalLength, hlast, ite_false]
    exact ⟨le_rfl, by omega⟩

end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

theorem mergedIntervals_length_bounds (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    H ≤ (mergedIntervals N H hH hHN).length k ∧
      (mergedIntervals N H hH hHN).length k < 2 * H :=
  mergedInterval_length_bounds hH k.isLt

theorem cell_eq_iff_of_step_one {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (n : Fin N) (k : P.Label) :
    P.cell n = k ↔ P.start k ≤ n.val ∧ n.val < P.start k + P.length k := by
  constructor
  · intro hn
    subst k
    have heq := congrArg Fin.val (P.point_cell_offset n)
    rw [P.point_val, hstep, one_mul] at heq
    have hj := (P.offset n).isLt
    omega
  · rintro ⟨hlo, hhi⟩
    let j : Fin (P.length k) := ⟨n.val - P.start k, by omega⟩
    have heq : P.point k j = n := by
      apply Fin.ext
      rw [P.point_val, hstep, one_mul]
      dsimp only [j]
      omega
    rw [← heq, P.cell_point]

theorem end_le_of_step_one {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (k : P.Label) (hpos : 0 < P.length k) :
    P.start k + P.length k ≤ N := by
  have h := P.point_lt k (j := P.length k - 1) (by omega)
  rw [hstep, one_mul] at h
  omega

end Erdos3.FiniteProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem le_monomialScale_of_ne_zero {σ : Type*} (T : σ → ℝ) {R : ℝ}
    (hR : 1 ≤ R) (hT : ∀ i, R ≤ T i) {α : σ →₀ ℕ} (hα : α ≠ 0) :
    R ≤ monomialScale T α := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hα
    ext i
    exact hn i
  have hTi : 1 ≤ T i := hR.trans (hT i)
  have hp : T i ≤ T i ^ α i := by
    simpa only [pow_one] using pow_le_pow_right₀ hTi (Nat.one_le_iff_ne_zero.mpr hi)
  have hs : ({i} : Finset σ) ⊆ α.support :=
    Finset.singleton_subset_iff.mpr (Finsupp.mem_support_iff.mpr hi)
  have hprod := Finset.prod_le_prod_of_subset_of_one_le hs
    (fun index _ => pow_nonneg (zero_le_one.trans (hR.trans (hT index))) (α index))
    (fun index _ _ => one_le_pow₀ (hR.trans (hT index)))
  exact (hT i).trans (hp.trans (by
    simpa only [Finset.prod_singleton, monomialScale, Finsupp.prod] using hprod))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

noncomputable def correlation (v w : Ω → ℂ) : ℂ :=
  ∑ x, (p.weight x : ℂ) * (v x * star (w x))

theorem norm_correlation_symm (v w : Ω → ℂ) :
    ‖p.correlation v w‖ = ‖p.correlation w v‖ := by
  have h : star (p.correlation v w) = p.correlation w v := by
    unfold correlation
    simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [← h, norm_star]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

noncomputable def pointWeights {Y : Type*} [Fintype Y] (y : Y) : FiniteProbabilityWeights Y where
  weight z := if z = y then 1 else 0
  nonneg z := by split_ifs <;> norm_num
  total := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hz
      simp [hz]
    · simp

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem lie_coordinate_formula (e : Basis ι ℚ L) (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ ij : ι × ι, lieStructureConstants e ij.1 ij.2 k * e.repr a ij.1 * e.repr b ij.2 := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    lieStructureConstants, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieStructureTransport
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

omit [Fintype κ] in
theorem transportedLieConstants_formula (e : Basis ι ℚ L) (P : Matrix κ ι ℚ)
    (S : Matrix ι κ ℚ) (a b : L) (i j k : κ)
    (ha : ∀ u, e.repr a u = S u i) (hb : ∀ u, e.repr b u = S u j) :
    (P *ᵥ e.repr ⁅a, b⁆) k = transportedLieConstants (lieStructureConstants e) P S i j k := by
  classical
  simp only [Matrix.mulVec, dotProduct, transportedLieConstants, lie_coordinate_formula,
    ha, hb, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in

theorem lieStructureConstants_embedding (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (P : Matrix κ ι ℚ)
    (hP : P * LinearMap.toMatrix b e φ.toLinearMap = 1) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      P (LinearMap.toMatrix b e φ.toLinearMap) i j k := by
  have hretract (x : M) : P *ᵥ e.repr (φ x) = b.repr x := by
    change P *ᵥ e.repr (φ.toLinearMap x) = b.repr x
    rw [← LinearMap.toMatrix_mulVec_repr b e φ.toLinearMap x, Matrix.mulVec_mulVec,
      hP, Matrix.one_mulVec]
  rw [lieStructureConstants, ← congrFun (hretract ⁅b i, b j⁆) k, LieHom.map_lie]
  apply transportedLieConstants_formula
  · intro u
    exact (LinearMap.toMatrix_apply b e φ.toLinearMap u i).symm
  · intro u
    exact (LinearMap.toMatrix_apply b e φ.toLinearMap u j).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHDenominatorBudget
namespace OAI

section

namespace Erdos3

theorem lieCoordinateHeight_le_exp (d H n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (lieCoordinateHeight d H n : ℝ) ≤ Real.exp ((p + 2) ^ (3 * n + 2)) := by
  have hd2 : (d : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg d) hd 2
  have hpexp : Real.exp p ≤ Real.exp (p ^ 2 + 1) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p - 1)])
  have hsmall : (d : ℝ) ^ 2 + 2 ≤ Real.exp (p ^ 2 + 1) := by
    have h := Real.add_one_le_exp (p ^ 2 + 1)
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hbase : (d : ℝ) ^ 2 + H + 2 ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ 2 * Real.exp (p ^ 2 + 1) := by linarith [hH.trans hpexp]
      _ ≤ Real.exp 1 * Real.exp (p ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (p ^ 2 + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hexponent : ((2 * d ^ 2 + 2) ^ n : ℕ) ≤ (p + 2) ^ (3 * n) := by
    push_cast
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [pow_nonneg hp 3]
  unfold lieCoordinateHeight
  push_cast
  calc
    _ ≤ (Real.exp ((p + 2) ^ 2)) ^ ((2 * d ^ 2 + 2) ^ n) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((((2 * d ^ 2 + 2) ^ n : ℕ) : ℝ) * (p + 2) ^ 2) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (3 * n) * (p + 2) ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexponent (by positivity))
    _ = _ := by rw [pow_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dynkinWord_eq_zero_of_abelian [IsLieAbelian L] (f : X → L)
    (w : FreeSemigroup X) (hw : w.tail ≠ []) : dynkinWord f w = 0 := by
  unfold dynkinWord
  cases h : w.tail with
  | nil => exact False.elim (hw h)
  | cons x xs =>
      simp only [rightBracketList_cons, Module.End.mul_apply, rightBracket_apply,
        trivial_lie_zero, map_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [DecidableEq ι] [DecidableEq κ]

theorem rationalLieStructureHeight_inverse_budget (d r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalLieStructureHeight d (max H (rationalSolveHeight r H)) : ℝ) ≤
      Real.exp ((p + 2) ^ 11) := by
  apply rationalLieStructureHeight_le_exp d _ hp hd 5
  rw [Nat.cast_max]
  apply max_le
  · exact hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 5)))
  · exact rationalSolveHeight_le_budget r H hp hr hH

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

def scalarCubeDifferenceMatrix {I J : Type*} {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) : Matrix I J ℤ :=
  sampledColumnMatrix (fun _j y i => (y (some i) : ℤ)) x


open scoped BigOperators

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d n : ℕ}

theorem centralLieBasis_of_finite_flag (P : ℕ → Submodule ℚ L)
    (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hzero : P 0 = ⊤) (hterminal : P n = ⊥)
    (hstep : ∀ i, ∀ {x y : L}, y ∈ P i → ⁅x, y⁆ ∈ P (i + 1))
    (hw : Monotone w)
    (hspan : ∀ i : Fin (n + 1), P i.val = Submodule.span ℚ (e '' {j | i.val < w j})) :
    IsCentralLieBasis e := by
  intro j a
  have hjn : w j ≤ n := finite_flag_weight_le P e w hterminal (hspan ⟨n, by omega⟩) j
  have hbr : ⁅a, e j⁆ ∈ P (w j) := by
    cases hweight : w j with
    | zero => simp only [hzero, Submodule.mem_top]
    | succ k =>
        apply hstep k
        rw [hspan ⟨k, by omega⟩]
        exact Submodule.subset_span ⟨j, by change k < w j; omega, rfl⟩
  rw [hspan ⟨w j, by omega⟩] at hbr
  rw [basisTail_eq_span]
  apply Submodule.span_mono (Set.image_mono ?_) hbr
  intro k hk
  change j.val + 1 ≤ k.val
  change w j < w k at hk
  by_contra h
  have hkj : k ≤ j := by change k.val ≤ j.val; omega
  exact (not_lt_of_ge (hw hkj)) hk

end Erdos3

end

section

namespace Erdos3

open Module

theorem span_weight_gt_eq_basisTail {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ) (hw : Monotone w) (k : ℕ) :
    Submodule.span ℚ (b '' {j | k < w j}) = basisTail b (weightCut w k) := by
  rw [basisTail_eq_span]
  apply congrArg (Submodule.span ℚ)
  apply congrArg (fun S : Set (Fin d) => b '' S)
  ext j
  exact weight_gt_iff_cut_le w hw k j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightBracketList_mem_intModule (M : Submodule ℤ L)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ M)
    (f : X → L) (hf : ∀ x, f x ∈ M) (xs : List X) {z : L} (hz : z ∈ M) :
    rightBracketList f xs z ∈ M := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih => exact ih (hbr z hz (f x) (hf x))

theorem dynkinWord_mem_multiple (M : Submodule ℤ L) (D : ℕ)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (f : X → L) (hf : ∀ x, f x ∈ M) (w : FreeSemigroup X) (hw : w.tail ≠ []) :
    ∃ z ∈ M, dynkinWord f w = (D : ℚ) • z := by
  have hclosed : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ M := by
    intro a ha b hb
    obtain ⟨z, hz, heq⟩ := hbr a ha b hb
    rw [heq]
    exact rational_nat_smul_mem M hz D
  cases htail : w.tail with
  | nil => exact False.elim (hw htail)
  | cons x xs =>
      obtain ⟨z, hz, heq⟩ := hbr (f w.head) (hf _) (f x) (hf _)
      refine ⟨rightBracketList f xs z, rightBracketList_mem_intModule M hclosed f hf xs hz, ?_⟩
      simp only [dynkinWord, htail, rightBracketList_cons, Module.End.mul_apply,
        rightBracket_apply, heq, map_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieTreeSupport
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

theorem lieTreeEval_eq_zero_of_leaf (v : I → L) (a : FreeMagma I) {i : I}
    (hi : i ∈ lieTreeSupport a) (hv : v i = 0) : lieTreeEval v a = 0 := by
  induction a using FreeMagma.rec with
  | of j =>
    have hij : i = j := hi
    simpa only [lieTreeEval, ← hij] using hv
  | mul a b ha hb =>
    rcases hi with hi | hi
    · change ⁅lieTreeEval v a, lieTreeEval v b⁆ = 0
      rw [ha hi, zero_lie]
    · change ⁅lieTreeEval v a, lieTreeEval v b⁆ = 0
      rw [hb hi, lie_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

theorem lieTreeHeight_le_coordinateHeight (d H n : ℕ) :
    lieTreeHeight d H n ≤ lieCoordinateHeight d H (2 * n) := by
  unfold lieTreeHeight lieCoordinateHeight
  apply Nat.pow_le_pow_right (by omega)
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  nlinarith [sq_nonneg (d : ℤ)]

theorem lieTreeHeight_le_exp (d H n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (lieTreeHeight d H n : ℝ) ≤ Real.exp ((p + 2) ^ (6 * n + 2)) := by
  have h := lieCoordinateHeight_le_exp d H (2 * n) hp hd hH
  have hle : (lieTreeHeight d H n : ℝ) ≤ lieCoordinateHeight d H (2 * n) := by
    exact_mod_cast lieTreeHeight_le_coordinateHeight d H n
  simpa only [show 3 * (2 * n) + 2 = 6 * n + 2 by omega] using hle.trans h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def imageDefiningHeight (d n H : ℕ) : ℕ :=
  2 * ((d + 1) * (H * rationalKernelHeight n H) ^ d)

theorem imageDefiningHeight_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (imageDefiningHeight d n H : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
  have hK := rationalKernelHeight_le_budget n H hp hn hH
  have hp7 : p ≤ (p + 2) ^ 7 := le_power_budget hp (by decide)
  have hbase : (H : ℝ) * rationalKernelHeight n H ≤ Real.exp ((p + 2) ^ 8) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + 2) ^ 7) := mul_le_mul hH hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p + (p + 2) ^ 7) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          p + (p + 2) ^ 7 ≤ 2 * (p + 2) ^ 7 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 7 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (p + 2) ^ 8 := by ring
  have hpow : (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
    rw [Nat.cast_pow, Nat.cast_mul]
    apply (pow_le_pow_left₀ (by positivity) hbase d).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (d : ℝ) * (p + 2) ^ 8 ≤ (p + 2) * (p + 2) ^ 8 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p + 2) ^ 9 := by ring
  have hfront : 2 * ((d : ℝ) + 1) ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul htwo ((by linarith : (d : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  change ((2 * ((d + 1) * (H * rationalKernelHeight n H) ^ d) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc
    2 * (((d : ℝ) + 1) * (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ)) =
        (2 * ((d : ℝ) + 1)) * (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ) := by ring
    _ ≤ Real.exp (p + 1) * Real.exp ((p + 2) ^ 9) := mul_le_mul hfront hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + 1 + (p + 2) ^ 9) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hp9 : p + 1 ≤ (p + 2) ^ 9 := by
        apply (show p + 1 ≤ p + 2 by linarith).trans
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 1 ≤ 9)
      calc
        p + 1 + (p + 2) ^ 9 ≤ 2 * (p + 2) ^ 9 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (p + 2) ^ 10 := by ring

theorem imageSection_bound_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (coordinateLipschitzBound d n (rationalKernelHeight n H) : ℝ) ≤ Real.exp ((p + 2) ^ 18) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 7)
  have h := coordinateLipschitzBound_le_exp d n (rationalKernelHeight n H)
    (by positivity : 0 ≤ (p + 2) ^ 7) (hd.trans hpp) (hn.trans hpp)
    (by exact_mod_cast rationalKernelHeight_le_budget n H hp hn hH)
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 7 2))

theorem imageDefiningRow_bound_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * ((imageDefiningHeight d n H : ℝ) + 1) ≤ Real.exp ((p + 2) ^ 24) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have h := coordinateLipschitzBound_le_exp n n (imageDefiningHeight d n H)
    (by positivity : 0 ≤ (p + 2) ^ 10) (hn.trans hpp) (hn.trans hpp)
    (by exact_mod_cast imageDefiningHeight_le_exp d n H hp hd hn hH)
  apply le_trans _ (h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 2)))
  change _ ≤ ((n : ℝ) + n + 1) * ((imageDefiningHeight d n H : ℝ) + 1)
  gcongr
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SpectralLogBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem spectralIterations_pos (epsilon p : ℝ) : 0 < spectralIterations epsilon p := by
  unfold spectralIterations
  omega

theorem spectralIterations_le {epsilon p : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) :
    (spectralIterations epsilon p : ℝ) ≤ spectralIterationFactor epsilon * (p + 1) := by
  have hlog : 0 ≤ Real.log (16 / epsilon) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hepsilon]
    linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (p + Real.log (16 / epsilon)) / Real.log 2 by positivity)
  have hfirst : (spectralIterations epsilon p : ℝ) ≤
      (p + Real.log (16 / epsilon)) / Real.log 2 + 2 := by
    unfold spectralIterations
    push_cast
    linarith
  apply hfirst.trans
  unfold spectralIterationFactor
  apply (le_of_sub_nonneg ?_)
  have hid : ((1 + Real.log (16 / epsilon)) / Real.log 2 + 2) * (p + 1) -
      ((p + Real.log (16 / epsilon)) / Real.log 2 + 2) =
      (1 + p * Real.log (16 / epsilon)) / Real.log 2 + 2 * p := by ring
  rw [hid]
  positivity

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

open scoped Matrix NNReal

namespace Erdos3

theorem real_matrix_image_section_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ) (hS : A * S * A = A)
    (y : ι → ℝ) (hy : y ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ)))) :
    (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y) = y := by
  obtain ⟨x, rfl⟩ := hy
  change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
    (Matrix.of (fun i j => (S i j : ℝ)) *ᵥ
      (Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x)) =
    Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, real_matrix_image_section A S hS]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCyclicFreimanModel
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclic_model (A : Finset ℤ) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (hsmall : ((A - A).card : ℝ) ≤ K * A.card)
    (s : ℕ) (hs : 0 < s) :
    ∃ (N : ℕ) (A' : Finset ℤ) (B : Finset (ZMod N)) (f : ℤ → ZMod N),
      0 < N ∧ A'.Nonempty ∧ A' ⊆ A ∧ A.card ≤ (2 * s) * A'.card ∧
      B.Nonempty ∧ B = A'.image f ∧ B.card = A'.card ∧
      IsAddFreimanIso s (A' : Set ℤ) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card ∧
      (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  let D := s • A - s • A
  have hD : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate s a).sum ∈ s • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate s a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hN : 0 < 2 * D.card := Nat.mul_pos (by decide) hD.card_pos
  obtain ⟨A', B, f, hA'ne, hA'sub, hsize, hB, hf⟩ :=
    exists_large_cyclic_freiman_model A s hA hs
  have hBcard : B.card = A'.card := by
    rw [hB]
    exact Finset.card_image_of_injOn hf.bijOn.injOn
  have hBne : B.Nonempty := Finset.card_pos.mp (hBcard ▸ hA'ne.card_pos)
  have hDsize : (D.card : ℝ) ≤ K ^ (2 * s) * A.card := by
    simpa only [D, two_mul] using Erdos3.higher_difference_card_le A hA hsmall s s
  have hNsize : ((2 * D.card : ℕ) : ℝ) ≤ 2 * K ^ (2 * s) * A.card := by
    push_cast
    calc
      2 * (D.card : ℝ) ≤ 2 * (K ^ (2 * s) * A.card) :=
        mul_le_mul_of_nonneg_left hDsize (by norm_num)
      _ = _ := by ring
  have hsizeR : (A.card : ℝ) ≤ (2 * (s : ℝ)) * B.card := by
    rw [hBcard]
    exact_mod_cast hsize
  have hmodelSize : ((2 * D.card : ℕ) : ℝ) ≤
      (4 * (s : ℝ) * K ^ (2 * s)) * B.card := by
    calc
      ((2 * D.card : ℕ) : ℝ) ≤ 2 * K ^ (2 * s) * A.card := hNsize
      _ ≤ 2 * K ^ (2 * s) * ((2 * (s : ℝ)) * B.card) :=
        mul_le_mul_of_nonneg_left hsizeR (by positivity)
      _ = _ := by ring
  have hdensity : (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤
      (B.card : ℝ) / (2 * D.card : ℕ) := by
    apply (le_div_iff₀ (by exact_mod_cast hN)).mpr
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hmodelSize
  exact ⟨2 * D.card, A', B, f, hN, hA'ne, hA'sub, hsize, hBne, hB,
    hBcard, hf, hNsize, hdensity⟩

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealGridRationalLift
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realDenominatorGrid_exists_rational {ι : Type*} (l : ℕ) (hl : 0 < l)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ∃ y : ι → ℚ, y ∈ denominatorGrid l ∧ (fun i => (y i : ℝ)) = x := by
  obtain ⟨z, hz⟩ := hx
  let y : ι → ℚ := fun i => (z i : ℚ) / l
  have hy : (fun i => (y i : ℝ)) = x := by
    funext i
    change (((z i : ℚ) / l : ℚ) : ℝ) = x i
    push_cast
    apply (div_eq_iff (show (l : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hl.ne')).mpr
    have hi := congrFun hz i
    change (z i : ℝ) = (l : ℝ) * x i at hi
    simpa only [mul_comm] using hi
  refine ⟨y, (real_cast_mem_denominatorGrid_iff l y).mp ?_, hy⟩
  rw [hy]
  exact ⟨z, hz⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*}

theorem replicatedIndex_card [Fintype σ] (bound : σ → ℕ) :
    Fintype.card (ReplicatedIndex bound) = ∑ i, bound i := by
  simp only [ReplicatedIndex, Fintype.card_sigma, Fintype.card_fin]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem matrix_weighted_factor_le_exp_power (n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a) :
    ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ a) + 1) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
  have hA : 1 ≤ (p + 2) ^ a := one_le_pow₀ (by linarith)
  have hpA : p ≤ (p + 2) ^ a := le_power_budget hp ha
  have hplus : Real.exp ((p + 2) ^ a) + 1 ≤ Real.exp ((p + 2) ^ a + 1) := by
    calc
      _ ≤ Real.exp ((p + 2) ^ a) * 2 := by
        have h := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ (p + 2) ^ a)
        linarith
      _ ≤ Real.exp ((p + 2) ^ a) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ a + 1) :=
      mul_le_mul (by linarith [Real.add_one_le_exp p]) hplus (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + ((p + 2) ^ a + 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (a + 2)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 3 * (p + 2) ^ a := by linarith
        _ ≤ (p + 2) ^ 2 * (p + 2) ^ a :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by rw [pow_add]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
namespace OAI

section

namespace Erdos3

theorem lieTreeEval_hom {I L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] (φ : L →ₗ⁅ℚ⁆ M) (v : I → L) (a : FreeMagma I) :
    lieTreeEval (fun i => φ (v i)) a = φ (lieTreeEval v a) := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    simp only [lieTreeEval, ha, hb, LieHom.map_lie]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

theorem realQuotientCoordinateMap_tmul_one (f : Basis ι ℚ (L ⧸ V)) (x : L) (i : ι) :
    realQuotientCoordinateMap f ((1 : ℝ) ⊗ₜ[ℚ] x) i = (f.repr (V.mkQ x) i : ℝ) := by
  rw [realQuotientCoordinateMap_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype μ] {V : Submodule ℚ L}

omit [Fintype ι] in
theorem realQuotientCoordinateMap_eq_matrix (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    (x : ℝ ⊗[ℚ] L) :
    realQuotientCoordinateMap f x =
      (fun i j => (quotientCoordinateMatrix b f i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x := by
  classical
  have h : (realQuotientCoordinateMap f).comp
      (b.baseChange ℝ).equivFun.symm.toLinearMap =
        Matrix.mulVecLin (fun i j => (quotientCoordinateMatrix b f i j : ℝ)) := by
    apply (Pi.basisFun ℝ μ).ext
    intro j
    change realQuotientCoordinateMap f ((b.baseChange ℝ).equivFun.symm (Pi.single j 1)) =
      Matrix.of (fun i n => (quotientCoordinateMatrix b f i n : ℝ)) *ᵥ Pi.single j 1
    rw [Basis.equivFun_symm_single, Matrix.mulVec_single_one, Basis.baseChange_apply]
    funext i
    exact realQuotientCoordinateMap_tmul_one f (b j) i
  have hx := DFunLike.congr_fun h ((b.baseChange ℝ).equivFun x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  exact hx.trans (Matrix.mulVecLin_apply _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WordTruncationBracket
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem wordTruncation_eq_zero_iff (s : ℕ) (p : WordPolynomial X) :
    wordTruncation s p = 0 ↔ ∀ w, w.length ≤ s → p.coeff w = 0 := by
  simpa using wordTruncation_eq_iff s p 0

theorem wordTruncation_succ_mul_eq_zero (s : ℕ) (p q : WordPolynomial X)
    (h : wordTruncation s p = 0 ∨ wordTruncation s q = 0) :
    wordTruncation (s + 1) (p * q) = 0 := by
  classical
  apply (wordTruncation_eq_zero_iff _ _).mpr
  intro w hw
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hne : u * v ≠ w := by
    intro he
    have hlen : u.length + v.length ≤ s + 1 := by
      simpa only [← he, FreeSemigroup.length_mul] using hw
    have hu0 : 0 < u.length := by change 0 < u.tail.length + 1; omega
    have hv0 : 0 < v.length := by change 0 < v.tail.length + 1; omega
    rcases h with hp | hq
    · exact (Finsupp.mem_support_iff.mp hu)
        ((wordTruncation_eq_zero_iff s p).mp hp u (by omega))
    · exact (Finsupp.mem_support_iff.mp hv)
        ((wordTruncation_eq_zero_iff s q).mp hq v (by omega))
  simp only [hne, ite_false]

theorem wordTruncation_succ_lie_eq_zero (s : ℕ) (p q : WordPolynomial X)
    (hq : wordTruncation s q = 0) : wordTruncation (s + 1) ⁅p, q⁆ = 0 := by
  rw [wordPolynomial_lie, map_sub, wordTruncation_succ_mul_eq_zero s p q (Or.inr hq),
    wordTruncation_succ_mul_eq_zero s q p (Or.inl hq), sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

noncomputable instance instRealTopology (d : ℕ) : TopologicalSpace (ℝ ⊗[ℚ] Algebra d) :=
  moduleTopology ℝ (ℝ ⊗[ℚ] Algebra d)

instance instRealTopologicalAddGroup (d : ℕ) : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d) :=
  IsModuleTopology.topologicalAddGroup ℝ _

instance instRealT2Space (d : ℕ) : T2Space (ℝ ⊗[ℚ] Algebra d) :=
  realification_moduleTopology_t2 (basis d)

end Erdos3.RationalTorus

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

noncomputable def samplingRankProjection (a : J → ℤ) (e : J → ℝ) :
    (J → ℝ) →ₗ[ℝ] (J → ℝ) :=
  LinearMap.id - (integerRowLinear a).smulRight e

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteExcessMassCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

noncomputable def excessMass {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) : ℝ :=
  ∑ x, max (q.weight x - C * p.weight x) 0

theorem excessMass_nonneg {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) : 0 ≤ p.excessMass q C :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem excessMass_antitone_cap {X : Type*} [Fintype X]
    (reference law : FiniteProbabilityWeights X) :
    Antitone (reference.excessMass law) := by
  intro C D hCD
  apply Finset.sum_le_sum
  intro x _
  exact max_le_max (sub_le_sub_left
    (mul_le_mul_of_nonneg_right hCD (reference.nonneg x)) _) le_rfl

theorem excessMass_max_one_le {X : Type*} [Fintype X]
    (reference law : FiniteProbabilityWeights X) (C : ℝ) :
    reference.excessMass law (max 1 C) ≤ reference.excessMass law C :=
  reference.excessMass_antitone_cap law (le_max_right _ _)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NaturalFrequencyMultiples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_nsmul {L : Type*} [AddCommGroup L] [Module ℚ L]
    (n : ℕ) (η : L →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] L) :
    realifyFunctional (n • η) x = n • realifyFunctional η x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, LinearMap.smul_apply, nsmul_eq_mul,
      Rat.cast_mul, Rat.cast_natCast]
    ring
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerVectorFreimanEmbedding
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped BigOperators Pointwise

theorem exists_integer_vector_embedding {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) : ∃ f : (I → ℤ) →+ ℤ, Set.InjOn f (A : Set _) := by
  classical
  let e := Fintype.equivFin I
  let r : (I → ℤ) →+ (Fin (Fintype.card I) → ℤ) :=
    { toFun := fun x j => x (e.symm j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hr : Function.Injective r := by
    intro x y h
    funext i
    simpa only [r, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply] using
      congrFun h (e i)
  obtain ⟨f, hf⟩ := exists_fin_integer_embedding (A.image r)
  refine ⟨f.comp r, ?_⟩
  intro x hx y hy hxy
  exact hr (hf (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩) hxy)

theorem isAddFreimanIso_of_injOn_iterated_sums
    {G H : Type*} [AddCommMonoid G] [AddCommMonoid H] [DecidableEq G] [DecidableEq H]
    (f : G →+ H) (A : Finset G) (s : ℕ) (hinj : Set.InjOn f (A : Set G))
    (hsinj : Set.InjOn f (s • A : Finset G)) :
    IsAddFreimanIso s (A : Set G) (A.image f : Set H) f := by
  refine ⟨⟨?_, hinj, ?_⟩, ?_⟩
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro y hy
    exact Finset.mem_image.mp hy
  · intro T U hT hU hTc hUc
    rw [← map_multiset_sum, ← map_multiset_sum]
    have hTs : T.sum ∈ s • A := by
      simpa only [hTc] using multiset_sum_mem_iterated_sumset A (fun x hx => hT hx)
    have hUs : U.sum ∈ s • A := by
      simpa only [hUc] using multiset_sum_mem_iterated_sumset A (fun x hx => hU hx)
    exact ⟨fun h => hsinj hTs hUs h, congrArg f⟩

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery
namespace OAI

section

namespace Erdos3.FreimanModel

theorem residueLift_sum_cast {q : ℕ} [NeZero q] (T : Multiset (ZMod q)) :
    (((T.map residueLift).sum : ℤ) : ZMod q) = T.sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Int.cast_add, ih]
      simp [residueLift]

theorem residueLift_sum_eq_iff {q : ℕ} [NeZero q] {c : Fin 16}
    (T U : Multiset (ZMod q)) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, residueBlock x = c) (hcU : ∀ x ∈ U, residueBlock x = c) :
    (T.map residueLift).sum = (U.map residueLift).sum ↔ T.sum = U.sum := by
  constructor
  · intro h
    simpa only [residueLift_sum_cast] using congrArg (fun z : ℤ => (z : ZMod q)) h
  · intro h
    have hsmall := abs_lt.mp (residueLift_sum_sub_abs_lt T U hT hU hcT hcU)
    have hdiv : (q : ℤ) ∣ (T.map residueLift).sum - (U.map residueLift).sum := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
      rw [Int.cast_sub, residueLift_sum_cast, residueLift_sum_cast, h, sub_self]
    apply sub_eq_zero.mp
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
    simpa only [Int.natAbs_natCast] using
      int_natAbs_lt_of_neg_lt_and_lt hsmall.1 hsmall.2

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

variable {I : Type*} (q : I → ℕ) [∀ i, NeZero (q i)]

omit [∀ i, NeZero (q i)] in
theorem cyclicProduct_sum_apply (T : Multiset (∀ i, ZMod (q i))) (i : I) :
    T.sum i = (T.map fun x => x i).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih => simp [ih]

theorem cyclicProductLift_sum_eq_iff {c : I → Fin 16}
    (T U : Multiset (∀ i, ZMod (q i))) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, cyclicProductBlock q x = c)
    (hcU : ∀ x ∈ U, cyclicProductBlock q x = c) :
    (T.map (cyclicProductLift q)).sum = (U.map (cyclicProductLift q)).sum ↔ T.sum = U.sum := by
  have hi (i : I) :
      ((T.map (cyclicProductLift q)).sum) i = ((U.map (cyclicProductLift q)).sum) i ↔
        T.sum i = U.sum i := by
    rw [cyclicProductLift_sum_apply, cyclicProductLift_sum_apply,
      cyclicProduct_sum_apply, cyclicProduct_sum_apply]
    have ht : ∀ x ∈ T.map (fun x => x i), residueBlock x = c i := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact congrFun (hcT y hy) i
    have hu : ∀ x ∈ U.map (fun x => x i), residueBlock x = c i := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact congrFun (hcU y hy) i
    simpa only [Multiset.map_map, Function.comp_def] using
      residueLift_sum_eq_iff (T.map fun x => x i) (U.map fun x => x i)
        (by simpa only [Multiset.card_map] using hT)
        (by simpa only [Multiset.card_map] using hU) ht hu
  constructor
  · intro h
    funext i
    exact (hi i).mp (congrFun h i)
  · intro h
    funext i
    exact (hi i).mpr (congrFun h i)

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {I : Type*}

def variableIntegerGraphLift (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) : Option I → ℤ :=
  cyclicProductLift (variableRoundedGraphModuli N M)
    (variableRoundedGraphCoordinateEquiv N M x)

@[simp] theorem variableIntegerGraphReduction_lift (N : ℕ) (M : I → ℕ)
    [NeZero N] [∀ i, NeZero (M i)] (x : ZMod N × (∀ i, ZMod (M i))) :
    variableIntegerGraphReduction N M (variableIntegerGraphLift N M x) = x := by
  apply Prod.ext
  · change (((x.1.val : ℤ) : ZMod N)) = x.1
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  · funext i
    change ((((x.2 i).val : ℤ) : ZMod (M i))) = x.2 i
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

@[simp] theorem variableIntegerGraphLift_none (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) :
    variableIntegerGraphLift N M x none = (x.1.val : ℤ) := rfl

@[simp] theorem variableIntegerGraphLift_some (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) (i : I) :
    variableIntegerGraphLift N M x (some i) = ((x.2 i).val : ℤ) := rfl

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3

def mixedExchangeCoordinate (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem conditionalMean_smul {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => c * f y) x =
      c * conditionalMean P f x := by
  exact (Finset.mul_expect (P.part x) f c).symm

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

namespace FacePartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem le_iff_part_subset {P Q : FacePartition Ω} :
    P ≤ Q ↔ ∀ x, P.part x ⊆ Q.part x := by
  constructor
  · exact fun h x => part_subset_of_le h x
  · intro h s hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    refine ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x), ?_⟩
    rw [← P.part_eq_of_mem hs hx]
    exact h x

noncomputable def representative
    (P : FacePartition Ω) (a : P.parts) : Ω :=
  Classical.choose (P.nonempty_of_mem_parts a.2)

theorem join_le_left (P Q : FacePartition Ω) :
    join P Q ≤ P :=
  inf_le_left

theorem le_join_iff {P Q R : FacePartition Ω} :
    R ≤ join P Q ↔ R ≤ P ∧ R ≤ Q :=
  le_inf_iff

theorem complexity_join_le (P Q : FacePartition Ω) :
    complexity (join P Q) ≤ complexity P * complexity Q := by
  change (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card
  calc
    (P ⊓ Q).parts.card =
        (((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).erase ⊥).card :=
      congrArg Finset.card (Finpartition.parts_inf P Q)
    _ ≤
        ((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ (P.parts ×ˢ Q.parts).card :=
      Finset.card_image_le
    _ = P.parts.card * Q.parts.card :=
      Finset.card_product P.parts Q.parts

theorem joinFinset_le_of_mem {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (P : ι → FacePartition Ω)
    {i : ι} (hi : i ∈ s) :
    joinFinset s P ≤ P i :=
  Finset.inf_le hi

theorem le_joinFinset_iff {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {P : ι → FacePartition Ω}
    {Q : FacePartition Ω} :
    Q ≤ joinFinset s P ↔ ∀ i ∈ s, Q ≤ P i :=
  Finset.le_inf_iff

theorem mem_part_joinFinset_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω)
    (x y : Ω) :
    y ∈ (joinFinset s P).part x ↔
      ∀ i ∈ s, y ∈ (P i).part x := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [joinFinset_empty]
      simp
  | @insert a s ha ih =>
      simp only [joinFinset_insert, part_join,
        Finset.mem_inter, Finset.mem_insert, forall_eq_or_imp,
        ih]

theorem generatedBy_antitone {F G : Finset (Finset Ω)}
    (hFG : F ⊆ G) :
    generatedBy G ≤ generatedBy F := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_generatedBy_iff] at hy ⊢
  intro s hs
  exact hy s (hFG hs)

theorem mem_part_pullback_iff_image_mem {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      f y ∈ Q.part (f x) := by
  rw [mem_part_pullback_iff]
  constructor
  · intro h
    exact
      (Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).2 h.symm
  · intro h
    exact
      ((Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).1 h).symm

theorem pullback_mono {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) {P Q : FacePartition Λ}
    (h : P ≤ Q) :
    pullback f P ≤ pullback f Q := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_pullback_iff_image_mem] at hy ⊢
  exact part_subset_of_le h (f x) hy

end FacePartition

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem conditionalMean_mul_right_of_constant_on_part
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω)
    (hv : ∀ y ∈ P.part x, v y = v x) :
    conditionalMean P (fun y => u y * v y) x =
      conditionalMean P u x * v x := by
  calc
    conditionalMean P (fun y => u y * v y) x =
        conditionalMean P (fun y => v x * u y) x := by
      rw [conditionalMean, conditionalMean]
      apply Finset.expect_congr rfl
      intro y hy
      rw [hv y hy]
      ring
    _ = v x * conditionalMean P u x :=
      conditionalMean_smul P (v x) u x
    _ = conditionalMean P u x * v x := by
      ring

theorem conditionalMean_mul_conditionalMean_right
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω) :
    conditionalMean P
        (fun y => u y * conditionalMean P v y) x =
      conditionalMean P u x * conditionalMean P v x := by
  apply conditionalMean_mul_right_of_constant_on_part
  intro y hy
  exact conditionalMean_eq_of_mem_part P v hy

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleUniversalMaskProductiveGood
namespace OAI

section

namespace Erdos3

attribute [instance] FinitePrecenterInputFamily.branchFintype

structure FinitePrecenterSelectedModels (X : Type*) where
  Branch : Type
  [branchFintype : Fintype Branch]
  input : Branch → X → ℂ
  models : Branch → CenteredForecastModel X

attribute [instance] FinitePrecenterSelectedModels.branchFintype

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SimplexTelescoping
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace WeightedSimplexSystem

def simplexWeight {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) (x : (i : Fin k) → V i) : ℝ :=
  ∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)

end WeightedSimplexSystem

def apSimplexSystem (k N : ℕ) (f : ZMod N → ℝ) :
    WeightedSimplexSystem (fun _ : Fin k => ZMod N) where
  edgeWeight j x := f (apSimplexForm k N j x)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def simplexAPEquiv (r N : ℕ) :
    (Fin (r + 2) → ZMod N) ≃
      (ZMod N × ZMod N) × (Fin r → ZMod N) where
  toFun x :=
    ((simplexCoordinateMoment (r + 2) N x,
      -simplexCoordinateSum (r + 2) N x),
      fun i => x i.succ.succ)
  invFun y := simplexCoordinatesOfAP r N y.1.1 y.1.2 y.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => rfl) i) i
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 0 =
          x 0
      rw [simplexCoordinatesOfAP_zero,
        simplexCoordinateMoment_decompose,
        simplexCoordinateSum_decompose]
      ring
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 1 =
          x 1
      rw [simplexCoordinatesOfAP_one,
        simplexCoordinateMoment_decompose]
      ring
  right_inv y := by
    rcases y with ⟨⟨a, d⟩, tail⟩
    apply Prod.ext
    · apply Prod.ext
      · change
          simplexCoordinateMoment (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            a
        exact simplexCoordinateMoment_coordinatesOfAP r N a d tail
      · change
          -simplexCoordinateSum (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            d
        rw [simplexCoordinateSum_coordinatesOfAP]
        simp
    · funext i
      change simplexCoordinatesOfAP r N a d tail i.succ.succ = tail i
      exact simplexCoordinatesOfAP_succ_succ r N a d tail i

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def IsBoundedCutTest {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) : Prop :=
  (∀ i x, 0 ≤ u i x) ∧ (∀ i x, u i x ≤ 1)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPattern
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace WeightedOrderedPattern

noncomputable def patternWeight
    {G : Type*} {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (x : Fin k → G) : ℝ :=
  ∏ e : OrderedFace k r,
    H.edgeWeight e (orderedFaceTuple e x)

end WeightedOrderedPattern

namespace OrderedPattern

noncomputable def toWeighted
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r) :
    WeightedOrderedPattern G k r := by
  classical
  exact
    { edgeWeight := fun e y =>
        if H.edge e y then 1 else 0 }

abbrev DeletionFamily
    {G : Type*} [DecidableEq G] (k r : ℕ) :=
  (e : OrderedFace k r) → Finset (Fin r → G)

def IsCover
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (D : DeletionFamily (G := G) k r) : Prop :=
  ∀ x, x ∈ H.occurrenceFinset →
    ∃ e, orderedFaceTuple e x ∈ D e

noncomputable def faceDeletionDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k r)
    (e : OrderedFace k r) : ℝ :=
  (D e).card / Fintype.card (Fin r → G)

end OrderedPattern

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedCounting
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*}
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

def deletionCount {k : ℕ} {V : Fin k → Type*}
    (deleted : DeletionFamily V) : ℕ :=
  ∑ j, (deleted j).card

end SimplexHypergraph

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.StrongOrderedComplexRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def selectedOrderedComplexTolerance
    {r : ℕ}
    (ε : (j : Fin r) → ℕ → ℝ)
    (index : Fin r → ℕ) :
    OrderedRegularityTolerance r :=
  fun j => ε j (index j)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.AdaptiveCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

namespace AdaptiveCoarseTargetSchedule

inductive Landing {k : ℕ} :
    {r : ℕ} → AdaptiveCoarseTargetSchedule k r → Type
  | nil : Landing (.nil : AdaptiveCoarseTargetSchedule k 0)
  | node {r : ℕ}
      {tolerance : ℕ → ℝ}
      {budget : ℕ → ℕ}
      {length : ℕ}
      {next : Fin length → AdaptiveCoarseTargetSchedule k r}
      (index : Fin length)
      (lower : Landing (next index)) :
      Landing (.node tolerance budget length next)

namespace Landing

def tolerance {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℝ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (tolerance := tolerance) _ lower =>
      fun j => Fin.lastCases tolerance lower.tolerance j

def budget {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (budget := budget) _ lower =>
      fun j => Fin.lastCases budget lower.budget j

def length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (length := length) _ lower =>
      fun j => Fin.lastCases length lower.length j

def index {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node chosen lower =>
      fun j => Fin.lastCases chosen.1 lower.index j

@[simp]
theorem tolerance_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance (Fin.last r) =
      tolerance := by
  simp [Landing.tolerance]

@[simp]
theorem tolerance_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance j.castSucc =
      lower.tolerance j := by
  simp [Landing.tolerance]

@[simp]
theorem budget_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget (Fin.last r) =
      budget := by
  simp [Landing.budget]

@[simp]
theorem budget_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget j.castSucc =
      lower.budget j := by
  simp [Landing.budget]

@[simp]
theorem length_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length (Fin.last r) =
      length := by
  simp [Landing.length]

@[simp]
theorem length_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length j.castSucc =
      lower.length j := by
  simp [Landing.length]

@[simp]
theorem index_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index (Fin.last r) =
      chosen.1 := by
  simp [Landing.index]

@[simp]
theorem index_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index j.castSucc =
      lower.index j := by
  simp [Landing.index]

end Landing

end AdaptiveCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

namespace SourceFullCoarseTargetSchedule

def nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (P :
      (AdaptiveCoarseTargetSchedule.node
        tolerance budget length next).Landing) :
    Fin (r + 2) → ℕ :=
  match P with
  | .node chosen lower =>
      Fin.lastCases topScale
        (lowerScale chosen lower)

@[simp]
theorem nodeScale_node
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower) =
      Fin.lastCases topScale
        (lowerScale chosen lower) :=
  rfl

@[simp]
theorem nodeScale_node_last
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        (Fin.last (r + 1)) =
      topScale := by
  simp [nodeScale]

@[simp]
theorem nodeScale_node_castSucc
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (q : Fin (r + 1)) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        q.castSucc =
      lowerScale chosen lower q := by
  simp [nodeScale]

@[simp]
theorem sourceFullCommonTolerance_nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    sourceFullCommonTolerance F
        (nodeScale (tolerance := tolerance) (budget := budget)
          topScale lowerScale
          (AdaptiveCoarseTargetSchedule.Landing.node
            (tolerance := tolerance) (budget := budget)
            chosen lower)) =
      sourceFullCommonTolerance F
        (lowerScale chosen lower) := by
  unfold sourceFullCommonTolerance
  rw [show
    (0 : Fin (r + 2)) =
      (0 : Fin (r + 1)).castSucc by rfl]
  rw [nodeScale_node_castSucc]

end SourceFullCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI
end


