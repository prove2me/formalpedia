-- Prove2me | Definitions.Def_OAIE3v2B220
-- name    : OAIE3v2B220
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:26:40.68691+00:00
-- url     : https://prove2.me/theorems/09efbbe0-0a91-461c-be33-8b947be579d4
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 225 of 311
-- statement:
--   Definitions bundle 225 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B200`, `OAIE3v2B201` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateOptionJointConclusion.lean`, `Estimates/BiasedSynchronizedSquareFamily.lean`, `Estimates/ExtractedInitialState.lean`, `Estimates/FullFastHorizontalNormalization.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Fourier/SquareModeGradedFrequency.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Lattices/AllocatedRecoveredIntegerFullChart.lean`, `Lattices/NativeCorrelatedAffineExistence.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/RankIntervalFactorization.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B200
import Definitions.Def_OAIE3v2B201

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
  (hW : BasisGradedSubmodule
    (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
    (fun i => squareBasisWeight ω i.val) W.toSubmodule)

include hW

theorem fullFast_horizontal_derivative_mem [DecidableEq σ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : B ∈ F.realFastDiagonalSubgroup (fun _ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
    (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.coord) 0 = 0) (i : σ) :
    F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
      (F.realFastCoefficientDirectionMap (F.fastPointwiseSquare e ω hF (fun _ => 1) W) B (Pi.single i 1)) ∈
      (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ := by
  have hb : B ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) (F.fullFastGradedDiagonal W) := by
    rw [F.fullFastPointwise_subgroup_eq e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW]
    exact hB
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1) (F.fullFastGradedDiagonal W) B).mp hb
  exact F.pointwise_horizontal_derivative_mem e ω hF (F.fullFastGradedDiagonal W) B.coord hs hzero i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem normalizedLower_of_mem (b : ℝ) (h : ZMod N) (hh : h ∈ W.shifts) (x : ZMod N) :
    W.normalizedLower b h x =
      ((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).evalCyclic N (fun _ => x) := by
  simp only [normalizedLower, dif_pos hh]

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure NativeReducedIntervalFamily {s r N : ℕ} [NeZero N] {p q P : ℝ}
    {f : ZMod N → ℂ} {W : NativeCorrelationStructure s r N p f}
    (B : NativeMultilinearIntervalFamily W q) (D : NativeMixedReductionData B.mixed P)
    (K : ℝ) where
  base_budget : q ≤ K
  correlation_budget : q + 7 * P ≤ K
  global_budget : mixedErrorBudget P ≤ K
  lower_budget : mixedErrorPairBudget P ≤ K
  code : D.ReductionCode (fun _ => B.coordinate)
  retained : Finset B.quadruples
  retained_nonempty : retained.Nonempty
  density : Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (retained.card : ℝ)
  lowerChoice : ∀ t : retained,
    D.LowerCode code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val)
  correlation : ∀ t : retained, Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
    B.residual t.val n * D.globalError (fun _ => B.coordinate) code (B.sample t.val n) *
      D.translationLower code.translations (t.val.val.2.1 - t.val.val.1).val
        (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (lowerChoice t) n‖

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def IntervalGlobalReductionStatement (s c : ℕ) : Prop :=
  ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
    {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K),
    ∃ (weight : ℤ → ℂ) (Q : Finset R.retained), (∀ n, ‖weight n‖ ≤ 1) ∧ Q.Nonempty ∧
      Real.exp (-(2 * K + intervalSplitTermBudget c K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤
        (Q.card : ℝ) ∧
      ∀ t ∈ Q, ∃ v : ℤ → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (intervalSplitLocalBudget c K)
          (fun x => v (x ()))) ∧
        Real.exp (-intervalSplitTermBudget c K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
          B.rankProduct t.val n * weight n * v n‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SquareModeGradedFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "δ" => F.reducedSquareGradedDifference e ω hF

theorem fullFastGradedRelative_top_frequency (hs : 1 ≤ s)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (ξ : F.squareFiltration.quotientTop.AssociatedGraded →ₗ[ℚ] ℚ)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (F.reducedSquareGradedRelativePiece s hs x) = η (F.associatedGradedPieceMap (s + 1) x))
    (hξ : ∀ y ∈ W, basisGradeProjection bW ωW s y = y → ξ y = 0) :
    ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0 := by
  rintro x ⟨y, hy, rfl⟩ hpure
  let ys := basisGradeProjection bW ωW s y
  have hys : ys ∈ F.fastGradedRelativeKernel W :=
    F.fastGradedRelativeKernel_graded e ω hF W hW s y hy
  have hysPure : basisGradeProjection bW ωW s ys = ys :=
    basisCoordinateProjection_idempotent bW {i | ωW i = s} y
  have hδ : δ ys = δ y := (F.reducedSquareGradedDifference_gradeProjection e ω hF s y).trans hpure
  obtain ⟨z, hz⟩ := F.exists_reducedSquareGradedRelativePiece_of_pure_kernel e ω hF
    s hs le_rfl ys hysPure hys.2
  calc
    η (δ y) = η (δ ys) := congrArg η hδ.symm
    _ = η (δ (F.reducedSquareGradedRelativePiece s hs z)) :=
      congrArg (fun u => η (δ u)) hz.symm
    _ = η (F.associatedGradedPieceMap (s + 1) z) :=
      congrArg η (F.reducedSquareGradedDifference_relativePiece e ω hF s hs z)
    _ = ξ (F.reducedSquareGradedRelativePiece s hs z) := (hrestriction z).symm
    _ = ξ ys := congrArg ξ hz
    _ = 0 := hξ ys hys.1 hysPure

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF
local notation "bG" => F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq

theorem square_mode_fullFast_top_frequency (hs : 1 ≤ s)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bG ωq W.toSubmodule)
    (hξ : ∀ y ∈ W, basisGradeProjection bG ωq s y = y →
      F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ y = 0) :
    ∀ x ∈ F.fullFastGradedRelative b ω hF W,
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω (s + 1) x = x →
        F.gradedFrequency b ω hF η x = 0 := by
  exact F.fullFastGradedRelative_top_frequency b ω hF hs W hW
    (F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ)
    (F.gradedFrequency b ω hF η)
    (F.square_gradedFrequency_restriction b ω hF hs η ξ hrestriction) hξ

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "bG" => F.associatedGradedBasis e ω hF

theorem layerOneGradedMap_coordinate_zero (x : L ⧸ F.layer 2) (i : ι) (hi : ω i ≠ 1) :
    (bG).repr (F.layerOneGradedMap e ω hF x) i = 0 := by
  have h := congrArg (fun y => (bG).repr y i) (F.layerOneGradedMap_pure e ω hF x)
  rw [basisGradeProjection_repr, if_neg hi] at h
  exact h.symm

theorem layerOneGradedMap_height (x : L ⧸ F.layer 2) {H : ℕ} (hH : 1 ≤ H)
    (hx : ∀ i, RationalHeightLE ((F.layerOneBasis e ω hF).repr x i) H) :
    ∀ i, RationalHeightLE ((bG).repr (F.layerOneGradedMap e ω hF x) i) H := by
  intro i
  by_cases hi : ω i = 1
  · have hni : ¬ 2 ≤ ω i := by omega
    rw [F.layerOneGradedMap_coordinate e ω hF x ⟨i, hni⟩]
    exact hx ⟨i, hni⟩
  · rw [F.layerOneGradedMap_coordinate_zero e ω hF x i hi]
    exact rationalHeightLE_zero hH

theorem gradedHorizontalKernelBasis_height (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (b j : L ⧸ F.layer 2) i) H) :
    ∀ j i, RationalHeightLE ((bG).repr (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded) i) H := by
  intro j i
  rw [F.gradedHorizontalKernelBasis_coe]
  exact F.layerOneGradedMap_height e ω hF _ hH (hb j) i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullFastHorizontalNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ν τ L V : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) Wf)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

theorem exists_fullFast_derivative_absorption
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (Q : Matrix (LayerOneBasisIndex ω) ν ℚ)
    (hQspan : Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col) = K.map (cH).toLinearMap)
    (b : ν → K) (hb : ∀ j, cH (b j).val = (Q.map (Rat.castHom ℝ)).col j)
    (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (c : 𝓔 →ₗ[ℝ] (τ → ℝ)) (N : 𝓔 →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) J)
    (hQ : ∀ i j, RationalHeightLE (Q i j) J)
    {p : ℝ} (hp : 0 ≤ p)
    (hsize : ((Fintype.card κ + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖cH x.val‖)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, ‖cH (𝓟 (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        𝓟 (small i - S (ks i)) ∈ 𝓤 ∧
        𝓟 (rational i - R (kr i)) ∈ 𝓤 ∧
        (k i + ks i + kr i).val ∈ 𝓤 ∧
        Y g i = (small i - S (ks i)) + ρ g (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖cH (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖cH (𝓟 (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  have hrow : Fintype.card (LayerOneBasisIndex ω) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hrows : (Fintype.card (LayerOneBasisIndex ω) : ℝ) ≤ p := by
    have hle : Fintype.card (LayerOneBasisIndex ω) ≤
        Fintype.card κ + Fintype.card ι + Fintype.card ν := by omega
    exact (Nat.cast_le.mpr hle).trans hsize
  have hcol : Fintype.card ((κ ⊕ TopGradedBasisIndex s ω) ⊕ ν) ≤
      Fintype.card κ + Fintype.card ι + Fintype.card ν := by
    rw [Fintype.card_sum]
    exact Nat.add_le_add_right (fullFastDiagonalGenerators_card (κ := κ) (s := s) (ω := ω)) _
  have hf : (𝓟).comp (ρ g).toLinearMap = 𝓟 := by
    apply LinearMap.ext
    intro x
    exact F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Wf e ω hF g x
  exact exists_controlled_derivative_absorption cH 𝓤 K (F.fullFastHorizontalMatrix e ω hF v) Q
    (F.fullFastHorizontalMatrix_span e ω hF W hW v hv) hQspan b hb 𝓟 (ρ g).toLinearMap hf
    S R hSR hS hR c N n rden hRgrid hJ hl (F.fullFastHorizontalMatrix_height e ω hF v hJ hheight)
    hQ hp hrows ((Nat.cast_le.mpr hcol).trans hsize) hJp hlp T hT M C hC hSbound
    (Y g) small rational k hsystem
    (fun i => F.fullFast_horizontal_derivative_mem e ω hF W hW g.val g.property hzero i)
    hsmall hNsmall hrational hrgrid

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExtractedInitialState
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "Y" => (fun (g : G) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

theorem exists_initialFormalState_after_removal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (a g c : G)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (hSR : S = (ρ (a * g * c)).toLinearMap.comp R)
    (hsystem : ∀ i, Y (a * g * c) i = small i + ρ (a * g * c) (rational i) + S (k i))
    (hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (haH : ∀ i, Hq (Y a i) = Hq (small i)) (hcH : ∀ i, Hq (Y c i) = Hq (rational i))
    (hlinear : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
        (k i).val)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (D M B A C p q : ℝ) (hD : 0 ≤ D)
    (haction : ∀ x, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) ((ρ a).symm x)‖ ≤
      D * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖)
    (hsmall : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤ M / T i)
    (hYa : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (Y a i)‖ ≤ A / T i)
    (hSbound : ∀ z, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
      (S (realSubmoduleBasis K bK z))‖ ≤ B)
    (hSBudget : D * B ≤ Real.exp p) (hsmallBudget : D * (M + A) ≤ Real.exp p)
    (hsectionBudget : C * Real.exp p ≤ Real.exp q)
    (hsectionBound : ∀ N : ℝ, 0 ≤ N → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ N / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * N) (sectionMap y))
    (l r m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp q)
    (hsectionGrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid r →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (hrational : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l)
    (hc : ∀ x, b.equivFun x ∈ realDenominatorGrid l → b.equivFun (ρ c x) ∈ realDenominatorGrid r)
    (hYc : ∀ i, b.equivFun (Y c i) ∈ realDenominatorGrid r) :
    ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 q,
      X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
  let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
  let Sn := (ρ a).symm.toLinearMap.comp S
  let Rn := (ρ c).toLinearMap.comp R
  let smalln := fun i => (ρ a).symm (small i - Y a i)
  let rationaln := fun i => ρ c (rational i) - Y c i
  have hnSR : Sn = (ρ g).toLinearMap.comp Rn :=
    F.realFastCoefficient_remove_lifts (K := K.baseChange ℝ) Wf a g c S R hSR
  have hnH : (Hq).comp Sn = (K.baseChange ℝ).subtype ∧
      (Hq).comp Rn = (K.baseChange ℝ).subtype :=
    F.realFastCoefficient_remove_horizontal_lifts (K := K.baseChange ℝ) Wf e ω hF a c S R
      (K.baseChange ℝ).subtype hS hR
  have hnSystem (i : σ) := F.realFastCoefficient_remove_derivative Wf e ω hF a g c
    (Pi.single i 1) (small i) (rational i) (S (k i)) (hsystem i)
  have hnHorizontal (i : σ) : Hq (smalln i) = 0 ∧ Hq (rationaln i) = 0 :=
    horizontal_remove_zero Hq (ρ a) (ρ c)
      (F.realFastCoefficientAction_horizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf e ω hF a)
      (F.realFastCoefficientAction_horizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf e ω hF c)
      (small i) (rational i) (Y a i) (Y c i) (haH i) (hcH i)
  apply F.exists_initialFormalState_of_normalized_quotient e ω hF W hW g K bK b rows sectionMap hsection
    Sn Rn smalln rationaln k hnSR hnSystem hnH.1 hnH.2
    (fun i => (hnHorizontal i).1) (fun i => (hnHorizontal i).2) hlinear T hT C p q
    hsectionBudget hsectionBound r m hm hmp hsectionGrid
  · intro z i
    have hz : ‖N (Sn (realSubmoduleBasis K bK z))‖ ≤ Real.exp p :=
      (haction _).trans ((mul_le_mul_of_nonneg_left (hSbound z) hD).trans hSBudget)
    exact (basisWeightedCoordinates_norm_le_iff b _ (fun j => monomialScale_pos T hT _)
      (Real.exp_pos p).le _).mp hz i
  · exact fun z => hc _ (hRgrid z)
  · intro j i
    have hj : ‖N (smalln j)‖ ≤ Real.exp p / T j :=
      (norm_removed_derivative_bound N (ρ a).symm.toLinearMap (small j) (Y a j)
        D M A (T j) hD (hT j) haction (hsmall j) (hYa j)).trans
          (div_le_div_of_nonneg_right hsmallBudget (hT j).le)
    exact (basisWeightedCoordinates_norm_le_iff b _ (fun i => monomialScale_pos T hT _)
      (div_nonneg (Real.exp_pos p).le (hT j).le) _).mp hj i
  · intro i
    change b.equivFun (ρ c (rational i) - Y c i) ∈ realDenominatorGrid r
    rw [map_sub]
    exact realDenominatorGrid_sub r _ _ (hc _ (hrational i)) (hYc i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_controlled_initialFormalState_after_removal (s aExp : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledInitialRemovalSpec s aExp C := by
  have hslowExists := exists_fastCoefficient_slow_removal_bound s aExp
  obtain ⟨cS, _, hslow⟩ := hslowExists
  have hgridExists := exists_fastCoefficient_rational_removal_grid s
  obtain ⟨cR, _, hgrid⟩ := hgridExists
  obtain ⟨C, hC, hbudget⟩ := exists_initial_removal_budget cS cR
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ν L _ _ _ _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure
    W Wf E J Q G ρ Hq Y hW a g c K bK b rows sectionMap hsection T hT Kscale hKscale hKscalep
    hprojection hsectionBound l δ hl hδ hδlp hprojectionGrid hsectionGrid ha hc
    S R small rational k hSR hsystem hS hR haH hcH hlinear hsmall hSbound hRgrid hrational
  have hδp : (δ : ℝ) ≤ Real.exp p := by
    have hlone : (1 : ℝ) ≤ l := by exact_mod_cast hl
    calc
      (δ : ℝ) ≤ (δ : ℝ) * l := le_mul_of_one_le_right (Nat.cast_nonneg _) hlone
      _ = ((δ * l : ℕ) : ℝ) := (Nat.cast_mul _ _).symm
      _ ≤ Real.exp p := hδlp
  have hslowData := hslow F e ω hF H p hH hp hι hσ hHp hstructure
    Wf b sectionMap hsection rows T hT Kscale hKscale hKscalep hprojection hsectionBound a ha
  have hgridData := hgrid F e ω hF H p hH hp hι hσ hHp hstructure
    Wf b sectionMap hsection l (δ * l) δ (Nat.mul_pos hδ hl) hδlp hδ hδp
    (hsectionGrid l) hprojectionGrid
  obtain ⟨r, hr, hrp, hactionGrid⟩ := hgridData
  have hcData := hactionGrid c hc
  have hYc : ∀ i, b.equivFun (Y c i) ∈ realDenominatorGrid r := by
    intro i
    have hcast : (fun j => (((Pi.single i 1 : σ → ℤ) j) : ℝ)) =
        (Pi.single i 1 : σ → ℝ) := by
      funext j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have hi := hcData.2.1 (Pi.single i 1)
    rw [hcast] at hi
    exact hi
  obtain ⟨hSBudget, hsmallBudget, hsectionBudget, hgridBudget⟩ := hbudget p hp
  have hsectionFinal : Kscale * Real.exp (p + 1 + 2 * (p + cS) ^ cS) ≤
      Real.exp ((p + C) ^ C) :=
    (mul_le_mul_of_nonneg_right hKscalep (Real.exp_nonneg _)).trans hsectionBudget
  have hdenomFinal : ((δ * r : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hδp hrp (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans hgridBudget
  exact F.exists_initialFormalState_after_removal e ω hF W hW a g c K bK b rows sectionMap hsection
    S R small rational k hSR hsystem hS hR haH hcH hlinear T hT
    (Real.exp ((p + cS) ^ cS)) (Real.exp p) (Real.exp p) (Real.exp ((p + cS) ^ cS))
    Kscale (p + 1 + 2 * (p + cS) ^ cS) ((p + C) ^ C) (Real.exp_nonneg _)
    hslowData.1 hsmall hslowData.2.1 hSbound hSBudget hsmallBudget
    hsectionFinal hsectionBound l r (δ * r) (Nat.mul_pos hδ hr) hdenomFinal
    (hsectionGrid r) hRgrid hrational hcData.1 hYc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uκ uν uL

variable {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem exists_horizontal_initialState_bound (s aExp : ℕ) (haExp : 2 ≤ aExp) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι]
        [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.HorizontalInitialStateSpec (σ := σ) (κ := κ) (ν := ν) e ω hF W aExp C := by
  have h := exists_controlled_initialFormalState_after_removal.{uσ, uι, uκ, uν, uL} s aExp
  obtain ⟨C, hC, hcontrol⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ν L _ _ _ _ _ _ _ F e ω hF W
  exact F.exists_initialFormalState_of_horizontal_data e ω hF W aExp C haExp hcontrol

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uκ uν uτ uL

variable {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

theorem exists_initialFormalState_after_absorption (C : ℕ)
    (hinit : F.HorizontalInitialStateSpec (σ := σ) (κ := κ) (ν := ν) e ω hF W 2 C) :
    F.AbsorbedInitialStateSpec (σ := σ) (κ := κ) (ν := ν) (τ := τ) e ω hF W C := by
  intro H p hH hp hι hσ hHp hstructure hW v hv hheight hsize g₀ hzero K bK hKb
    b rows sectionMap hsection T hT Kscale hKscale hKscalep hprojection hsectionBound
    l δ hl hδ hδlp hprojectionGrid hsectionGrid S R small rational k hSR hsystem hS hR
    hsmallH hsmall hSbound hRgrid hrational
  let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
  let A := submoduleBasisMatrix (F.layerOneBasis e ω hF) K bK
  have hAspan := realSubmoduleBasis_matrix_span (F.layerOneBasis e ω hF) K bK
  have hAcol := realSubmoduleBasis_matrix_coordinates (F.layerOneBasis e ω hF) K bK
  have hA : ∀ i j, RationalHeightLE (A i j) H := hKb
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hrH (i : σ) : cH (Hq (rational i)) ∈ realDenominatorGrid (δ * l) :=
    F.realFastCoefficientHorizontal_section_grid e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Uf b sectionMap hsection l (δ * l) (hsectionGrid l) (rational i) (hrational i)
  have habs := F.exists_fullFast_derivative_absorption e ω hF W hW v hv g₀ hzero
    (K.baseChange ℝ) A hAspan (realSubmoduleBasis K bK) hAcol S R hSR hS hR
    b.equivFun.toLinearMap N l l hRgrid hH (Nat.mul_pos hδ hl) hheight hA hp hsize hHp hδlp
    T hT (Real.exp p) (Real.exp p) (Real.exp_nonneg _) hSbound small rational k hsystem
    hsmallH hsmall hrH hrational
  obtain ⟨m, hm, hmp, ks, kr, habs⟩ := habs
  let small₀ := fun i => small i - S (ks i)
  let rational₀ := fun i => rational i - R (kr i)
  let k₀ := fun i => k i + ks i + kr i
  let l₀ := l * (l * m)
  have hbudget := absorbedInitialParameter_bounds hp
  have hep : Real.exp p ≤ Real.exp (absorbedInitialParameter p) := Real.exp_le_exp.mpr hbudget.1
  have hlp : (l : ℝ) ≤ Real.exp p := by
    have hd : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
    have h := le_mul_of_one_le_left (Nat.cast_nonneg l) hd
    exact h.trans (by simpa only [Nat.cast_mul] using hδlp)
  have hδp : (δ : ℝ) ≤ Real.exp p := by
    have hlone : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have h := le_mul_of_one_le_right (Nat.cast_nonneg δ) hlone
    exact h.trans (by simpa only [Nat.cast_mul] using hδlp)
  have hl₀ : 0 < l₀ := Nat.mul_pos hl (Nat.mul_pos hl hm)
  have hdenom : ((δ * l₀ : ℕ) : ℝ) ≤ Real.exp (absorbedInitialParameter p) := by
    simp only [l₀, Nat.cast_mul]
    apply le_trans _ hbudget.2.2
    gcongr
  have hRgrid₀ (z : κ) : b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l₀ :=
    realDenominatorGrid_subset_of_dvd hl (dvd_mul_right l (l * m)) (hRgrid z)
  have hsmall₀ (i : σ) : ‖N (small₀ i)‖ ≤ Real.exp (absorbedInitialParameter p) / T i := by
    have hi := (habs i).2.2.2.2.2.1
    exact hi.trans (div_le_div_of_nonneg_right hbudget.2.1 (hTpos i).le)
  have hSbasis (z : κ) : ‖N (S (realSubmoduleBasis K bK z))‖ ≤
      Real.exp (absorbedInitialParameter p) := by
    have hnorm : ‖cH (realSubmoduleBasis K bK z).val‖ ≤ (H : ℝ) := by
      rw [hAcol z]
      apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg H)).mpr
      intro i
      exact (hA i z).abs_real_le
    have htwo : 2 * p ≤ absorbedInitialParameter p := by
      unfold absorbedInitialParameter
      have h19 : 0 ≤ (p + 2) ^ 19 := by positivity
      have h36 : 0 ≤ (p + 2) ^ 36 := by positivity
      linarith
    calc
      _ ≤ Real.exp p * (H : ℝ) := (hSbound _).trans (mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _))
      _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_left hHp (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr htwo
  have hout := hinit H (absorbedInitialParameter p) hH (absorbedInitialParameter_nonneg hp)
    (hι.trans hbudget.1) (hσ.trans hbudget.1) (hHp.trans hep) hstructure hW g₀ hzero K bK
    b rows sectionMap hsection T hTpos Kscale hKscale (hKscalep.trans hep) hprojection hsectionBound
    l₀ δ hl₀ hδ hdenom hprojectionGrid hsectionGrid S R small₀ rational₀ k₀ hSR
    (fun i => (habs i).2.2.2.1) hS hR (fun i => (habs i).1)
    (fun i => (habs i).2.1) (fun i => (habs i).2.2.1)
    hsmall₀ hSbasis hRgrid₀ (fun i => (habs i).2.2.2.2.2.2.2)
  exact ⟨δ * l₀, Nat.mul_pos hδ hl₀, hdenom, hout⟩

theorem exists_absorbed_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ]
        [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.AbsorbedInitialStateSpec (σ := σ) (κ := κ) (ν := ν) (τ := τ) e ω hF W C := by
  have h := exists_horizontal_initialState_bound.{uσ, uι, uκ, uν, uL} s 2 (by decide)
  obtain ⟨C, hC, hinit⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ν τ L _ _ _ _ _ _ _ _ F e ω hF W
  exact F.exists_initialFormalState_after_absorption e ω hF W C (hinit F e ω hF W)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem exists_extracted_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) (a d : ℕ),
        F.ExtractedInitialStateSpec (σ := σ) (τ := τ) (a := a) (d := d) e ω hF W C := by
  have h := exists_absorbed_initialState_bound.{uσ, uι, 0, 0, uτ, uL} s
  obtain ⟨C, _, habs⟩ := h
  obtain ⟨D, hD, hbudget⟩ := exists_extractedInitialParameter_budget C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W a d
  exact F.exists_initialFormalState_from_extraction e ω hF W C D hbudget
    (fun r => habs (κ := Fin r) (ν := Fin d) F e ω hF W)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem exists_common_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) (d : ℕ),
        F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W C := by
  have h := exists_extracted_initialState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, _, hinit⟩ := h
  obtain ⟨D, hD, hbudget⟩ := exists_commonInitialParameter_budget C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W d
  exact F.exists_initialFormalState_from_common e ω hF W C D hbudget
    (fun a => hinit F e ω hF W a d)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
    (D.filtration.squareFinBasis b ω (hF 2)) (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b ω (hF 2))
    (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel
  (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
  (D.filtration.squareFinBasis_layers b ω hF) (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers
  (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
  (D.filtration.squareFinBasis_layers b ω hF) (D.filtration.squareLattice D.lattice) N hN hin hout

theorem HasFixedNativeSquareFactors.fullFast_top_frequency {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {h : σ → ℤ} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors (D.filtration.squareFinBasis b ω (hF 2))
      (squareFinWeight ω) (D.filtration.squareFinBasis_layers b ω hF)
      N hN hin hout hs g η T h p l W)
    (hW : BasisGradedSubmodule ((Q).filtration.associatedGradedBasis (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) W.toSubmodule) :
    ∀ x ∈ D.filtration.fullFastGradedRelative b ω hF W,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω (s + 1) x = x →
        D.filtration.gradedFrequency b ω hF η x = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, ξ, _, hrestriction, hξ, _⟩ := hdata
  exact D.filtration.square_mode_fullFast_top_frequency b ω hF hs η ξ hrestriction W
    ((D.filtration.squareTopQuotientModel_graded_iff b ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout W.toSubmodule).mp hW)
    ((D.filtration.squareTopQuotientModel_top_annihilation_iff b ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout ξ W).mp hξ)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

theorem exists_biased_synchronized_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedSynchronizedSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_common_fixed_native_square_family s c hI
  obtain ⟨b, _, hsynchronize⟩ := exists_synchronized_native_square_family s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + G + 2 * Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + squareGeometryBudget p + 2 * p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbracket : 0 ≤ (p + 4) ^ 11 := by positivity
  have hgeompos := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have hbracketq : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have hgeomq : squareGeometryBudget p ≤ q := by dsimp [q]; linarith
  have h2pq : 2 * p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hbq : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, k, q, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hqC : q + 1 ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, _, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨S, l, W, u, hS, hcount, hl, hlk, hu, hW, hheight, hgood⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  obtain ⟨h₀, hh₀⟩ := hS
  have hWcanonical := (D.filtration.squareTopQuotientModel_graded_iff e ω hF
    (D.filtration.squareLattice D.lattice) N hN hin hout W.toSubmodule).mp hW
  have hcanonicalHeight : BasisFamilyLogHeight
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)) u k :=
    D.filtration.squareTopQuotientModel_graded_logHeight e ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout u hheight
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHq : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hdimq : 2 * (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q + 1 := by
    have := mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hκq : (Fintype.card (Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i})) : ℝ) ≤ q + 1 := by
    rw [Fintype.card_fin]
    exact hgeometry.1.trans (hgeomq.trans (by linarith))
  have hσq : (Fintype.card σ : ℝ) ≤ q + 1 := hσ.trans (hpq.trans (by linarith))
  have hlq : (l : ℝ) ≤ Real.exp (q + 1) :=
    hlk.trans (Real.exp_le_exp.mpr (hkq.trans (by linarith)))
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans hbracketq)
  have hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) H :=
    fun i j => rationalHeightLE_ceil_exp ((hcanonicalHeight i j).trans hkq)
  obtain ⟨m, hm, hmb, hlm, hsync⟩ := hsynchronize D e ω hF N hN hin hout W u hu hWcanonical
    H l (q + 1) hH hl hq1 hdimq hσq hκq hHq hlq hc hh
  have hfixed : ∀ h ∈ S, D.HasFixedNativeSquareFactors
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h (q + 1) l W := by
    intro h hh
    exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.mono D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      (hgood h hh).2.2 (hkq.trans (by linarith)) hTpos
  have hdata := hsync (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) hs g η S h₀ hh₀ hfixed
  refine ⟨S, h₀, l, m, W, u, hh₀, ?_, hl, hlk.trans (Real.exp_le_exp.mpr hkC),
    hm, hmb.trans (Real.exp_le_exp.mpr hbC), hlm, hu, hWcanonical, ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkC))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · exact fun i j => (hcanonicalHeight i j).trans hkC
  · exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.fullFast_top_frequency
      D e ω hF N hN hin hout (hgood h₀ hh₀).2.2 hW
  · intro h hh
    exact ⟨(hgood h hh).1, fun i =>
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkC))
        (Nat.cast_nonneg (lengths i))).trans_lt ((hgood h hh).2.1 i)⟩
  · exact RationalFilteredNilmanifold.SynchronizedNativeSquareData.mono
      D e ω hF hdata hqC hbC hTpos

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_product (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          letI : FiniteDimensional ℚ
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
            (productFinBasis (I.productModels i)).finiteDimensional_of_finite
          letI := moduleTopology ℝ (ℝ ⊗[ℚ]
            (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
          letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
            IsModuleTopology.topologicalAddGroup ℝ _
          letI : T2Space (ℝ ⊗[ℚ]
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
            realification_moduleTopology_t2 (productFinBasis (I.productModels i))
          ∃ T : (pi (I.productModels i)).Niltest (fun _ : Unit => 1),
            T.ComplexityLE ((p + C) ^ C) ∧
            (piRank (I.productModels i) (I.productRanks i R₀)).ComplexityLE ((p + C) ^ C) ∧
            T.orbit = NilpotentLieFiltration.piRealOrbit (fun k => (I.productModels i k).filtration)
              (fun k => (I.productTests i k).orbit) ∧
            (∀ n, T.eval (fun _ => n) =
              fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
                (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
                  ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n)) ∧
            (∀ z ∈ (piRank (I.productModels i) (I.productRanks i R₀)).realSubgroup s r, ∀ x,
              T.observable (z • x) = CircleFourier.character
                ((realifyFunctional (piFrequency (I.productFrequencies i)) z.coord : ℝ) :
                  CircleFourier.Circle) * T.observable x) ∧
            Real.exp (-(2 * p)) ≤
              ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length), T.eval x‖ := by
  obtain ⟨c, _, hlower⟩ := exists_rank_interval_raised_lower_term s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_interval_product_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I
  obtain ⟨i, R₀, hR₀, hzero, hT₀, hcorr⟩ := hlower I
  let u := rankIntervalInputBudget c p
  obtain ⟨hu5, hup, huraise, hurank⟩ := rankIntervalInputBudget_bounds c hp
  have hu : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 5).trans hu5
  have hub : u ≤ productNiltestBudget u := by
    have hg := productNiltestBudget_geometry hu
    nlinarith [sq_nonneg u]
  have hcost : productNiltestBudget u ≤ (p + C) ^ C := hbudget p hp
  have hsmall : u ≤ (p + C) ^ C := hub.trans hcost
  have hb : 0 ≤ b := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hbu : b ≤ u := hbp.trans (by linarith)
  have hcard : (Fintype.card (Option (Fin 4)) : ℝ) ≤ u := by
    simpa using hu5
  have htests : ∀ k, (I.productTests i k).ComplexityLE u := by
    intro k
    cases k with
    | none => exact hT₀.mono huraise
    | some k => exact (W.fourPointFactors_complexity hb out (rankQuadrupleParameters t)
        (cyclicBranchOffset t.1 branch) k).mono (by linarith)
  have hranks : ∀ k, (I.productRanks i R₀ k).ComplexityLE u := by
    intro k
    cases k with
    | none => exact hR₀.mono R₀ hurank
    | some _ => exact W.complexity.mono W.rank hbu
  refine ⟨i, R₀, hR₀.mono R₀ (hurank.trans hsmall), hzero, ?_⟩
  let : FiniteDimensional ℚ
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
    (productFinBasis (I.productModels i)).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    realification_moduleTopology_t2 (productFinBasis (I.productModels i))
  let T := piNiltest (I.productModels i) (I.productTests i) hu hcard htests
  have heval (n : ℤ) : T.eval (fun _ => n) =
      fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
        (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) :=
    (piNiltest_eval (I.productModels i) (I.productTests i) hu hcard htests _).trans
      (I.productTests_eval i n)
  refine ⟨T, (piNiltest_complexity _ _ hu hcard htests).mono hcost,
    (piRank_complexity _ _ hu hcard hranks).mono (piRank (I.productModels i) (I.productRanks i R₀))
      ((productNiltestBudget_geometry hu).trans hcost), rfl, heval, ?_, ?_⟩
  · exact piNiltest_rank_vertical _ _ _ _ hu hcard htests (I.productTests_vertical hs i R₀)
  · rw [unitIntervalBox_expect]
    simpa only [heval, two_mul] using hcorr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeCorrelatedAffineExistence
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedAffineComparison (hs : 2 ≤ s) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let Lv := sharedFreePetalLiftBudget s Q P'
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-(Λ + C)) * H'.card ≤ (J.card : ℝ) ∧
      ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
        (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
        (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
        (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
        (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
        (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
        ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
          (A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
          (∀ h : {h // h ∈ J},
            (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
            (A h).log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            ∀ d : Fin s,
              coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan d)
                  (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                    (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators
variable {m : ℕ} {K X : Type*} [Fintype K] (J : Fin m → Type*)
    (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ)

theorem eval_jointIntegerPhysicalSite_eq_frame
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : VectorPolynomial X ℝ V) (x : K → ℤ) :
    eval (fun i => (jointIntegerPhysicalSite x (a, v) i : ℝ)) p =
      eval (fun i => (jointIntegerFrame (a, v) none i : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) i : ℝ) * (x k : ℝ)) p := by
  rw [cast_jointIntegerPhysicalSite_eq_frame]
end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem allocatedRecoveredIntegerFullChart_spatial
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : LayerSamplerVariables G I n B → ℤ) :
    integerSampledSpatial (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x =
      jointIntegerPhysicalSite x (a, v) :=
  jointIntegerFullChart_spatial J a v _ x

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℝ) (j : Fin m) (i : J j) :
    eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) i - (c j).val i =
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 x i +
      MvPolynomial.eval x (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩)) := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a, v) k z : ℝ)
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  have hβ := canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample
    (centeredAffineCoefficientArray U poly hm c frame) hc j i
  change eval (fun z => frame none z + ∑ k, frame (some k) z * x k) (poly j) i - (c j).val i =
    mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 x i +
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ)
        (coefficientIntegerFloorPolynomial U b o sample
          (centeredAffineCoefficientArray U poly hm c frame) j i))
  rw [← coefficientRowPolynomial_centered_affine_eval U poly hm hp c frame j i x,
    hβ.1, map_add, mixedLiftPolynomial_eval]

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℤ)
    (hx : ∀ k, |(x k : ℝ)| ≤ layerSamplerBox B U b S k) (j : Fin m) (i : J j) :
    |eval (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)) (poly j) i - (c j).val i -
      (MvPolynomial.eval x (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)) : ℝ)| ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  rw [eval_jointIntegerPhysicalSite_eq_frame a v,
    ← integerSampledRealChart_eval (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample),
    h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read,
    add_sub_cancel_right]
  exact allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart
    j (sample j) (h.2.2.1 j).2 (fun k => (x k : ℝ)) hx i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedFrozenParameterBox_bound
    (keep : LayerSamplerVariables G I n B → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i.val)
    (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} => sides i.val)) :
    ∀ i, |((finiteSplitPoint keep u fixed i : ℤ) : ℝ)| ≤ layerSamplerBox B U b S i := by
  intro i
  have hi := (mem_integerBox sides _).mp
    (allocatedFrozenParameterBox_mem B U b S keep fixed hfixed u hu) i
  have hnonneg : (0 : ℝ) ≤ (finiteSplitPoint keep u fixed i : ℤ) := by exact_mod_cast hi.1
  rw [abs_of_nonneg hnonneg, allocatedParameterBox_side_eq B U b S]
  exact_mod_cast hi.2.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem allocatedFrozenIntegerFullChart_spatial
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (u : {i // keep i} → ℤ) :
    integerSampledSpatial
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u =
      jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (a, v) := by
  change integerSampledSpatial (fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) u = _
  rw [integerSampledSpatial_freeze, allocatedRecoveredIntegerFullChart_spatial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem integerChart_spatial (u : C.Variables → ℤ) :
    integerSampledSpatial C.integerChart u = C.physical u :=
  allocatedFrozenIntegerFullChart_spatial B U b o poly hm C.centerLift
    C.path.1.val C.path.2.val C.sample C.keep C.fixed u

theorem chartValues_spatial (u : C.Variables → ℤ) (x : X) :
    C.chartValues u (Sum.inl x) = C.physical u x :=
  congrFun (C.integerChart_spatial u) x

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators
variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace LocalMajorSliceTest
variable {D : RationalFilteredNilmanifold L s d} {N : I → ℕ} {cost budget : ℝ}
theorem weight_norm (A : LocalMajorSliceTest D N cost budget) (x : I → ℤ) :
    ‖A.weight x‖ ≤ 1 := by
  simpa only [weight, norm_star] using
    (A.test.norm_eval_le (commonStrideIndex (fun i => (A.slice.start i : ℤ))
      A.stride x)).trans A.norm

noncomputable def full (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (cost budget : ℝ) (hcost : 0 ≤ cost)
    (T : D.Niltest (fun _ : I => 1)) (hT : (T.normBound : ℝ) ≤ 1)
    (hcomplexity : T.ComplexityLE budget) : LocalMajorSliceTest D N cost budget := by
  let A : ResidueBoxSlice N 1 :=
    { start := fun _ => 0
      length := N
      inside := fun i j hj => by simpa using hj }
  refine ⟨1, Nat.zero_lt_one, A, ?_, T, hT, hcomplexity⟩
  have hA := A.isDenseCommonStrideBox Nat.zero_lt_one (ρ := 4) (by norm_num)
    hN (fun i => by dsimp [A]; norm_num)
  have hzero : IsDenseCommonStrideBox N 0 A.integerPoints := by simpa using hA
  exact hzero.mono hcost
end LocalMajorSliceTest

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

namespace LocalMajorSliceTest

variable [Fintype V] [DecidableEq V] {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {N : V → ℕ} {cost budget B : ℝ}

noncomputable def freezeShort
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    LocalMajorSliceTest D N (max cost (Real.log B)) budget where
  stride := A.stride
  stride_pos := A.stride_pos
  slice := A.slice.freezeShort Long fixed hfixed
  dense := A.slice.freezeShort_dense Long fixed hfixed A.stride_pos A.dense hB hshort
  test := A.test.liftLong Long
  norm := A.norm
  complexity := A.complexity

theorem freezeShort_weight
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) (x : V → ℤ) :
    (A.freezeShort Long fixed hfixed hB hshort).weight x = A.weight (fun i => x i.val) := by
  change star ((A.test.liftLong Long).eval
    (commonStrideIndex (fun i => ((A.slice.freezeShort Long fixed hfixed).start i : ℤ))
      A.stride x)) = _
  rw [A.test.eval_liftLong, A.slice.freezeShort_commonStrideIndex]
  rfl

theorem expect_freezeShort
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B)
    (signal : (V → ℤ) → ℂ) :
    (𝔼 x ∈ (A.freezeShort Long fixed hfixed hB hshort).slice.integerPoints,
      signal x * (A.freezeShort Long fixed hfixed hB hshort).weight x) =
    (𝔼 x ∈ A.slice.integerPoints, signal (frozenLongExtension Long fixed x) * A.weight x) := by
  change (𝔼 x ∈ (A.slice.freezeShort Long fixed hfixed).integerPoints,
    signal x * (A.freezeShort Long fixed hfixed hB hshort).weight x) = _
  rw [A.slice.expect_freezeShort]
  apply Finset.expect_congr rfl
  intro x hx
  rw [A.freezeShort_weight]
  congr 2
  funext i
  exact frozenLongExtension_long Long fixed x i

end LocalMajorSliceTest

end Erdos3

end

end OAI
end


