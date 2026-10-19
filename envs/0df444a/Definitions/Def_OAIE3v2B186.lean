-- Prove2me | Definitions.Def_OAIE3v2B186
-- name    : OAIE3v2B186
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:50:23.90733+00:00
-- url     : https://prove2.me/theorems/086add0f-fc3f-4613-a4fe-296614c5313e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 189 of 311
-- statement:
--   Definitions bundle 189 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B163`, `OAIE3v2B164`, `OAIE3v2B165`, `OAIE3v2B169`, `OAIE3v2B170`, `OAIE3v2B171` of this split.
--
--   Modules: `Dynamics/ComparisonEquivalenceBudget.lean`, `Estimates/ComparisonAmbient.lean`, `Estimates/ControlledComparisonModel.lean`, `Estimates/CubicAntisymmetricTransfer.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/NativeDilationObservable.lean`, `Estimates/NativeSelectedCorrelators.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NormalizedComparisonOrbit.lean`, `Estimates/SymmetricSquarefreeMonotonicity.lean`, `Estimates/TensorSquarePairComparison.lean`, `Estimates/UniformFrozenDescent.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Geometry/ComparisonProductMetric.lean`, `Geometry/NativeDilationObservableMetric.lean`, `Lattices/ComparisonLattice.lean`, `Lattices/TopInvariantIntegerExpansion.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativeComparisonProjections.lean`, `Linear/NativeDilationPairProjections.lean`, `Nilpotent/TopInvariantNiltestBudget.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/PositivePolynomialVectorOrbit.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B163
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B169
import Definitions.Def_OAIE3v2B170
import Definitions.Def_OAIE3v2B171

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.TopInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]

theorem exists_topInvariant_niltest
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientTop)
    (hQL : Q.lattice = D.lattice.map
      (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound ∧
      ∀ x, S.eval x = T.eval x := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (lieQuotientMap (D.filtration.layerIdeal (s + 1)))) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
    (lieQuotientMap_surjective _) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff
        (D.filtration.layerIdeal (s + 1)).toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := D.topQuotientOrbit Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  }
  refine ⟨S, rfl, rfl, rfl, ?_⟩
  intro x
  exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
    (D.topQuotientOrbit_eval Q hQF T.orbit x)).trans (hf _)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_topInvariant_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d n : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
      (hQF : Q.filtration = D.filtration.quotientTop)
      (_hQL : Q.lattice = D.lattice.map
        (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p) →
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x, S.eval x = T.eval x := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 1 + Polynomial.C a) ^ a + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d n D _ _ _ _ Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hSe⟩ := D.exists_topInvariant_niltest Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + C) ^ C := by
    simpa [r, P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩, hSe⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace NativeCrossWitnesses

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

theorem extension_of_mem (h : ZMod N) (hh : h ∈ H) (x : ZMod N) :
    U.extension h x = U.product ⟨h, hh⟩ x := by
  simp only [extension, dif_pos hh]

theorem extension_of_not_mem (h : ZMod N) (hh : h ∉ H) (x : ZMod N) :
    U.extension h x = 0 := by
  simp only [extension, dif_neg hh]

theorem product_norm (hm : ∀ h x, ‖m h x‖ ≤ 1) (h : H) (x : ZMod N) :
    ‖U.product h x‖ ≤ Real.exp p := by
  have hT := (U h).test.eval_budget (U h).complexity (fun _ : Unit => (x.val : ℤ))
  change ‖(U h).test.evalCyclic N (fun _ => x)‖ ≤ Real.exp p at hT
  rw [product, norm_mul]
  simpa only [one_mul] using mul_le_mul (hm h.val x) hT (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem extension_norm (hm : ∀ h x, ‖m h x‖ ≤ 1) (h x : ZMod N) :
    ‖U.extension h x‖ ≤ Real.exp p := by
  by_cases hh : h ∈ H
  · rw [U.extension_of_mem h hh]
    exact U.product_norm hm ⟨h, hh⟩ x
  · rw [U.extension_of_not_mem h hh, norm_zero]
    exact Real.exp_nonneg _

theorem product_correlation (h : H) :
    Real.exp (-p) ≤
      ‖𝔼 x, (f₀ x * star (f₁ (x + h.val))) * star (U.product h x)‖ := by
  simpa only [product, nativeCrossResidual, star_mul, mul_assoc, mul_left_comm, mul_comm]
    using (U h).correlation

noncomputable def mono (hpq : p ≤ q) : NativeCrossWitnesses s N q f₀ f₁ m H :=
  fun h => (U h).mono hpq

end NativeCrossWitnesses

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSelectedCorrelators
namespace OAI

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

theorem exists_quadruples (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1)
    (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(12 * p)) / 2 * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        Real.exp (-(8 * p)) / 2 ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  let g (h x : ZMod N) := (Real.exp (-p) : ℂ) * U.extension h x
  have hg (h x : ZMod N) : ‖g h x‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-p) * Real.exp p :=
        mul_le_mul_of_nonneg_left (U.extension_norm hm h x) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzero (h : ZMod N) (hh : h ∉ H) (x : ZMod N) : g h x = 0 := by
    simp only [g, U.extension_of_not_mem h hh, mul_zero]
  have hmean (h : ZMod N) :
      (𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)) =
        (Real.exp (-p) : ℂ) * (𝔼 x, (f₀ x * star (f₁ (x + h))) * star (U.extension h x)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [g, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hcorr (h : ZMod N) (hh : h ∈ H) :
      Real.exp (-(2 * p)) ≤ ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖ := by
    rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hu : Real.exp (-p) ≤
        ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (U.extension h x)‖ := by
      simpa only [U.extension_of_mem h hh] using U.product_correlation ⟨h, hh⟩
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (Real.exp_nonneg _)
  obtain ⟨Q, hQ, hsize, hquad⟩ := exists_many_cross_correlated_quadruples f₀ f₁ g H
    hf₀ hf₁ hg hzero (Real.exp_pos (-p)) (Real.exp_pos (-(2 * p))) hdense hcorr
  have hscale (a h k : ZMod N) : additiveQuadrupleCorrelation g a h k =
      Real.exp (-(4 * p)) * additiveQuadrupleCorrelation U.extension a h k := by
    rw [show g = (fun h x => (Real.exp (-p) : ℂ) * U.extension h x) from rfl,
      additiveQuadrupleCorrelation_real_scale U.extension (Real.exp (-p)) (Real.exp_nonneg _) a h k]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨Q, hQ, ?_, ?_⟩
  · simpa only [derivative_quadruple_exp_threshold] using hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    rw [derivative_quadruple_exp_threshold, hscale] at hc
    have heq : Real.exp (-(4 * p)) * (Real.exp (-(8 * p)) / 2) = Real.exp (-(12 * p)) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [← heq] at hc
    exact le_of_mul_le_mul_left hc (Real.exp_pos _)

theorem exists_quadruples_budget (hH : H.Nonempty)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(13 * p + 2)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        Real.exp (-(13 * p + 2)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨h, hh⟩ := hH
  have hp : 0 ≤ p := (Nat.cast_nonneg (U ⟨h, hh⟩).dim).trans (U ⟨h, hh⟩).complexity.1.1
  have h12 : Real.exp (-(13 * p + 2)) ≤ Real.exp (-(12 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hp])).trans (exp_sub_one_le_half_exp (-(12 * p)))
  have h8 : Real.exp (-(13 * p + 2)) ≤ Real.exp (-(8 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hp])).trans (exp_sub_one_le_half_exp (-(8 * p)))
  obtain ⟨Q, hQ, hsize, hcorr⟩ := U.exists_quadruples hf₀ hf₁ hm hdense
  refine ⟨Q, hQ, (mul_le_mul_of_nonneg_right h12 (by positivity)).trans hsize, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hcorr t ht
  exact ⟨h₁, h₂, h₃, h₄, h8.trans hc⟩

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3.NativeCrossWitnesses

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H S : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def restrict (hSH : S ⊆ H) : NativeCrossWitnesses s N p f₀ f₁ m S :=
  fun h => U ⟨h.val, hSH h.property⟩

theorem restrict_extension_of_mem (hSH : S ⊆ H) (h : ZMod N) (hh : h ∈ S) (x : ZMod N) :
    (U.restrict hSH).extension h x = U.extension h x := by
  rw [extension_of_mem _ h hh, U.extension_of_mem h (hSH hh)]
  rfl

theorem restrict_quadruple (hSH : S ⊆ H) (a h k : ZMod N)
    (h₁ : h ∈ S) (h₂ : h - a ∈ S) (h₃ : k ∈ S) (h₄ : k - a ∈ S) :
    additiveQuadrupleCorrelation (U.restrict hSH).extension a h k =
      additiveQuadrupleCorrelation U.extension a h k := by
  simp only [additiveQuadrupleCorrelation, U.restrict_extension_of_mem hSH h h₁,
    U.restrict_extension_of_mem hSH (h - a) h₂,
    U.restrict_extension_of_mem hSH k h₃, U.restrict_extension_of_mem hSH (k - a) h₄]

theorem exists_short_quadruples (hH : H.Nonempty)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧ CyclicShortShiftSet S ∧
      Real.exp (-(p + 1)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) ∧
      ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
        Real.exp (-(13 * (p + 1) + 2)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.2.1 ∈ S ∧ t.2.1 - t.1 ∈ S ∧ t.2.2 ∈ S ∧ t.2.2 - t.1 ∈ S ∧
          -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
          Real.exp (-(13 * (p + 1) + 2)) ≤
            additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨S, hSH, hS, hsize, hshort⟩ := exists_cyclicShortShiftSet H hH
  have hhalf : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    rw [show -(p + 1) = -p - 1 by ring]
    exact exp_sub_one_le_half_exp (-p)
  have hdenseS : Real.exp (-(p + 1)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ ≤ (Real.exp (-p) / 2) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)
      _ = (Real.exp (-p) * Fintype.card (ZMod N)) / 2 := by ring
      _ ≤ (H.card : ℝ) / 2 := div_le_div_of_nonneg_right hdense (by norm_num)
      _ ≤ _ := hsize
  let V := (U.restrict hSH).mono (show p ≤ p + 1 by linarith)
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := V.exists_quadruples_budget hS hf₀ hf₁ hm hdenseS
  refine ⟨S, hSH, hS, hshort, hdenseS, Q, hQ, hQsize, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hQcorr t ht
  refine ⟨h₁, h₂, h₃, h₄, hshort.quadruple_relation t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄, ?_⟩
  change Real.exp (-(13 * (p + 1) + 2)) ≤
    additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2 at hc
  rwa [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄] at hc

end Erdos3.NativeCrossWitnesses

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComparisonAmbient
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonToAmbient :=
  optionProductMap (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))
    (fun _ : PUnit.{1} => M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))

theorem comparisonToAmbient_injective : Function.Injective M.comparisonToAmbient := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrFun h none) (congrFun h (some PUnit.unit))

theorem comparisonAmbient_point_logHeight (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (x : M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
    {q : ℝ} (hx : ∀ k, rationalLogHeight
      ((D.basis.prod (M.squarefreeFinBasis p)).repr x.val k) ≤ q) :
    ∀ k, rationalLogHeight
      ((M.comparisonAmbient p B hB hstable).basis.repr (M.comparisonToAmbient x) k) ≤ q := by
  apply optionProductMap_point_logHeight
  · exact fun k => hx (Sum.inl k)
  · exact fun _ k => hx (Sum.inr k)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeLattice_frequency_integral (p : ℝ) (η : L →ₗ[ℚ] ℚ) (l B : ℕ)
    (hstable : M.SquarefreeGridStable p B) (hdiv : l ∣ B)
    (hη : ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
      (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n)
    (g : (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group)
    (hg : g ∈ M.squarefreeLattice p B hstable) :
    ∃ n : ℤ, M.filtration.replicatedFrequency η g.coord = n :=
  coordinateGrid_functional_integral (M.squarefreeBasis p) (M.filtration.replicatedFrequency η)
    l B hdiv hη hg

theorem squarefreeRealLattice_frequency_integral (p : ℝ) (η : L →ₗ[ℚ] ℚ) (l B : ℕ)
    (hB : 0 < B) (hstable : M.SquarefreeGridStable p B) (hdiv : l ∣ B)
    (hη : ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
      (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n)
    (z : (M.squarefreeModel p B hB hstable).RealGroup)
    (hz : z ∈ (M.squarefreeModel p B hB hstable).realLattice) :
    ∃ n : ℤ, realifyFunctional (M.filtration.replicatedFrequency η) z.coord = n :=
  (M.squarefreeModel p B hB hstable).realLattice_functional_integral
    (M.filtration.replicatedFrequency η)
    (M.squarefreeLattice_frequency_integral p η l B hstable hdiv hη) z hz

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ComparisonLattice
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonLattice (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) : Subgroup
      (M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).Group :=
  (M.comparisonAmbient p B hB hstable).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient)

theorem comparisonLattice_first (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    M.comparisonLattice p B hB hstable ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))) := by
  intro g hg
  have hg' : NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient g ∈
      (M.comparisonAmbient p B hB hstable).lattice := hg
  have h := (mem_piBCHSubgroup _ _ _).mp hg' none
  exact D.raiseStep_lattice_back (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))) h

theorem comparisonLattice_second (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    M.comparisonLattice p B hB hstable ≤ (M.squarefreeModel p B hB hstable).lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))) := by
  intro g hg
  have hg' : NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient g ∈
      (M.comparisonAmbient p B hB hstable).lattice := hg
  have h := (mem_piBCHSubgroup _ _ _).mp hg' (some PUnit.unit)
  exact (M.squarefreeModel p B hB hstable).raiseStep_lattice_back
    (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))) h

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_filtration_basis {p : ℝ} (hM : M.ComplexityLE p)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : Basis (Fin (finrank ℚ
        ((M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).layer n))) ℚ
        ((M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).layer n),
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val.val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis hM n
  let e := M.filtration.comparisonFiltrationLayerEquiv
    (fun i : ReplicatedIndex bound => i.1) n hn
  let c := (b.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) : (c j).val.val = (b ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [c, Basis.reindex_apply, Basis.map_apply, e,
      MultidegreeLieFiltration.comparisonFiltrationLayerEquiv]
    rfl
  refine ⟨c, fun j k => ?_⟩
  rw [hval]
  exact hb _ k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_model {p q : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q) :
    ∃ E : RationalFilteredNilmanifold
        (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
        (max s (Fintype.card (ReplicatedIndex bound)))
        (finrank ℚ (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))),
      E.filtration = M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1) ∧
      E.lattice = M.comparisonLattice p B hB hstable ∧
      E.GeometryComplexityLE (comparisonGeometryBudget (∑ i, bound i) p q) ∧
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (E.basis j).val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := M.comparisonAmbient p B hB hstable
  let K := M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1)
  let F := M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)
  let C := comparisonBasisBudget (∑ i, bound i) p
  let R := (p + q + 4) ^ 2 + C + 3
  have hC : 0 ≤ C := by dsimp [C, comparisonBasisBudget]; positivity
  have hCR : C ≤ R := by dsimp [R]; nlinarith only [sq_nonneg (p + q + 4)]
  have hP : P.GeometryComplexityLE R :=
    (M.comparisonAmbient_geometry B hB hstable hM.1 hE).mono P
      (by dsimp [R]; linarith)
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis hM 1
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hbK (j k) : rationalLogHeight (P.basis.repr (M.comparisonToAmbient (bK j)) k) ≤ R :=
    (M.comparisonAmbient_point_logHeight p B hB hstable (bK j) (hb j) k).trans hCR
  have hlayers (n : Fin (max s (Fintype.card (ReplicatedIndex bound)) + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight
          (P.basis.repr (M.comparisonToAmbient (a j : K)) k) ≤ R := by
    obtain ⟨a, ha⟩ := M.exists_comparison_filtration_basis hM (n.val + 1) (by omega)
    exact ⟨a, fun j k =>
      (M.comparisonAmbient_point_logHeight p B hB hstable (a j) (ha j) k).trans hCR⟩
  obtain ⟨E, hEF, hEb, hEL, hgeom⟩ := P.exists_model_of_embedding_logHeight F bK
    M.comparisonToAmbient M.comparisonToAmbient_injective hP hbK hlayers
  refine ⟨E, hEF, hEL, ?_, ?_⟩
  · simpa only [R, C, comparisonGeometryBudget, add_assoc,
      show (3 : ℝ) + 3 = 6 by norm_num] using hgeom
  · intro j k
    rw [hEb]
    exact hb j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_top_quotient {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
        Q.filtration = D.filtration.quotientTop ∧
        Q.lattice = D.lattice.map
          (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
        Q.GeometryComplexityLE ((p + 3) ^ 11) ∧
        (∀ i k, rationalLogHeight (Q.basis.repr
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis i)) k) ≤ (p + 3) ^ 5) ∧
        ∃ w : Fin n → ℕ, ∀ j, Q.filtration.layer j = Submodule.span ℚ (Q.basis '' {i | j ≤ w i}) := by
  classical
  obtain ⟨b, w, N, _, _, hF, _, hinverse, hbracket, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let Q := D.filtration.topQuotientModel b w hF D.lattice N hN hin hout
  have hdim : finrank ℚ L = d := by simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hn : Fintype.card {i : Fin (finrank ℚ L) // ¬ s + 1 ≤ w i} ≤ d := by
    simpa only [Fintype.card_fin, hdim] using
      Fintype.card_subtype_le (fun i : Fin (finrank ℚ L) => ¬ s + 1 ≤ w i)
  have hp1 : 0 ≤ p + 1 := by linarith
  have hpPow : p + 1 ≤ (p + 3) ^ 11 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      (le_power_budget hp1 (by decide : 1 ≤ 11))
  have hpr : p ≤ (p + 3) ^ 11 := (by linarith : p ≤ p + 1).trans hpPow
  have hbase : 1 ≤ p + 3 := by linarith
  have h9 : (p + 3) ^ 9 ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hbase (by decide)
  have hgeom : Q.GeometryComplexityLE ((p + 3) ^ 11) := by
    apply D.filtration.topQuotientModel_geometry b w hF D.lattice N hN hin hout (by positivity)
    apply D.filtration.ofAdaptedBasis_geometry b w hF D.lattice N hN hin hout (by positivity)
    · exact (by simpa only [hdim] using hD.1 : (finrank ℚ L : ℝ) ≤ p).trans hpr
    · exact hNp.trans (Real.exp_le_exp.mpr h9)
    · exact hbracket
  refine ⟨_, hn, Q, rfl, rfl, hgeom, ?_, quotientFinWeight w {i | s + 1 ≤ w i}, ?_⟩
  · intro i k
    have hspan : (D.filtration.layerIdeal (s + 1)).toSubmodule =
        Submodule.span ℚ (b '' {i | s + 1 ≤ w i}) := hF (s + 1)
    have hcoord := quotientFinBasis_repr_mk b (D.filtration.layerIdeal (s + 1))
      {i | s + 1 ≤ w i} hspan (D.basis i) k
    exact (congrArg rationalLogHeight hcoord).le.trans (hinverse i _)
  · intro j
    exact D.filtration.quotientFinBasis_layers b w hF (D.filtration.layerIdeal (s + 1)) le_rfl
      {i | s + 1 ≤ w i} (hF (s + 1)) j

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TopInvariantIntegerExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_topInvariant_integer_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) T.eval) := by
  obtain ⟨a, _, hdescent⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D w T p hp hT hinv
  let q := (p + 3) ^ 11
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + 3 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 1 ≤ 11)
  obtain ⟨n, _, Q, hQF, hQL, hQ, he, _⟩ := D.exists_controlled_top_quotient hp hT.1
  have heq : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ q := by
    intro i j
    apply (he j i).trans
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 5 ≤ 11)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, _, hS, hSe⟩ := hdescent D Q hQF hQL T q hq (hT.mono hpq) hQ heq hinv
  have hfinal : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, R, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨NativeIntegerExpansion.ofTest S (hS.mono hfinal) (fun x => (hSe x).symm)⟩

noncomputable def topInvariantIntegerExponent (s : ℕ) : ℕ :=
  (exists_topInvariant_integer_expansion.{0} s).choose

theorem topInvariant_integer_expansion {L σ : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {w : σ → ℕ}
    (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = T.observable x) :
    Nonempty (NativeIntegerExpansion w s
      ((p + topInvariantIntegerExponent s) ^ topInvariantIntegerExponent s) T.eval) :=
  (exists_topInvariant_integer_expansion s).choose_spec.2 D T hp hT hinv

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def comparisonDescentBudget (s : ℕ) (p : ℝ) : ℝ :=
  (comparisonProductCost p + RationalFilteredNilmanifold.topInvariantIntegerExponent s) ^
    RationalFilteredNilmanifold.topInvariantIntegerExponent s

end Erdos3

end

section

namespace Erdos3

noncomputable def comparisonEquivalenceBudget (s : ℕ) (p : ℝ) : ℝ :=
  comparisonDescentBudget s p + ((s + 1).factorial + 1 : ℝ) * (p + 1)

theorem comparisonEquivalenceBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    comparisonDescentBudget s p ≤ comparisonEquivalenceBudget s p ∧
    p ≤ comparisonEquivalenceBudget s p ∧
    ((s + 1).factorial : ℝ) * p ≤ comparisonEquivalenceBudget s p := by
  have hdescent : 0 ≤ comparisonDescentBudget s p := by
    dsimp [comparisonDescentBudget, comparisonProductCost]
    positivity
  have hf : 0 ≤ ((s + 1).factorial : ℝ) := Nat.cast_nonneg _
  dsimp [comparisonEquivalenceBudget]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exists_comparisonEquivalence_cost (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → comparisonEquivalenceBudget s p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let a := RationalFilteredNilmanifold.topInvariantIntegerExponent s
  let P := ((X + 3) ^ 2 + 3 * X + 5 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + Polynomial.C ((s + 1).factorial + 1) * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [comparisonEquivalenceBudget, comparisonDescentBudget, comparisonProductCost,
    a, X, P, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_controlled_group_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : D.RealGroup, ∃ (ε γ : D.RealGroup) (A : ℝ≥0),
        γ ∈ D.realLattice ∧ g = ε * γ ∧ 0 < A ∧ (A : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        letI := D.metricSpace
        LipschitzWith A (fun x : D.Space => ε • x) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD g
  have hcost : normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, hApos, hA, hLip⟩ := hleft D p hp hD
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  exact ⟨ε, γ, A, hγ, hfactor, hApos, hA.trans (Real.exp_le_exp.mpr hcost), hLip ε hε⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeDilationPairProjections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realDilationPairProjection_mem (q : ℚ) (j : Fin 2) {n : ℕ}
    {g : (F.dilationPairFiltration q).realification.Group}
    (hg : g ∈ (F.dilationPairFiltration q).realification.subgroup n) :
    F.realDilationPairProjection q j g ∈ F.realification.subgroup n := by
  have hm := (F.realifiedDilationPairEquiv_mem_layer q n g.coord).mp hg
  change (F.realDilationPairProjection q j g).coord ∈ F.realification.layer n
  rw [F.realDilationPairProjection_coord]
  fin_cases j
  · exact hm.1
  · exact hm.2.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def dilationSpaceProjection (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hE : E.lattice = M.dilationPairLattice q) (j : Fin 2) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (M.filtration.ordinary.realDilationPairProjection q j)
    (realificationMap_subgroup (M.filtration.ordinary.dilationPairProjection q j) _ _
      (by rw [hE]; exact M.dilationPairProjection_lattice q j))

theorem dilationSpaceProjection_smul (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hE : E.lattice = M.dilationPairLattice q) (j : Fin 2) (g : E.RealGroup) (x : E.Space) :
    M.dilationSpaceProjection q E hE j (g • x) =
      M.filtration.ordinary.realDilationPairProjection q j g •
        M.dilationSpaceProjection q E hE j x := cosetMap_smul _ _ _ _ _ _

theorem dilationSpaceProjection_lipschitz (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hEL : E.lattice = M.dilationPairLattice q) (j : Fin 2)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection q j (E.basis a)) k) ≤ p) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.dilationSpaceProjection q E hEL j) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D (M.filtration.ordinary.dilationPairProjection q j)
        (by rw [hEL]; exact M.dilationPairProjection_lattice q j)
        hp hE hD (fun k a => hheight a k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_dilation_family {σ I : Type*} [Fintype I]
    {s : ℕ} {p b r : ℝ} (f : I → (σ → ℤ) → ℂ) (q : ℤ) (t : ℕ)
    (R : NativeIntegerModelFamily (fun _ : σ => 1) s b (dilationTensorCrossProduct f q t))
    (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hpr : p ≤ r) (htr : ((q ^ t).natAbs : ℝ) * p ≤ r) (hbr : b ≤ r) :
    NativeIntegerVectorEquivalence s r (integerDilationVector f q) (signedTensorVector f (q ^ t)) := by
  refine {
    left_dimension := hcard.trans (Real.exp_le_exp.mpr hpr)
    right_dimension := ?_
    expansion := ?_ }
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ (q ^ t).natAbs := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
      _ = Real.exp (((q ^ t).natAbs : ℝ) * p) := (Real.exp_nat_mul p _).symm
      _ ≤ Real.exp r := Real.exp_le_exp.mpr htr
  · intro a b
    exact ⟨(NativeIntegerExpansion.ofModelFamily R (a, b)).mono hbr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (q : ℚ)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
  (hEL : E.lattice = M.dilationPairLattice q)

noncomputable def dilationObservable (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ) (x : E.Space) : ℂ :=
  u₀ (ε • M.dilationSpaceProjection q E hEL 0 x) *
    star (signedTensorProduct m (fun a => u a (ε • M.dilationSpaceProjection q E hEL 1 x)))

theorem dilationObservable_mk (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ) (g : E.RealGroup) :
    M.dilationObservable q E hEL m ε u₀ u (QuotientGroup.mk g) =
      u₀ (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection q 0 g)) *
        star (signedTensorProduct m (fun a => u a
          (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection q 1 g)))) := rfl

theorem dilationObservable_norm_le (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (h₀ : ∀ x, ‖u₀ x‖ ≤ 1) (hu : ∀ a x, ‖u a x‖ ≤ 1) (x : E.Space) :
    ‖M.dilationObservable q E hEL m ε u₀ u x‖ ≤ 1 := by
  simp only [dilationObservable, norm_mul, norm_star]
  simpa only [mul_one] using mul_le_mul (h₀ _)
    (signedTensorProduct_norm_le m _ (fun a => hu a _))
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeComparisonProjections
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p B hB hstable)

noncomputable def comparisonFirstSpace : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)))
    (realificationMap_subgroup _ _ _ (by rw [hEL]; exact M.comparisonLattice_first p B hB hstable))

noncomputable def comparisonSecondSpace : E.Space → (M.squarefreeModel p B hB hstable).Space :=
  cosetMap E.realLattice (M.squarefreeModel p B hB hstable).realLattice
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)))
    (realificationMap_subgroup _ _ _ (by rw [hEL]; exact M.comparisonLattice_second p B hB hstable))

theorem comparisonFirstSpace_mk (g : E.RealGroup) :
    M.comparisonFirstSpace p B hB hstable E hEL (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)) g) := rfl

theorem comparisonSecondSpace_mk (g : E.RealGroup) :
    M.comparisonSecondSpace p B hB hstable E hEL (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)) g) := rfl

theorem comparisonFirstSpace_smul (g : E.RealGroup) (x : E.Space) :
    M.comparisonFirstSpace p B hB hstable E hEL (g • x) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)) g •
        M.comparisonFirstSpace p B hB hstable E hEL x := cosetMap_smul _ _ _ _ _ _

theorem comparisonSecondSpace_smul (g : E.RealGroup) (x : E.Space) :
    M.comparisonSecondSpace p B hB hstable E hEL (g • x) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)) g •
        M.comparisonSecondSpace p B hB hstable E hEL x := cosetMap_smul _ _ _ _ _ _

variable
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]

theorem comparisonFirstSpace_lipschitz
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {q : ℝ} (hq : 0 ≤ q) (hD : D.GeometryComplexityLE q) (hE : E.GeometryComplexityLE q)
    (hheight : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ q) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.comparisonFirstSpace p B hB hstable E hEL) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))
        (by rw [hEL]; exact M.comparisonLattice_first p B hB hstable)
        hq hE hD (fun k j => hheight j k) x y

theorem comparisonSecondSpace_lipschitz
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    {q : ℝ} (hq : 0 ≤ q)
    (hA : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q)
    (hE : E.GeometryComplexityLE q)
    (hheight : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ q) :
    letI := E.metricSpace
    letI := (M.squarefreeModel p B hB hstable).metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.comparisonSecondSpace p B hB hstable E hEL) := by
  let := E.metricSpace
  let := (M.squarefreeModel p B hB hstable).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E (M.squarefreeModel p B hB hstable)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))
        (by rw [hEL]; exact M.comparisonLattice_second p B hB hstable)
        hq hE hA (fun k j => hheight j k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedComparisonOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem comparisonSpaceOrbit_projections (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (E : RationalFilteredNilmanifold
      (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
      (max s (Fintype.card (ReplicatedIndex bound))) r)
    (hEL : E.lattice = M.comparisonLattice p B hB hstable)
    (g : M.filtration.realification.PolynomialOrbit)
    (hg : M.filtration.realification.polynomialOrbitEval 0 g = 1) (x : σ → ℤ) :
    let π := fun i : ReplicatedIndex bound => i.1
    let z := (M.filtration.comparisonFiltration π).realification.polynomialOrbitEval
      (fun _ => 1) x (M.filtration.compareRealOrbit π g)
    M.comparisonFirstSpace p B hB hstable E hEL (QuotientGroup.mk z) =
      QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) ∧
    M.comparisonSecondSpace p B hB hstable E hEL (QuotientGroup.mk z) =
      QuotientGroup.mk ((M.filtration.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun i => x (π i)) (M.filtration.polarizeRealOrbit π g)) := by
  have h := M.filtration.compareRealOrbit_projections
    (fun i : ReplicatedIndex bound => i.1) g hg x
  constructor
  · simpa only [comparisonFirstSpace_mk, realificationMap] using
      congrArg (fun y : D.RealGroup => (QuotientGroup.mk y : D.Space)) h.1
  · simpa only [comparisonSecondSpace_mk, realificationMap] using
      congrArg (fun y : (M.squarefreeModel p B hB hstable).RealGroup =>
        (QuotientGroup.mk y : (M.squarefreeModel p B hB hstable).Space)) h.2

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_normalized_comparison_orbit (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (E : RationalFilteredNilmanifold
      (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
      (max s (Fintype.card (ReplicatedIndex bound))) r)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    (hEL : E.lattice = M.comparisonLattice p B hB hstable)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    let g₀ := M.filtration.realification.normalizeMultidegreeOrbit g ε γ
    ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 h = 1 ∧
      ∀ x : σ → ℤ,
        ε • M.comparisonFirstSpace p B hB hstable E hEL
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) ∧
        M.comparisonSecondSpace p B hB hstable E hEL
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) =
            QuotientGroup.mk
              ((M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).realification.polynomialOrbitEval
                (fun j => x j.1) (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g₀)) := by
  let π := fun j : ReplicatedIndex bound => j.1
  let g₀ := M.filtration.realification.normalizeMultidegreeOrbit g ε γ
  have hg₀ : M.filtration.realification.polynomialOrbitEval 0 g₀ = 1 :=
    M.filtration.realification.normalizeMultidegreeOrbit_zero g ε γ hfactor
  have hF : (M.filtration.comparisonFiltration π).realification = E.filtration.realification := by rw [hEF]
  let h := (M.filtration.comparisonFiltration π).realification.orbitEquivOfEq hF (fun _ : σ => 1)
    (M.filtration.compareRealOrbit π g₀)
  have heval (x : σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x h =
      (M.filtration.comparisonFiltration π).realification.polynomialOrbitEval _ x
        (M.filtration.compareRealOrbit π g₀) :=
    (M.filtration.comparisonFiltration π).realification.orbitEquivOfEq_eval hF _ _ x
  refine ⟨h, (heval 0).trans (M.filtration.compareRealOrbit_zero π g₀), fun x => ?_⟩
  rw [heval]
  obtain ⟨h₁, h₂⟩ := M.comparisonSpaceOrbit_projections p B hB hstable E hEL g₀ hg₀ x
  constructor
  · rw [h₁]
    change (QuotientGroup.mk (ε * M.filtration.realification.polynomialOrbitEval x g₀) : D.Space) = _
    change (QuotientGroup.mk (ε * M.filtration.realification.polynomialOrbitEval x
      (M.filtration.realification.normalizeMultidegreeOrbit g ε γ)) : D.Space) = _
    rw [M.filtration.realification.normalizeMultidegreeOrbit_eval]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)
  · exact h₂

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

theorem exists_of_unit_data {σ I : Type*} {L : Type}
    [Fintype σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
    (M : D.MultidegreeStructure bound) (hstep : t = ∑ i, bound i)
    {p : ℝ} (hM : M.ComplexityLE p)
    (g : M.filtration.realification.PolynomialOrbit)
    (V : D.UnitVerticalObservable (D.filtration.realification.subgroup t) I p)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp p) :
    ∃ W : NativeMultidegreeNilcharacter bound p, ∃ e : I ≃ Fin W.outputDim,
      W.dim = d ∧ ∀ i x, W.eval (e i) x = V.observable i
        (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) := by
  classical
  subst hstep
  let V' : D.UnitVerticalObservable (M.realSubgroup bound) I p :=
    { V with
      vertical := fun i z hz x => V.vertical i z (M.realSubgroup_top ▸ hz) x
      integral := fun z hz hL => V.integral z (M.realSubgroup_top ▸ hz) hL }
  obtain ⟨i, _⟩ := exists_large_unit_coordinate
    (fun i => V.observable i (QuotientGroup.mk 1)) (V.unit _)
  let W : NativeMultidegreeNilcharacter bound p :=
    { L := L
      dim := d
      model := D
      multi := M
      complexity := hM
      orbit := g
      outputDim := Fintype.card I
      output_pos := Fintype.card_pos_iff.mpr ⟨i⟩
      output_bound := hI
      vertical := V'.reindex (Fintype.equivFin I) }
  refine ⟨W, Fintype.equivFin I, rfl, ?_⟩
  intro i x
  change V.observable ((Fintype.equivFin I).symm ((Fintype.equivFin I) i)) _ = _
  rw [Equiv.symm_apply_apply]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

theorem tensorPower_eval (n : ℕ) (a : Fin (W.outputDim ^ n)) (x : σ → ℤ) :
    (W.tensorPower n).eval a x = ∏ j, W.eval ((tensorIndexEquiv W.outputDim n).symm a j) x := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.tensorPower_tensor_eval
    {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter bound p) (q t : ℕ) (ht : 1 ≤ t)
    (a : Fin q → Fin (W.outputDim ^ (q ^ (t - 1)))) (x : σ → ℤ) :
    tensorVector (W.tensorPower (q ^ (t - 1))).eval q a x =
      signedTensorVector W.eval ((q : ℤ) ^ t) (rootTensorIndex W.outputDim q t ht a) x := by
  unfold tensorVector
  simp_rw [W.tensorPower_eval]
  have hnonneg : 0 ≤ (q : ℤ) ^ t := pow_nonneg (Int.natCast_nonneg q) _
  simp only [signedTensorVector, signedTensorProduct, if_neg (not_lt.mpr hnonneg)]
  exact product_flatten (rootTensorEquiv q t ht) _

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

structure SymmetricSquarefreeUnitData (p : ℝ) (η : L →ₗ[ℚ] ℚ) (q : ℝ) where
  grid : ℕ
  grid_pos : 0 < grid
  stable : M.SquarefreeGridStable p grid
  complexity : (M.squarefreeModelMultidegree p grid grid_pos stable).ComplexityLE q
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  observable : (M.squarefreeModel p grid grid_pos stable).UnitVerticalObservable
    ((M.squarefreeModel p grid grid_pos stable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound)))
    (SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin coordinateCount)) q
  frequency : observable.frequency = M.filtration.replicatedFrequency η
  invariant : ∀ (e : ReplicatedPermutation bound) k x,
    observable.observable k (M.squarefreeSpacePermute p grid grid_pos stable e x) =
      observable.observable k x
  dimension :
    (Fintype.card (SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound))
      (Fin coordinateCount)) : ℝ) ≤ Real.exp q

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ : Type} {L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)

noncomputable def comparisonVerticalProduct (ε : D.RealGroup)
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : E.Space) : ℂ :=
  (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x) *
  star (U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x))

theorem comparisonVerticalProduct_norm (ε : D.RealGroup)
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : E.Space) : ‖M.comparisonVerticalProduct V U E hEL ε a k x‖ ≤ 1 := by
  unfold comparisonVerticalProduct
  rw [norm_mul, norm_star]
  simpa only [mul_one] using mul_le_mul
    ((V.tensorPower (multidegreeFactorial bound)).norm a _) (U.observable.norm k _)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  {M : D.MultidegreeStructure bound} {p q : ℝ} {η : L →ₗ[ℚ] ℚ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (U : M.SymmetricSquarefreeUnitData p η q)

noncomputable def eval (g : M.filtration.realification.PolynomialOrbit)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) : ℂ :=
  U.observable.observable k (QuotientGroup.mk
    ((M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).realification.polynomialOrbitEval
      x (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g)))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  {M : D.MultidegreeStructure bound} {p q r : ℝ} {η : L →ₗ[ℚ] ℚ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

noncomputable def mono (U : M.SymmetricSquarefreeUnitData p η q) (hqr : q ≤ r) :
    M.SymmetricSquarefreeUnitData p η r := {
  U with
  complexity := U.complexity.mono _ hqr
  observable := U.observable.mono hqr
  dimension := U.dimension.trans (Real.exp_le_exp.mpr hqr) }

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialFinBasis_evaluation_height {p : ℝ} (hM : M.ComplexityLE p) (i k) :
    RationalHeightLE (D.basis.repr
      (M.filtration.positivePolynomialEvaluation (M.positivePolynomialFinBasis p i)) k) ⌈Real.exp p⌉₊ := by
  rw [positivePolynomialFinBasis, Basis.reindex_apply]
  exact M.positivePolynomialBasis_evaluation_height hM _ _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

omit [DecidableEq σ] [DecidablePred (· ∈ J)] in
theorem positivePolynomialDownsetBasis_structure (p : ℝ) (i j k) :
    lieStructureConstants (M.positivePolynomialDownsetBasis J hJ p) i j k =
      lieStructureConstants (M.positivePolynomialBasis p) i.val j.val k.val := by
  exact supportedQuotientBasis_lieStructure _ _ _
    (M.filtration.positivePolynomialDownsetIdeal_eq_span (M.positiveCoefficientBasis p) J hJ) i j k

theorem positivePolynomialDownsetFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (M.filtration.positivePolynomialDownsetDegreeBasis (M.positiveCoefficientBasis p) J hJ n j).val k) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDownsetDegreeBasis_height
    (M.positiveCoefficientBasis p) J hJ n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def positivePolynomialEvaluationCosetMap (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) :
    (M.positivePolynomialModel p B hB hstable).Space → D.Space :=
  cosetMap _ _
    (realificationMap (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation)
    (realificationMap_subgroup M.filtration.positivePolynomialEvaluation _ _ hmap)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]

theorem positivePolynomialEvaluationCosetMap_lipschitz {p : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) :
    letI := (M.positivePolynomialModel p B hB hstable).metricSpace
    letI := D.metricSpace
    LipschitzWith (coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊)
      (M.positivePolynomialEvaluationCosetMap p B hB hstable hmap) := by
  let := (M.positivePolynomialModel p B hB hstable).metricSpace
  let := D.metricSpace
  have h := lipschitz_realificationMap_quotient
    (M.positivePolynomialModel p B hB hstable).basis D.basis
    M.filtration.positivePolynomialEvaluation
    (M.positivePolynomialLattice p B hstable) D.lattice hmap B D.grid hB D.grid_pos
    (M.positivePolynomialModel p B hB hstable).outer_grid D.outer_grid ⌈Real.exp p⌉₊
    (fun k i => M.positivePolynomialFinBasis_evaluation_height hM i k)
  simp only [Fintype.card_fin] at h
  convert h using 1
  rfl

theorem exists_positivePolynomial_observable_pullback {p q : ℝ} (hM : M.ComplexityLE p)
    (hpq : p ≤ q) (hdim : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation))
    (u : D.Space → ℂ) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp q)
    (hu : letI := D.metricSpace; LipschitzWith ℓ u) :
    ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp (q + (q + 3) ^ 2) ∧
      (letI := (M.positivePolynomialModel p B hB hstable).metricSpace
       LipschitzWith K (u ∘ M.positivePolynomialEvaluationCosetMap p B hB hstable hmap)) := by
  let := D.metricSpace
  let := (M.positivePolynomialModel p B hB hstable).metricSpace
  let C := coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊
  refine ⟨ℓ * C, ?_, hu.comp (M.positivePolynomialEvaluationCosetMap_lipschitz hM B hB hstable hmap)⟩
  calc
    (ℓ * C : ℝ≥0) ≤ Real.exp q * Real.exp ((q + 3) ^ 2) :=
      mul_le_mul hℓ (M.positivePolynomialEvaluation_metric_bound hM hpq hdim)
        C.coe_nonneg (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialVectorOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial NilpotentLieBCHGroup

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

noncomputable def positivePolynomialQuotientProductModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :=
  RationalFilteredNilmanifold.pi (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ComparisonProductMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct NNReal

variable {σ : Type} {L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

theorem comparisonVerticalProduct_lipschitz {R : ℝ} (hR : 0 ≤ R)
    (hD : D.GeometryComplexityLE R)
    (hQ : (M.squarefreeModel p U.grid U.grid_pos U.stable).GeometryComplexityLE R)
    (hE : E.GeometryComplexityLE R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (ε : D.RealGroup) (A : ℝ≥0)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount)) :
    letI := E.metricSpace
    let P : ℝ≥0 := ⟨Real.exp ((R + 3) ^ 2), (Real.exp_pos _).le⟩
    LipschitzWith ((V.tensorPower (multidegreeFactorial bound)).lipBound * (A * P) +
      U.observable.lipBound * P) (M.comparisonVerticalProduct V U E hEL ε a k) := by
  let := D.metricSpace
  let := (M.squarefreeModel p U.grid U.grid_pos U.stable).metricSpace
  let := E.metricSpace
  have h₁ := ((V.tensorPower (multidegreeFactorial bound)).lipschitz a).comp
    (hε.comp (M.comparisonFirstSpace_lipschitz p U.grid U.grid_pos U.stable E hEL hR hD hE hfirst))
  have h₂ := (U.observable.lipschitz k).comp
    (M.comparisonSecondSpace_lipschitz p U.grid U.grid_pos U.stable E hEL hR hQ hE hsecond)
  have h := lipschitz_mul_star_of_bounds
      (fun x => (V.tensorPower (multidegreeFactorial bound)).observable a
        (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x))
      (fun x => U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x))
      (Bf := 1) (Bg := 1) h₁ h₂
      (fun x => (V.tensorPower (multidegreeFactorial bound)).norm a _) (fun x => U.observable.norm k _)
  simp only [one_mul] at h
  rw [add_comm] at h
  convert h using 1
  all_goals rfl

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeDilationObservableMetric
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem dilationObservable_lipschitz (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hEL : E.lattice = M.dilationPairLattice q)
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection q j (E.basis a)) k) ≤ p)
    (m : ℤ) (ε : D.RealGroup) (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (K A : ℝ≥0) (h₀ : ∀ x, ‖u₀ x‖ ≤ 1) (hu : ∀ j x, ‖u j x‖ ≤ 1)
    (hLip₀ : letI := D.metricSpace; LipschitzWith K u₀)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith K (u j))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    letI := E.metricSpace
    LipschitzWith ((m.natAbs + 1 : ℝ≥0) *
      (K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)))
      (M.dilationObservable q E hEL m ε u₀ u) := by
  let := E.metricSpace
  let := D.metricSpace
  apply lipschitz_signed_tensor_cross_product m
    (fun x => u₀ (ε • M.dilationSpaceProjection q E hEL 0 x))
    (fun j x => u j (ε • M.dilationSpaceProjection q E hEL 1 x))
  · exact hLip₀.comp (hε.comp (M.dilationSpaceProjection_lipschitz q E hEL 0 hp hD hE (hheight 0)))
  · exact fun j => (hLip j).comp
      (hε.comp (M.dilationSpaceProjection_lipschitz q E hEL 1 hp hD hE (hheight 1)))
  · exact fun x => h₀ _
  · exact fun j x => hu j _

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

theorem rationalDilation_eval_rescaled (r : ℚ) (q : ℤ) (hr : r * (q : ℚ) = 1)
    (a : Fin W.outputDim) (x : σ → ℤ) :
    (W.rationalDilation r).eval a (fun i => q * x i) = W.eval a x := by
  unfold eval rationalDilation
  rw [W.multi.filtration.realification.rationalDilationOrbit_rescaled r q hr]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem topInvariant_integer_expansion_of_step {L σ : Type}
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s t d : ℕ} (ht : t = s + 1) (D : RationalFilteredNilmanifold L t d)
    {w : σ → ℕ} (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup t, ∀ x,
      T.observable (z • x) = T.observable x) :
    Nonempty (NativeIntegerExpansion w s
      ((p + topInvariantIntegerExponent s) ^ topInvariantIntegerExponent s) T.eval) := by
  subst t
  exact topInvariant_integer_expansion D T hp hT hinv

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

noncomputable def projectedDenominator : ℕ :=
  matrixDenominator (fun i j => (pi (I.productModels D.index)).basis.repr (D.adapted.basis j) i) *
    D.denominator

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedCanonicalTensor (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (mixedSampledInput (mixedCanonicalSample v.val) x))

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end


