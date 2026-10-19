-- Prove2me | Definitions.Def_OAIE3v2B195
-- name    : OAIE3v2B195
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:52:51.142181+00:00
-- url     : https://prove2.me/theorems/031e7925-0e17-4bc3-8ae5-bea3063162ee
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 198 of 311
-- statement:
--   Definitions bundle 198 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B171`, `OAIE3v2B172`, `OAIE3v2B173`, `OAIE3v2B174`, `OAIE3v2B176` of this split.
--
--   Modules: `Dynamics/AllocatedFullSiteRadiusBudget.lean`, `Dynamics/AllocatedUnitSiteEarlyBudget.lean`, `Estimates/AllocatedCoverLogBounds.lean`, `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/AllocatedFullSiteRadius.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/NativeLocalPivotVerticalPartners.lean`, `Estimates/NormalizedFixedPatchFunction.lean`, `Estimates/SelectedJointSiteDomination.lean`, `Geometry/AllocatedSiteTermSupport.lean`, `Geometry/AllocatedSupportedBufferedPhysicalFactorization.lean`, `Geometry/MixedReplicatedCoordinates.lean`, `Geometry/PositiveCyclicCoordinateProduct.lean`, `Geometry/ScalarReferenceNativeDetectionCoordinateEquiv.lean`, `Geometry/SelectedCenteredJointSupport.lean`, `Lattices/NormalizedTwistAffineCells.lean`, `Lattices/RetainedPhysicalCRT.lean`, `Lattices/SelectedResidueCutoffDomination.lean`, `Linear/AllocatedFixedKernelCover.lean`, `Linear/AllocatedKernelSiteMask.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Polynomial/PrescribedFastPolynomialFactorization.lean`, `Probability/AllocatedAmbientProjectedDensityMultiple.lean`, `Probability/PositiveDensityNormalization.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/AllocatedClippedFullGridGlobal.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`, `Sampling/AllocatedGridlessProfileBound.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B171
import Definitions.Def_OAIE3v2B172
import Definitions.Def_OAIE3v2B173
import Definitions.Def_OAIE3v2B174
import Definitions.Def_OAIE3v2B176

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PositiveCyclicCoordinateProduct
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] PositiveCyclicModel.lie PositiveCyclicModel.algebra
  PositiveCyclicModel.topology PositiveCyclicModel.topologicalAdd
  PositiveCyclicModel.continuousSMul PositiveCyclicModel.hausdorff

theorem exists_positive_coordinate_product {σ : Type} [Fintype σ]
    {s N : ℕ} [NeZero N] {p : ℝ} {f : σ → ZMod N → ℝ}
    (hp : 0 ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hf : ∀ i, PositiveCyclicNiltest.{0} s N p (f i)) :
    ∃ g : (σ → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
        (productNiltestBudget (raisedNiltestBudget p)) g) ∧
      ∀ x : σ → ZMod N, g (fun i => ((x i).val : ℤ)) = ∏ i, (f i (x i) : ℂ) := by
  classical
  let R := fun i => Classical.choice ((hf i).model_nonempty hp)
  let D := fun i => (R i).model
  let T := fun i => (R i).coordinateTest i
  let : FiniteDimensional ℚ (∀ i, (R i).L) := (productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, (R i).L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, (R i).L)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, (R i).L)) := realification_moduleTopology_t2 (productFinBasis D)
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hσ' : (Fintype.card σ : ℝ) ≤ raisedNiltestBudget p := hσ.trans (le_raisedNiltestBudget p)
  have hT : ∀ i, (T i).ComplexityLE (raisedNiltestBudget p) :=
    fun i => (R i).coordinateTest_complexity i
  let S := piNiltest D T hp' hσ' hT
  refine ⟨S.eval, ⟨NativeIntegerExpansion.ofTest S
    (piNiltest_complexity D T hp' hσ' hT) (fun _ => rfl)⟩, ?_⟩
  intro x
  change (piNiltest D T hp' hσ' hT).eval _ = _
  rw [piNiltest_eval]
  apply Finset.prod_congr rfl
  intro i _
  exact (R i).coordinateTest_evalCyclic i x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrescribedFastPolynomialFactorization
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_native_polynomial_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (weight : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weight i}))
      (w : σ → ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
      ∃ (a κ : D.RealGroup) (q : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        κ ∈ D.realLattice ∧
        D.filtration.realification.adaptedConstantGroupHom w a * q *
          D.filtration.realification.adaptedConstantGroupHom w κ = g ∧
        coefficients (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        D.filtration.realPolynomialSymbolHom D.basis weight hF w q =
          D.filtration.realPolynomialSymbolHom D.basis weight hF w g := by
  obtain ⟨c, _, hnormalize⟩ := exists_bounded_polynomial_normalization s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D weight hF w p hp hD g
  have hbound : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨a, κ, q, ha, hκ, hfactor, hzero, hsymbol⟩ :=
    hnormalize D.filtration D.basis weight hF w D.lattice D.grid ⌈Real.exp p⌉₊ (p + 1)
      D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) (by linarith)
      (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  exact ⟨a, κ, q, fun i => (ha i).trans (Real.exp_le_exp.mpr hbound), hκ,
    hfactor, hzero, hsymbol⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

theorem selectedJointFiniteLaw_weight (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (z : A × rectangularWeightIndices 0 W 1) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).weight z =
      (A.card : ℝ)⁻¹ * (selectedResidueSmoothPMF modulus T W hW hZ z.2.val).toReal *
        D z.1.val z.2.val / selectedJointDensityMass A modulus T W D := by
  rw [selectedJointFiniteLaw, FiniteProbabilityWeights.reweightPositive_weight,
    selectedJointReference_densityMass, selectedResidueSmoothPMF_toReal]
  simp only [selectedJointReference, FiniteProbabilityWeights.prod,
    FiniteProbabilityWeights.uniformFinset, FiniteProbabilityWeights.uniform, Fintype.card_coe,
    selectedResidueFiniteLaw, finiteSupportProbability]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_weighted_native_vertical_partners
    {Ω K T σ : Type*} [Fintype Ω] [Fintype K] {L : K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)] {s : ℕ} {d : K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k)) {w : σ → ℕ}
    (Q : ∀ k, (D k).Niltest w)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (S : Ω → K → Finset T) (point : Ω → T → σ → ℤ)
    (weight : Ω → K → T → ℂ) {p q delta : ℝ}
    (hq : 0 ≤ q) (hpq : p ≤ q) (hdelta : 0 < delta)
    (hprecision : (delta / 2)⁻¹ ≤ Real.exp q)
    (hQ : ∀ k, (Q k).ComplexityLE p) (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hS : ∀ a ∈ H, ∀ k, (S a k).Nonempty)
    (hweight : ∀ a ∈ H, ∀ k t, t ∈ S a k → ‖weight a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, delta ≤
      ‖𝔼 t ∈ S a k, weight a k t * (Q k).eval (point a t)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE p ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 t ∈ S a k, weight a k t * (V k).eval (point a t)‖ := by
  classical
  choose I instI freq V hcard hheight hcert hvert hint hpres hobs happrox using
    fun k => (Q k).exists_vertical_decomposition_preserving_bounds_and_characters
      hq ((hQ k).mono hpq) (by positivity : 0 < delta / 2) hprecision
  let : ∀ k, Fintype (I k) := instI
  let rel : ∀ (_ : Ω) (k : K), I k → Prop := fun a k i =>
    delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤
      ‖𝔼 t ∈ S a k, weight a k t * (V k i).eval (point a t)‖
  have hex (a : Ω) (ha : a ∈ H) (k : K) : ∃ i, rel a k i := by
    have hh := exists_correlating_summand (hS a ha k) (weight a k)
      (fun t => star ((Q k).eval (point a t)))
      (fun i t => star ((V k i).eval (point a t))) hdelta (Real.exp_pos _)
      (hcard k) (hweight a ha k)
    apply (by simpa only [finiteCorrelation, star_star, rel] using hh)
    · intro t _
      simpa only [← star_sum, ← star_sub, norm_star] using happrox k (point a t)
    · simpa only [finiteCorrelation, star_star] using hcorr a ha k
  obtain ⟨choice, retained, hsub, hpos, hmass, hselected⟩ :=
    weighted_fixed_choices outer H hH rel hex hcard
  have hnonzero (k : K) : ∃ x, (V k (choice k)).observable x ≠ 0 := by
    by_contra! hz
    have hne : retained.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hpos
      simp only [FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hpos
    obtain ⟨a, ha⟩ := hne
    have he := hselected a ha k
    have heval (t : T) : (V k (choice k)).eval (point a t) = 0 := hz _
    change delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤ _ at he
    simp only [heval, mul_zero, Finset.expect_const_zero, norm_zero] at he
    exact (not_le_of_gt (by positivity : 0 < delta / (2 * Real.exp
      (verticalDecompositionBudget q)))) he
  refine ⟨fun k => freq k (choice k), fun k => V k (choice k), retained,
    hsub, hpos, hmass, ?_, fun k => hheight k (choice k), fun k => hvert k (choice k),
    fun k => hint k (choice k) (hnonzero k), fun k z c hc x => hpres k z c hc (choice k) x,
    hselected⟩
  intro k
  obtain ⟨_, ho, hn, hl⟩ := hcert k (choice k)
  have hcOriginal : (V k (choice k)).ComplexityLE p := by
    refine ⟨(hQ k).1, ?_⟩
    rw [hn, hl]
    exact (hQ k).2
  exact ⟨hcOriginal, ho, hn, hl, hn ▸ hcap k⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_localPivot_weighted_native_vertical_partners
    {Ω K T σ τ : Type*} [Fintype Ω] [Fintype K]
    {L : K → Type*} {Llocal : Ω → K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ a k, LieRing (Llocal a k)] [∀ a k, LieAlgebra ℚ (Llocal a k)]
    {s : ℕ} {d : K → ℕ} {sLocal dLocal : Ω → K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)]
    [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ a k, TopologicalSpace (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, IsTopologicalAddGroup (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, ContinuousSMul ℝ (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, T2Space (ℝ ⊗[ℚ] Llocal a k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (Dlocal : ∀ a k, RationalFilteredNilmanifold (Llocal a k) (sLocal a k) (dLocal a k))
    {w : σ → ℕ} {wLocal : τ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (P : ∀ a k, (Dlocal a k).Niltest wLocal)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (S : Ω → K → Finset T)
    (pointAmbient : Ω → T → σ → ℤ) (pointLocal : Ω → K → T → τ → ℤ)
    (twist : Ω → K → T → ℂ) {pNative pLocal r q : ℝ}
    (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hQ : ∀ k, (Q k).ComplexityLE pNative)
    (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hP : ∀ a ∈ H, ∀ k, (P a k).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ k t, t ∈ S a k → ‖twist a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, Real.exp (-r) ≤
      ‖𝔼 t ∈ S a k,
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE pNative ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 t ∈ S a k,
          ((P a k).eval (pointLocal a k t) * twist a k t) * (V k).eval (pointAmbient a t)‖ := by
  classical
  let weight : Ω → K → T → ℂ := fun a k t =>
    (Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)
  have hweight (a : Ω) (ha : a ∈ H) (k : K) (t : T) (ht : t ∈ S a k) :
      ‖weight a k t‖ ≤ 1 := by
    change ‖((Real.exp (-pLocal) : ℂ) *
      ((P a k).eval (pointLocal a k t) * twist a k t))‖ ≤ 1
    rw [← mul_assoc, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (exp_scaled_norm_le_one ((P a k).eval_budget (hP a ha k) _))).trans
      (htwist a ha k t ht)
  have hS (a : Ω) (ha : a ∈ H) (k : K) : (S a k).Nonempty := by
    by_contra hn
    have hh := hcorr a ha k
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hh
    simp only [Finset.expect_empty, norm_zero] at hh
    exact (not_le_of_gt (Real.exp_pos _)) hh
  have hnormalized (a : Ω) (ha : a ∈ H) (k : K) :
      Real.exp (-pLocal) * Real.exp (-r) ≤
        ‖𝔼 t ∈ S a k, weight a k t * (Q k).eval (pointAmbient a t)‖ := by
    change _ ≤ ‖𝔼 t ∈ S a k,
      ((Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)) *
        (Q k).eval (pointAmbient a t)‖
    rw [norm_expect_scaled_product _ _ (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hcorr a ha k) (Real.exp_nonneg _)
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint,
      hpres, hselected⟩ := exists_weighted_native_vertical_partners D Q outer H hH S
    pointAmbient weight (by linarith : 0 ≤ q) hpq (by positivity)
    (nativeLocalPivotVertical_inverse_precision_le_exp hprecision) hQ hcap hS hweight hnormalized
  refine ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint, hpres, ?_⟩
  intro a ha k
  have hs := hselected a ha k
  change (Real.exp (-pLocal) * Real.exp (-r)) /
      (2 * Real.exp (verticalDecompositionBudget q)) ≤
    ‖𝔼 t ∈ S a k,
      ((Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)) *
        (V k).eval (pointAmbient a t)‖ at hs
  rw [norm_expect_scaled_product _ _ (Real.exp_nonneg _), mul_div_assoc] at hs
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (-pLocal))).mp
    (by simpa only [mul_comm] using hs)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedReplicatedCoordinates
namespace OAI

section

namespace Erdos3

theorem mixedReplicatedInput_diagonal {s : ℕ} {α : Type*} (h n : α) :
    mixedReplicatedInput h (fun _ : Fin s => n) =
      fun j : MixedReplicatedIndex s => correlationInput h n j.1 := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rfl
  · rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem kernelCubeBox_site_le_exp {G : Type*} {q L : ℕ}
    (c : G → ℤ) (x : G → IntegerScalarCubeBox (Fin q) L) {P : ℝ}
    (hc : ∀ g, |(c g : ℝ)| ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (s : Finset (Fin q)) (g : G) :
    |((BooleanCubeKernel.affineSite (fun g => c g + (x g none : ℤ))
      (fun i g => (x g (some i) : ℤ)) s (some g) : ℤ) : ℝ)| ≤ Real.exp (P + (q + 2 : ℕ)) := by
  have hx (i) : |((x g i : ℤ) : ℝ)| ≤ Real.exp P := by
    have hi := Finset.mem_Ico.mp (x g i).property
    have hl : |((x g i : ℤ) : ℝ)| ≤ L := by exact_mod_cast abs_le.mpr ⟨hi.1, hi.2.le⟩
    exact hl.trans hL
  have hs : (s.card : ℝ) ≤ q := by
    exact_mod_cast (show s.card ≤ q from by simpa only [Fintype.card_fin] using s.card_le_univ)
  have hsum : |∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| ≤ (q : ℝ) * Real.exp P := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i ∈ s, Real.exp P := Finset.sum_le_sum (fun i _ => hx (some i))
      _ = (s.card : ℝ) * Real.exp P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg P)
  have hraw : |(c g : ℝ) + ((x g none : ℤ) : ℝ) + ∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| ≤
      ((q : ℝ) + 2) * Real.exp P := by
    have h := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hc g) (hx none))) hsum)
    nlinarith
  calc
    _ = |(c g : ℝ) + ((x g none : ℤ) : ℝ) + ∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| := by
      simp only [BooleanCubeKernel.affineSite, Int.cast_add, Int.cast_sum]
    _ ≤ ((q : ℝ) + 2) * Real.exp P := hraw
    _ ≤ Real.exp ((q : ℝ) + 2) * Real.exp P := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg P)
      linarith [Real.add_one_le_exp ((q : ℝ) + 2)]
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

omit [Fintype α] in
theorem allocatedPhysicalCube_root_bound (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ |(c k : ℝ)| + S.value := by
  have hv : |((Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k : ℤ) : ℝ)| ≤ S.value := by
    cases k with
    | inl g =>
      have hx := Finset.mem_Ico.mp (x g none).property
      change |((x g none : ℤ) : ℝ)| ≤ S.value
      exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
    | inr j =>
      have hy := Finset.mem_Ico.mp (y j none).property
      have hbound : |(y j none : ℤ)| ≤ allocatedPrincipalSides B U basis S j :=
        abs_le.mpr ⟨hy.1, hy.2.le⟩
      exact (by exact_mod_cast hbound : |((y j none : ℤ) : ℝ)| ≤
        allocatedPrincipalSides B U basis S j).trans
          (Nat.cast_le.mpr (allocatedPrincipalSides_le_scale B U basis S j))
  unfold allocatedPhysicalCubeRoot
  push_cast
  exact (abs_add_le _ _).trans (add_le_add le_rfl hv)

omit [Fintype α] in
theorem allocatedPhysicalCube_root_sum :
    (∑ k, |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)|) ≤
      allocatedPhysicalRootBudget B U basis S c := by
  calc
    _ ≤ ∑ k, (|(c k : ℝ)| + (S.value : ℝ)) :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_root_bound B U basis S c x y k)
    _ = _ := by simp [allocatedPhysicalRootBudget, Finset.sum_add_distrib]

omit [Fintype α] in
theorem allocatedPhysicalCube_root_budget (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤
      allocatedPhysicalRootBudget B U basis S c :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (allocatedPhysicalCubeRoot B U basis S c x y j : ℝ))
    (Finset.mem_univ k)).trans (allocatedPhysicalCube_root_sum B U basis S c x y)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedFixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_fixed_weight_patch_function_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ},
      ∀ (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
        (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (_hs : ∀ i, w i ≤ s) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p →
      (∀ a i, realPolynomialMass ((A a).center i) ≤ p) →
      (∀ a, ((Φ a).lip : ℝ) ≤ Real.exp p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
        (score : Ω → T → ℝ), (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤
        (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue (Φ a))) →
      ∃ (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
        (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ p + 1 / 4) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained, Real.exp (-((p + 2) ^ C)) ≤ (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (point a t))).patchValue Ψ) := by
  obtain ⟨a, ha, htop⟩ := exists_patch_top_net_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R : Polynomial ℕ := (X + 1) * (2 * X + 11)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (3 * R + (4 * R + 2) ^ a + X + 5)
  refine ⟨C, hC, ?_⟩
  intro X₀ Ω T _ _ _ d w A Φ hw hpos hs p hp hd hA hΦ outer productive localLaw point score hscore hpositive
  let r := (p + 1) * (2 * p + 11)
  let q := 4 * r
  have hr : 11 ≤ r := by dsimp only [r]; nlinarith
  have hpR : p + 1 ≤ r := by dsimp only [r]; nlinarith
  have hq : 0 ≤ q := by dsimp only [q]; linarith
  have hpq : p ≤ q := by dsimp only [q]; linarith
  have hbudget' : 3 * r + (q + 2) ^ a + p + 5 ≤ (p + 2) ^ C := by
    simpa [X, R, r, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + 2) ^ a := by positivity
  have hmassBudget : r + (q + 2) ^ a ≤ (p + 2) ^ C := by linarith
  have hscoreBudget : p + (r + 3) ≤ (p + 2) ^ C := by linarith
  have hLipBudget : 2 * r + 2 ≤ (p + 2) ^ C := by linarith
  obtain ⟨N, hN, _, hNerror, hNcount, hNlip⟩ :=
    exists_patch_kernel_mesh d hp (Real.exp_nonneg p) hd (le_refl (Real.exp p))
  let K : ℝ≥0 := (2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N
  have hKq : (K : ℝ) ≤ Real.exp q := hNlip.trans (Real.exp_le_exp.mpr (by dsimp only [q]; linarith))
  have hMq : p + 1 / 4 ≤ Real.exp q := by
    have h := (Real.add_one_le_exp p).trans (Real.exp_le_exp.mpr hpq)
    linarith
  obtain ⟨J, hJ, _, hJcount, hJsmall, hJerror⟩ :=
    htop d (p + 1 / 4) K q hq (by linarith) K.coe_nonneg (hd.trans hpq) hMq hKq
  have htwocount : 2 * ((N + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (r + 1) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp r := mul_le_mul h2 (by exact_mod_cast hNcount) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlocalScore : Real.exp (-q) ≤ Real.exp (-p) / (2 * ((N + 1 : ℕ) : ℝ) ^ d) :=
    exp_neg_le_div (by positivity) htwocount (by dsimp only [q]; linarith)
  have hhomogeneous : (K : ℝ) * patchTopNetError d s J (p + 1 / 4) ≤
      Real.exp (-p) / (4 * ((N + 1 : ℕ) : ℝ) ^ d) := by
    apply hJerror.trans
    have h := div_le_div_of_nonneg_right hlocalScore (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1; ring
  obtain ⟨i, B, localForm, retained, hB, hretained, hmass, hlocal⟩ :=
    fixed_weight_patch_function A Φ hw hpos hs hp (Real.exp_nonneg p) (Real.exp_pos (-p)) hA hΦ
      hN hNerror hJ hJsmall hhomogeneous outer productive localLaw point score hscore hpositive
  refine ⟨gridPatchKernel d N hN i, B, localForm, retained,
    hNlip.trans (Real.exp_le_exp.mpr hLipBudget), hB, hretained, ?_, ?_⟩
  · let D : ℝ := ((N + 1 : ℕ) : ℝ) ^ d * ((J + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s)
    have hD : 0 < D := by dsimp only [D]; positivity
    have hDupper : D ≤ Real.exp ((p + 2) ^ C) := by
      calc
        D ≤ Real.exp r * Real.exp ((q + 2) ^ a) := by
          exact mul_le_mul (by exact_mod_cast hNcount) (by exact_mod_cast hJcount)
            (by positivity) (Real.exp_nonneg _)
        _ = Real.exp (r + (q + 2) ^ a) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hmassBudget
    have hi : Real.exp (-((p + 2) ^ C)) ≤ 1 / D := by
      simpa only [neg_zero, Real.exp_zero] using
        exp_neg_le_div (P := (p + 2) ^ C) (a := 0) hD hDupper (by linarith)
    exact (mul_le_mul_of_nonneg_left hi (outer.mass_nonneg productive)).trans
      (by simpa only [mul_one_div, D] using hmass)
  · intro x hx
    have hfourcount : 4 * ((N + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (r + 3) := by
      have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
      calc
        _ ≤ Real.exp 3 * Real.exp r := mul_le_mul h4 (by exact_mod_cast hNcount) (by positivity) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact (exp_neg_le_div (by positivity) hfourcount hscoreBudget).trans (hlocal x hx)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_unrestricted_fixed_weight_patch_function (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {X Ω T : Type*} [Fintype X] [Fintype Ω] [Nonempty Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ},
      ∀ (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
        (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (_hs : ∀ i, w i ≤ s) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (∀ a, ((Φ a).lip : ℝ) ≤ Real.exp p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℤ)
        (score : Ω → T → ℝ), (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤ (localLaw a).mean (fun t =>
        score a t * ((A a).slots (fun i => (point a t i : ℝ))).patchValue (Φ a))) →
      ∃ (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
        (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ E)) ≤ outer.mass retained ∧
        ∀ a ∈ retained, Real.exp (-((p + 2) ^ E)) ≤ (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (fun i => (point a t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨C, hC, hfixed⟩ := exists_fixed_weight_patch_function_budget s
  let Z : Polynomial ℕ := Polynomial.X
  let Q := Z + Polynomial.C (s + 1) * (2 * Z + 1) ^ s + 2
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((Q + 2) ^ C + Q + 1)
  refine ⟨E, hE, ?_⟩
  intro X Ω T _ _ _ _ d w A Φ hw hpos hs p hp hd hX hΦ outer productive localLaw point score hscore hpositive
  let q : ℝ := p + ((s : ℝ) + 1) * (2 * p + 1) ^ s + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p ≤ q := by
    have : 0 ≤ ((s : ℝ) + 1) * (2 * p + 1) ^ s := by positivity
    dsimp only [q]
    linarith
  have hbudget' : (q + 2) ^ C + q + 1 ≤ (p + 2) ^ E := by
    simpa [Z, Q, q, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_one] using hbudget p hp
  have hpower : (q + 2) ^ C ≤ (p + 2) ^ E := by linarith
  have hmassBudget : q + 1 / 4 ≤ (p + 2) ^ E := by
    have : 0 ≤ (q + 2) ^ C := by positivity
    linarith
  choose norm hnorm hperm using fun a => (A a).exists_coefficient_normalized
  have hnormMass (a) (i) : realPolynomialMass ((norm a).center i) ≤ q := by
    have h := (norm a).center_mass_le_of_normalized hpos s hs (hnorm a) i
    have hbound : (((s + 1) * (Fintype.card X + d + 1) ^ s : ℕ) : ℝ) ≤
        ((s : ℝ) + 1) * (2 * p + 1) ^ s := by
      push_cast
      gcongr
      linarith
    have ht := h.trans hbound
    dsimp only [q]
    linarith
  have hvalues (a : Ω) (t : X → ℤ) :
      ((norm a).slots (fun i => (t i : ℝ))).patchValue (Φ a) =
        ((A a).slots (fun i => (t i : ℝ))).patchValue (Φ a) := by
    obtain ⟨e, he⟩ := hperm a t
    unfold TriangularSlots.patchValue
    simp_rw [he]
    exact e.tsum_eq (fun b => (Φ a).value
      (((A a).slots (fun i => (t i : ℝ))).residual b))
  have hnormScore (a) (ha : a ∈ productive) : Real.exp (-q) ≤
      (localLaw a).mean (fun t => score a t *
        ((norm a).slots (fun i => (point a t i : ℝ))).patchValue (Φ a)) := by
    simp_rw [hvalues]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive a ha)
  obtain ⟨Ψ, B, localForm, retained, hLip, hMass, hretained, hprob, hlocal⟩ :=
    hfixed norm Φ hw hpos hs q hq (hd.trans hpq) hnormMass
      (fun a => (hΦ a).trans (Real.exp_le_exp.mpr hpq)) outer productive localLaw
      (fun a t i => (point a t i : ℝ)) score hscore hnormScore
  refine ⟨Ψ, B, localForm, retained, hLip.trans (Real.exp_le_exp.mpr hpower),
    fun i => (hMass i).trans hmassBudget, hretained, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hpower))
      (outer.mass_nonneg productive)).trans hprob
  · intro a ha
    exact (Real.exp_le_exp.mpr (neg_le_neg hpower)).trans (hlocal a ha)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SelectedCenteredJointSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedJointFiniteLaw_support {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (z : A × rectangularWeightIndices 0 W 1)
    (hz : 0 < (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).weight z) :
    columnResiduePattern modulus z.2.val ∈ T ∧ 0 < D z.1.val z.2.val := by
  rw [selectedJointFiniteLaw_weight] at hz
  constructor
  · by_contra h
    rw [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight, if_neg h] at hz
    simp only [zero_div, mul_zero, zero_mul] at hz
    exact (lt_irrefl 0) hz
  · apply lt_of_le_of_ne (hD0 _ _)
    intro he
    rw [← he] at hz
    simp only [mul_zero, zero_div] at hz
    exact (lt_irrefl 0) hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

omit [Fintype X] [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCenteredJointDensity_measurable_center
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    Measurable (fun center =>
      allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z) :=
  (canonicalCoefficientDensity_measurable U b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S)).comp
      ((coefficientConstantCenter_continuous U).measurable.add measurable_const)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedFixedScaleCenteredOneSiteStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let sample := fun (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) =>
      affineSampleCoefficientTorus U p hm (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
    let D₀ := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ),
      (∀ k, |(root k : ℝ)| ≤ Real.exp P) →
    ∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (φ : (X → ℝ) → ℂ), (∀ u, ‖φ u‖ ≤ 1) →
      let fiber := fun z => coefficientFiberAverage U μ root
        (fun x => D₀ (coefficientConstantCenter U center + x))
        (coefficientEvaluationTorus U root (sample base z))
      ‖(∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
        (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
          (allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center base z : ℂ))) -
        (∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
          (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) * (fiber z : ℂ)))‖ ≤
        3 * positiveProjectionAccuracy P

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedJointSiteDomination
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

theorem selectedJointFiniteLaw_site_excess
    {K I X T : Type*} [Fintype K] [Fintype I]
    [Fintype X] [Nonempty X] [Fintype T] [Nonempty T]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (D : (I → ℤ) → (Option K × I → ℤ) → ℝ) (hD : ∀ a z, 0 ≤ D a z)
    (htotal : 0 < selectedJointDensityMass A modulus cells W D)
    (hlower : 1 / 2 ≤ selectedJointDensityMass A modulus cells W D)
    (e : X → I → ℝ) (he : Function.Injective e)
    (root : T → K → ℤ)
    (F : (A × rectangularWeightIndices 0 W 1) → T → X)
    (hF : ∀ z t, e (F z t) = (fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val)
    (hcard : (Fintype.card X : ℝ) / A.card ≤ 2)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ (a : I → ℤ) (t : T) (φ : (I → ℝ) → ℝ),
      (∀ u, φ u ∈ Set.Icc (0 : ℝ) 1) →
      (∑' z, (selectedResidueSmoothPMF modulus cells W hW hZ z).toReal *
        (φ ((fun i => (a i : ℝ)) + physicalAffineSite (root t) z) * D a z)) ≤
      M * (∑' z, (selectedResidueSmoothPMF modulus cells W hW hZ z).toReal *
        φ ((fun i => (a i : ℝ)) + physicalAffineSite (root t) z)) + ε) :
    (FiniteProbabilityWeights.uniform X).excessMass
      ((selectedJointFiniteLaw A hA modulus cells W hW hZ D hD htotal).siteLaw F)
      (4 * M) ≤ 2 * ε := by
  let : Nonempty A := hA.to_subtype
  let q := selectedResidueFiniteLaw modulus cells W hW hZ
  apply FiniteProbabilityWeights.siteLaw_excessMass_le_of_test_bound
  intro φ hφ t
  let ψ : (I → ℝ) → ℝ := fun u => φ (Function.invFun e u)
  have hψ (u) : ψ u ∈ Set.Icc (0 : ℝ) 1 := hφ _
  have hvalue (z : A × rectangularWeightIndices 0 W 1) :
      ψ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val) = φ (F z t) := by
    rw [← hF z t]
    exact congrArg φ (Function.leftInverse_invFun he (F z t))
  have hinj (z : rectangularWeightIndices 0 W 1) :
      Function.Injective (fun a : A => F (a, z) t) := by
    intro a b hab
    have hc := congrArg e hab
    rw [hF, hF] at hc
    have hd := add_right_cancel hc
    apply Subtype.ext
    funext i
    exact_mod_cast congrFun hd i
  have hlocal' (a : A) :
      q.mean (fun z => D a.val z.val * φ (F (a, z) t)) ≤
        M * q.mean (fun z => φ (F (a, z) t)) + ε := by
    have h := hlocal a.val t ψ hψ
    rw [← selectedResidueFiniteLaw_mean, ← selectedResidueFiniteLaw_mean] at h
    have hv (z : rectangularWeightIndices 0 W 1) :
        ψ ((fun i => (a.val i : ℝ)) + physicalAffineSite (root t) z.val) = φ (F (a, z) t) :=
      hvalue (a, z)
    simpa only [hv, mul_comm] using h
  have hz : 0 < ((FiniteProbabilityWeights.uniform A).prod q).mean
      (fun z => D z.1.val z.2.val) := by
    change 0 < (selectedJointReference A hA modulus cells W hW hZ).mean _
    rw [selectedJointReference_densityMass]
    exact htotal
  have hl : 1 / 2 ≤ ((FiniteProbabilityWeights.uniform A).prod q).mean
      (fun z => D z.1.val z.2.val) := by
    change 1 / 2 ≤ (selectedJointReference A hA modulus cells W hW hZ).mean _
    rw [selectedJointReference_densityMass]
    exact hlower
  have h := FiniteProbabilityWeights.uniform_base_reweight_test_le q
    (fun z => D z.1.val z.2.val) (fun z => hD z.1.val z.2.val) hz
    (fun z => F z t) hinj φ (fun x => (hφ x).1) hM (by norm_num : (0 : ℝ) < 1 / 2)
    hl hlocal'
  change (selectedJointFiniteLaw A hA modulus cells W hW hZ D hD htotal).mean
    (fun z => φ (F z t)) ≤ _ at h
  apply h.trans
  have hn := (FiniteProbabilityWeights.uniform X).mean_nonneg (fun x => (hφ x).1)
  have hr : (Fintype.card X : ℝ) / Fintype.card A ≤ 2 := by simpa using hcard
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hM) hn
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

noncomputable abbrev bases (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Finset (X → ℤ) :=
  trimmedIntegerBox N (spatialTrimMargin τ N)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

theorem zeroLayerVariables_card :
    Fintype.card (LayerSamplerVariables G I n B) = Fintype.card G :=
  Fintype.card_congr (zeroLayerVariablesEquiv B)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

noncomputable def b (q : ℕ) (j : Fin q) :
    Basis (Fin (n q j)) ℝ (euclideanSubspace (U q j))ᗮ :=
  Basis.empty _

theorem hb (q : ℕ) (j : Fin q) :
    span ℤ (Set.range (b q j)) = projectedIntegerLattice (euclideanSubspace (U q j)) :=
  Subsingleton.elim _ _

noncomputable def bW (q : ℕ) (j : Fin q) :
    Basis (Q q j) ℤ
      (latticeSection (standardEuclideanLattice (J q j)) (euclideanSubspace (U q j))) :=
  Basis.empty _

instance lattice_full (q : ℕ) (j : Fin q) :
    IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J q j)) (euclideanSubspace (U q j))) := by
  constructor
  exact Subsingleton.elim _ _

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSiteTermSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedSiteJetSize (α : Type*) [Fintype α] (j : Fin m) : ℝ :=
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
    ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) + idealSiteEnvelopeRadius α m

theorem allocatedSiteJetSize_nonneg (α : Type*) [Fintype α] (j : Fin m) :
    0 ≤ allocatedSiteJetSize (G := G) B α j := by
  have h := (idealSiteEnvelopeRadius_pos α m).le
  unfold allocatedSiteJetSize
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFullSiteRadius
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedSiteChartRadius_le_original (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (j : Fin m) :
    allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j ≤
      allocatedPhysicalChartRadius (G := G) B α C 1 j := by
  have hH := allocatedSiteRootAllowance_one_le α m
  have hCj := hC j
  unfold allocatedPhysicalChartRadius
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem allocatedSiteChartRadius_inv_le_exp (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {P : ℝ} (hP : 0 ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1)) :=
  allocatedPhysicalChartRadius_inv_le_exp B α C hC (allocatedSiteRootAllowance_one_le α m) hP
    ((allocatedSiteRootAllowance_le_exp α m).trans (Real.exp_le_exp.mpr hallow)) hCP hNP hIP j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedSiteJetSize_le_allowance (j : Fin m) :
    allocatedSiteJetSize (G := G) B α j ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        allocatedSiteRootAllowance α m := by
  let N : ℝ := Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr
      ⟨constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1)⟩)
  have hpow : ((Fintype.card α : ℝ) + 1) ^ (j.val + 1) ≤
      ((Fintype.card α : ℝ) + 1) ^ (m + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)])
      (Nat.succ_le_succ (Nat.le_of_lt j.isLt))
  have he := (idealSiteEnvelopeRadius_pos α m).le
  have hm := mul_le_mul_of_nonneg_left hpow
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card α))
  unfold allocatedSiteJetSize allocatedSiteRootAllowance
  change N * _ + _ ≤ N * _
  nlinarith [mul_le_mul_of_nonneg_left hm (zero_le_one.trans hN),
    mul_le_mul_of_nonneg_right hN he]

noncomputable def allocatedFullSiteRadius : ℝ≥0 :=
  ⟨1 + (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j,
    add_nonneg zero_le_one (mul_nonneg (pow_nonneg (by norm_num) _)
      (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)))⟩

theorem allocatedFullSiteRadius_one_le : 1 ≤ allocatedFullSiteRadius (G := G) B α := by
  change (1 : ℝ) ≤ 1 + (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)))

theorem allocatedFullSiteRadius_pos : 0 < allocatedFullSiteRadius (G := G) B α :=
  zero_lt_one.trans_le (allocatedFullSiteRadius_one_le B α)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFullSiteRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedFullSiteRadius_le_exp {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hH : allocatedSiteRootAllowance α m ≤ Real.exp P)
    (hN : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P) :
    (allocatedFullSiteRadius (G := G) B α : ℝ) ≤ Real.exp (4 * P + 1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp P := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp (Fintype.card α : ℝ) := by rw [← Real.exp_nat_mul]; simp only [mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr hq
  have hj (j : Fin m) : allocatedSiteJetSize (G := G) B α j ≤ Real.exp (2 * P) := by
    calc
      _ ≤ _ := allocatedSiteJetSize_le_allowance B α j
      _ ≤ Real.exp P * Real.exp P := mul_le_mul (hN j) hH
        (zero_le_one.trans (allocatedSiteRootAllowance_one_le α m)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs : (∑ j : Fin m, allocatedSiteJetSize (G := G) B α j) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (2 * P) := Finset.sum_le_sum (fun j _ => hj j)
      _ = (m : ℝ) * Real.exp (2 * P) := by simp
      _ ≤ Real.exp P * Real.exp (2 * P) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmultip : (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j ≤
      Real.exp (4 * P) := by
    calc
      _ ≤ Real.exp P * Real.exp (3 * P) := mul_le_mul hp hs
        (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hunit : 1 ≤ Real.exp (4 * P) := Real.one_le_exp_iff.mpr (by positivity)
  change 1 + _ ≤ _
  calc
    _ ≤ Real.exp (4 * P) + Real.exp (4 * P) := add_le_add hunit hmultip
    _ = 2 * Real.exp (4 * P) := by ring
    _ ≤ Real.exp 1 * Real.exp (4 * P) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedBufferedPhysicalFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

noncomputable def allocatedBufferedPhysicalChartRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  min (allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (1 / (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ)))

theorem allocatedBufferedPhysicalChartRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedBufferedPhysicalChartRadius (G := G) B α C j := by
  have hCj := hC j
  have hr : (0 : ℝ) < allocatedFullSiteRadius (G := G) B α := allocatedFullSiteRadius_pos B α
  exact lt_min (allocatedPhysicalChartRadius_pos B α C hC
    (allocatedSiteRootAllowance_one_le α m) j) (by positivity)

theorem allocatedBufferedPhysicalChartRadius_le_supported (C : Fin m → ℝ) (j : Fin m) :
    allocatedBufferedPhysicalChartRadius (G := G) B α C j ≤
      allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j := min_le_left _ _

theorem allocatedBufferedPhysicalChartRadius_le_original (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedBufferedPhysicalChartRadius (G := G) B α C j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j :=
  (allocatedBufferedPhysicalChartRadius_le_supported B α C j).trans (allocatedSiteChartRadius_le_original B α C hC j)

theorem allocatedBufferedPhysicalChartRadius_inv_le_exp
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1) + (6 * P + 6)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hunit : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) htwo 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hr := allocatedFullSiteRadius_le_exp B α hP hm hq
    ((allocatedSiteRootAllowance_le_exp α m).trans (Real.exp_le_exp.mpr hallow)) hNP
  have hCj := hC j
  have hCp := hadd (hCP j)
  have hIp := hadd (hIP j)
  have hden : 8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ) ≤
      Real.exp (6 * P + 6) := by
    calc
      _ ≤ Real.exp 3 * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (4 * P + 1) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hold := allocatedSiteChartRadius_inv_le_exp B α C hC hP hallow hCP hNP hIP j
  unfold allocatedBufferedPhysicalChartRadius
  by_cases h : allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j ≤
      1 / (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ))
  · rw [min_eq_left h]
    exact hold.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity)))
  · rw [min_eq_right (le_of_not_ge h), one_div, inv_inv]
    exact hden.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (by positivity)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedUnitSiteEarlyBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedBufferedPhysicalChartRadius_inv_le_exp_uniform
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (((m : ℝ) + 10) * (P + Fintype.card α + 2)) := by
  apply (allocatedBufferedPhysicalChartRadius_inv_le_exp B α C hC hP hm hq hallow hCP hNP hIP j).trans
  apply Real.exp_le_exp.mpr
  have hj : ((j.val + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hfactor : 0 ≤ P + (Fintype.card α : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hj hfactor
  have hq0 : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

noncomputable def allocatedChartGridMultiplier (g : AllocatedFrozenJetRows B U b S O → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  restrictedChartDensity chart region 1 (fun z => g ((split z.1).1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def allocatedComplexGridMultiplier (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (y : EuclideanJetLayers U O) : ℂ :=
  (allocatedChartGridMultiplier B U b S O hb o bW d (fun z => (g z).re) y : ℂ) +
    (allocatedChartGridMultiplier B U b S O hb o bW d (fun z => (g z).im) y : ℂ) * Complex.I

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_half_le_physical
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedIdealCoverRadius (G := G) B rowSets C j / 2 ≤
      allocatedPhysicalChartRadius (G := G) B α C 1 j := by
  let N : ℝ := Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
  let A : ℝ := (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)
  let H := allocatedIdealCoverSupport (G := G) B rowSets j
  let D : ℝ := 4 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1)
  let r : ℝ := (rowSets j).card + 1
  let : Nonempty (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
    ⟨⟨0, by simp⟩⟩
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α :=
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))
  have hA : 0 < A := by dsimp [A]; positivity
  have hH : 0 ≤ H := allocatedIdealCoverSupport_nonneg B rowSets j
  have hNA : N * A ≤ H := allocatedIdealCoverSupport_inactive B rowSets j
  have hr : 1 ≤ r := by
    dsimp only [r]
    linarith [Nat.cast_nonneg (α := ℝ) (rowSets j).card]
  have hCj := hC j
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum : (N + 1) * A ≤ 2 * (H + 1) := by nlinarith
  have hden : D * ((N + 1) * A) ≤ 2 * (D * r * (H + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left hnum hD.le
    have hrow := mul_le_mul_of_nonneg_right hr (show 0 ≤ D * (H + 1) by positivity)
    nlinarith
  have hleft : 0 < D * r * (H + 1) := by positivity
  have hright : 0 < D * ((N + 1) * A) := by positivity
  have hi : 1 / (D * r * (H + 1)) ≤ 2 / (D * ((N + 1) * A)) :=
    (div_le_div_iff₀ hleft hright).mpr (by simpa only [one_mul] using hden)
  have hh : (1 / (D * r * (H + 1))) / 2 ≤ 1 / (D * ((N + 1) * A)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hi
  convert hh using 1 <;>
    simp only [allocatedIdealCoverRadius, finiteRowChartRadius, allocatedPhysicalChartRadius,
      D, r, H, N, A, add_comm (1 : ℝ)] <;> ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowMap" => (fun j : Fin m => (Subtype.val : rows j → Finset α))

noncomputable def allocatedKernelSiteLift (period : ℕ)
    (r : Finset α → ∀ j, Fin (n j) → ZMod period) : AllocatedLongJetRows B U b S rows
  | ⟨⟨_, .inl _⟩, _⟩ => fun _ => 0
  | ⟨⟨j, .inr i⟩, _⟩ => fun t => (booleanCoefficient (fun s => r s j i) t.val).val

variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)
variable (residue : ∀ j, Matrix {t : Finset α // t ∈ rowSets j}
  (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

noncomputable def allocatedKernelSiteMask (period : ℕ)
    (r : Finset α → ∀ j, Fin (n j) → ZMod period) : ℝ :=
  ∏ a, allocatedLongJetMask B U b S x rowMap modulus residue a
    (allocatedKernelSiteLift B U b S rowSets period r a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

noncomputable def allocatedFullGridSiteValues
    (z : AllocatedFrozenJetRows B U b S (rowTypes)) (s : Finset α) (a : gridAxes) : ℤ :=
  integerBooleanSitesFromRows (rowSets (ig a).1) (allocatedGridIntegerValues B U b S rowSets a (z a)) s

noncomputable def allocatedFullGridSiteApproximation
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : AllocatedFrozenJetRows B U b S (rowTypes)) : ℂ :=
  siteFamilyEval e (allocatedFullGridSiteValues B U b S rowSets z)
    (fun s a => (allocatedFullGridSiteValues B U b S rowSets z s a : ℝ) / axisN a)

noncomputable def allocatedFullGridNaturalVolume : ℝ :=
  ∏ a : gridAxes, (axisN a : ℝ) ^ (rowSets (ig a).1).card

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

theorem modularDeckPolynomial_resample_top {A : Type*} [Fintype A]
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (hdegree : ∀ a, (slot a).val.degree = j.val + 1) (c : A → ZMod N) :
    homogeneousComponent (j.val + 1)
      (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i slot c) j i) =
      homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1) slot (fun e => r j e i)) +
      ∑ a, MvPolynomial.monomial (slot a).val (c a) := by
  simp only [modularDeckPolynomial, resampleCoefficientDeckCoordinate_apply]
  exact modularBoundedCoefficientPolynomial_selected_top _ slot hinj hdegree _ c

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedTwistAffineCells
namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K X : Type*} [Fintype K] [Fintype X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem correlation_after_freezing {T : Type*} [Fintype T]
    (μ : FiniteProbabilityWeights T) (twist signal : T → ℂ) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (hsignal : ∀ t, ‖signal t‖ ≤ 1)
    {ε δ : ℝ} (hfreeze : ∀ t, μ.weight t ≠ 0 → ‖twist t - c‖ ≤ ε)
    (hbias : δ ≤ ‖μ.complexMean (fun t => star (twist t) * signal t)‖) :
    δ - ε ≤ ‖μ.complexMean signal‖ := by
  have he := μ.norm_complexMean_sub_le
    (fun t => star (twist t) * signal t) (fun t => star c * signal t)
    (fun _ => ε) (fun t ht => by
      rw [← sub_mul, ← star_sub, norm_mul, norm_star]
      exact (mul_le_mul (hfreeze t ht) (hsignal t) (norm_nonneg _) (by
        exact (norm_nonneg _).trans (hfreeze t ht))).trans_eq (mul_one _))
  rw [μ.mean_const] at he
  have hconst : μ.complexMean (fun t => star c * signal t) = star c * μ.complexMean signal := by
    simp only [FiniteProbabilityWeights.complexMean, Finset.mul_sum]
    congr 1
    funext t
    ring
  have hb : ‖μ.complexMean (fun t => star c * signal t)‖ ≤ ‖μ.complexMean signal‖ := by
    rw [hconst, norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
  have ht := norm_le_norm_sub_add
    (μ.complexMean (fun t => star (twist t) * signal t))
    (μ.complexMean (fun t => star c * signal t))
  linarith

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAmbientProjectedDensityMultiple
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_ambient_projected_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let root := allocatedPhysicalCubeRoot B U b S c x y
    let dirs := allocatedPhysicalCubeDirections B U b S x y
    let _ := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ z, g z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable g ξ ∧
      (∫ z, g z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))) =
        realDensityMeasure ξ g ∧
      physicalDensityProjection U root dirs d density g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) cap) ∧
      LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
      ∀ z, g z = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_euclidean_ambient_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod period hp hpP
  let Q := P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  obtain ⟨d, hdiv, hd, hdb, hcover⟩ := hcover (fun g => c (.inl g) + (x g none : ℤ))
    (fun i g => (x g (some i) : ℤ)) (a : ℤ) (by exact_mod_cast ha.ne') hperiod
    (hP.trans hPQ) (hG.trans hPQ) (kernelCubeBox_site_le_exp (fun g => c (.inl g)) x hc hL)
    period hp (hpP.trans (Real.exp_le_exp.mpr hPQ))
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs unusedJetMap cover ξ densityLip sectionLip reconstructionLip
  have hs := allocatedCoefficientDensity_positive_spec B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hambient := allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ
  have heq (z) := allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall z
  have hm : (∫ z, allocatedCoefficientAmbientDensity B U b o S (coefficientAmbientTorus U z) ∂μ) = 1 := by
    simp_rw [heq]
    exact hs.2.2.2.1
  obtain ⟨g, F, hgc, hgb, hgi, hgm, hglaw, hFb, hFl, hvalue, hprojection⟩ :=
    hcover root dirs Sum.inl (fun _ => rfl) (fun _ _ => rfl) U μ ν
      (allocatedCoefficientAmbientDensity B U b o S) hambient.2
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      (fun z => by simpa only [Set.mem_Icc, NNReal.coe_pow] using hambient.1 z) hm
  refine ⟨g, F, hgc, hgb, hgi, hgm, ?_, ?_, hFb, hFl, hvalue⟩
  · simp_rw [heq] at hglaw
    convert hglaw using 1
    rfl
  · intro X Index _ frequency coeff η happ p hp hm v
    apply hprojection frequency coeff ?_ p hp hm v
    intro z
    simpa only [heq] using happ z

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarReferenceNativeDetectionCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K K' X : Type*}

variable [Fintype K] [Fintype K'] [Fintype X]

noncomputable def scalarNoiseSupportEquiv (e : K ≃ K') (B τ : ℝ) (N : X → ℕ) :
    rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1 ≃
      rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1 where
  toFun z := ⟨fun j => z.val ((scalarNoiseIndexEquiv e).symm j), by
    apply (mem_rectangularWeightIndices_zero_iff _ _).mpr
    intro j
    simpa only [scalarNoiseIndexEquiv_symm,
      trimmedSpatialWidths_scalarNoiseIndexEquiv] using
      (mem_rectangularWeightIndices_zero_iff _ _).mp z.property
        ((scalarNoiseIndexEquiv e).symm j)⟩
  invFun z := ⟨fun i => z.val (scalarNoiseIndexEquiv e i), by
    apply (mem_rectangularWeightIndices_zero_iff _ _).mpr
    intro i
    simpa only [trimmedSpatialWidths_scalarNoiseIndexEquiv] using
      (mem_rectangularWeightIndices_zero_iff _ _).mp z.property
        (scalarNoiseIndexEquiv e i)⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    exact congrArg z.val ((scalarNoiseIndexEquiv e).symm_apply_apply i)
  right_inv z := by
    apply Subtype.ext
    funext j
    exact congrArg z.val ((scalarNoiseIndexEquiv e).apply_symm_apply j)

@[simp] theorem scalarNoiseSupportEquiv_val (e : K ≃ K') (B τ : ℝ)
    (N : X → ℕ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarNoiseSupportEquiv e B τ N z).val =
      fun j => z.val ((scalarNoiseIndexEquiv e).symm j) := rfl

@[simp] theorem scalarNoiseSupportEquiv_symm_val (e : K ≃ K') (B τ : ℝ)
    (N : X → ℕ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1) :
    ((scalarNoiseSupportEquiv e B τ N).symm z).val =
      fun i => z.val (scalarNoiseIndexEquiv e i) := rfl

noncomputable def scalarJointPathEquiv (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*) :
    A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1 ≃
      A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1 :=
  (Equiv.refl A).prodCongr (scalarNoiseSupportEquiv e B τ N)

@[simp] theorem scalarJointPathEquiv_fst (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarJointPathEquiv e B τ N A z).1 = z.1 := rfl

@[simp] theorem scalarJointPathEquiv_snd_val (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarJointPathEquiv e B τ N A z).2.val =
      fun j => z.2.val ((scalarNoiseIndexEquiv e).symm j) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

theorem affineSampleParameterKernel_mean (π : FiniteProbabilityWeights (J → ZMod q))
    (z : Option J × I → ZMod q) (f : (I → ZMod q) → ℝ) :
    (affineSampleParameterKernel π z).mean f =
      π.mean (fun t => f ((affineSampleAlphabetEquiv z).2 +
        residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)) :=
  π.fiberLaw_mean _ f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCutoffDomination
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
variable (V : K × I → ℝ)

theorem selectedResidueSmoothWeight_normalized_norm_le (z : K × I → ℤ)
    (hz : selectedResidueSmoothWeight q T V z ≠ 0) :
    ‖fun t => (z t : ℝ) / V t‖ ≤ 1 := by
  by_contra! hn
  have hp := smoothProductProfile_zero_outside (K × I) (fun t => (z t : ℝ) / V t) hn
  exact hz (by simp [selectedResidueSmoothWeight, hp])

end Erdos3

end

end OAI
end


