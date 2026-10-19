-- Prove2me | Definitions.Def_OAIE3v2B273
-- name    : OAIE3v2B273
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:16:13.583366+00:00
-- url     : https://prove2.me/theorems/37c5db56-041b-46a9-8935-14c59abf112f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 284 of 311
-- statement:
--   Definitions bundle 284 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B306`, `OAIE3v2B307`, `OAIE3v2B270` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateSelectedDescentRegularity.lean`, `Estimates/NativePresentPivotQuotientModel.lean`, `Fourier/ControlledFrequencyExternalTransfer.lean`, `Linear/PositiveKernelNativeDescentBudget.lean`, `Sampling/PreparedCanonicalPaddedSamplerData.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B306
import Definitions.Def_OAIE3v2B307
import Definitions.Def_OAIE3v2B270

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] integerProgressionSupport IsDenseCommonStrideBox ResidueBoxSlice.integerPoints

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AxisFreezing

variable {P} {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem ambientScore_extendSlice
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step) :
    P.ambientScore ambient z (freezing.extendSlice z slice).integerPoints =
      freezing.problem.ambientScore ambient z slice.integerPoints := by
  let f : ((P.chart z).Variables → ℤ) → ℂ := fun u =>
    weight ((P.chart z).physical u) * observable ((P.chart z).physical u)
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
        (fullTaggedVariableWeight J) ((P.chart z).chartValues u) ambient))
  have hexpect := slice.expect_extendAxes (N := A.sides)
    (oldKeep := (P.chart z).keep) (keep := keep z)
    (P.chart z).slice (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z) f
  have haxis : ResidueBoxSlice.axisInsertion (P.chart z).keep (keep z) (freezing.fixed z) =
      (P.chart z).axisPoint (keep z) (freezing.fixed z) := rfl
  rw [haxis] at hexpect
  calc
    _ = (𝔼 u ∈ slice.integerPoints,
        f ((P.chart z).axisPoint (keep z) (freezing.fixed z) u)).re :=
      congrArg Complex.re (by
        simpa only [ResidueBoxSlice.integerPoints_classical_eq, extendSlice, f] using hexpect)
    _ = _ := by
      unfold ambientScore
      dsimp only [problem]
      simp only [AllocatedExternalLocalChart.freezeAxes_physical,
        AllocatedExternalLocalChart.freezeAxes_chartValues]
      rfl

end AxisFreezing
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateSelectedDescentRegularity
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem Niltest.nativeQuotient_observable_sub_norm_le
    (T : D.Niltest w) (U : D.Niltest v)
    (I : LieIdeal ℚ L) (htop : I.toSubmodule ≤ D.filtration.layer s)
    (Q : RationalFilteredNilmanifold (L ⧸ I) t n) (f g : Q.Space → ℂ)
    (hf : ∀ x : D.RealGroup, f (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
      (T.kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk x))
    (hg : ∀ x : D.RealGroup, g (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
      (U.kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk x))
    {η : ℝ} (hTU : ∀ x, ‖T.observable x - U.observable x‖ ≤ η) :
    ∀ x : Q.Space, ‖f x - g x‖ ≤ η := by
  intro q
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) q.coord
    let z : D.RealGroup := ⟨x⟩
    have hz : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) z = q :=
      NilpotentLieBCHGroup.ext hx
    have hfz := hf z
    have hgz := hg z
    rw [hz] at hfz hgz
    rw [hfz, hgz]
    exact T.kernelProjection_observable_sub_norm_le U I.toSubmodule htop hTU
      (QuotientGroup.mk z)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledFrequencyExternalTransfer
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_frequency_quotient
    {L J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    (vP : Fin d → L) (hspan : Submodule.span ℚ (Set.range vP) = P)
    (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hr : (r : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) :
    let K := frequencyCodeKernel P eta code
    let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
    let I := D.filtration.topSubspaceIdeal K hK
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    let q := p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1
    ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
      Q.filtration = D.filtration.quotientLie I hI ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
      Q.GeometryComplexityLE ((q + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (q + 3) ^ 5 := by
  intro K hK I hI q
  obtain ⟨n, hn, bk, hbk⟩ := exists_frequency_code_kernel_basis_logHeight D.basis P vP hspan
    eta code hp hD.1 hr hvP heta
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have : 0 ≤ ((2 * p + 6) ^ 2 + 2) ^ 63 := by positivity
    dsimp [q]
    exact (le_add_of_nonneg_right this).trans (le_add_of_nonneg_right zero_le_one)
  have hbq : ((2 * p + 6) ^ 2 + 2) ^ 63 ≤ q := by dsimp [q]; linarith
  exact D.exists_controlled_top_subspace_quotient hs K hK bk bk.span_eq hq
    (hD.mono D hpq) (fun i j => (hbk i j).trans hbq)

theorem exists_controlled_frequency_quotient_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
      (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
      (vP : Fin d → L), Submodule.span ℚ (Set.range vP) = P →
      ∀ (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (r : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ p) →
      (∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) →
      let K := frequencyCodeKernel P eta code
      let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
      let I := D.filtration.topSubspaceIdeal K hK
      let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by
        rw [D.filtration.terminal]; exact bot_le
      ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        Q.filtration = D.filtration.quotientLie I hI ∧
        Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
        Q.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 2) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let q := X + ((2 * X + 6) ^ 2 + 2) ^ 63 + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((q + 3) ^ 11 + (q + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro L J _ _ s d r D hs P hP vP hspan eta code p hp hD hr hvP heta K hK I hI
  obtain ⟨n, hn, Q, hQF, hQL, hQ, he⟩ :=
    D.exists_controlled_frequency_quotient hs P hP vP hspan eta code hp hD hr hvP heta
  have hb : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 +
      (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 ≤ (p + 2) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hb11 : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 ≤ (p + 2) ^ C := by
    have : 0 ≤ (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 := by positivity
    exact (le_add_of_nonneg_right this).trans hb
  have hb5 : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 ≤ (p + 2) ^ C := by
    have : 0 ≤ (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 := by positivity
    exact (le_add_of_nonneg_left this).trans hb
  exact ⟨n, hn, Q, hQF, hQL, hQ.mono Q hb11, fun i j => (he i j).trans hb5⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePresentPivotQuotientModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped Classical

theorem exists_nativePresentPivotQuotient_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e r : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
      (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J) (p : ℝ),
      1 ≤ s → 0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p → (r : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) →
      let ideal := D.filtration.pivotAnnihilatorIdeal φ
        (fun k => eta (kernelProjectionSelectedPivot code k))
        (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList
      let hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule := by
        rw [D.filtration.terminal]; exact bot_le
      ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ ideal) s n,
        Q.filtration = D.filtration.quotientLie ideal hI ∧
        Q.lattice = D.lattice.map (D.filtration.quotientStepHom ideal hI) ∧
        Q.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤
          (p + 2) ^ C := by
  obtain ⟨a, _ha, hspan⟩ := exists_nativeTopMarkKernel_spanning_budget
  obtain ⟨bexp, _hb, hquotient⟩ := exists_controlled_frequency_quotient_budget
  let X : Polynomial ℕ := Polynomial.X
  let q := X + (X + 2) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((q + 2) ^ bexp)
  refine ⟨C, hC, ?_⟩
  intro L M J _ _ _ _ s d e r D b φ eta code p hs hp hD he hr hφ heta ideal hI
  let P := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
  obtain ⟨vP, hvP, hvPH⟩ := hspan D b φ p hs hp hD he hφ
  let p₀ := p + (p + 2) ^ a + 1
  have hpa : 0 ≤ (p + 2) ^ a := by positivity
  have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
  have hpp₀ : p ≤ p₀ := by dsimp [p₀]; linarith
  have hap₀ : (p + 2) ^ a ≤ p₀ := by dsimp [p₀]; linarith
  have hbudget' : (p₀ + 2) ^ bexp ≤ (p + 2) ^ C := by
    simpa [X, q, p₀, Polynomial.eval₂_pow] using hbudget p hp
  have hresult := hquotient D hs P inf_le_left vP hvP eta code p₀ hp₀
    (hD.mono D hpp₀) (hr.trans hpp₀)
    (fun i j => (hvPH i j).trans hap₀) (fun i j => (heta i j).trans hpp₀)
  let K := frequencyCodeKernel P eta code
  let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans inf_le_left
  let I := D.filtration.topSubspaceIdeal K hK
  have hIdeal : ideal = I := D.filtration.pivotAnnihilatorIdeal_presentPivots φ eta code hK
  revert hI
  rw [hIdeal]
  intro hI
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hmap⟩ := hresult
  exact ⟨n, hn, Q, hQF, hQL, hQ.mono Q hbudget', fun i j => (hmap j i).trans hbudget'⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PositiveKernelNativeDescentBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def nativePresentPivotQuotientExponent : ℕ :=
  Classical.choose (exists_nativePresentPivotQuotient_budget.{0, 0, 0})

noncomputable def positiveKernelNativeDescentPolynomial (s : ℕ) : Polynomial ℕ :=
  let q := Polynomial.X + (Polynomial.X + 2) ^ nativePresentPivotQuotientExponent + 1
  q + (q + 2) ^ nativeInvariantFamilyDescentExponent s

noncomputable def positiveKernelNativeDescentExponent (s : ℕ) : ℕ :=
  Classical.choose
    (exists_natPolynomial_fixed_power_budget (positiveKernelNativeDescentPolynomial s))

theorem positiveKernelNativeDescentExponent_ge_two (s : ℕ) :
    2 ≤ positiveKernelNativeDescentExponent s :=
  (Classical.choose_spec
    (exists_natPolynomial_fixed_power_budget (positiveKernelNativeDescentPolynomial s))).1

theorem positiveKernelNativeDescentBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let pDesc := p + (p + 2) ^ nativePresentPivotQuotientExponent + 1
    p ≤ pDesc ∧ 0 ≤ pDesc ∧
      (p + 2) ^ nativePresentPivotQuotientExponent ≤ pDesc ∧
      pDesc ≤ (p + 2) ^ positiveKernelNativeDescentExponent s ∧
      (pDesc + 2) ^ nativeInvariantFamilyDescentExponent s ≤
        (p + 2) ^ positiveKernelNativeDescentExponent s := by
  dsimp only
  have hquotient : 0 ≤ (p + 2) ^ nativePresentPivotQuotientExponent := by positivity
  have hdesc : 0 ≤
      (p + (p + 2) ^ nativePresentPivotQuotientExponent + 1 + 2) ^
        nativeInvariantFamilyDescentExponent s := by positivity
  have hbudget :
      p + (p + 2) ^ nativePresentPivotQuotientExponent + 1 +
        (p + (p + 2) ^ nativePresentPivotQuotientExponent + 1 + 2) ^
          nativeInvariantFamilyDescentExponent s ≤
        (p + 2) ^ positiveKernelNativeDescentExponent s := by
    simpa [positiveKernelNativeDescentPolynomial, positiveKernelNativeDescentExponent,
      Polynomial.eval₂_pow] using
      (Classical.choose_spec
        (exists_natPolynomial_fixed_power_budget (positiveKernelNativeDescentPolynomial s))).2 p hp
  exact ⟨by linarith, by positivity, by linarith, by linarith, by linarith⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCanonicalPaddedSamplerData
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule MeasureTheory VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
    (K : Type) [Fintype K]

noncomputable def PreparedHeights.canonicalSamplerMeasures
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R) :
    L.CanonicalSamplerMeasures K := by
  let : ∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)) :=
    hL.lattice_full L hp hR
  let : CompactSpace (CoefficientTorus (K := K) (fun j => (L j).space)) :=
    hL.coefficientTorus_compact L hp hR
  let : CompactSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space)) :=
    hL.coefficientTorus_compact L hp hR
  let : BorelSpace (CoefficientTorus (K := K) (fun j => (L j).space)) :=
    QuotientAddGroup.borelSpace
  let : BorelSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space)) :=
    QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (SubspaceArrayTorus (Finset (Fin (0 + 1))) (L j).space) :=
    fun _ => QuotientAddGroup.borelSpace
  let : BorelSpace (SiteTorus (Finset (Fin (0 + 1))) (fun j => (L j).space)) :=
    Pi.borelSpace
  let : ∀ j, CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup) :=
    hL.euclideanLayerTorus_compact L hp hR
  let : ∀ j, BorelSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  exact {
    lattice := inferInstance
    coefficientCompact := inferInstance
    coefficientBorel := inferInstance
    rowCompact := inferInstance
    rowBorel := inferInstance
    siteBorel := inferInstance
    layer := fun j => probabilityAddHaar (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup)
    layerInvariant := fun _ => inferInstance
    layerProbability := fun _ => inferInstance
    coefficient := probabilityAddHaar _
    coefficientInvariant := inferInstance
    coefficientProbability := inferInstance
    row := probabilityAddHaar _
    rowInvariant := inferInstance
    rowProbability := inferInstance }

noncomputable def PreparedHeights.paddedCanonicalSamplerMeasures
    {q : ℕ} {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hmq : m ≤ q) (hp : 0 ≤ p) (hR : 1 ≤ R) :
    (L.pad q).CanonicalSamplerMeasures K :=
  (hL.pad hmq hp).canonicalSamplerMeasures (L.pad q) K hp hR

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule MeasureTheory VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
    (K : Type) [Fintype K]

noncomputable def PreparedHeights.canonicalPaddedSamplerData
    {q : ℕ} {pPrep pLate : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hmq : m ≤ q) (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R) (hPrepLate : pPrep ≤ pLate)
    (hRLate : (R : ℝ) ≤ Real.exp pLate)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcapLate : (preparationCoordinateCap q D T : ℝ) ≤ pLate) :
    (L.pad q).CanonicalSamplerData K (preparationCoordinateCap q D T) pLate :=
  Classical.choice (by
    obtain ⟨b, o, bW, hb, hchart, hinverse, hcov, hnorm, haxis⟩ :=
      hL.exists_padded_early_late_sampler_geometry L hmq hpPrep hR hPrepLate hRLate
        hsize ht hcapLate
    exact ⟨{
      measures := hL.paddedCanonicalSamplerMeasures L K hmq hpPrep hR
      b := b
      o := o
      bW := bW
      span_eq := hb
      chart_bound := hchart
      inverse_chart_bound := hinverse
      covolume_bound := hcov
      integral_basis_bound := hnorm
      axis_bound := haxis }⟩)

end Erdos3.RankPreparationFamily

end

end OAI
end


