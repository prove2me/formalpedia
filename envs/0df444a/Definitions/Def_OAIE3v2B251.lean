-- Prove2me | Definitions.Def_OAIE3v2B251
-- name    : OAIE3v2B251
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:20:12.958572+00:00
-- url     : https://prove2.me/theorems/1feb12c8-c7a0-4def-a886-8ed2982eeebc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 256 of 311
-- statement:
--   Definitions bundle 256 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B237`, `OAIE3v2B238`, `OAIE3v2B241`, `OAIE3v2B242` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/TranslationMajorCorrelationDecomposition.lean`, `Estimates/TranslationMajorCorrelationIdentity.lean`, `Estimates/TranslationMajorTwistedCorrelationStepDrop.lean`, `Fourier/MajorPhaseLowFourierExtraction.lean`, `Geometry/CertifiedFullChartBudgetedTreeBounds.lean`, `Geometry/CertifiedFullChartForwardEarlyTree.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Polynomial/TranslationMajorTwistedCorrelationStepDropPolynomial.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B237
import Definitions.Def_OAIE3v2B238
import Definitions.Def_OAIE3v2B241
import Definitions.Def_OAIE3v2B242

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_intrinsic_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
      ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (e '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
        ∀ η : L →ₗ[ℚ] ℚ,
          (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
            T.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
          D.filtration.ControlledSymbolFactorization e ω hF η (fun i => (lengths i : ℝ))
            (T.symbol e ω hF) ((p + C) ^ C) := by
  cases s with
  | zero => omega
  | succ s =>
    have hs' : 1 ≤ s := by omega
    obtain ⟨c, _, hI⟩ := exists_translated_step_drop s hs'
    obtain ⟨C, hC, hstep⟩ := exists_biased_chosen_basis_step_drop s c hI
    refine ⟨C, hC, ?_⟩
    intro σ L _ _ _ _ d _ _ _ _ D p hp T hT
    obtain ⟨a, v, _grid, _hv, _central, hA, _rest⟩ := D.exists_controlled_adapted_basis hp hT.1
    obtain ⟨τS, hSA, hSM, hST⟩ := exists_real_module_topology
      (D.filtration.squareFinBasis a v (hA 2))
    let : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := τS
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSA
    let : ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSM
    let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hST
    obtain ⟨τQ, hQA, hQM, hQT⟩ := exists_real_module_topology
      (D.filtration.reducedSquareBasis a v hA)
    let : TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := τQ
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQA
    let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQM
    let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := hQT
    obtain ⟨e, ω, hF, _N, _hN, _hin, _hout, he, _geometry, hconstruct⟩ :=
      hstep hs' D p hp T hT
    obtain ⟨g, hg⟩ := D.filtration.nativePolynomialOrbit_surjective
      (fun _ : σ => 1) e ω hF T.orbit
    refine ⟨e, ω, hF, he, ?_⟩
    intro η hvert origin lengths hlengths hσ hlarge hbias
    have hresult := hconstruct g hg η hvert origin lengths hlengths hσ hlarge hbias
    rw [← T.symbol_of_native e ω hF g hg] at hresult
    exact hresult

end Erdos3

end

section

namespace Erdos3
open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_finite_product_vertical_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (T : ∀ i, (D i).Niltest (fun _ : σ => 1)) {p : ℝ} (hp : 0 ≤ p)
      (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (∀ i, L i))) ℚ (∀ i, L i))
        (ω : Fin (finrank ℚ (∀ i, L i)) → ℕ)
        (hF : ∀ j, (pi D).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi D).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ eta : ∀ i, L i →ₗ[ℚ] ℚ,
          (∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
            (T i).observable (z • x) = CircleFourier.character
              ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
                (T i).observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, ∏ i, (T i).eval x‖ →
          (pi D).filtration.ControlledSymbolFactorization b ω hF (piFrequency eta)
            (fun i => (lengths i : ℝ)) ((piNiltest D T hp hι hT).symbol b ω hF)
            ((p + C) ^ C) := by
  obtain ⟨a, _ha, hstep⟩ := exists_intrinsic_step_drop s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + 1 + (Q + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D T p hp hι hT
  let q := productNiltestBudget p + p + 2
  have hprod : 0 ≤ productNiltestBudget p := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hTq : productNiltestBudget p ≤ q := by dsimp [q]; linarith
  have hcost : q + 1 + (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hheight : q + 1 ≤ (p + C) ^ C := by
    have : 0 ≤ (q + a) ^ a := by positivity
    linarith
  have hfactor : (q + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (pi D) hq (piNiltest D T hp hι hT)
      ((piNiltest_complexity D T hp hι hT).mono hTq)
  refine ⟨b, ω, hF, fun i j => (hb i j).trans hheight, ?_⟩
  intro eta hvert origin lengths hlength hσ hlarge hbias
  have hpair : Real.exp (-q) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths, (piNiltest D T hp hι hT).eval x‖ := by
    simp_rw [piNiltest_eval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
  have hf := hconstruct (piFrequency eta) (piNiltest_vertical D T eta hp hι hT hvert)
    origin lengths hlength (hσ.trans hpq)
    (fun i => (Real.exp_le_exp.mpr hfactor).trans (hlarge i)) hpair
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
    (pi D).filtration b ω hF hf hfactor (fun i => by exact_mod_cast hlength i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
namespace OAI

universe u

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

open RationalFilteredNilmanifold

theorem exists_native_pair_vertical_step_drop (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p : ℝ} (_hp : 2 ≤ p) (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ),
          (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            V.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) →
          (∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
            W.observable (z • x) = CircleFourier.character
              ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, V.eval x * W.eval x‖ →
          (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
            (pairFrequency η θ) (fun i => (lengths i : ℝ))
            (pairOrbitSymbol D E V.orbit W.orbit b ω hF) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_finite_product_vertical_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
  let models := pairModels D E
  let tests := pairTests D E V W
  let : FiniteDimensional ℚ (PairAlgebra L M) :=
    (productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra L M)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra L M) :=
    realification_moduleTopology_t2 (productFinBasis models)
  have hp0 : 0 ≤ p := by linarith
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  have htests : ∀ i, (tests i).ComplexityLE p := pairTests_complexity D E V W hV hW
  obtain ⟨b, ω, hF, hb, hconstruct⟩ := hstep models tests hp0 hcard htests
  refine ⟨b, ω, hF, hb, ?_⟩
  intro η θ hη hθ origin lengths hlengths hσ hlarge hbias
  have hvert : ∀ i z, z ∈ (models i).filtration.realification.subgroup s → ∀ x,
      (tests i).observable (z • x) = CircleFourier.character
        ((realifyFunctional (pairFrequencies η θ i) z.coord : ℝ) : CircleFourier.Circle) *
          (tests i).observable x := by
    intro i
    cases i
    · exact hθ
    · exact hη
  have hbias' : Real.exp (-p) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths, ∏ i, (tests i).eval x‖ := by
    have heval (x : σ → ℤ) : (∏ i, (tests i).eval x) = V.eval x * W.eval x := by
      rw [Fintype.prod_bool]
      rfl
    simp_rw [heval]
    exact hbias
  exact hconstruct (pairFrequencies η θ) hvert origin lengths hlengths hσ hlarge hbias'

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_native_pair_positive_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p : ℝ} (_hp : 2 ≤ p) (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        ∀ (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ),
          (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
          (∀ i, rationalLogHeight (θ (E.basis i)) ≤ p) →
          (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            V.observable (z • x) = CircleFourier.character
              ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) →
          (∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
            W.observable (z • x) = CircleFourier.character
              ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x) →
          ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
          (Fintype.card σ : ℝ) ≤ p →
          (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
          Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, V.eval x * W.eval x‖ →
          (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
            (pairFrequency η θ) (fun i => (lengths i : ℝ))
            (pairOrbitSymbol D E V.orbit W.orbit b ω hF) ((p + C) ^ C) := by
  by_cases hs2 : 2 ≤ s
  · obtain ⟨C, hC, hstep⟩ := exists_native_pair_vertical_step_drop s hs2
    refine ⟨C, hC, ?_⟩
    intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
    obtain ⟨b, ω, hF, hb, hconstruct⟩ := hstep D E V W hp hV hW
    exact ⟨b, ω, hF, hb, fun η θ _ _ => hconstruct η θ⟩
  · have hs1 : s = 1 := by omega
    subst s
    let X : Polynomial ℕ := Polynomial.X
    let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + 2) ^ 4)
    refine ⟨C, hC, ?_⟩
    intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p hp hV hW
    let models := pairModels D E
    let N := pi models
    let : FiniteDimensional ℚ (PairAlgebra L M) :=
      (productFinBasis models).finiteDimensional_of_finite
    let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra L M)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    let : T2Space (ℝ ⊗[ℚ] PairAlgebra L M) :=
      realification_moduleTopology_t2 (productFinBasis models)
    have hp0 : 0 ≤ p := by linarith
    have hpq : p ≤ productNiltestBudget p := by
      have hr := productObservableLipBudget_nonneg hp0
      unfold productNiltestBudget
      nlinarith [sq_nonneg (p + 2), sq_nonneg p]
    have hq : 0 ≤ productNiltestBudget p := hp0.trans hpq
    have hcost : (productNiltestBudget p + 2) ^ 4 ≤ (p + C) ^ C := by
      simpa [X, Q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
        using hbudget p hp0
    have hnonneg : 0 ≤ (p + C) ^ C := by positivity
    have hdim : finrank ℚ (PairAlgebra L M) =
        Fintype.card (Σ i : Bool, Fin (Bool.rec e d i)) := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis N.basis
    rw [hdim]
    let ω : Fin (Fintype.card (Σ i : Bool, Fin (Bool.rec e d i))) → ℕ := fun _ => 1
    have hF : ∀ k, N.filtration.layer k =
        Submodule.span ℚ (N.basis '' {i | k ≤ ω i}) :=
      N.filtration.stepOne_basis_layers N.basis
    refine ⟨N.basis, ω, hF, ?_, ?_⟩
    · intro i j
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simpa [rationalLogHeight] using hnonneg
    · intro η θ hηheight hθheight hη hθ origin lengths hlengths _hσ _hlarge hbias
      let T := pairNiltest D E V W hp hV hW
      have hT : T.ComplexityLE (productNiltestBudget p) :=
        pairNiltest_complexity D E V W hp hV hW
      have hfreq : ∀ i, rationalLogHeight (pairFrequency η θ (N.basis i)) ≤
          productNiltestBudget p :=
        fun i => (pairFrequency_logHeight D E η θ hηheight hθheight i).trans hpq
      have hvert : ∀ z, z ∈ N.filtration.realification.subgroup 1 → ∀ x,
          T.observable (z • x) = CircleFourier.character
            ((realifyFunctional (pairFrequency η θ) z.coord : ℝ) : CircleFourier.Circle) *
              T.observable x := by
        apply piNiltest_vertical (pairModels D E) (pairTests D E V W)
          (pairFrequencies η θ)
        intro i
        cases i
        · exact hθ
        · exact hη
      have hbias' : Real.exp (-productNiltestBudget p) ≤
          ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ := by
        simp_rw [show ∀ x, T.eval x = V.eval x * W.eval x from
          pairNiltest_eval D E V W hp hV hW]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
      have hf := N.stepOne_controlled_symbol_factorization ω hF T (pairFrequency η θ)
        hq hT hfreq hvert origin lengths hlengths hbias'
      have hf' := NilpotentLieFiltration.ControlledSymbolFactorization.mono
        N.filtration N.basis ω hF hf hcost (fun i => by exact_mod_cast hlengths i)
      exact hf'

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_correlation_step_drop (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ M)
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p →
      Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x orbit)) * R.eval x‖ →
      let N := pi (pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hF : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d (by omega) 1) = 1 ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationNilmanifold w d hw hwd).basis i)) ≤
          (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le)
            orbit (D.raiseStepRealOrbit htd.le R.orbit) b ω hF) ((p + C) ^ C) := by
  obtain ⟨a, ha, hselect⟩ := exists_translation_major_vertical_selection
  obtain ⟨c, _hc, hstep⟩ := exists_native_pair_positive_step_drop d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorCorrelationBudget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ D htd Ψ D₀ M hdegree hD
    orbit R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge hcorr
  dsimp only
  have hbox : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    exact ⟨le_rfl, by have hi := hlengths i; omega⟩
  obtain ⟨η, V, W, hVc, hVo, _hVn, hWc, hWo, _hWn, hheight, hη, hvertV, hvertW,
      _hVne, _hWne, hbias⟩ :=
    hselect w hw (by omega) hwd D htd (fun _ : U => 1) Ψ D₀ M hdegree hD
      orbit R p hp hgeometry hbound hR hRcap (translatedIntegerBox origin lengths) hbox
      (fun x => x) (fun _ => 1) (fun _ _ => by simp)
      (by simpa only [one_mul] using hcorr)
  let r := translationMajorPairBudget a p
  have hcontrols := translationMajorPairBudget_controls a hp ha
  have hpr : p ≤ r := hcontrols.1.trans hcontrols.2.1
  have hr : 2 ≤ r := hcontrols.2.2
  have hcost := hbudget p hp
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le) V W hr hVc hWc
  have hzeroheight : ∀ i, rationalLogHeight ((0 : L →ₗ[ℚ] ℚ)
      ((D.raiseStep htd.le).basis i)) ≤ r := by
    intro i
    simpa [rationalLogHeight] using (show 0 ≤ r by linarith)
  have hfactor := hconstruct η (0 : L →ₗ[ℚ] ℚ) hheight hzeroheight hvertV hvertW origin lengths hlengths
    (hU.trans hpr) (fun i => (Real.exp_le_exp.mpr hcost.2).trans (hlarge i))
    (by simpa only [one_mul, r, translationMajorPairBudget] using hbias)
  rw [hVo, hWo] at hfactor
  refine ⟨η, b, ω, hF, hη, fun i => (hheight i).trans hcost.1,
    fun i j => (hb i j).trans hcost.2, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hF hfactor hcost.2
    (fun i => by exact_mod_cast hlengths i)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_twisted_correlation_step_drop (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (B K : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ B)
      (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ B K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval
            (fun _ : U => 1) x orbit)) * R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hF : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
            (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            (D.raiseStep htd.le) orbit (D.raiseStepRealOrbit htd.le R.orbit) b ω hF)
          ((p + C) ^ C) := by
  obtain ⟨a, ha, hselect⟩ := exists_translation_major_twisted_vertical_selection
  obtain ⟨c, _hc, hstep⟩ := exists_native_pair_positive_step_drop d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorCorrelationBudget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ D₀ B K hdegree hD
    T hT hLip orbit R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge hcorr
  dsimp only
  have hbox : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    exact ⟨le_rfl, by have hi := hlengths i; omega⟩
  obtain ⟨η, V, W, hVc, hVo, _hVn, hWc, hWo, _hWn, hheight, hη, hvertV, hvertW,
      _hVne, _hWne, hbias⟩ :=
    hselect w hw hd hwd M hM D htd (fun _ : U => 1) Ψ D₀ B K hdegree hD
      T hT hLip orbit R p hp hgeometry hbound hR hRcap
      (translatedIntegerBox origin lengths) hbox
      (fun x => x) (fun _ => 1) (fun _ _ => by simp)
      (by simpa only [one_mul] using hcorr)
  let r := translationMajorPairBudget a p
  have hcontrols := translationMajorPairBudget_controls a hp ha
  have hpr : p ≤ r := hcontrols.1.trans hcontrols.2.1
  have hr : 2 ≤ r := hcontrols.2.2
  have hcost := hbudget p hp
  obtain ⟨b, ω, hF, hb, hconstruct⟩ :=
    hstep (weightedTranslationResidueNilmanifold w d hw hwd M hM)
      (D.raiseStep htd.le) V W hr hVc hWc
  have hzero : ∀ i, rationalLogHeight
      ((0 : L →ₗ[ℚ] ℚ) ((D.raiseStep htd.le).basis i)) ≤ r := by
    intro i
    simpa [rationalLogHeight] using (show (0 : ℝ) ≤ r by linarith)
  have hfactor := hconstruct η (0 : L →ₗ[ℚ] ℚ) hheight hzero
    hvertV hvertW origin lengths hlengths (hU.trans hpr)
    (fun i => (Real.exp_le_exp.mpr hcost.2).trans (hlarge i))
    (by simpa only [one_mul, r, translationMajorPairBudget] using hbias)
  rw [hVo, hWo] at hfactor
  refine ⟨η, b, ω, hF, hη, fun i => (hheight i).trans hcost.1,
    fun i j => (hb i j).trans hcost.2, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hF hfactor hcost.2
    (fun i => by exact_mod_cast hlengths i)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationMajorTwistedCorrelationStepDropPolynomial
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ i, rationalLogHeight
          (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
            (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            (D.raiseStep htd.le)
            (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
              (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA)
            (D.raiseStepRealOrbit htd.le R.orbit) b ω hLayers) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_translation_major_twisted_correlation_step_drop d hd
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass (fractionalCoefficientPolynomial F) ≤ B := by
    change realPolynomialMass (fractionalCoefficientPolynomial F) ≤
      (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hv : ∀ i : U ⊕ Fin m, 0 < Sum.elim (fun _ : U => 1) w i := by
      intro i
      cases i with
      | inl i => exact Nat.zero_lt_one
      | inr i => exact hw i
    have hh := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE F
      (Sum.elim (fun _ : U => 1) w) hv d hF
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  apply hstep w hw hwd M hM D htd Ψ
    (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial F) 0) B K
    (majorZeroParameterSlice_degree w hw (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF))
    ((majorZeroParameterSlice_mass _).trans hmass) T hT hLip
    (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F
                (Sum.elim (fun _ : U => 1) w) d hF) A hA)
    R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge
  convert hcorr using 1
  congr 1
  apply Finset.expect_congr rfl
  intro x hx
  rw [majorTranslationDegreeReduced_twisted_integerEval w d hw hwd M Ψ F hF A hA T x (β x) (hβ x hx)]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_potential_data
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → N.filtration.AssociatedGraded)
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        Vfast = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ (p+C)^C) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : U => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C) := by
  obtain ⟨a, ha, hdetect⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_step_drop d hd
  obtain ⟨c, hc, hpotential⟩ := exists_translationMajorDetectedPotentialData d hd
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajor_detected_potential_budget a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    N orbit partner
  let p₁ : ℝ := (p + a)^a
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  have hbudget₁ : p₁ ≤ (p + C)^C := (hbudget p hp).2
  have hbudget₂ : (p₁ + (p₁ + 2)^4 + 1 + c)^c ≤ (p + C)^C := (hbudget p hp).1
  have hlarge₁ (i : U) : Real.exp ((p + a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hbudget₁).trans (hlarge i)
  obtain ⟨η, b, ω, hLayers, hη, _, hb, hfactor⟩ :=
    hdetect w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase : (Fintype.card (Fin m) : ℝ) ≤ p₁ :=
    (weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry).trans hpp₁
  obtain ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp, hprod, hE, hS, hfast, hVfast, hv, hW, hh, hP, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential w hw hwd M hM (D.raiseStep htd.le) orbit partner b ω hLayers η hη
      (fun i => (lengths i : ℝ)) p₁ hp₁ hdim hbase hb hfactor
  have hexp₁ := Real.exp_le_exp.mpr hbudget₁
  have hexp₂ := Real.exp_le_exp.mpr hbudget₂
  refine ⟨b, ω, hLayers, fun i j => (hb i j).trans hbudget₁, ?_⟩
  refine ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp.trans hexp₁, hprod, ?_⟩
  refine ⟨?_, hS, ?_⟩
  · exact N.filtration.symbolSlowBound_mono b ω hLayers (fun _ : U => 1)
      (fun i => (lengths i : ℝ)) (fun i => by exact_mod_cast hlengths i) hexp₁ E hE
  refine ⟨?_, hVfast, hv, ?_⟩
  · convert hfast using 1
  refine ⟨hW, ?_, ?_, hV, hderiv, ?_⟩
  · exact fun i j => (hh i j).trans hbudget₁
  · convert hP using 1
  refine ⟨hq, hqp.trans hexp₂, hgrid, hmass.trans hexp₂, ?_⟩
  intro α
  exact ⟨(hcoeff α).1.trans hexp₂, (hcoeff α).2.trans hexp₂⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      ∀ (retained : Fin d → Submodule ℝ (Fin m → ℝ)),
      (∀ h, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p + C)^C)) (retained h)
        (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i)))) →
      (∀ α, coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i))) α ∈
        ⨆ h, retained h) →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → N.filtration.AssociatedGraded)
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        Vfast = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ (p+C)^C) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : U => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        (∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C)) ∧
        (∀ h, retained h ≤ (Vfast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        ∀ u : U → ℝ,
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u E).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) ∧
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u S).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  obtain ⟨a, ha, hdata⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_potential_data d hd
  obtain ⟨c, hc, hcontain⟩ := exists_majorTranslation_samplingRank_le_real_base_image
  obtain ⟨s, hs, hsep⟩ := exists_detectedTranslation_separated_base
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorSeparated_budget a c s
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    retained hrank hAret N orbit partner
  let p₁ : ℝ := (p + a)^a
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  obtain ⟨hb₁, hb₂, hb₃⟩ := hbudget p hp
  have hlarge₁ (i : U) : Real.exp ((p + a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hb₁).trans (hlarge i)
  obtain ⟨b, ω, hLayers, hb, l, E, P, S, W, v, Vfast, V, q,
      hl, hlp, hprod, hE, hS, hfast, hVfast, hv, hW, hh, hP, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hdata w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase : (Fintype.card (Fin m) : ℝ) ≤ p₁ :=
    (weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry).trans hpp₁
  let Kfast := (Vfast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
  have hspan : Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM (D.raiseStep htd.le) (v j) i : ℝ))) = Kfast := by
    dsimp only [Kfast]
    rw [hVfast]
    exact detectedTranslationBase_span_eq_real_image w d hw hwd M hM (D.raiseStep htd.le) W v hv
  have hTpos (i : U) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hret : ∀ h, retained h ≤ Kfast := by
    intro h
    dsimp only [Kfast]
    rw [hVfast]
    apply hcontain w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers hd hp₁ hbase hdim hdim
      hb W v hv hh (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
      A hA partner E P S hprod (fun i => (lengths i : ℝ)) hTpos hE hP l hl hlp hS
      (h.val + 1) (Real.exp ((p + C)^C)) (retained h) (hrank h)
    exact Real.exp_le_exp.mpr hb₂
  let X := pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
    (D.raiseStep htd.le) orbit partner b ω hLayers
  have hX : ∀ α, coefficients
      (detectedTranslationBasePolynomial w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers X) α ∈
        ⨆ h, retained h := by
    intro α
    rw [detectedTranslationBasePolynomial_majorOrbitSymbol w d hw hwd M hM (D.raiseStep htd.le)
      b ω hLayers (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
      A hA partner]
    exact hAret α
  have hjoin : (⨆ h, retained h) ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM (D.raiseStep htd.le) (v j) i : ℝ))) := by
    rw [hspan]
    exact iSup_le hret
  obtain ⟨_, _, hgroup⟩ := hsep w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers
    hd hp₁ hbase hdim hdim hb W v hv hh E P S X hprod (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hb₃).trans (hlarge i)) hE hP l hl hlp hS
    (⨆ h, retained h) hX hjoin
  have hexp := Real.exp_le_exp.mpr hb₁
  refine ⟨b, ω, hLayers, fun i j => (hb i j).trans hb₁, ?_⟩
  refine ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp.trans hexp, hprod, ?_⟩
  refine ⟨?_, hS, ?_⟩
  · exact N.filtration.symbolSlowBound_mono b ω hLayers (fun _ : U => 1)
      (fun i => (lengths i : ℝ)) hTpos hexp E hE
  refine ⟨?_, hVfast, hv, ?_⟩
  · convert hfast using 1
  refine ⟨hW, ?_, ?_, hV, hderiv, ?_⟩
  · exact fun i j => (hh i j).trans hb₁
  · convert hP using 1
  refine ⟨hq, hqp.trans hexp, hgrid, hmass.trans hexp, ?_, hret, ?_⟩
  · intro α
    exact ⟨(hcoeff α).1.trans hexp, (hcoeff α).2.trans hexp⟩
  · intro u
    have hu := hgroup u
    rw [hspan] at hu
    exact hu

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationDecomposition
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_decomposition
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (_hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      ∀ (retained : Fin d → Submodule ℝ (Fin m → ℝ)),
      (∀ h, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p + C)^C)) (retained h)
        (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i)))) →
      (∀ α, coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i))) α ∈
        ⨆ h, retained h) →
      ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra w d))
        (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
        (Slow : MvPolynomial (U ⊕ Fin m) ℝ)
        (RatPart : MvPolynomial (U ⊕ Fin m) ℚ) (qOut : ℕ),
        (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ (p+C)^C ∧
        Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
        BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) fast.toSubmodule ∧
        (∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p+C)^C) ∧
        BasisGradedSubmodule (Pi.basisFun ℝ (Fin m)) w
          ((fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        (∀ h, retained h ≤ (fast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        realPolynomialMass Slow ≤ Real.exp ((p+C)^C) ∧
        (∀ α, |Slow.coeff α| ≤ Real.exp ((p+C)^C)) ∧
        0 < qOut ∧ (qOut : ℝ) ≤ Real.exp ((p+C)^C) ∧
        (fun α => RatPart.coeff α) ∈ denominatorGrid qOut ∧
        (∀ α, (RatPart.coeff α).den ≤ qOut) ∧
        Slow ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
        RatPart ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
        ∀ (u : U → ℝ) (z : Fin m → ℝ),
          z ∈ (fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
          eval (Sum.elim u z) (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F) =
            eval (Sum.elim (fun i => u i / (lengths i : ℝ))
              (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) Slow +
              eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) RatPart := by
  obtain ⟨a, ha, hdata⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data d hd
  let c := detectedTranslationCoordinateConstant d
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorDecomposition_budget d a c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    retained hrank hAret
  let p₁ : ℝ := (p+a)^a
  let B : ℝ := p₁ + (p₁+c)^c + (2*p+2)^d + 1
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  obtain ⟨hb₁, hb₂, hbmass, hbden⟩ := hbudget p hp
  have hTpos (i : U) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hlarge₁ (i : U) : Real.exp ((p+a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hb₁).trans (hlarge i)
  have hrank₁ h := (hrank h).mono (Real.exp_le_exp.mpr hb₁) hTpos
  obtain ⟨b, ω, hLayers, hb, l, E, P, Q, W, v, fast, V, qV,
      hl, hlp, hprod, hE, hQ, hfast, hfastdef, hv, hW, hh, hP, hV,
      hderiv, hqV, hqVp, hVgrid, hVmass, hVcoeff, hret, hgroup⟩ :=
    hdata w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr retained hrank₁ hAret
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
  let partner := D.raiseStepRealOrbit htd.le R.orbit
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase₀ : (Fintype.card (Fin m) : ℝ) ≤ p :=
    weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry
  have hbase := hbase₀.trans hpp₁
  obtain ⟨qNat, hqNat, hqNatp, hEmass, hebase, hphaseGrid, hbaseGrid⟩ :=
    detectedTranslationGroupCoordinates_uniform_bounds w d hw hwd M hM (D.raiseStep htd.le)
      b ω hLayers hp₁ (hU.trans hpp₁) hbase hdim hb (fun i => (lengths i : ℝ)) hTpos E Q hE l hl hlp hQ
  have hcpow : 0 ≤ (p₁+c)^c := by positivity
  have hdpow : 0 ≤ (2*p+2)^d := by positivity
  have hpB : p₁ ≤ B := by dsimp only [B]; linarith only [hcpow, hdpow]
  have hcB : (p₁+c)^c ≤ B := by dsimp only [B]; linarith only [hp₁, hdpow]
  have hB : 0 ≤ B := hp₁.trans hpB
  let F₀ := specializeMajorParameters (RingHom.id ℝ)
    (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d (fractionalCoefficientPolynomial F)) 0
  have hF₀mass : realPolynomialMass F₀ ≤ Real.exp B := by
    apply (reducedMajorZeroSlice_mass_le w hw d F hF).trans
    apply (pow_le_pow_left₀ (by positivity)
      (show (Fintype.card U : ℝ) + (Fintype.card (Fin m) : ℝ) + 1 ≤ 2*p+2 by linarith) d).trans
    have hb : (2*p+2)^d ≤ B := by dsimp only [B]; linarith only [hp₁, hcpow]
    exact hb.trans (by linarith only [Real.add_one_le_exp B])
  have hVm : realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp B :=
    hVmass.trans (Real.exp_le_exp.mpr hpB)
  have hEm : realPolynomialMass
      (detectedTranslationNormalizedPhase w d hw hwd M hM (D.raiseStep htd.le) E (fun i => (lengths i : ℝ))) ≤ Real.exp B :=
    hEmass.trans (Real.exp_le_exp.mpr hcB)
  have heb (i : Fin m) : realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM (D.raiseStep htd.le) E (fun i => (lengths i : ℝ)) i) ≤ Real.exp B :=
    (hebase i).trans (Real.exp_le_exp.mpr hcB)
  have hqVm : (qV : ℝ) ≤ Real.exp B := hqVp.trans (Real.exp_le_exp.mpr hpB)
  have hqNm : (qNat : ℝ) ≤ Real.exp B := hqNatp.trans (Real.exp_le_exp.mpr hcB)
  have hphaseGrid' := realPolynomialCoefficientGrid_mono (dvd_mul_left qNat qV) hphaseGrid
  have hbaseGrid' i := realPolynomialCoefficientGrid_mono (dvd_mul_left qNat qV) (hbaseGrid i)
  have hVgrid' := denominatorGrid_subset_of_dvd (dvd_mul_right qV qNat) hVgrid
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
  let hφ := pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le)
  let g := detectedTranslationProjectedGenerators N.filtration w d hw hwd φ hφ v
  have hgspan : Submodule.span ℚ (Set.range g) = fast.toSubmodule := by
    rw [hfastdef]
    exact detectedTranslationProjectedGenerators_span N.filtration w d hw hwd φ hφ W v hv
  have hgdata := residuePairProjectedGenerators_data w d hw hwd M hM (D.raiseStep htd.le)
    b ω hLayers W v hv hp₁ hdim hb hh
  have hgheight : ∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p+C)^C :=
    fun j i => (hgdata.2.2.1 j i).trans hb₂
  have hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) fast.toSubmodule := by
    rw [hfastdef]
    exact weightedTranslationGradedProjection_image_graded N.filtration w d hw hwd φ hφ b ω hLayers W hW
  have hVweight : V ∈ weightedSupportLE w d :=
    fun _ hα => (hV (mem_support_iff.mp hα)).le
  have hnormal := exists_detectedTranslation_normalized_weighted_decomposition w d hw hwd M hM
    (D.raiseStep htd.le) b ω hLayers hd (fractionalCoefficientPolynomial F)
    (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
    A hA partner E P Q hprod W hP V (fun i => (lengths i : ℝ)) (fun i => (hTpos i).ne')
    (qV*qNat) (Nat.mul_pos hqV hqNat) (Real.exp B) (Real.exp_pos B).le
    hphaseGrid' hbaseGrid' hVgrid' hVweight heb
  dsimp only at hnormal
  rw [← hfastdef] at hnormal
  obtain ⟨Slow, RatPart, hidentity, hSlowMass, hRatGrid, hSlowW, hRatW, _, _⟩ :=
    hnormal hderiv (fun u => (hgroup u).2)
  let qOut := (qV*qNat)^(d+1)
  have hqOut : 0 < qOut := pow_pos (Nat.mul_pos hqV hqNat) _
  have hdsq : (d : ℝ) ≤ ((d+1 : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg (d : ℝ), Nat.cast_nonneg (α := ℝ) d]
  have hmassBudget : ((d : ℝ)+3)*(B+2) ≤ (p+C)^C :=
    (mul_le_mul_of_nonneg_right (by linarith : (d : ℝ)+3 ≤ ((d+1 : ℕ) : ℝ)^2+3)
      (by positivity : 0 ≤ B+2)).trans hbmass
  have hdenBudget : 2*((d : ℝ)+1)*B ≤ (p+C)^C :=
    (mul_le_mul_of_nonneg_right (by linarith : 2*((d : ℝ)+1) ≤ 2*(((d+1 : ℕ) : ℝ)^2+1)) hB).trans hbden
  have hSlowFinal : realPolynomialMass Slow ≤ Real.exp ((p+C)^C) := by
    apply hSlowMass.trans
    apply (algebraicMajor_mass_le_exp d hB (realPolynomialMass_nonneg _)
      (realPolynomialMass_nonneg _) (realPolynomialMass_nonneg _) (Real.exp_pos B).le
      hF₀mass hEm hVm le_rfl).trans
    exact Real.exp_le_exp.mpr hmassBudget
  have hqFinal : (qOut : ℝ) ≤ Real.exp ((p+C)^C) :=
    (algebraicMajor_denominator_le_exp d qV qNat hqVm hqNm).trans (Real.exp_le_exp.mpr hdenBudget)
  obtain ⟨hrestGrid, hrestW, hrestIdentity⟩ := algebraic_major_restore_integer_coefficients
    F (Sum.elim (fun _ : U => 1) w) d
    ((fast.toSubmodule.baseChange ℝ).map (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)))
    (majorTranslationTopCoordinates w A) (fun i => (lengths i : ℝ)) Slow RatPart qOut hRatGrid hRatW hidentity
  refine ⟨fast, g, Slow, restoredMajorRemainder F (Sum.elim (fun _ : U => 1) w) d RatPart,
    qOut, ?_, hgspan, hgraded, hgheight,
    weightedTranslationBase_real_image_graded w d hw fast.toSubmodule hgraded g hgspan,
    hret, hSlowFinal, ?_, hqOut, hqFinal,
    hrestGrid, (fun α => den_le_of_mem_denominatorGrid hqOut hrestGrid α), hSlowW, hrestW, hrestIdentity⟩
  · simpa only [Fintype.card_fin] using hdim.trans hb₁
  · intro α
    exact (realPolynomialMass_coeff_le Slow α).trans hSlowFinal

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_polynomial_phase_factorization (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (hts : t < s)
      (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) * R.eval x‖ →
      let N := pi (pairModels (nilmanifold s) (D.raiseStep hts.le))
      ∃ (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L)))
          ℚ (PairAlgebra (weightedSubalgebra weight s) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement weight s hs 1) = 1 ∧
        (∀ i, rationalLogHeight (η ((nilmanifold s).basis i)) ≤ (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ (p + C) ^ C ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (nilmanifold s) (D.raiseStep hts.le)
            (orbit s hs P hP) (D.raiseStepRealOrbit hts.le R.orbit) b ω hLayers)
          ((p + C) ^ C) := by
  obtain ⟨c, hc, hstep⟩ := exists_translation_major_correlation_step_drop s hs
  obtain ⟨C, hC, hbudget⟩ := exists_factorizationBudget s c
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ _ _ _ _ D hts P hP R p hp hR hRcap
    origin lengths hlengths hU hlarge hcorr
  let := phaseBasisFintype s
  dsimp only
  let q : ℝ := p + factorizationInputOffset s
  have hpq : p ≤ q := le_factorizationInputBudget s hp
  have hq : 0 ≤ q := hp.trans hpq
  have hfixed : budget s ≤ q := budget_le_factorizationInputBudget s hp
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := hbudget p hp
  have hgeometry : (nilmanifold s).GeometryComplexityLE q :=
    GeometryComplexityLE.mono _ (nilmanifold_geometry s) hfixed
  have hlog : Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)) ≤ q :=
    (le_max_right _ _).trans hfixed
  have hdetector (x : U → ℤ) :
      bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
        (bchRealTranslationHom weight s (weight_le s)
          ((nilmanifold s).filtration.realification.polynomialOrbitEval (fun _ : U => 1)
            x (orbit s hs P hP))) = (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) := by
    rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
    exact orbit_buffered_eval s hs P hP (fun i => (x i : ℝ))
  have hcorrelation : Real.exp (-q) ≤
      ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
          (bchRealTranslationHom weight s (weight_le s)
            ((nilmanifold s).filtration.realification.polynomialOrbitEval (fun _ : U => 1)
              x (orbit s hs P hP))) * R.eval x‖ := by
    simp_rw [hdetector]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  obtain ⟨η, b, ω, hLayers, hη, hηheight, hbheight, hfactor⟩ :=
    hstep weight weight_pos (weight_le s) D hts (localTentKernel 0 8 (by decide)) 0 0
      (by simp) (by simp [realPolynomialMass]) (orbit s hs P hP)
      R q hq hgeometry hlog (hR.mono hpq) hRcap origin lengths hlengths (hU.trans hpq)
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hlarge i)) hcorrelation
  have hdim : (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤
      (p + C) ^ C := by
    apply (phasePair_finrank_le (s := s) D R hR).trans
    apply le_trans (b := q)
    · dsimp [q]
      linarith [budget_le_factorizationInputOffset s]
    · exact (factorizationInputBudget_le_power s c hc hp).trans hcost
  refine ⟨η, b, ω, hLayers, hη, fun i => (hηheight i).trans hcost,
    fun i j => (hbheight i j).trans hcost, hdim, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ b ω hLayers
    hfactor hcost (fun i => by exact_mod_cast hlengths i)

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_ordinary_polynomial_phase_inverse (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (_hts : t < s)
      (P : MvPolynomial U ℝ) (_hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) * R.eval x‖ →
      PolynomialRationalApproximation (fun i => (lengths i : ℝ))
        (Real.exp ((p + C) ^ C)) (homogeneousComponent s P) := by
  obtain ⟨a, _ha, hfactorization⟩ := exists_polynomial_phase_factorization s hs
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ D hts P hP R p hp hR hRcap
    origin lengths hlengths hU hlarge hcorr
  let : FiniteDimensional ℚ (weightedSubalgebra weight s) :=
    (nilmanifold s).basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
    realification_moduleTopology_t2 (nilmanifold s).basis
  let q : ℝ := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfirst : q ≤ (p + C) ^ C := by nlinarith [show 0 ≤ (q + 3) ^ 3 by positivity]
  have hlast : (q + 3) ^ 3 ≤ (p + C) ^ C := by linarith
  obtain ⟨η, b, ω, hF, hη, _hηheight, hb, hdim, hfactor⟩ :=
    hfactorization D hts P hP R p hp hR hRcap origin lengths hlengths hU
      (fun i => (Real.exp_le_exp.mpr hfirst).trans (hlarge i)) hcorr
  let N := pi (pairModels (nilmanifold s) (D.raiseStep hts.le))
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  let X := pairOrbitSymbol (nilmanifold s) (D.raiseStep hts.le)
    (orbit s hs P hP) (D.raiseStepRealOrbit hts.le R.orbit) b ω hF
  have hT : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  have hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional N.filtration φ
        (N.filtration.associatedGradedBasis b ω hF i)) ≤ q :=
    pairScalarFunctional_basis_logHeight s hs (D.raiseStep hts.le) b ω hF hq hb
  have hfactor' : N.filtration.ControlledSymbolFactorization b ω hF
      (η.comp φ.toLinearMap) (fun i => (lengths i : ℝ)) X q := by
    rw [← pairFrequency_zero_comp]
    exact hfactor
  have happ := controlledFactorization_approximation_of_normalized_frequency
    N.filtration b ω hF φ hs η hη (fun i => (lengths i : ℝ)) hT X q hq
    (by simpa only [Fintype.card_fin] using hdim) hθ hfactor'
  have htop : N.filtration.scalarSymbolPolynomial b ω hF (fun _ : U => 1)
      (projectedScalarFunctional N.filtration φ) X = homogeneousComponent s P :=
    pairOrbitSymbol_scalar_top s hs (D.raiseStep hts.le) b ω hF P hP
      (D.raiseStepRealOrbit hts.le R.orbit)
  rw [htop] at happ
  exact happ.mono (Real.exp_le_exp.mpr hlast) hT

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_ordinary_polynomial_phase_affine_inverse (s : ℕ) (hs : 0 < s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (_hts : t < s)
      (P : MvPolynomial U ℝ) (_hP : P.totalDegree ≤ s)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (r : U → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : U → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * x i : ℤ) : ℝ)) P) : ℂ) *
          R.eval x‖ →
      PolynomialRationalApproximation N (Real.exp ((p + C) ^ C))
        (homogeneousComponent s P) := by
  obtain ⟨a, _, hinverse⟩ := exists_ordinary_polynomial_phase_inverse s hs
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.C s * Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ t e _ _ _ _ D hts P hP R p hp hR hRcap
    q hq hqp r K hK hKp N hN origin lengths hlengths hNL hdim hlarge hcorr
  let b : ℝ := (p + a) ^ a
  have hcost : b + (s : ℝ) * p ≤ (p + C) ^ C := by
    simpa [Q, b, Polynomial.eval₂_pow] using hbudget p hp
  have hfirst : b ≤ (p + C) ^ C := by
    exact (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hp)).trans hcost
  let P' := residueAffinePolynomial q r P
  have hP' : P'.totalDegree ≤ s := residueAffinePolynomial_totalDegree_le q r P s hP
  have hcorr' : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
      (Real.fourierChar (eval (fun i => (x i : ℝ)) P') : ℂ) * R.eval x‖ := by
    simpa only [P', residueAffinePolynomial_eval] using hcorr
  have happ : PolynomialRationalApproximation (fun i => (lengths i : ℝ))
      (Real.exp b) (homogeneousComponent s P') :=
    hinverse D hts P' hP' R p hp hR hRcap origin lengths hlengths hdim
      (fun i => (Real.exp_le_exp.mpr hfirst).trans (hlarge i)) hcorr'
  have hbound {z : ℝ} (hz : 0 ≤ z) (hzp : z ≤ Real.exp p) :
      z ^ s * Real.exp b ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ (Real.exp p) ^ s * Real.exp b :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz hzp s) (Real.exp_nonneg b)
      _ = Real.exp (b + (s : ℝ) * p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  exact happ.affine_pullback N (fun i => (lengths i : ℝ)) hN
    (fun i => by exact_mod_cast hlengths i) q s hq r K hK hNL
    (Real.exp b) (Real.exp ((p + C) ^ C))
    (hbound (Nat.cast_nonneg q) hqp) (hbound (by linarith) hKp) P hP

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_normalizedTwist_high_frequency_removal_on_progression (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
      (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (cover : ℕ) (_hcover : 0 < cover) (a : (Σ j, J j) → ℤ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (cover : ℝ) ≤ Real.exp p → (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        N Rrank (W j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * R.eval x‖ →
      ∀ j, d < j.val + 1 → W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  classical
  choose c hc hinverse using fun j : Fin m =>
    OrdinaryPolynomialPhase.exists_ordinary_polynomial_phase_affine_inverse (j.val + 1)
      (Nat.succ_pos _)
  let B := (∑ j, c j) + 2
  have hcB (j : Fin m) : c j ≤ B :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Nat.le_add_right _ _)
  have hB : 2 ≤ B := by dsimp [B]; omega
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ d D htd R cover hcover a poly hpoly W hcoeff p Rrank hp
    hR hRcap hcoverp ha q hq hqp start K hK hKp N hN origin lengths hlengths hNL hX hlarge hRrank hrank hcorr
  have hbudget' : p + (p + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  have hbase : 1 ≤ p + B := by
    have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hlocal (j : Fin m) : (p + c j) ^ c j ≤ (p + B) ^ B := by
    have hb : p + (c j : ℝ) ≤ p + B := by
      have hh : (c j : ℝ) ≤ B := Nat.cast_le.mpr (hcB j)
      linarith
    apply (pow_le_pow_left₀ (by positivity) hb _).trans
    exact pow_le_pow_right₀ hbase (hcB j)
  rcases highest_nonannihilating_tag d W a with hann | ⟨h, hd, hw, hhigher⟩
  · exact hann
  · exfalso
    have hhigh (j : Fin m) (hj : h < j) :
        integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) =
          MvPolynomial.C ((integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)).coeff 0) :=
      integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hhigher j hj)
    have hdegree (j : Fin m) := integerRowPolynomial_totalDegree_le
      (fun i => a ⟨j, i⟩) (hpoly j)
    have hphase : (normalizedTwistFrequencyPolynomial cover a poly).totalDegree ≤ h.val + 1 := by
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact taggedScalar_sum_degree h _ hdegree hhigh
    have htop : homogeneousComponent (h.val + 1) (normalizedTwistFrequencyPolynomial cover a poly) =
        MvPolynomial.C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
          (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h)) := by
      rw [normalizedTwistFrequencyPolynomial, homogeneousComponent_C_mul,
        taggedScalar_sum_top h _ hdegree hhigh]
    have hcost : p + (p + c h) ^ c h ≤ (p + C) ^ C := by linarith [hlocal h]
    have hap := hinverse h D (by omega) (normalizedTwistFrequencyPolynomial cover a poly)
      hphase R p hp hR hRcap q hq hqp start K hK hKp N hN origin lengths hlengths hNL hX
      (fun i => (Real.exp_le_exp.mpr (by linarith : (p + c h) ^ c h ≤ (p + C) ^ C)).trans
        (hlarge i)) (by
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hcorr)
    apply normalizedTwistFrequencyPolynomial_top_not_approximation cover hcover h a poly
      (W h) N Rrank (Real.exp ((p + c h) ^ c h)) hN
      ?_ (hrank h hd) ?_ hw htop hap
    · calc
        _ ≤ Real.exp p * Real.exp ((p + c h) ^ c h) :=
          mul_le_mul_of_nonneg_right hcoverp (Real.exp_nonneg _)
        _ = Real.exp (p + (p + c h) ^ c h) := (Real.exp_add _ _).symm
        _ ≤ Rrank := (Real.exp_le_exp.mpr hcost).trans hRrank
    · intro i
      exact (ha ⟨h, i⟩).trans ((Real.exp_le_exp.mpr
        (by linarith [pow_nonneg (show 0 ≤ p + B by positivity) B] : p ≤ (p + C) ^ C)).trans hRrank)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_rank_localized_correlating_frequency (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (d : ℕ) (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (Fintype.card X : ℝ) ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        ∀ j, d < j.val + 1 → U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  obtain ⟨aC, _, hselect⟩ := exists_localized_correlating_frequency
  obtain ⟨bC, _, hremove⟩ := exists_normalizedTwist_high_frequency_removal_on_progression m
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedTwistExtractionBudget aC bC
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W d D htd R N poly hpoly
    U hcoeff p Rrank hp hR hcap hX hJ hmod hcover hLip hN hRrank hrank hcorr
  let q : ℝ := (p + aC) ^ aC + 3 * p + 16
  have hpow : 0 ≤ (p + aC) ^ aC := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsideq : 3 * p + 16 ≤ q := by dsimp [q]; linarith
  have hfreqq : (p + aC) ^ aC ≤ q := by dsimp [q]; linarith
  have hbudget' : q + (q + bC) ^ bC + 3 * p + 16 ≤ (p + C) ^ C := hbudget p hp
  have hremoven : 0 ≤ (q + bC) ^ bC := by positivity
  have hqfinal : q ≤ (p + C) ^ C := by linarith
  have hremovefinal : (q + bC) ^ bC ≤ (p + C) ^ C := by linarith
  have hsidefinal : 3 * p + 16 ≤ (p + C) ^ C := hsideq.trans hqfinal
  have hsmallN (i : X) : Real.exp (3 * p + 16) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hsidefinal).trans (hN i)
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected⟩ :=
    hselect W N poly R.eval p hp hJ hmod hLip hsmallN
      (fun u _ => (R.norm_eval_le u).trans hcap) hcorr
  let R' := R.scalarAffinePullback (W.modulus : ℚ) (fun i => (start i : ℚ))
  have hR' : R'.ComplexityLE q := hR.mono hpq
  have hR'cap : (R'.normBound : ℝ) ≤ 1 := hcap
  have hR'eval (v : X → ℤ) :
      R'.eval v = R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) := by
    simpa only [R', Int.cast_natCast, add_comm] using
      R.scalarAffinePullback_eval_integer (W.modulus : ℤ) (fun i => (start i : ℤ)) v
  have hzero : translatedIntegerBox (0 : X → ℤ) length = integerBox length := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hlong (i : X) : Real.exp ((q + bC) ^ bC) ≤ (length i : ℝ) := by
    calc
      _ = Real.exp ((q + bC) ^ bC + (3 * p + 16)) * Real.exp (-(3 * p + 16)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((p + C) ^ C) * Real.exp (-(3 * p + 16)) := by
        gcongr
        linarith
      _ ≤ (N i : ℝ) * Real.exp (-(3 * p + 16)) :=
        mul_le_mul_of_nonneg_right (hN i) (Real.exp_nonneg _)
      _ ≤ _ := hlength i
  have hselected' : Real.exp (-q) ≤ ‖𝔼 v ∈ translatedIntegerBox (0 : X → ℤ) length,
      (Real.fourierChar (MvPolynomial.eval
        (fun i => ((start i : ℤ) : ℝ) + (W.modulus : ℝ) * (v i : ℝ))
        (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) * R'.eval v‖ := by
    rw [hzero]
    simpa only [hR'eval, Int.cast_natCast] using
      (Real.exp_le_exp.mpr (neg_le_neg hfreqq)).trans hselected
  have hann := hremove J d D htd R' W.cover W.cover_pos a poly hpoly U hcoeff q Rrank
    hq hR' hR'cap (hcover.trans (Real.exp_le_exp.mpr hpq))
    (fun i => (ha i).trans (Real.exp_le_exp.mpr hfreqq))
    W.modulus W.modulus_pos (hmod.trans (Real.exp_le_exp.mpr hpq))
    (fun i => (start i : ℤ)) (Real.exp (3 * p + 16))
    (Real.one_le_exp (by positivity)) (Real.exp_le_exp.mpr hsideq)
    (fun i => (N i : ℝ)) (fun i => (Real.exp_pos _).trans_le (hN i))
    0 length hpos hcomparison (hX.trans hpq) hlong
    ((Real.exp_le_exp.mpr hremovefinal).trans hRrank) hrank hselected'
  refine ⟨start, length, a, hpos, hlength, hcomparison, hinside, ?_, ?_, hann⟩
  · exact fun i => (ha i).trans (Real.exp_le_exp.mpr (hfreqq.trans hqfinal))
  · exact (Real.exp_le_exp.mpr (neg_le_neg (hfreqq.trans hqfinal))).trans hselected

theorem exists_low_localized_correlating_frequency (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (d : ℕ) (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (Fintype.card X : ℝ) ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        (∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0) ∧
        (normalizedTwistFrequencyPolynomial W.cover a poly).totalDegree ≤ d := by
  obtain ⟨C, hC, hextract⟩ := exists_rank_localized_correlating_frequency m
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W d D htd R N poly hpoly
    U hcoeff p Rrank hp hR hcap hX hJ hmod hcover hLip hN hRrank hrank hcorr
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected, hann⟩ :=
    hextract J W d D htd R N poly hpoly U hcoeff p Rrank hp hR hcap hX hJ
      hmod hcover hLip hN hRrank hrank hcorr
  refine ⟨start, length, truncateTaggedFrequency d a, hpos, hlength, hcomparison, hinside,
    ?_, ?_, ?_, normalizedTwistFrequencyPolynomial_low_degree W.cover d a poly hpoly⟩
  · intro i
    by_cases hi : i.1.val + 1 ≤ d
    · simpa only [truncateTaggedFrequency, if_pos hi] using ha i
    · simp only [truncateTaggedFrequency, if_neg hi, Int.cast_zero, abs_zero]
      exact Real.exp_nonneg _
  · rw [← normalizedTwistFrequencyPolynomial_truncate_correlation W.cover d U a poly
      hcoeff hann (integerBox length)
      (fun v i => (start i : ℝ) + (W.modulus : ℝ) * v i)
      (fun v => R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i))]
    exact hselected
  · intro j hj i
    simp only [truncateTaggedFrequency, if_neg (not_le_of_gt hj)]

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

theorem exists_majorPhase_low_localized_correlating_frequency (m d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1)) (_hd : 0 < d)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J d poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-((p + C) ^ C)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp ((p + C) ^ C) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          majorPhaseSample J d poly Ψ c F β R.eval
            (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        (∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0) ∧
        (normalizedTwistFrequencyPolynomial W.cover a poly).totalDegree ≤ d := by
  obtain ⟨aC, _, hpartner⟩ := exists_majorTranslation_partner_niltest d
  obtain ⟨bC, _, hextract⟩ :=
    NormalizedPolynomialTwist.exists_low_localized_correlating_frequency m
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseLowFourierExtraction_budget aC bC
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W D htd R hd
    N poly hpoly U hcoeff Ψ c F hF β hβ p Rrank hp hR hcap hdim hmod hcover hLip hΨ
    hN hRrank hrank hcorr
  let w := lowTaggedWeight J d
  have hw : ∀ i, 0 < w i := lowTaggedWeight_pos J d
  have hwd : ∀ i, w i ≤ d := lowTaggedWeight_le J d
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  let A := fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    (MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i)
  have hdimMajor : ((Fintype.card X + Fintype.card (LowTaggedIndex J d) : ℕ) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.add_le_add_left (lowTaggedIndex_card_le J d) _
  let M := majorTranslationPartnerModel w d hw hwd D htd
  let : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
    M.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    realification_moduleTopology_t2 M.basis
  obtain ⟨S, hSnorm, hS, hSeval⟩ :=
    hpartner w hw hwd D htd R hd Ψ F hF A hA p hp hdimMajor hΨ hR hcap
  have hsample (u : X → ℤ) (hu : u ∈ integerBox N) :
      S.eval u = majorPhaseSample J d poly Ψ c F β R.eval u := by
    have hclose : ∀ i, |MvPolynomial.eval (fun j => (u j : ℝ)) (A i) - (β u i : ℝ)| ≤ 1/2 := by
      simpa only [A, map_sub, eval_C] using hβ u hu
    simpa only [majorPhaseSample, A, map_sub, eval_C] using hSeval u (β u) hclose
  let q : ℝ := (p + aC) ^ aC + p + 1
  have hpow : 0 ≤ (p + aC) ^ aC := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hSq : S.ComplexityLE q := hS.mono (by dsimp [q]; linarith)
  have hcapS : (S.normBound : ℝ) ≤ 1 := by rw [hSnorm]; rfl
  have hX : (Fintype.card X : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.le_add_right (Fintype.card X) (Fintype.card (Σ j, J j))
  have hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.le_add_left (Fintype.card (Σ j, J j)) (Fintype.card X)
  obtain ⟨_, hfinal, hside⟩ := hbudget p hp
  have hcorrS : Real.exp (-q) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * S.eval u‖ := by
    have heq : (𝔼 u ∈ integerBox N, W.eval N poly u * S.eval u) =
        𝔼 u ∈ integerBox N, W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u := by
      apply Finset.expect_congr rfl
      intro u hu
      rw [hsample u hu]
    rw [heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected, hhigh, hdegree⟩ :=
    hextract J W d M le_rfl S N poly hpoly U hcoeff q Rrank hq hSq hcapS
      (hX.trans hpq) (hJ.trans hpq)
      (hmod.trans (Real.exp_le_exp.mpr hpq)) (hcover.trans (Real.exp_le_exp.mpr hpq))
      (hLip.trans (Real.exp_le_exp.mpr hpq))
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hN i))
      ((Real.exp_le_exp.mpr hfinal).trans hRrank) hrank hcorrS
  refine ⟨start, length, a, hpos, ?_, ?_, hinside, ?_, ?_, hhigh, hdegree⟩
  · intro i
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hside))
      (Nat.cast_nonneg (N i))).trans (hlength i)
  · intro i
    exact (hcomparison i).trans (by
      gcongr)
  · exact fun j => (ha j).trans (Real.exp_le_exp.mpr hfinal)
  · have heq : (𝔼 v ∈ integerBox length,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
        S.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)) =
        𝔼 v ∈ integerBox length,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
        majorPhaseSample J d poly Ψ c F β R.eval
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) := by
      apply Finset.expect_congr rfl
      intro v hv
      rw [hsample _ (hinside v hv)]
    rw [heq] at hselected
    exact (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hselected

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)

theorem majorPhasePlateauSignal_norm_le_one
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) (u : X → ℤ) :
    ‖majorPhasePlateauSignal J k poly c P u‖ ≤ 1 := by
  unfold majorPhasePlateauSignal majorPhaseSample
  rw [mul_one, norm_mul]
  simp only [Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg ((majorPhasePlateauKernel _).nonneg _)]
  exact (majorPhasePlateauKernel _).le_one _

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {X ι η L : Type} [Fintype η] [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
  {lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem globalRestriction_terminal_mem_pointwise
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basis lift
      Z Kinitial Utag poly N Bphase s)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (β : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE wt (wt i))
    (g : (F.realification.adaptedPolynomialFiltration wt).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF wt g = Z)
    (htop : ∀ t : X ⊕ (Σ j, J j) → ℝ,
      (fun i => MvPolynomial.eval t (weightedHomogeneousComponent wt (wt i) (β i))) ∈ history.K) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF wt wt
      (fun i => weightedHomogeneousComponent wt (wt i) (β i))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    ((pull history.outer.1)⁻¹ *
      F.realPolynomialSymbolHom b ω hF wt (F.weightedAdaptedRealChartHom wt wt β hβ g) *
      (pull history.outer.2)⁻¹).coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF wt W) := by
  intro pull
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF wt wt β hβ g, hZ]
  change ((pull history.outer.1)⁻¹ * pull Z * (pull history.outer.2)⁻¹).coord ∈ _
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
  exact F.realSymbolHomogeneousPullback_mem_of_range b ω hF wt wt _ _ W history.K _
    (history.terminal_mem_fast hW) htop

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost shortCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

def keptInclusion (i : {i // keep i}) : C.Variables := ⟨i.val, hkeep i.val i.property⟩

variable (fixed : {i : C.Variables // ¬keep i.val} → ℤ)

noncomputable def axisFixed : {i // ¬keep i} → ℤ :=
  fun i => if hi : C.keep i.val then fixed ⟨⟨i.val, hi⟩, i.property⟩ else C.fixed ⟨i.val, hi⟩

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

theorem exists_finite_children_at_budget {n : ℕ} (H : State n)
    (budget : ℝ) (hcap : budget ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hpast : Bphase ≤ p) (hbudget : budget ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ children : Finset (State (n + 1)),
      (children.card : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant (n + 1) 254) ^
            fullChartStageCountConstant (n + 1) 254) ∧
      (∀ Hnext ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
        Utag poly N Bphase budget H Hnext) ∧
      ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1)
        fast basis lift Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair →
        ∃ Hnext ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
          Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨count, hcount, candidate, hgood, hcover⟩ :=
    exists_full_chart_finite_stage_branches F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget 254 (by omega)
      H.certificate hp hpast hbudget hX hm hJ hη
      (by simpa only [Nat.succ_mul] using hblocks)
      (fun point hpoint => H.retained point (Set.mem_univ _) hpoint) hpoly hN
  let next (i : Fin count) : State (n + 1) :=
    H.append_admissible budget hcap (candidate i).1.1 (candidate i).1.2
      (candidate i).2 (hgood i)
  refine ⟨Finset.univ.image next, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr ((Finset.card_image_le).trans_eq
      (Finset.card_fin count))).trans hcount
  · intro Hnext hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact append_admissible_is_child_at H budget hcap _ _ _ (hgood i)
  · intro q K' pair hpair
    obtain ⟨i, hlabel, heval⟩ := hcover q K' pair hpair
    refine ⟨next i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hentry := append_admissible_entry H budget hcap
      (candidate i).1.1 (candidate i).1.2 (candidate i).2 (hgood i)
    refine ⟨hentry.2.2.trans (congrArg Prod.fst hlabel), ?_, ?_⟩
    · exact (append_admissible_K H budget hcap _ _ _ (hgood i)).trans
        (congrArg Prod.snd hlabel)
    · intro t ht
      change eval₂ t ((next i).slow n) = _ ∧ _
      dsimp only [next]
      rw [hentry.1, hentry.2.1]
      with_reducible exact heval t ht

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartForwardEarlyTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

theorem exists_finite_children_of_stage_bounds {n : ℕ} (H : State n)
    {cap cumulative : ℕ → ℝ} (hH : StageBounds cap cumulative H)
    (hcap : cap n ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hpast : cumulative n ≤ p) (hbudget : cap n ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ children : Finset (State (n + 1)),
      (children.card : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * cap n + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant (n + 1) 254) ^
            fullChartStageCountConstant (n + 1) 254) ∧
      (∀ Hnext ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
        Utag poly N Bphase (cap n) H Hnext) ∧
      ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1)
        fast basis lift Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) q K' pair →
        ∃ Hnext ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
          Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨count, hcount, candidate, hgood, hcover⟩ :=
    exists_full_chart_finite_stage_branches F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) 254 (by omega)
      hH.certificate hp hpast hbudget hX hm hJ hη
      (by simpa only [Nat.succ_mul] using hblocks)
      (fun point hpoint => H.retained point (Set.mem_univ _) hpoint) hpoly hN
  let next (i : Fin count) : State (n + 1) :=
    H.append_admissible (cap n) hcap (candidate i).1.1 (candidate i).1.2
      (candidate i).2 (hgood i)
  refine ⟨Finset.univ.image next, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr ((Finset.card_image_le).trans_eq
      (Finset.card_fin count))).trans hcount
  · intro Hnext hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact append_admissible_is_child_at H (cap n) hcap _ _ _ (hgood i)
  · intro q K' pair hpair
    obtain ⟨i, hlabel, heval⟩ := hcover q K' pair hpair
    refine ⟨next i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hentry := append_admissible_entry H (cap n) hcap
      (candidate i).1.1 (candidate i).1.2 (candidate i).2 (hgood i)
    refine ⟨hentry.2.2.trans (congrArg Prod.fst hlabel), ?_, ?_⟩
    · exact (append_admissible_K H (cap n) hcap _ _ _ (hgood i)).trans
        (congrArg Prod.snd hlabel)
    · intro t ht
      change eval₂ t ((next i).slow n) = _ ∧ _
      dsimp only [next]
      rw [hentry.1, hentry.2.1]
      with_reducible exact heval t ht

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

theorem exists_prefix_counted_budgeted_branch_tree (depth : ℕ)
    (cap cumulative pCount : ℕ → ℝ) (pTree : ℝ)
    (hpTree : 0 ≤ pTree) (hstorage : Bphase ≤ pTree)
    (hcaps : ∀ n < depth, cap n ≤ Bphase)
    (hmono : ∀ n < depth, cumulative n ≤ cumulative (n + 1))
    (hcap : ∀ n < depth, cap n ≤ cumulative (n + 1))
    (hcount : ∀ n < depth, 0 ≤ pCount n)
    (hpast : ∀ n < depth, cumulative n ≤ pCount n)
    (hbudget : ∀ n < depth, cap n ≤ pCount n)
    (hcountTree : ∀ n < depth, pCount n ≤ pTree)
    (hX : (Fintype.card X : ℝ) ≤ pTree) (hm : (m : ℝ) ≤ pTree)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ pTree)
    (hη : (Fintype.card η : ℝ) ≤ pTree)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ pTree)
    (hXlocal : ∀ n < depth, (Fintype.card X : ℝ) ≤ pCount n)
    (hmlocal : ∀ n < depth, (m : ℝ) ≤ pCount n)
    (hJlocal : ∀ n < depth, (Fintype.card (Σ j, J j) : ℝ) ≤ pCount n)
    (hηlocal : ∀ n < depth, (Fintype.card η : ℝ) ≤ pCount n)
    (hblockslocal : ∀ n < depth, (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ pCount n)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree,
      ∀ n, n < depth → ∀ history ∈ T.level n,
        ((T.children n history).card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n)) := by
  have hchildren (n : ℕ) (hn : n < depth) (history : State n) :
      ∃ children : Finset (State (n + 1)),
        (children.card : ℝ) ≤ Real.exp (stageBranchLog (Fintype.card η) n (cap n) pTree) ∧
        (∀ next ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
          Utag poly N Bphase (cap n) history next) ∧
        (∀ q K pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
          Z history.outer.1 history.outer.2 history.K Utag poly N (cap n) q K pair →
          ∃ next ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
            Utag poly N Bphase next q K pair) ∧
        (StageBounds cap cumulative history → (children.card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n))) := by
    by_cases hvalid : StageBounds cap cumulative history
    · obtain ⟨children, hcard, hadmissible, hcomplete⟩ :=
        exists_finite_children_of_stage_bounds history hvalid (hcaps n hn)
          (hcount n hn) (hpast n hn) (hbudget n hn) (hXlocal n hn) (hmlocal n hn)
          (hJlocal n hn) (hηlocal n hn) (hblockslocal n hn) hpoly hN
      refine ⟨children, ?_, hadmissible, hcomplete, fun _ => hcard⟩
      exact hcard.trans (Real.exp_le_exp.mpr
        (stageBranchLog_mono _ _ _ (hcount n hn) (hcountTree n hn)))
    · obtain ⟨children, hcard, hadmissible, hcomplete⟩ :=
        exists_finite_children_at_budget history (cap n) (hcaps n hn) hpTree hstorage
          ((hcaps n hn).trans hstorage) hX hm hJ hη
          ((Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
            (Nat.succ_le_of_lt hn))).trans hblocks) hpoly hN
      exact ⟨children, hcard, hadmissible, hcomplete, fun h => (hvalid h).elim⟩
  let children : ∀ n, State n → Finset (State (n + 1)) := fun n history =>
    if hn : n < depth then Classical.choose (hchildren n hn history) else ∅
  let T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree := {
    children := children
    card := by
      intro n hn history
      dsimp only [children]
      rw [dif_pos hn]
      exact_mod_cast (Classical.choose_spec (hchildren n hn history)).1.trans (Nat.le_ceil _)
    admissible := by
      intro n hn history next hmem
      have hm' : next ∈ Classical.choose (hchildren n hn history) := by
        simpa only [children, dif_pos hn] using hmem
      exact (Classical.choose_spec (hchildren n hn history)).2.1 next hm'
    complete := by
      intro n hn history q K pair hpair
      obtain ⟨next, hmem, hrep⟩ :=
        (Classical.choose_spec (hchildren n hn history)).2.2.1 q K pair hpair
      exact ⟨next, by simpa only [children, dif_pos hn] using hmem, hrep⟩ }
  refine ⟨T, ?_⟩
  intro n hn history hmem
  have hvalid := T.stage_bounds hmono hcap n (Nat.le_of_lt hn) history hmem
  have hsharp := (Classical.choose_spec (hchildren n hn history)).2.2.2 hvalid
  simpa only [T, children, dif_pos hn] using hsharp

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

variable (depth scheduleExponent : ℕ) (x : ℝ)
    (hx : 0 ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hm : (m : ℝ) ≤ x)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ x)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ x)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i)

local notation "cap" => fun n => preparedFiniteForwardCap scheduleExponent countConstants n x
local notation "cumulative" => fun n => preparedFiniteForwardCumulative scheduleExponent countConstants n x
local notation "count" => fun n => preparedFiniteForwardCount scheduleExponent countConstants n x
local notation "storage" => preparedFiniteForwardParameter scheduleExponent countConstants depth x
local notation "Tree" => BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N
  (cumulative depth) cap depth storage

include hx hX hm hJ hη hblocks hpoly hN

theorem exists_early_forward_branch_tree :
    ∃ T : Tree,
      (∀ n, n < depth → ∀ history ∈ T.level n,
        ((T.children n history).card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (count n))) ∧
      (∀ n, n ≤ depth → ((T.level n).card : ℝ) ≤
        Real.exp (preparedFiniteForwardPrefixLog scheduleExponent countConstants n x)) := by
  have hstorage0 := preparedFiniteForwardParameter_nonneg scheduleExponent countConstants depth hx
  have hstorage := (preparedFiniteForward_prefix_bounds scheduleExponent countConstants depth hx).1.2
  have hxtoStorage := le_preparedFiniteForwardParameter scheduleExponent countConstants depth hx
  have hxtoCount (n : ℕ) : x ≤ count n :=
    le_preparedFiniteForwardCount scheduleExponent countConstants n hx
  have hcountTree (n : ℕ) (hn : n < depth) : count n ≤ storage :=
    preparedFiniteForwardCount_le_parameter scheduleExponent countConstants hx hn
  obtain ⟨T, hsharp⟩ := exists_prefix_counted_budgeted_branch_tree
    (F := F) (b := b) (ω := ω) (hF := hF) (J := J)
    (fast := fast) (basis := basis) (lift := lift) (Z := Z)
    depth cap cumulative count storage hstorage0 hstorage
    (fun _ hn => preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hn)
    (fun n _ => preparedFiniteForwardCumulative_le_succ scheduleExponent countConstants n hx)
    (fun n _ => preparedFiniteForwardCap_le_cumulative_succ scheduleExponent countConstants n hx)
    (fun n _ => preparedFiniteForwardCount_nonneg scheduleExponent countConstants n hx)
    (fun n _ => ((preparedFiniteForward_prefix_bounds scheduleExponent countConstants n hx).1.2).trans
      (preparedFiniteForwardParameter_le_count scheduleExponent countConstants n hx))
    (fun n _ => preparedFiniteForwardCap_le_count scheduleExponent countConstants n hx)
    hcountTree (hX.trans hxtoStorage) (hm.trans hxtoStorage) (hJ.trans hxtoStorage)
    (hη.trans hxtoStorage) (hblocks.trans hxtoStorage)
    (fun n _ => hX.trans (hxtoCount n)) (fun n _ => hm.trans (hxtoCount n))
    (fun n _ => hJ.trans (hxtoCount n)) (fun n _ => hη.trans (hxtoCount n))
    (fun n hn => (Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
      (Nat.succ_le_of_lt hn))).trans (hblocks.trans (hxtoCount n))) hpoly hN
  exact ⟨T, hsharp, fun n hn =>
    T.card_level_le_forward_prefix scheduleExponent hx hη hsharp n hn⟩

noncomputable def earlyForwardBranchTree : Tree :=
  Classical.choose (exists_early_forward_branch_tree F b ω hF J fast basis lift Z Utag poly N
    depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN)

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
end


