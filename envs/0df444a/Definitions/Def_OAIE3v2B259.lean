-- Prove2me | Definitions.Def_OAIE3v2B259
-- name    : OAIE3v2B259
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:53:23.913829+00:00
-- url     : https://prove2.me/theorems/cafcf3c4-f8da-425b-ba9d-7d19821f09ce
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 266 of 311
-- statement:
--   Definitions bundle 266 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B248`, `OAIE3v2B249`, `OAIE3v2B251`, `OAIE3v2B302`, `OAIE3v2B253` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateKeptSymbolFactors.lean`, `Estimates/AllocatedExternalLocalFiniteFreezing.lean`, `Estimates/AllocatedExternalRetainedResidual.lean`, `Estimates/AllocatedOrdinaryLongPhysicalTerminalConclusion.lean`, `Estimates/InheritedTaggedQuotientPrecenterMasks.lean`, `Estimates/MixedPairStepDrop.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/NativeSeparatedSumIntervals.lean`, `Estimates/PreparedCenteredStagedModelProductiveGood.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`, `Probability/AllocatedExternalCandidateAllSiteLaw.lean`, `Probability/AllocatedExternalCandidateRetainedSliceLaw.lean`, `Probability/AllocatedExternalLocalSliceLaw.lean`, `Sampling/AllocatedExternalCandidateNativeFrozenScore.lean`, `Sampling/PreparedCenteredForecastEarlyWidth.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B249
import Definitions.Def_OAIE3v2B251
import Definitions.Def_OAIE3v2B302
import Definitions.Def_OAIE3v2B253

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_quadratic_bounded_family :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p →
      ∀ {N : ℕ} (a : ℝ) (b u c : Fin t → ℝ) (h₀ : ZMod N),
      ∃ F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree 1) (Fin 1 × Unit) ((p + C) ^ C),
        ∀ h : ZMod N, (∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) → ∀ n : ℤ,
          F.eval (0, ()) (correlationInput (h.val : ℤ) n) =
            CircleFourier.character (((n : ℝ) *
              (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) : CircleFourier.Circle) / 2 := by
  obtain ⟨A, _, hmodel⟩ := QuadraticMarked.exists_model
  obtain ⟨B, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + 6 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p hp t ht N a b u c h₀
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : productNiltestBudget (q + 6) ≤ (p + C) ^ C := by
    apply (hproduct (q + 6) (by positivity)).trans
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp0
  obtain ⟨η, hη, m, hm, _, d, D, _, M, hMF, hM, _, hlat, hG⟩ := hmodel hp t ht
  let := moduleTopology ℝ (ℝ ⊗[ℚ] QuadraticMarked.Algebra t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] QuadraticMarked.Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  obtain ⟨G, hGn, hGL, hGe⟩ := hG
  let W := NativeMultidegreeNilcharacter.constOne (mixedCorrelationDegree 1) (p := 0) (by positivity)
  have hreal : (QuadraticMarked.multidegree t).realification = M.filtration.realification :=
    congrArg MultidegreeLieFiltration.realification hMF.symm
  let g := (QuadraticMarked.multidegree t).realification.orbitEquivOfEq hreal
    (QuadraticMarked.localOrbit t m a b u c h₀)
  have hstep : 2 = ∑ i, mixedCorrelationDegree 1 i := (mixedCorrelationDegree_sum 1).symm
  obtain ⟨F, hF⟩ := W.exists_product_with_bounded_family D M hstep g (fun _ : Unit => G)
    hq hM (fun _ => hGn) (fun _ => hGL)
  have hcost' : productNiltestBudget (0 + q + 2 + 4) ≤ (p + C) ^ C := by
    rw [show 0 + q + 2 + 4 = q + 6 by ring]
    exact hcost
  refine ⟨F.mono hcost', ?_⟩
  intro h hsmall n
  change F.eval ((0 : Fin 1), ()) (correlationInput (h.val : ℤ) n) = _
  apply (hF ((0 : Fin 1), ()) (correlationInput (h.val : ℤ) n)).trans
  change 1 * G (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) g)) / 2 = _
  rw [one_mul]
  congr 1
  have he := (QuadraticMarked.multidegree t).realification.orbitEquivOfEq_eval hreal
    (QuadraticMarked.localOrbit t m a b u c h₀) (correlationInput (h.val : ℤ) n)
  change G (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval _ g)) = _
  rw [he]
  exact QuadraticMarked.localOrbit_observable D η hη m hm hlat G hGe a b u c h₀ h hsmall n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_step_drop :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeAntisymmetricPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ k, mixedCorrelationDegree 1 k)
    (by decide)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + (X + 2) ^ 2 + 3) + 4
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (antisymmetricPairBudget p q) + (p + q) + 2
  have hprod : 0 ≤ productNiltestBudget (antisymmetricPairBudget p q) := by
    have hbase := V.antisymmetricPairBudget_four_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have h2r : 2 ≤ r := by dsimp [r]; linarith
  have hTr : productNiltestBudget (antisymmetricPairBudget p q) ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, antisymmetricPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.antisymmetricPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) := htT
  let D := pi V.antisymmetricPairModels
  let T := V.antisymmetricPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.antisymmetricPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : Fin 2 => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin 2 => N) = integerBox (fun _ : Fin 2 => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.antisymmetricPairNiltest_bias
  have hf := hconstruct (piFrequency V.antisymmetricPairFrequencies)
    V.antisymmetricPairNiltest_vertical 0 (fun _ : Fin 2 => N)
    (fun _ => NeZero.pos N) (by simpa using h2r)
    (fun _ => (Real.exp_le_exp.mpr hfactor).trans hN) hbias
  exact ⟨{
    topology := τ
    topologicalAdd := htA
    continuousSMul := htM
    hausdorff := htT
    basis := e
    weight := ω
    adapted := hF
    height := fun a b => (he a b).trans hheight
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration e ω hF hf hfactor (fun _ => by exact_mod_cast NeZero.pos N) }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairStepDrop
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_step_drop (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeMixedPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : MixedReplicatedIndex (n + 1), 1) (by rw [mixedReplicated_totalDegree]; omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (mixedPairBudget p q) + (p + q) + ((n + 2 : ℕ) : ℝ)
  have hprod : 0 ≤ productNiltestBudget (mixedPairBudget p q) := by
    have hbase := V.mixedPairBudget_six_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqr : q ≤ r := by dsimp only [r]; linarith only [hp, hprod, hdim]
  have hdimr : ((n + 2 : ℕ) : ℝ) ≤ r := by dsimp only [r]; linarith only [hp, hq, hprod]
  have hTr : productNiltestBudget (mixedPairBudget p q) ≤ r := by dsimp only [r]; linarith only [hp, hq, hdim]
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, mixedPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.mixedPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htT
  let D := pi V.mixedPairModels
  let T := V.mixedPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.mixedPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 x ∈ translatedIntegerBox 0 (fun _ : Fin (n + 2) => N), T.eval x‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin (n + 2) => N) = integerBox (fun _ : Fin (n + 2) => N) := by
      ext x
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.mixedPairNiltest_bias
  have hf := hconstruct (piFrequency V.mixedPairFrequencies) V.mixedPairNiltest_vertical
    0 (fun _ : Fin (n + 2) => N) (fun _ => NeZero.pos N) (by simpa only [Fintype.card_fin] using hdimr)
    (fun _ => (Real.exp_le_exp.mpr hfactor).trans hN) hbias
  exact ⟨{
    topology := τ
    topologicalAdd := htA
    continuousSMul := htM
    hausdorff := htT
    basis := e
    weight := ω
    adapted := hF
    height := fun a b => (he a b).trans hheight
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration e ω hF hf hfactor (fun _ => by exact_mod_cast NeZero.pos N) }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_separated_sum_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p q r : ℝ}, 0 ≤ q → r ≤ q →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f)
        (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) r),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) →
      HasSumTargetIntervals f M (fun k x => W.eval k (fun j => x j.1)) q →
      HasMixedTargetIntervals f M
        (fun k x => (W.tensorPower (d + 2).factorial).eval k
          (mixedReplicatedInput (x 0) (fun j => x j.succ))) ((q + C) ^ C) := by
  obtain ⟨a, _, hseparate⟩ := NativeMultidegreeNilcharacter.exists_mixed_separated_family
    (d + 2) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ p q r hq hrq f hf M W hsym H
  classical
  let v := (q + a) ^ a
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : q + v ≤ (q + C) ^ C := by
    simpa [X, P, v, Polynomial.eval₂_pow] using hbudget q hq
  have hqC : q ≤ (q + C) ^ C := by linarith
  have hvC : v ≤ (q + C) ^ C := by linarith
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let sample (t : Q) := mixedDifferencePoint t.val
  let signal (t : Q) (n : ℤ) := star (f ((∑ k, sample t n k : ℤ) : ZMod N))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  obtain ⟨a', B, hB, hBi, S, _, hS, hSdense, hScor⟩ := hseparate (W.mono hrq) hsym
    Finset.univ Finset.univ_nonempty I (fun t _ => hI t) sample signal
    (fun t _ n _ => by simpa only [signal, norm_star] using hf _) j A hA hAi
    (fun t _ => by simpa only [I, signal, sample, mixedReplicatedInput_diagonal, NativeMultidegreeNilcharacter.mono_eval] using hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hsize : Real.exp (-v) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  have htarget (x : Fin (d + 3) → ℤ) :
      (W.tensorPower (d + 2).factorial).eval (mixedPermutationTensorIndex W.outputDim a')
        (mixedReplicatedInput (x 0) (fun j => x j.succ)) =
      mixedPermutationProduct (W.mono hrq).eval a' x :=
    (W.mixedPermutationProduct_tensorPower a' x).symm
  refine ⟨mixedPermutationTensorIndex W.outputDim a', B, hB, hBi, Q', hS.map, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + v)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-v) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-v) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    refine ⟨hshift t', start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'), ?_⟩
    simpa only [htarget, I, signal, sample, embed, Function.Embedding.coeFn_mk] using (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans (hScor t' ht')

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_sum_pair_factors (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ (j k : Fin W.outputDim)
        (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
          Finset.univ (fun x : Fin (n + 2) → ZMod N => fun l => ((x l).val : ℤ))
          (fun x => W.mixedAntisymmetric j k (fun l => ((x l).val : ℤ)))),
        Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
          V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
          (fun _ : Fin (n + 2) => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨a, _, hkernel⟩ := NativeMultidegreeNilcharacter.exists_mixed_sum_kernel_correlation n
  obtain ⟨b, _, hstep⟩ := exists_mixed_pair_step_drop n
  obtain ⟨c, _, horbit⟩ := exists_mixed_pair_orbit_factors n
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let U := (X + Q + Polynomial.C b) ^ b
  let T := (X + Q + U + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + U + T)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hN hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let u := (p + q + b) ^ b
  let t := (p + q + u + c) ^ c
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hsum : q + u + t ≤ (p + C) ^ C := by
    simpa [X, Q, U, T, q, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hu, ht]
  have huC : u ≤ (p + C) ^ C := by linarith only [hsum, hq, ht]
  have htC : t ≤ (p + C) ^ C := by linarith only [hsum, hq, hu]
  obtain ⟨j, k, ⟨V⟩⟩ := hkernel W f hf i A hA hmiss hcorr
  obtain ⟨F⟩ := hstep (W := W) V ((Real.exp_le_exp.mpr huC).trans hN)
  obtain ⟨O⟩ := horbit (W := W) F hu ((Real.exp_le_exp.mpr htC).trans hN)
  exact ⟨q, hq, hqC, j, k, V, ⟨O.mono htC (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_cyclic_target_pair_factors (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      p ≤ q → ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((q + C) ^ C) ≤ (N : ℝ) →
      HasCyclicMixedTargetCorrelation f
        (fun k x => W.eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q →
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ (q + C) ^ C ∧
      ∃ (i j : Fin W.outputDim)
        (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
          Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
        Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
          V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
          (fun _ : Fin (d + 3) => (N : ℝ)) ((q + C) ^ C)) := by
  obtain ⟨C, hC, hpair⟩ := exists_mixed_sum_pair_factors (d + 1)
  refine ⟨C, hC, ?_⟩
  intro N _ p q W hpq f hf hN H
  have H' : HasCyclicMixedTargetCorrelation f
      (fun k x => (W.mono hpq).eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q := H
  obtain ⟨i, A, hA, hmiss, hc⟩ := HasCyclicMixedTargetCorrelation.mixed_sum (W.mono hpq) H'
  obtain ⟨u, hu, huC, i', j', V, R⟩ := hpair (W.mono hpq) (fun x => star (f x))
    (fun x => by simpa only [norm_star] using hf x) i A hA hmiss hN hc
  exact ⟨u, hu, huC, i', j', V, R⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateKeptSymbolFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

theorem exists_withKeep_marked_frozen_symbol_factors
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν)]
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ den : ℕ, 0 < den ∧ (den : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ den ∧
      ∀ (z : P.productive) (q : ℝ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded),
      (∀ i, s < ((P.withKeep keep hkeep).chart z).slice.length i) →
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates _
          ((P.withKeep keep hkeep).candidate z).orbit) →
      ∃ El Pl Rl : Fmark.RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1),
        El * Pl * Rl = Fmark.realPolynomialSymbolHom bF ν hF (fun _ => 1)
          (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : {i // keep i} => 1)
            (integerSampledRealChart
              (allocatedFrozenIntegerFullChart B U b o poly hm P.centerLift
                z.val.1.val z.val.2.val (P.chart z).sample keep
                ((P.withKeep keep hkeep).chart z).fixed))
            (allocatedFrozenIntegerFullChart_support B U b o poly hm P.centerLift
              z.val.1.val z.val.2.val (P.chart z).sample keep
              ((P.withKeep keep hkeep).chart z).fixed)
            (Fmark.realification.polynomialOrbitCoordinates _ marked)) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ => 1)
            (W.map (D.filtration.associatedGradedMap Fmark φ hφ))) ∧
        Fmark.SymbolSlowBound bF ν hF (fun _ => 1)
          (fun i : {i // keep i} => (A.sides i.val : ℝ))
          (Real.exp ((p + 2) ^ 3 + q)) El ∧
        Fmark.SymbolRationalGrid bF ν hF (fun _ => 1) den Rl := by
  obtain ⟨den, hden, hdenBound, hlden, hmap⟩ :=
    D.filtration.exists_common_refiltered_marked_symbol_factors (σ := {i // keep i})
      Fmark bD ω hD bF ν hF φ hφ hH hl hentries hp hsource htarget hHp hlp
  refine ⟨den, hden, hdenBound, hlden, ?_⟩
  intro z q W hlength hfactor
  have hside (i : {i // keep i}) : (0 : ℝ) < A.sides i.val := by
    apply Nat.cast_pos.mpr
    change 0 < Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val
    cases i.val with
    | inl x => exact S.positive
    | inr x => exact allocatedPrincipalSides_pos B U b S x
  obtain ⟨El, Pl, Rl, hprod, hPl, hEl, hRl⟩ :=
    hmap (fun i : {i // keep i} => (A.sides i.val : ℝ)) hside q W
      (D.filtration.realification.polynomialOrbitCoordinates _
        ((P.withKeep keep hkeep).candidate z).orbit) hfactor
  refine ⟨El, Pl, Rl, ?_, hPl, hEl, hRl⟩
  have hmark := ((P.withKeep keep hkeep).candidate z).formal_mark_group hφ
    (by simpa only [max_self] using hlength)
  have hmarked := hprod.trans (congrArg
    (Fmark.realPolynomialSymbolHom bF ν hF (fun _ : {i // keep i} => 1)) hmark)
  apply hmarked.trans
  apply congrArg (Fmark.realPolynomialSymbolHom bF ν hF (fun _ : {i // keep i} => 1))
  apply adaptedChart_eq_of_chart_eq
  exact congrArg integerSampledRealChart (P.withKeep_chart_integerChart keep hkeep z)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalLocalFiniteFreezing
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : F.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D F φ marked)

variable (sectionMap : M →ₗ[ℚ] L)
    (hsectionLayer : ∀ j, ∀ y ∈ F.layer j, sectionMap y ∈ D.filtration.layer j)
    (EF RF : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (middle : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)

theorem finiteFreezing_of_selection
    {Left Right : Type*} (Q modulus : ℕ) (hQ : 0 < Q) (hmodulus : 0 < modulus)
    (left : Left → D.RealGroup) (right : Right → D.RealGroup)
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1)) (weight : (X → ℤ) → ℂ)
    {budget Bweight Lip ε τ θ Sscore : ℝ}
    (hQbound : (Q : ℝ) ≤ max 1 budget) (hmodulusBound : (modulus : ℝ) ≤ budget)
    (htwo : ∀ i, 2 ≤ C.slice.length i)
    (hlong : ∀ i, 2 * budget * max 1 budget ≤ (C.slice.length i : ℝ))
    {densityCost : ℝ}
    (hsourceDense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints)
    (hθ : 0 < θ) (herr : 0 ≤ Bweight * (Lip * ε))
    (hscore : Sscore ≤ candidate.score (fun x value => (tests x).observable value) weight)
    (hselect :
      (∀ i, 0 < C.slice.length i) →
      (∀ i v, v < C.slice.length i →
        |((C.slice.start i : ℤ) : ℝ) + C.step * v| ≤ (A.sides i.val : ℝ)) →
      (∀ i, (C.step : ℝ) * C.slice.length i ≤ 2 * (A.sides i.val : ℝ)) →
      (∀ i, 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * C.slice.length i) →
      (Sscore ≤ 𝔼 x : (∀ i, Fin (C.slice.length i)),
        (weight (C.physical (affineParentIntegerPoint C.slice.length
            (fun i => (C.slice.start i : ℤ)) C.step x)) *
          C.freezingOriginalValue candidate tests (affineParentIntegerPoint C.slice.length
            (fun i => (C.slice.start i : ℤ)) C.step x)).re) →
      ∃ T : ResidueBoxSlice C.slice.length modulus, (∀ i, 0 < T.length i) ∧
        (∀ i, θ * C.slice.length i /
          (4 * modulus * Q * (Fintype.card C.Variables + 1 : ℝ)) ≤ T.length i) ∧
        ∃ i j,
          (∀ x : ∀ k, Fin (T.length k),
            ‖C.freezingOriginalValue candidate tests
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x) -
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)‖ ≤ Lip * ε) ∧
          (∀ x : ∀ k, Fin (T.length k),
            ‖weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
                C.freezingOriginalValue candidate tests
                  (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x) -
              weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
                C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                  (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)‖ ≤ Bweight * (Lip * ε)) ∧
          τ < 𝔼 x : (∀ k, Fin (T.length k)),
            (weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)).re) :
    ∃ slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) (C.step * modulus),
      IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
        (densityCost + Real.log ((4 * modulus * Q * (Fintype.card C.Variables + 1 : ℝ)) / θ))
        slice.integerPoints ∧
      slice.integerPoints ⊆ C.slice.integerPoints ∧
      ∃ i j,
        (∀ u ∈ slice.integerPoints,
          ‖(tests (C.physical u)).observable (candidate.value u) -
            C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u‖ ≤ Lip * ε) ∧
        (∀ u ∈ slice.integerPoints,
          ‖weight (C.physical u) * (tests (C.physical u)).observable (candidate.value u) -
            weight (C.physical u) *
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u‖ ≤
            Bweight * (Lip * ε)) ∧
        τ < (𝔼 u ∈ slice.integerPoints, weight (C.physical u) *
          C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u).re ∧
        τ - Bweight * (Lip * ε) ≤
          (𝔼 u ∈ slice.integerPoints, weight (C.physical u) *
            (tests (C.physical u)).observable (candidate.value u)).re := by
  have hparent (i) (v : ℕ) (hv : v < C.slice.length i) :
      |((C.slice.start i : ℤ) : ℝ) + C.step * v| ≤ (A.sides i.val : ℝ) := by
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (C.slice.inside i v hv).le
  have hwidth (i) : (C.step : ℝ) * C.slice.length i ≤ 2 * (A.sides i.val : ℝ) := by
    exact_mod_cast C.slice.stride_mul_length_le_twice i (htwo i)
  have hlarge (i) : 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * C.slice.length i := by
    have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    have hmnonneg : (0 : ℝ) ≤ modulus := Nat.cast_nonneg _
    have hBnonneg : 0 ≤ budget := hmnonneg.trans hmodulusBound
    have hprod : (2 * (modulus : ℝ)) * Q ≤ (C.slice.length i : ℝ) := by
      calc
        _ ≤ (2 * budget) * max 1 budget :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmodulusBound (by norm_num)) hQbound
            (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hBnonneg)
        _ ≤ _ := hlong i
    have hdiv := (le_div_iff₀ hQpos).mpr hprod
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm (C.slice.length i : ℝ)] using hdiv
  have hindexed : Sscore ≤ 𝔼 x : (∀ i, Fin (C.slice.length i)),
      (weight (C.physical (affineParentIntegerPoint C.slice.length
          (fun i => (C.slice.start i : ℤ)) C.step x)) *
        C.freezingOriginalValue candidate tests (affineParentIntegerPoint C.slice.length
          (fun i => (C.slice.start i : ℤ)) C.step x)).re := by
    rw [AllocatedExternalLocalCandidate.score, C.slice.expect_integerPoints C.step_pos,
      Complex.re_expect] at hscore
    have hpoint (x : ∀ i, Fin (C.slice.length i)) :
        affineParentIntegerPoint C.slice.length (fun i => (C.slice.start i : ℤ)) C.step x =
          C.slice.integerPoint x := by
      funext i
      simp only [affineParentIntegerPoint, ResidueBoxSlice.integerPoint,
        ResidueBoxSlice.point, Nat.cast_add, Nat.cast_mul]
    simpa only [C.freezingOriginalValue_eq candidate tests, hpoint] using hscore
  obtain ⟨T, hTlen, hTlong, i, j, herror, hweighted, hfrozen⟩ :=
    hselect (C.slice.length_pos_of_dense hsourceDense) hparent hwidth hlarge hindexed
  have hdenom : (0 : ℝ) < 4 * modulus * Q * (Fintype.card C.Variables + 1) := by
    have hmpos : (0 : ℝ) < modulus := Nat.cast_pos.mpr hmodulus
    have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    positivity
  refine ⟨C.slice.composeSlice T,
    C.slice.composeSlice_isDenseCommonStrideBox_of_fraction T C.step_pos hmodulus hsourceDense
      hθ hdenom hTlong,
    C.slice.composeSlice_integerPoints_subset T, i, j, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [C.slice.composeSlice_integerPoints_eq_affine_image T] at hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    simpa only [C.freezingOriginalValue_eq candidate tests] using herror x
  · intro u hu
    rw [C.slice.composeSlice_integerPoints_eq_affine_image T] at hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    simpa only [C.freezingOriginalValue_eq candidate tests] using hweighted x
  · rw [C.slice.expect_composeSlice_integerPoints T C.step_pos hmodulus, Complex.re_expect]
    exact hfrozen
  · rw [C.slice.expect_composeSlice_integerPoints T C.step_pos hmodulus, Complex.re_expect]
    let orig := fun x : ∀ k, Fin (T.length k) =>
      weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
        C.freezingOriginalValue candidate tests
          (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)
    let froz := fun x : ∀ k, Fin (T.length k) =>
      weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
        C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
          (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)
    have he := complex_expect_error_le Finset.univ froz orig herr (by
      intro x _
      simpa only [norm_sub_rev] using hweighted x)
    have hre := (Complex.re_le_norm _).trans he
    rw [Complex.sub_re, Complex.re_expect, Complex.re_expect] at hre
    have hmean : τ - Bweight * (Lip * ε) ≤ 𝔼 x, (orig x).re := by
      change τ < 𝔼 x, (froz x).re at hfrozen
      linarith
    simpa only [orig, C.freezingOriginalValue_eq candidate tests] using hmean

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalLocalSliceLaw
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

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

theorem localLaw_score (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) :
    (C.localLaw.complexMean (fun site => weight (A.physical C.path site) *
      observable (A.physical C.path site) (candidate.siteValue site))).re =
      candidate.score observable weight := by
  unfold score siteValue
  have h := C.localLaw_complexMean_parameter (fun x =>
    weight (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)) *
    observable (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))
      (candidate.value (C.retainedParameter x)))
  simp only [C.retainedParameter_parameter] at h
  exact congrArg Complex.re h

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InheritedTaggedQuotientPrecenterMasks
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

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e dQ dQF : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s dQ)
    (hQ : Q.filtration = D.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold (M ⧸ Fmark.filtration.layerIdeal (s + 1)) s dQF)
    (hQF : QF.filtration = Fmark.filtration.quotientTop)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark.filtration φ marked)

theorem topQuotient_value (u : C.Variables → ℤ) :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).value u =
      (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
          (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) : Q.Space) := by
  unfold value
  rw [topQuotient_orbit, D.topQuotientOrbit_eval Q hQ]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateNativeFrozenScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

variable (hσ1 : ∀ j, σ j ≤ 1)
  (H : Fin m → ℝ)
  (hH : ∀ j, 0 ≤ H j)
  (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
  (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
  (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
  (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

variable {frozenScoreThreshold : ℝ}

variable (hmarkFactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) left *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) right) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked)

omit [PseudoMetricSpace Fref.Space] in
include hmarkFactor in

theorem refilteredScoredAssembly_mark_on_slice
    (ambientMiddle : Dref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (hmarkedMiddle : map (realLieHomToRat (realificationLieHom (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W))).toLinearMap
      ambientMiddle.log = markedMiddle.log)
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
        (D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked := by
  have hglobal := Dref.filtration.formal_mark_realEval Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (fullTaggedVariableWeight (X := X) J)
    ambientMiddle markedMiddle hmarkedMiddle (fun i => ((P.chart z).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at hglobal
  have heval := D.externalCandidateOrbit_realEval W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
    (fun i => ((P.chart z).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at heval
  rw [heval, ← hmarkFactor z u hu]
  simp only [map_mul]
  rw [D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    hglobal, (middle z).mark_on_slice u hu]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw
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
    (points : Finset (C.Variables → ℤ))
    (hpoints : points.Nonempty)
    (hbox : points ⊆ integerBox (fun i : C.Variables => A.sides i.val))

theorem retainedLaw_complexMean_parameter
    (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    (C.retainedLaw points hpoints hbox).complexMean (fun site => f site.val) =
      𝔼 u ∈ points, f (C.parameter u) := by
  rw [retainedLaw, FiniteProbabilityWeights.complexMean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_complexMean _ _ (fun u => f (C.parameter u))

theorem retainedLaw_complexMean_physical (f : (X → ℤ) → ℂ) :
    (C.retainedLaw points hpoints hbox).complexMean
        (fun site => f (A.physical C.path site)) =
      𝔼 u ∈ points, f (C.physical u) :=
  C.retainedLaw_complexMean_parameter points hpoints hbox
    (fun x => f (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

theorem siteLaw_complexMean_physical (z : out.retained) (f : (X → ℤ) → ℂ) :
    (out.siteLaw z).complexMean (fun site => f (A.physical z.val site)) =
      𝔼 u ∈ (out.slice z).integerPoints,
        f ((P.chart ⟨z.val, out.subset z.property⟩).physical u) := by
  have h := (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw_complexMean_physical
    (out.slice z).integerPoints (out.dense z).nonempty
    (out.slice z).integerPoints_subset_integerBox f
  rw [P.chart_path] at h
  exact h

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalRetainedResidual
namespace OAI


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

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

theorem sliceTest_eval (j : C.Variables → ℤ) :
    (candidate.sliceTest reference).eval j =
      reference.observable (candidate.value
        (commonStridePoint (fun i => (C.slice.start i : ℤ)) C.step j)) := by
  have h := (reference.withOrbit candidate.orbit).scalarAffinePullback_eval_integer
    (C.step : ℤ) (fun i => (C.slice.start i : ℤ)) j
  have hpoint : (fun i => (C.step : ℤ) * j i + (C.slice.start i : ℤ)) =
      commonStridePoint (fun i => (C.slice.start i : ℤ)) C.step j := by
    funext i
    exact add_comm _ _
  rw [hpoint] at h
  simpa only [sliceTest, Int.cast_natCast, RationalFilteredNilmanifold.Niltest.withOrbit_eval,
    value] using h

theorem sliceTest_eval_on_slice (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    (candidate.sliceTest reference).eval
      (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u) =
      reference.observable (candidate.value u) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
  rw [C.slice_index, candidate.sliceTest_eval, ← C.slice.integerPoint_eq]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

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

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.candidateVariableDecidableEq
noncomputable def normalizedSlicePacket {p : ℝ} (hreference : reference.ComplexityLE p) :
    LocalMajorSliceTest D (fun i : C.Variables => A.sides i.val) cost p where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice
  dense := by
    have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
      Subsingleton.elim _ _
    rw [he]
    exact C.dense
  test := (candidate.sliceTest reference).conjugate.expNormalize p
  norm := by
    exact_mod_cast ((candidate.sliceTest reference).conjugate.expNormalize_norm hreference)
  complexity := (candidate.sliceTest reference).conjugate.expNormalize_complexity hreference

theorem normalizedSlicePacket_weight {p : ℝ} (hreference : reference.ComplexityLE p)
    (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    (candidate.normalizedSlicePacket reference hreference).weight u =
      (Real.exp (-p) : ℂ) * reference.observable (candidate.value u) := by
  have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
    Subsingleton.elim _ _
  have hu' : u ∈ @ResidueBoxSlice.integerPoints C.Variables _ _ _ (Classical.decEq _) C.slice := by
    rw [← he]
    exact hu
  change star (((candidate.sliceTest reference).conjugate.expNormalize p).eval
    (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u)) = _
  rw [RationalFilteredNilmanifold.Niltest.expNormalize_eval,
    RationalFilteredNilmanifold.Niltest.eval_conjugate,
    candidate.sliceTest_eval_on_slice reference u hu', star_mul, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

end AllocatedExternalLocalCandidate

namespace AllocatedExternalLocalChart
variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem frozenLongExtension_fixedNatural (u : C.Variables → ℤ) :
    frozenLongExtension C.keep C.fixedNatural u = C.parameter u := by
  funext i
  by_cases hi : C.keep i
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, dif_pos hi]
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, fixedNatural, dif_neg hi]
    exact Int.toNat_of_nonneg (C.fixed_in_box ⟨i, hi⟩).1

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

attribute [local instance] candidateVariableDecidableEq

noncomputable def admissibleFullPacket {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost) :
    LocalMajorSliceTest D A.sides cost p where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice.freezeShort C.keep C.fixedNatural C.fixedNatural_lt
  dense := by
    have h := (candidate.normalizedSlicePacket reference hreference).slice.freezeShort_dense
      C.keep C.fixedNatural C.fixedNatural_lt C.step_pos
      (candidate.normalizedSlicePacket reference hreference).dense
      (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩)
    simpa only [Real.log_exp, max_self, normalizedSlicePacket] using h
  test := (candidate.normalizedSlicePacket reference hreference).test.liftLong C.keep
  norm := (candidate.normalizedSlicePacket reference hreference).norm
  complexity := (candidate.normalizedSlicePacket reference hreference).complexity

theorem admissibleFullPacket_expect {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (signal : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
      signal site.val * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      (Real.exp (-p) : ℂ) * C.localLaw.complexMean
        (fun site => signal site.val * reference.observable (candidate.siteValue site)) := by
  let short := candidate.normalizedSlicePacket reference hreference
  let full := short.freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩)
  have hmean := short.expect_freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩) signal
  have hleft :
      (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
        signal site.val * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      𝔼 u ∈ C.slice.integerPoints,
        signal (C.parameter u) * short.weight u := by
    rw [(candidate.admissibleFullPacket reference hreference hcost hshort).slice.expect_subtypeSites
      (fun x => signal x * (candidate.admissibleFullPacket reference hreference hcost hshort).weight x)]
    simpa only [admissibleFullPacket, full, short, Real.log_exp, max_self,
      C.frozenLongExtension_fixedNatural, normalizedSlicePacket,
      LocalMajorSliceTest.freezeShort, LocalMajorSliceTest.weight] using hmean
  rw [hleft]
  change _ = (Real.exp (-p) : ℂ) * C.localLaw.complexMean
    (fun site => signal site.val * reference.observable (candidate.value (C.retainedParameter site.val)))
  rw [C.localLaw_complexMean_parameter
    (fun x => signal x * reference.observable (candidate.value (C.retainedParameter x)))]
  rw [Finset.mul_expect]
  have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
    Subsingleton.elim _ _
  have hpoints := congrArg
    (fun dec : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables _ _ _ dec C.slice) he
  rw [hpoints]
  apply Finset.expect_congr rfl
  intro u hu
  have hu' : u ∈ C.slice.integerPoints := by
    rw [hpoints]
    exact hu
  rw [candidate.normalizedSlicePacket_weight reference hreference u hu']
  change signal (C.parameter u) * ((Real.exp (-p) : ℂ) * reference.observable (candidate.value u)) =
    (Real.exp (-p) : ℂ) * (signal (C.parameter u) *
      reference.observable (candidate.value (C.retainedParameter (C.parameter u))))
  rw [C.retainedParameter_parameter]
  ring

theorem admissibleFullPacket_site_expect {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ) :
    (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
      err site * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      (Real.exp (-p) : ℂ) * C.localLaw.complexMean
        (fun site => err site * reference.observable (candidate.siteValue site)) := by
  let signal : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    Function.extend Subtype.val err (fun _ => 0)
  have heval (site : A.Site) : signal site.val = err site :=
    Subtype.val_injective.extend_apply _ _ site
  have h := candidate.admissibleFullPacket_expect reference hreference hcost hshort signal
  simpa only [heval] using h

theorem localLaw_residual_le_of_uniform {p ε : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides cost p,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤ ε) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp p * ε := by
  have h := hUniform (candidate.admissibleFullPacket reference hreference hcost hshort)
  rw [candidate.admissibleFullPacket_site_expect reference hreference hcost hshort err,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))] at h
  calc
    _ = Real.exp p * (Real.exp (-p) * ‖C.localLaw.complexMean
        (fun site => err site * reference.observable (candidate.siteValue site))‖) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp p * ε := mul_le_mul_of_nonneg_left h (Real.exp_nonneg p)

theorem localLaw_residual_le_exp_of_uniform {p Eres : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides cost p,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  simpa only [← Real.exp_add, sub_eq_add_neg] using
    candidate.localLaw_residual_le_of_uniform reference hreference hcost hshort err hUniform

theorem localLaw_residual_le_exp_of_uniform_budget
    {p Eres sliceBudget testBudget : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : p ≤ testBudget)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides sliceBudget testBudget,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  apply candidate.localLaw_residual_le_exp_of_uniform reference hreference hcost hshort err
  intro packet
  exact hUniform (packet.mono hSliceBudget hTestBudget)

end AllocatedExternalLocalCandidate
end
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L : Type} {M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

theorem localLaw_residual_le_exp_of_universal_native_budget
    {p Eres sliceBudget testBudget : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : p ≤ testBudget)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  apply candidate.localLaw_residual_le_exp_of_uniform_budget reference hreference hcost hshort
    hSliceBudget hTestBudget err
  intro packet
  exact hUniform (UniversalLocalMajorSliceTest.ofLocalMajorSliceTest packet)

end AllocatedExternalLocalCandidate
end
end Erdos3.VectorPolynomial


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastEarlyWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem preparedCenteredForecast_slice_bounds {p : ℝ} {A : Finset (integerBox sides)}
    (hA : IsDenseCommonStrideBox sides p (A.image Subtype.val)) :
    A.Nonempty ∧ (Fintype.card (integerBox sides) : ℝ) / A.card ≤
      Real.exp (p * Fintype.card (LayerSamplerVariables G I n B)) := by
  exact ⟨Finset.image_nonempty.mp hA.nonempty, allocatedParameterBox_slice_cost B U b S hA⟩

theorem preparedCenteredForecast_slice_family_bounds
    {Path : Type*} {Tests : Path → Type*}
    (slices : ∀ z, Tests z → Finset (integerBox sides)) {p : ℝ}
    (hDense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image Subtype.val)) :
    (∀ z j, (slices z j).Nonempty) ∧
    (∀ z j, (Fintype.card (integerBox sides) : ℝ) / (slices z j).card ≤
      Real.exp (p * Fintype.card (LayerSamplerVariables G I n B))) := by
  exact ⟨fun z j => (preparedCenteredForecast_slice_bounds B U b S (hDense z j)).1,
    fun z j => (preparedCenteredForecast_slice_bounds B U b S (hDense z j)).2⟩

theorem preparedCenteredForecast_niltest_star_eval_bound
    {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : ι → ℕ}
    (V : D.Niltest w) (hcap : (V.normBound : ℝ) ≤ 1) (x : ι → ℤ) :
    ‖star (V.eval x)‖ ≤ 1 := by
  simpa only [norm_star] using (V.norm_eval_le x).trans hcap

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def allocatedExternalConditionalExcessExponent (m : ℕ) : ℕ :=
  (exists_allocated_centered_narrow_prescribed_marginal_pointwise.{0,0,0,0,0,0} m).choose

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOrdinaryLongPhysicalTerminalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

noncomputable abbrev nativePhysicalTerminalAffineBudget (s scheduleExponent : ℕ) (x : ℝ) : ℝ :=
  preparedFiniteForwardCumulative scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s x

noncomputable abbrev nativePhysicalTerminalWorkBudget (s scheduleExponent : ℕ) (x : ℝ) : ℝ :=
  preparedFiniteForwardWork scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s x

noncomputable abbrev nativePhysicalTerminalFullBudget
    (s m Cprimitive scheduleExponent : ℕ) (x : ℝ) : ℝ :=
  allocatedCandidateTerminalFullInput s m Cprimitive x
    (nativePhysicalTerminalWorkBudget s scheduleExponent x)
    (nativePhysicalTerminalAffineBudget s scheduleExponent x)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredStagedModelProductiveGood
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

def AllocatedPathProductivity {nX : ℕ}
    (N : Fin nX → ℕ)
    (widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)) (test : (Fin nX → ℝ) → ℝ) (gain : ℝ)
    (z : bases × rectangularWeightIndices 0 widths 1) : Prop :=
  let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
  let Sites := integerBox sides
  Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val, z.2.val)) ∧
    (gain / 2 ≤ 𝔼 q : Sites, test
      (fun i => (jointIntegerPhysicalSite q.val (z.1.val, z.2.val) i : ℝ))) ∧
    ∀ q : Sites, jointIntegerPhysicalSite q.val (z.1.val, z.2.val) ∈ integerBox N

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateSampler

local instance degreeSourceProfileSiteNonempty_r46e5a6_1 : Nonempty A.Site := A.site_nonempty
noncomputable abbrev degreeSourceCountConstants (r : ℕ) : ℕ :=
  fullChartStageCountConstant (r + 1) 254

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end


