-- Prove2me | Definitions.Def_OAIE3v2B221
-- name    : OAIE3v2B221
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:39:54.422535+00:00
-- url     : https://prove2.me/theorems/54aa9d11-63f1-4d22-97fc-9e928e6a408f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 226 of 311
-- statement:
--   Definitions bundle 226 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B200`, `OAIE3v2B201`, `OAIE3v2B202` of this split.
--
--   Modules: `Dynamics/MixedQuadrupleBudget.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/ControlledRealFastCoefficientAction.lean`, `Estimates/MixedFixedReduction.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/TerminalControlledFactorization.lean`, `Estimates/UniformFastCoefficientSpec.lean`, `Geometry/FastCoefficientDerivativeCoordinates.lean`, `Geometry/FullFastCoefficientCoordinates.lean`, `Lattices/NativeFrozenAffineExpansion.lean`, `Lattices/NativeIntegerSelfEquivalence.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Linear/FullFastRelativeSpanning.lean`, `Linear/NativeRankRelationExistence.lean`.
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
import Definitions.Def_OAIE3v2B202

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

universe u v

open Module
open scoped TensorProduct NNReal

theorem freezingExponent_control {σ : Type u} {L : Type v} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L s d)
    (M : D.MultidegreeStructure bound) (S : Finset σ) (b : σ → ℤ)
    (g : M.filtration.realification.PolynomialOrbit)
    (f : D.Space → ℂ) (ℓ B : ℝ≥0)
    (hf : letI := D.metricSpace; LipschitzWith ℓ f) (hfb : ∀ x, ‖f x‖ ≤ B)
    {p : ℝ} (hM : M.ComplexityLE p) (hℓ : (ℓ : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold
        (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
        (multidegreeWeight (retainedCoordinateWeight S) bound)
        (finrank ℚ (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))),
      E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S) ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps
          (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl) ∧
      letI := moduleTopology ℝ
        (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
      letI : IsTopologicalAddGroup
          (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
        realification_moduleTopology_t2 E.basis
      ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
        T.ComplexityLE ((p + freezingExponent.{u, v} s) ^ freezingExponent.{u, v} s) ∧
        E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
        ∀ x, T.eval x = f (QuotientGroup.mk
          (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) g)) :=
  (Classical.choose_spec (exists_controlled_frozen_niltest.{u, v} s)).2
    D M S b g f ℓ B hf hfb hM hℓ hB

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

universe u

open Module
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_freezing_niltest {σ : Type u} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (b : σ → ℤ) (i : Fin W.outputDim),
      ∃ t n : ℕ, t = (∑ j ∈ S, bound j) ∧ n ≤ W.dim ∧
        ∃ E : RationalFilteredNilmanifold
          (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) t n,
          letI := moduleTopology ℝ
            (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S))
          letI : IsTopologicalAddGroup
              (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
            IsModuleTopology.topologicalAddGroup ℝ _
          letI : T2Space
              (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
            realification_moduleTopology_t2 E.basis
          ∃ T : E.Niltest (fun _ : S => 1), T.normBound = 1 ∧
            T.ComplexityLE ((p + C) ^ C) ∧
            E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
            ∀ x, T.eval x = W.eval i (freezeCoordinates S b x) := by
  refine ⟨freezingExponent.{u, 0} (∑ j, bound j), freezingExponent_ge_two.{u, 0} _, ?_⟩
  intro p W S b i
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E, _, _, hE⟩ := freezingExponent_control W.model W.multi S b W.orbit (W.vertical.observable i)
    W.vertical.lipBound 1 (W.vertical.lipschitz i) (W.vertical.norm i) W.complexity
    W.vertical.lip_bound (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  refine ⟨multidegreeWeight (retainedCoordinateWeight S) bound,
    finrank ℚ (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)),
    retainedCoordinate_degree S bound, ?_, E, hE⟩
  simpa only [Fintype.card_fin] using
    lie_subalgebra_finrank_le W.model.basis
      (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S))

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerSelfEquivalence
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_integer_self_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C) W.eval W.eval := by
  obtain ⟨a, _, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  let i : σ := Classical.arbitrary σ
  let A : Option σ → ((σ → ℤ) →+ ℤ) := fun j => match j with
    | none => 0
    | some k => ⟨⟨fun x => x k, rfl⟩, fun _ _ => rfl⟩
  let E := (hadd W i).linearPullbackHom A
  have hleft (k : Fin W.outputDim) (x : σ → ℤ) :
      coordinateSumVector W.eval i k (fun j => A j x) = W.eval k x := by
    simp [coordinateSumVector, coordinateAdditionInputs, A]
  have hunit (x : σ → ℤ) :
      ∑ k, ‖coordinateTensorVector W.eval i k (fun j => A j x)‖ ^ 2 = 1 :=
    coordinateTensorVector_unit W.eval W.unit_eval i _
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have F := htrans hq E E.symm hunit
  have hcost : ((p + a) ^ a + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  simpa only [hleft] using F.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_translation_expansion_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateTranslatedInput l x))
        (coordinateTranslationExpansion W.eval l) := by
  induction l with
  | nil =>
    obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
    refine ⟨C, hC, ?_⟩
    intro p W _
    have E := (hself W).coordinatePullback (some : σ → Option σ)
    have hinput (x : Option σ → ℤ) :
        coordinateTranslatedInput [] x = fun j => x (some j) := by
      funext j
      simp [coordinateTranslatedInput]
    simp only [hinput, coordinateTranslationExpansion]
    convert E using 1 <;> rfl
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨b, _, hstep⟩ := exists_coordinate_translation_equivalence (σ := σ)
    obtain ⟨c, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
    obtain ⟨d, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
    let X : Polynomial ℕ := Polynomial.X
    let A := (X + Polynomial.C a) ^ a
    let B := (X + Polynomial.C b) ^ b
    let T := (A + Polynomial.C c) ^ c
    let Q := B + T + 2
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C d) ^ d)
    refine ⟨C, hC, ?_⟩
    intro p W hl
    have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
    let q := (p + a) ^ a
    let r := (q + c) ^ c
    let t := (p + b) ^ b + r + 2
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hb : 0 ≤ (p + b) ^ b := by positivity
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hbt : (p + b) ^ b ≤ t := by dsimp [t]; linarith only [hr]
    have hrt : r ≤ t := by dsimp [t]; linarith only [hb]
    have E := hprevious W hl.tail
    have F := htensor hq E (E.coordinatePullback (coordinateReplaceIndex i))
    have F' : NativeIntegerVectorEquivalence (Fintype.card σ - 1) r
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x)))
        (coordinateTranslationExpansion W.eval (i :: l)) := F
    have hunit (x : Option σ → ℤ) :
        ∑ k : Fin W.outputDim × Fin W.outputDim,
          ‖W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x))‖ ^ 2 = 1 := by
      simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]
    have R := htrans ht ((hstep W l i (List.nodup_cons.mp hl).1).mono hbt) (F'.mono hrt) hunit
    have hcost : (t + d) ^ d ≤ (p + C) ^ C := by
      simpa [X, A, B, T, Q, q, r, t, Polynomial.eval₂_pow] using hbudget p hp
    exact R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem exists_mixed_translation_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
        (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s x)) := by
  let := replicatedMixed_nonempty s
  obtain ⟨C, hC, hexpand⟩ := exists_translation_expansion_equivalence (mixedTranslationCoordinates s)
  refine ⟨C, hC, ?_⟩
  intro p V
  have E := (hexpand V (mixedTranslationCoordinates_nodup s)).linearPullbackHom
    (mixedTranslationSampleHom s)
  change NativeIntegerVectorEquivalence _ _
    (fun k x => V.eval k (coordinateTranslatedInput (mixedTranslationCoordinates s)
      (mixedTranslationSample s x)))
    (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
      (mixedTranslationSample s x)) at E
  simpa only [replicatedMixed_card, Nat.add_sub_cancel, mixedTranslationSample_translated] using E

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeFrozenAffineExpansion
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_frozen_affine_expansion {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (A b : σ → ℤ) (k : Fin W.outputDim),
      (∀ i, i ∉ S → A i = 0) →
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (∑ i ∈ S, bound i) ((p + C) ^ C)
          (fun x => W.eval k (fun i => b i + A i * x ())), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest bound
  refine ⟨C, hC, ?_⟩
  intro p W S A b k hA
  classical
  obtain ⟨t, n, ht, _, D, hD⟩ := hfreeze W S b k
  subst t
  let K := W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _, hT, _, heval⟩ := hD
  let U := T.affinePullback (fun i (_ : Unit) => A i.val) (fun i => b i.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = W.eval k (fun i => b i + A i * x ()) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · simp [freezeCoordinates, hi, integerAffineMap]
    · simp [freezeCoordinates, hi, hA i hi]
  exact ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_frozen_translation_expansion {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (A b : Option σ → ℤ) (a : BinaryTensorIndex (Fin W.outputDim) l.length),
      A none = 0 → (∀ i, i ∉ S → A (some i) = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (∑ i ∈ S, bound i) ((p + C) ^ C)
        (fun x => coordinateTranslationExpansion W.eval l a (fun j => b j + A j * x ()))) := by
  induction l with
  | nil =>
    obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion bound
    refine ⟨C, hC, ?_⟩
    intro p W S A b a _ hA
    obtain ⟨E, _⟩ := hfreeze W S (fun i => A (some i)) (fun i => b (some i)) a hA
    exact ⟨E⟩
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨c, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
      (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
    refine ⟨C, hC, ?_⟩
    intro p W S A b k hnone hA
    have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
    let q := (p + a) ^ a
    have hq : 0 ≤ q := by dsimp [q]; positivity
    let A' (j : Option σ) := A (coordinateReplaceIndex i j)
    let b' (j : Option σ) := b (coordinateReplaceIndex i j)
    have hnone' : A' none = 0 := by simp [A', coordinateReplaceIndex, hnone]
    have hA' (j : σ) (hj : j ∉ S) : A' (some j) = 0 := by
      by_cases hji : j = i
      · simp [A', coordinateReplaceIndex, hji, hnone]
      · simp [A', coordinateReplaceIndex, hji, hA j hj]
    obtain ⟨E⟩ := hprevious W S A b k.1 hnone hA
    obtain ⟨F⟩ := hprevious W S A' b' k.2 hnone' hA'
    obtain ⟨R⟩ := hmul hq E F
    have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
      simpa [q, X, Polynomial.eval₂_pow] using hbudget p hp
    exact ⟨R.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_replaced_mixed_translation_expansion (s : ℕ)
    (l : List (ReplicatedIndex (mixedCorrelationDegree s))) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (i : ReplicatedIndex (mixedCorrelationDegree s)), i.1 = 1 →
      ∀ (h δ : ℤ) (a : BinaryTensorIndex (Fin V.outputDim) l.length),
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => coordinateTranslationExpansion V.eval l a
            (coordinateReplaceInput i (mixedTranslationSample s ![h, x (), δ])))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_translation_expansion
    (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) l
  refine ⟨C, hC, ?_⟩
  intro p V i hi h δ a
  let S := (mixedEvaluationCoordinates s).erase i
  let A (j) := mixedTranslationSlope s (coordinateReplaceIndex i j)
  let b (j) := mixedTranslationIntercept s h δ (coordinateReplaceIndex i j)
  have hA : ∀ j, j ∉ S → A (some j) = 0 :=
    fun j hj => mixedTranslationSlope_replaced_vanishes s i j hj
  have hdegree : (∑ _j ∈ S, (1 : ℕ)) = s - 1 := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      mixedEvaluationCoordinates_erase_card s i hi
  have hinput (x : Unit → ℤ) : (fun j => b j + A j * x ()) =
      coordinateReplaceInput i (mixedTranslationSample s ![h, x (), δ]) := by
    change coordinateReplaceInput i
      (fun j => mixedTranslationIntercept s h δ j + mixedTranslationSlope s j * x ()) = _
    rw [mixedTranslationSample_affine]
  have R := hfreeze V S A b a (mixedTranslationSlope_replaced_none s i) hA
  simpa only [hdegree, hinput] using R

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_remainder_expansion_of_evaluation_coordinates (s : ℕ)
    (l : List (ReplicatedIndex (mixedCorrelationDegree s))) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      (∀ i ∈ l, i.1 = 1) → ∀ (h δ : ℤ) (a : BinaryTensorIndex (Fin V.outputDim) l.length),
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => translationExpansionRemainder V.eval l a (mixedTranslationSample s ![h, x (), δ]))) := by
  induction l with
  | nil =>
    refine ⟨2, le_rfl, ?_⟩
    intro p V _ h δ a
    have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
    have hbudget : 2 ≤ (p + (2 : ℕ)) ^ (2 : ℕ) := by
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hp, sq_nonneg p]
    exact ⟨NativeIntegerExpansion.constOne (fun _ : Unit => 1) (s - 1) hbudget⟩
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨b, _, hright⟩ := exists_replaced_mixed_translation_expansion s l
    obtain ⟨c, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    let Q := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b + 2
    obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
    refine ⟨C, hC, ?_⟩
    intro p V hl h δ k
    have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
    let q := (p + a) ^ a + (p + b) ^ b + 2
    have ha : 0 ≤ (p + a) ^ a := by positivity
    have hb : 0 ≤ (p + b) ^ b := by positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith only [hb]
    have hbq : (p + b) ^ b ≤ q := by dsimp [q]; linarith only [ha]
    obtain ⟨E⟩ := hprevious V (fun j hj => hl j (List.mem_cons_of_mem i hj)) h δ k.1
    obtain ⟨F⟩ := hright V i (hl i (List.mem_cons_self)) h δ k.2
    obtain ⟨R⟩ := hmul hq (E.mono haq) (F.mono hbq)
    have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
      simpa [q, Q, X, Polynomial.eval₂_pow] using hbound p hp
    exact ⟨R.mono hcost⟩

theorem exists_mixed_remainder_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (h δ : ℤ)
      (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
        (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s ![h, x (), δ]))) := by
  obtain ⟨C, hC, hrem⟩ := exists_remainder_expansion_of_evaluation_coordinates s (mixedTranslationCoordinates s)
  exact ⟨C, hC, fun V h δ a => hrem V
    (fun i hi => (mem_mixedTranslationCoordinates s i).mp hi) h δ a⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MixedQuadrupleBudget
namespace OAI

section

namespace Erdos3

theorem exists_native_mixed_reduction_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      Nonempty (NativeMixedReductionData V ((p + C) ^ C)) := by
  obtain ⟨a, _, htranslation⟩ := NativeMultidegreeNilcharacter.exists_mixed_translation_equivalence s
  obtain ⟨b, _, hlower⟩ := NativeMultidegreeNilcharacter.exists_mixed_remainder_expansion s
  obtain ⟨c, _, hquad⟩ := NativeMultidegreeNilcharacter.exists_mixed_parallelogram_expansion s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b + (X + Polynomial.C c) ^ c + 2)
  refine ⟨C, hC, ?_⟩
  intro p V
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ (p + b) ^ b := by positivity
  have hc : 0 ≤ (p + c) ^ c := by positivity
  have hs : (p + a) ^ a + (p + b) ^ b + (p + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨{
    budget_two := by linarith only [ha, hb, hc, hs]
    translation := (htranslation V).mono (by linarith only [hb, hc, hs])
    lower := fun h δ j => (Classical.choice (hlower V h δ j)).mono (by linarith only [ha, hc, hs])
    parallelogram := fun k => (Classical.choice (hquad V k)).mono (by linarith only [ha, hb, hs]) }⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_mixed_quadruple_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      ∃ P : ℝ, Nonempty (NativeMixedReductionData V P) ∧
        7 * P ≤ (p + C) ^ C ∧ mixedErrorPairBudget P ≤ (p + C) ^ C ∧
        mixedErrorBudget P ≤ (p + C) ^ C := by
  obtain ⟨a, _, hdata⟩ := exists_native_mixed_reduction_data s
  obtain ⟨b, _, herror⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (7 * Y + (Y + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p V
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hE : 0 ≤ (P + b) ^ b := by positivity
  have hb : 7 * P + (P + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, P, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨P, hdata V, ?_, ?_, ?_⟩
  · linarith only [hb, hE]
  · exact (herror P hP).1.trans (by linarith only [hb, hP])
  · exact (herror P hP).2.trans (by linarith only [hb, hP])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFixedReduction
namespace OAI

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem reductionCode_card (k : Fin 4 → Fin V.outputDim) :
    (Fintype.card (D.ReductionCode k) : ℝ) ≤ Real.exp (5 * P) := by
  classical
  calc
    (Fintype.card (D.ReductionCode k) : ℝ) =
        ∑ t : D.TranslationCode k, ((D.parallelogram (D.translationCoordinates k t)).count : ℝ) := by
      rw [Fintype.card_congr (D.reductionCodeEquiv k)]
      simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    _ ≤ ∑ _ : D.TranslationCode k, Real.exp P := by
      exact Finset.sum_le_sum (fun t _ => (D.parallelogram (D.translationCoordinates k t)).count_bound)
    _ = (Fintype.card (D.TranslationCode k) : ℝ) * Real.exp P := by simp
    _ ≤ Real.exp (4 * P) * Real.exp P :=
      mul_le_mul_of_nonneg_right (D.translationCode_card k) (Real.exp_nonneg P)
    _ = Real.exp (5 * P) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Erdos3.NativeMixedReductionData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

theorem extension_quadruple_integer (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (a h k : ZMod N)
    (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H) :
    additiveQuadrupleCorrelation U.extension a h k =
      ‖𝔼 x : ZMod N,
        fourPointProduct (fun x : ZMod N => U.integerProduct M ⟨h, h₁⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨h - a, h₂⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨k, h₃⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨k - a, h₄⟩ x.val) a x‖ := by
  simp only [additiveQuadrupleCorrelation, fourPointProduct, U.integerProduct_val M hM,
    U.extension_of_mem h h₁, U.extension_of_mem (h - a) h₂,
    U.extension_of_mem k h₃, U.extension_of_mem (k - a) h₄]

theorem exists_integer_quadruple_interval (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (a h k : ZMod N) (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H)
    {ρ : ℝ} (hρ : 0 < ρ) (hcorr : ρ ≤ additiveQuadrupleCorrelation U.extension a h k) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨h, h₁⟩) (U.integerProduct M ⟨h - a, h₂⟩)
          (U.integerProduct M ⟨k, h₃⟩) (U.integerProduct M ⟨k - a, h₄⟩)
          (cyclicBranchOffset a branch) n‖ ∧
      ρ / (20 * Real.exp (4 * p)) ≤ (len : ℝ) / N := by
  apply exists_fourPoint_integer_interval _ _ _ _ a hρ (Real.exp_pos _)
  · intro x
    simp only [fourPointProduct, U.integerProduct_val M hM, norm_mul, norm_star]
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul (mul_le_mul (U.product_norm hm _ _) (U.product_norm hm _ _)
          (norm_nonneg _) (Real.exp_nonneg _)) (U.product_norm hm _ _)
          (norm_nonneg _) (by positivity)) (U.product_norm hm _ _) (norm_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · rwa [← U.extension_quadruple_integer M hM a h k h₁ h₂ h₃ h₄]

theorem exists_integer_quadruple_interval_budget (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (a h k : ZMod N) (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H)
    {b : ℝ} (hcorr : Real.exp (-b) ≤ additiveQuadrupleCorrelation U.extension a h k) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-(b + 4 * p + 5)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨h, h₁⟩) (U.integerProduct M ⟨h - a, h₂⟩)
          (U.integerProduct M ⟨k, h₃⟩) (U.integerProduct M ⟨k - a, h₄⟩)
          (cyclicBranchOffset a branch) n‖ ∧
      Real.exp (-(b + 4 * p + 5)) ≤ (len : ℝ) / N := by
  have hp : 0 ≤ p := (Nat.cast_nonneg (U ⟨h, h₁⟩).dim).trans (U ⟨h, h₁⟩).complexity.1.1
  have h20 : (20 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (20 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  have hfrac : Real.exp (-(b + 4 * p + 5)) ≤ Real.exp (-b) / (20 * Real.exp (4 * p)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * Real.exp (4 * p))).mpr
    calc
      _ ≤ Real.exp (-(b + 4 * p + 5)) * (Real.exp 5 * Real.exp (4 * p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h20 (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (4 * p) := Real.one_le_exp_iff.mpr (by positivity)
  have hfrac' : Real.exp (-(b + 4 * p + 5)) ≤ Real.exp (-b) / 20 :=
    hfrac.trans (div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
      (by nlinarith only [hone]))
  obtain ⟨branch, c, len, hlen, hN, hshort, hc, hvol⟩ := U.exists_integer_quadruple_interval
    M hM hm a h k h₁ h₂ h₃ h₄ (Real.exp_pos (-b)) hcorr
  exact ⟨branch, c, len, hlen, hN, hshort, hfrac'.trans hc, hfrac.trans hvol⟩

end Erdos3.NativeCrossWitnesses

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem product_factorization (t : B.quadruples) (n : ℤ) :
    fourPointProduct
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1, (B.interval t).first_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2, (B.interval t).third_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n =
    B.residual t n * translatedMixedProduct B.mixed (fun _ => B.coordinate)
      t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
      (B.delta t) n := by
  have h := B.lower.integerProduct_fourPoint_factorization
    (fun h n => B.mixed.eval B.coordinate (fun j => correlationInput (h.val : ℤ) n j.1))
    (W.family.eval B.rankCoordinate)
    ⟨t.val.2.1, (B.interval t).first_mem⟩
    ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩
    ⟨t.val.2.2, (B.interval t).third_mem⟩
    ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩ (B.delta t) n
  calc
    _ = translatedMixedProduct B.mixed (fun _ => B.coordinate)
        t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
        (B.delta t) n * B.rankProduct t n * B.lowerProduct t n := h
    _ = _ := by rw [residual]; ring

theorem mixed_correlation (t : B.quadruples) :
    Real.exp (-q) ≤ ‖𝔼 n ∈ B.intervalSet t,
      B.residual t n * translatedMixedProduct B.mixed (fun _ => B.coordinate)
        t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
        (B.delta t) n‖ := by
  have hc := (B.interval t).correlation
  change Real.exp (-q) ≤ ‖𝔼 n ∈ B.intervalSet t,
    fourPointProduct
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1, (B.interval t).first_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2, (B.interval t).third_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n‖ at hc
  simpa only [B.product_factorization] using hc

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem intervalSet_nonempty (t : B.quadruples) : (B.intervalSet t).Nonempty := by
  refine ⟨((B.interval t).start : ℤ), Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
  exact lt_add_of_pos_right _ (Nat.cast_pos.mpr (B.interval t).length_pos)

end Erdos3.NativeMultilinearIntervalFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

namespace NativeWeightedRankIntervals

theorem remove_weight {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) :
    Nonempty (NativeRankRelation W out H (11 * p + 7) (mixedErrorPairBudget p)) := by
  classical
  obtain ⟨A⟩ := F.exists_anchored_fibers
  have hdata (a : A.parameters) := A.exists_interval_pairs a.val a.property
  choose P _ hPsize hP using hdata
  have hpair (a : A.parameters) :
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) *
        (Fintype.card (ZMod N) : ℝ) ^ 2 ≤ ((P a).card : ℝ) := by
    have hf := A.fiber_density a.val a.property
    calc
      _ = Real.exp (-(8 * p + 1)) *
          (Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ)) ^ 2 := by ring
      _ ≤ Real.exp (-(8 * p + 1)) * ((A.fiber a.val).card : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact pow_le_pow_left₀ (by positivity) hf 2
      _ ≤ _ := hPsize a
  obtain ⟨Q, hQsize, hQmem⟩ := dense_triple_fibers A.parameters P
    (by positivity) A.parameters_density hpair
  have hdense : Real.exp (-(11 * p + 7)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (rank_pair_density_loss p) (by positivity)).trans hQsize
  have hN : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
  have hQpos : (0 : ℝ) < Q.card := lt_of_lt_of_le (by positivity) hdense
  have hbudget : 8 * p + 1 ≤ 11 * p + 7 := by linarith only [F.budget_two]
  have hinterval (t : Q) : Nonempty
      (NativeRankInterval W out H t.val A.branch (11 * p + 7) (mixedErrorPairBudget p)) := by
    obtain ⟨a, ha, ht⟩ := (hQmem t.val).mp t.property
    obtain ⟨I⟩ := hP a t.val.2 ht
    have heq : (a.val, t.val.2) = t.val := Prod.ext ha rfl
    rw [heq] at I
    exact ⟨I.mono hbudget le_rfl⟩
  exact ⟨{
    quadruples := Q
    quadruples_nonempty := Finset.card_pos.mp (by exact_mod_cast hQpos)
    density := hdense
    branch := A.branch
    interval := fun t => Classical.choice (hinterval t) }⟩

end NativeWeightedRankIntervals

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRealFastCoefficientAction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_real_fast_coefficient_unitriangular_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
          (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ = D.map (Rat.castHom ℝ) ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        (∀ y : Fin d → ℝ, b.equivFun.symm y =
          (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
            ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
              (S.map (Rat.castHom ℝ) *ᵥ y))) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
  have h := F.exists_real_fast_coefficient_quotient_basis e ω hF w hw U.toSubmodule hU
    v hspan hH hv hp hn hm hq hd hdm hHp
  rw [← F.realFirstCoefficientFastSubmodule_relative w hw U] at h
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, hrep⟩ := h
  refine ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, hrep, ?_⟩
  intro g hg a c hac
  exact F.realFastCoefficientAdjoint_unitriangular e ω hF w hw U rows b D S hD hDS
    hDb hSb g hg a c hac

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FastCoefficientDerivativeCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_controlled_real_fast_coefficient_coordinates
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 2958) ∧ l ∣ m ∧
        (∀ x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid m) ∧
        (∀ y : Fin d → ℝ, y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w m (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + 2) ^ 2958) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + 2) ^ 2958) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
  have hb := F.exists_real_fast_coefficient_unitriangular_basis e ω hF w hw U hU
    v hspan hH hv hp hn hm hq hd hdm hHp
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, _, haction⟩ := hb
  have hDh' : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
      ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954) := by
    have hpow : Real.exp ((p + 2) ^ 420) ≤ Real.exp ((p + 2) ^ 2954) :=
      Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by decide))
    exact fun i j => ⟨(hDh i j).1.trans hpow, (hDh i j).2.trans hpow⟩
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr hdim).trans hd
  have hc := controlled_weighted_quotient_coordinates (F.realFirstCoefficientBasis e ω hF w) b
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (fun i => i.val.1) (fun i => (rows i).val.1) D S hD hDS hDb hSb hp hd hd'
    2954 (by decide) hDh' hSh l hl hlp
  obtain ⟨m, hmpos, hmbound, hlm, hgrid, hRgrid, hR, hweighted⟩ := hc
  refine ⟨d, hdim, rows, hinj, b, rationalCoordinateSection (F.realFirstCoefficientBasis e ω hF w) S,
    m, hmpos, hmbound, hlm, hgrid, hRgrid, hR, ?_, ?_, haction⟩
  · intro T hT M hM
    exact hweighted (monomialScale T) (monomialScale_pos T hT) M hM
  · intro i j hij
    have h := congrArg (fun A => A j i) hD
    simpa only [LinearMap.toMatrix_apply, Matrix.map_apply, hDb j i hij, map_zero] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_fast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ FastCoefficientCoordinateSpec s C := by
  let Q : Polynomial ℕ :=
    3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) * (Polynomial.X + 1) +
    2 * Polynomial.X + 2 +
    (Polynomial.X + Polynomial.C (s + 3)) ^ (s + 3) * (Polynomial.X + 1) + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + 2) ^ 2958
  have hexists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hexists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U hU v hspan H hH hv p hp hι hσ hκ hHp l hl hlp
  classical
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  let q := fastCoefficientMatrixParameter s p
  have hq : 0 ≤ q := fastCoefficientMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_fastCoefficientMatrixParameter s hp
  have hdims := F.fastCoefficient_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hfinal : (q + 2) ^ 2958 ≤ (p + C) ^ C := by
    simpa [B, Q, q, fastCoefficientMatrixParameter, reducedMatrixParameter, Polynomial.eval₂_pow]
      using hbound p hp
  have hraw := F.exists_controlled_real_fast_coefficient_coordinates e ω hF w hw U hU
    v hspan hH hv hq hdims.1 (hκ.trans hpq) hdims.2.1 hdims.2.2.1 hdims.2.2.2
    (hHp.trans (Real.exp_le_exp.mpr hpq)) l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, hlm, hgrid, hRgrid, hR, hweighted, hblock, haction⟩ := hraw
  have hdim' : d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) := by
    exact hdim.trans (firstCoefficientIndex_card_le w ω (s + 1) hw
      (F.adaptedBasis_weight_le_step e ω hF))
  have hbudget : Real.exp ((q + 2) ^ 2958) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hfinal
  refine ⟨d, hdim', rows, hinj, b, R, m, hm, hmp.trans hbudget, hlm,
    hgrid, hRgrid, hR, ?_, hblock, haction⟩
  intro T hT M hM
  obtain ⟨hproj, hlift⟩ := hweighted T hT M hM
  constructor
  · intro x hx i
    exact (hproj x hx i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget hM) (monomialScale_pos T hT _).le)
  · intro y hy i
    exact (hlift y hy i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget hM) (monomialScale_pos T hT _).le)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastRelativeSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun a : QuotientTopBasisIndex s ω => ω (Subtype.val a))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

variable [Fintype ι] [Fintype κ]

theorem exists_bounded_fast_graded_relative_kernel_generators
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopBasisIndex s ω) ∧
      ∃ z : κ → F.squareFiltration.quotientTop.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fastGradedRelativeKernel W ∧
        ∀ j i, RationalHeightLE ((bW).repr (z j) i)
          (fastKernelGeneratorHeight (Fintype.card (ReducedSquareBasisIndex s ω))
            (Fintype.card κ) r H) := by
  have hPv (j : κ) (i : QuotientTopBasisIndex s ω) :
      RationalHeightLE ((bQ).repr (F.reducedSquareGradedSndMap (v j)) i)
        ((Fintype.card (ReducedSquareBasisIndex s ω) + 1) *
          H ^ Fintype.card (ReducedSquareBasisIndex s ω)) := by
    simpa only [mul_one, LieHom.coe_toLinearMap] using linearMap_coordinate_height
      bW bQ F.reducedSquareGradedSndMap.toLinearMap
      (F.reducedSquareGradedSndMap_basis_height e ω hF) (v j) (hv j) i
  have hB : 1 ≤ (Fintype.card (ReducedSquareBasisIndex s ω) + 1) *
      H ^ Fintype.card (ReducedSquareBasisIndex s ω) := by
    have hHp : 0 < H := hH
    exact Nat.succ_le_of_lt (by positivity)
  have he := exists_bounded_span_kernel_generators bW bQ
    F.reducedSquareGradedSndMap.toLinearMap v hB hv hPv
  simpa only [hspan, fastKernelGeneratorHeight, fastGradedRelativeKernel,
    LieHom.ker_toSubmodule] using he

theorem exists_bounded_full_fast_relative_generators
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopBasisIndex s ω) ∧
      ∃ z : κ → F.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fullFastGradedRelative e ω hF W ∧
        ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr (z j) i)
          (fastCoefficientGeneratorHeight (Fintype.card (ReducedSquareBasisIndex s ω))
            (Fintype.card κ) r H) := by
  obtain ⟨r, hr, z, hz, hzh⟩ :=
    F.exists_bounded_fast_graded_relative_kernel_generators e ω hF W v hspan hH hv
  refine ⟨r, hr, (F.reducedSquareGradedDifference e ω hF) ∘ z, ?_, fun j i => ?_⟩
  · rw [fullFastGradedRelative, ← hz, Submodule.map_span, ← Set.range_comp]
  · simpa only [Function.comp_apply, mul_one, fastCoefficientGeneratorHeight] using
      linearMap_coordinate_height bW (F.associatedGradedBasis e ω hF)
        (F.reducedSquareGradedDifference e ω hF)
        (F.reducedSquareGradedDifference_basis_height e ω hF) (z j) (hzh j) i

theorem exists_full_fast_relative_generators_exp
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 40) ∧
      ∃ z : κ → F.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fullFastGradedRelative e ω hF W ∧
        ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr (z j) i) H' := by
  obtain ⟨r, hr, z, hz, hzh⟩ :=
    F.exists_bounded_full_fast_relative_generators e ω hF W v hspan hH hv
  exact ⟨_, fastCoefficientGeneratorHeight_pos _ _ _ _ hH,
    fastCoefficientGeneratorHeight_le_exp _ _ _ _ hp hn hm
      ((Nat.cast_le.mpr hr).trans hq) hHp, z, hz, hzh⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem exists_full_fast_quotient_bases
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hdim : 2 * (Fintype.card ι : ℝ) + (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, H ≤ H' ∧ 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 294) ∧
      ∃ dU : ℕ, dU ≤ Fintype.card ι ∧
      ∃ fU : Basis (Fin dU) ℚ (F.AssociatedGraded ⧸ (F.fullFastGradedDiagonal W).toSubmodule),
      ∃ dV : ℕ, dV ≤ Fintype.card ι ∧
      ∃ fV : Basis (Fin dV) ℚ (F.AssociatedGraded ⧸ F.fullFastGradedRelative e ω hF W),
        (∀ i j, RationalHeightLE (fU.repr ((F.fullFastGradedDiagonal W).toSubmodule.mkQ
          (F.associatedGradedBasis e ω hF j)) i) H') ∧
        (∀ i j, RationalHeightLE (fV.repr ((F.fullFastGradedRelative e ω hF W).mkQ
          (F.associatedGradedBasis e ω hF j)) i) H') := by
  have hn0 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hm : (Fintype.card κ : ℝ) ≤ p := by linarith
  have hUcard : (Fintype.card (κ ⊕ TopGradedBasisIndex s ω) : ℝ) ≤ p := by
    have h := Nat.cast_le (α := ℝ).mpr (fullFastDiagonalGenerators_card (κ := κ) (s := s) ω)
    push_cast at h
    linarith
  obtain ⟨HU, hHU, hHUp, dU, hdU, fU, hfU⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis e ω hF) (F.fullFastGradedDiagonal W).toSubmodule
    (F.fullFastDiagonalGenerators e ω hF v) (F.fullFastDiagonalGenerators_span e ω hF W v hspan)
    hH (F.fullFastDiagonalGenerators_height e ω hF v hH hv) hp hUcard hHp
  have hn : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p := by
    have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have h := Nat.cast_le (α := ℝ).mpr hcard
    push_cast at h
    linarith
  have hq : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p := by
    have h := Nat.cast_le (α := ℝ).mpr
      (Fintype.card_subtype_le (fun i : ι => ¬ s + 1 ≤ ω i))
    linarith
  obtain ⟨Hz, hHz, hHzp, z, hz, hzh⟩ :=
    F.exists_full_fast_relative_generators_exp e ω hF W v hspan hH hv hp hn hm hq hHp
  obtain ⟨HV, hHV, hHVp, dV, hdV, fV, hfV⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis e ω hF) (F.fullFastGradedRelative e ω hF W) z hz hHz hzh
    (by positivity : 0 ≤ (p + 2) ^ 40)
    (hm.trans (le_power_budget hp (by decide : 1 ≤ 40))) hHzp
  have hVbudget : (HV : ℝ) ≤ Real.exp ((p + 2) ^ 294) :=
    exponential_budget_comp hp (by positivity) 40 7 le_rfl hHVp
  have hUbudget : (HU : ℝ) ≤ Real.exp ((p + 2) ^ 294) := hHUp.trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 7 ≤ 294)))
  have hbudget : (H : ℝ) ≤ Real.exp ((p + 2) ^ 294) :=
    hHp.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 294)))
  refine ⟨max H (max HU HV), Nat.le_max_left _ _, hH.trans (Nat.le_max_left _ _), ?_,
    dU, hdU, fU, dV, hdV, fV, ?_, ?_⟩
  · rw [Nat.cast_max, Nat.cast_max]
    exact max_le hbudget (max_le hUbudget hVbudget)
  · intro i j
    exact (hfU i j).mono ((Nat.le_max_left HU HV).trans (Nat.le_max_right _ _))
  · intro i j
    exact (hfV i j).mono ((Nat.le_max_right HU HV).trans (Nat.le_max_right _ _))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFastCoefficientSpec
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_uniform_fast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ UniformFastCoefficientCoordinateSpec s C := by
  obtain ⟨C, hC, hspec⟩ := exists_fast_coefficient_coordinate_bound s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U hU v hspan H hH hv p hp hι hσ hκ hHp
  have hOne : ((1 : ℕ) : ℝ) ≤ Real.exp p := by simpa only [Nat.cast_one] using Real.one_le_exp hp
  have hraw := hspec F e ω hF w hw U hU v hspan hH hv hp hι hσ hκ hHp 1 (by decide) hOne
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, _, hproj, hlift, hright, hweighted, hblock, haction⟩ := hraw
  classical
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  refine ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, ?_, ?_, hright, hweighted, hblock, haction⟩
  · intro l x hx
    exact linearMap_grid_of_integer (F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap
      (b.equivFun.toLinearMap.comp (F.realFirstCoefficientFastSubmodule w hw
        (F.reducedSquareFastRelativeSubmodule w U)).mkQ) m hproj l x hx
  · intro l y hy
    exact linearMap_grid_of_integer (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      ((F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap.comp R) m hlift l y hy

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_fullFast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ FullFastCoefficientCoordinateSpec s C := by
  have hex := exists_uniform_fast_coefficient_coordinate_bound s
  obtain ⟨c, _, hcoords⟩ := hex
  let Q : Polynomial ℕ := 3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) *
    (Polynomial.X + 1) + 2 * Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw W hW v hspan H hH hv p hp hι hσ hκ hHp U J
  classical
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let bW := F.reducedSquareBasis e ω hF
  let ωW := fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val
  let v' := F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily bW ωW
    (F.reducedSquareBasis_layers e ω hF) w v
  have hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w)
      (fun i => i.val.1) U.toSubmodule :=
    F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_blockInvariant bW ωW
      (F.reducedSquareBasis_layers e ω hF) w W
  have hspan' : Submodule.span ℚ (Set.range v') = U.toSubmodule :=
    F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_span bW ωW
      (F.reducedSquareBasis_layers e ω hF) w W hW v hspan
  have hv' : ∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v' j) i) H :=
    F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_height bW ωW
      (F.reducedSquareBasis_layers e ω hF) w v hH hv
  let q := reducedMatrixParameter s p
  have hq : 0 ≤ q := reducedMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_reducedMatrixParameter s hp
  have hdims := F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hcount : (Fintype.card (ReducedSquareSymbolIndex s w ω × κ) : ℝ) ≤ q := by
    simpa only [Fintype.card_prod] using hdims.2.2
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, q, reducedMatrixParameter, Polynomial.eval₂_pow] using hbudget p hp
  have hraw := hcoords F e ω hF w hw U hU v' hspan' hH hv' hq
    (hι.trans hpq) (hσ.trans hpq) hcount (hHp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, hproj, hlift, hright, hweighted, hblock, haction⟩ := hraw
  have hexp : Real.exp ((q + c) ^ c) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hfinal
  refine ⟨d, hdim, rows, hinj, b, R, m, hm, hmp.trans hexp, hproj, hlift, hright, ?_, hblock, haction⟩
  intro T hT M hM
  obtain ⟨hproj', hlift'⟩ := hweighted T hT M hM
  constructor
  · intro x hx i
    exact (hproj' x hx i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp hM) (monomialScale_pos T hT _).le)
  · intro y hy i
    exact (hlift' y hy i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp hM) (monomialScale_pos T hT _).le)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

def coefficientIsDependent : D.CoefficientAlphabet → Bool := Sum.elim (fun _ => false) (fun _ => true)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end


