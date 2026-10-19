-- Prove2me | Definitions.Def_OAIE3v2B240
-- name    : OAIE3v2B240
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:46:13.15798+00:00
-- url     : https://prove2.me/theorems/71cb2dfa-3789-434b-9005-3b6530ab7bb3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 245 of 311
-- statement:
--   Definitions bundle 245 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B219`, `OAIE3v2B221`, `OAIE3v2B223`, `OAIE3v2B224`, `OAIE3v2B225` of this split.
--
--   Modules: `Estimates/CommonDependentWordLayers.lean`, `Estimates/CommonFreeSunflower.lean`, `Estimates/CommonInducedCorrelation.lean`, `Estimates/CommonMarkedMultidegree.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/DiagonalWrapComparison.lean`, `Estimates/MarkedUnitOrbit.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/MixedRootCyclicComparison.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeMultidegreeDilation.lean`, `Estimates/NativeRetainedInverseIntervals.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Geometry/MixedCoordinateTransfer.lean`, `Geometry/NativeFiniteSumCoordinate.lean`, `Geometry/NativeMixedCoordinateSlices.lean`, `Lattices/LocalMarkedLatticeCorrection.lean`, `Lattices/NormalizedMarkedLattice.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/NativeRankFamilyConstruction.lean`, `Polynomial/BoundedRootDegreeEquivalence.lean`, `Polynomial/CommonDependentPolynomialIntersections.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B219
import Definitions.Def_OAIE3v2B221
import Definitions.Def_OAIE3v2B223
import Definitions.Def_OAIE3v2B224
import Definitions.Def_OAIE3v2B225

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeFiniteSumCoordinate
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_finite_sum_coordinate_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ), NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k (x : (σ ⊕ Fin (n + 1)) → ℤ) => W.eval k (finiteSumCoordinateInput i x))
        (fun a : Fin (n + 1) → Fin W.outputDim => fun x =>
          ∏ j, W.eval (a j) (finiteTermCoordinateInput i j x)) := by
  induction n with
  | zero =>
      obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
      refine ⟨C, hC, ?_⟩
      intro p W i
      have E := (hself W).linearPullbackHom (finiteTermCoordinateHom i (0 : Fin 1))
      apply E.of_coordinate_maps _ _ id (fun a => a 0) _ _ E.left_dimension _ le_rfl
      · intro k x
        rw [finiteSumCoordinateInput_one]
        rfl
      · intro a x
        rw [Fin.prod_univ_one]
        rfl
      · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.zero_add, pow_one] using E.right_dimension
  | succ n ih =>
      obtain ⟨A, _, hprevious⟩ := ih
      obtain ⟨B, _, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
      obtain ⟨D, _, hself⟩ := exists_integer_self_equivalence (σ := σ)
      obtain ⟨F, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
      obtain ⟨G, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
      let X : Polynomial ℕ := Polynomial.X
      let R := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B +
        (X + Polynomial.C D) ^ D
      let Q := (R + (R + Polynomial.C F) ^ F + Polynomial.C G) ^ G
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        (Q + Polynomial.C (n + 2) * X + X)
      refine ⟨C, hC, ?_⟩
      intro p W i
      have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
      let r := (p + A) ^ A + (p + B) ^ B + (p + D) ^ D
      let t := (r + F) ^ F
      let q := (r + t + G) ^ G
      have hA : 0 ≤ (p + A) ^ A := by positivity
      have hB : 0 ≤ (p + B) ^ B := by positivity
      have hD : 0 ≤ (p + D) ^ D := by positivity
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hAr : (p + A) ^ A ≤ r := by dsimp [r]; linarith
      have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
      have hDr : (p + D) ^ D ≤ r := by dsimp [r]; linarith
      have hsum : q + (n + 2 : ℕ) * p + p ≤ (p + C) ^ C := by
        simpa [X, R, Q, r, t, q, Polynomial.eval₂_pow] using hbudget p hp
      have hnp : 0 ≤ (n + 2 : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hqC : q ≤ (p + C) ^ C := by linarith
      have hpC : p ≤ (p + C) ^ C := by linarith
      have hnC : (n + 2 : ℕ) * p ≤ (p + C) ^ C := by linarith
      let tailMap : (σ ⊕ Fin (n + 1)) → (((σ ⊕ Fin (n + 2)) → ℤ) →+ ℤ) := fun j =>
        match j with
        | Sum.inl j =>
          { toFun := fun x => x (Sum.inl j)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        | Sum.inr a =>
          { toFun := fun x => x (Sum.inr a.succ)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
      let addMap : Option σ → (((σ ⊕ Fin (n + 2)) → ℤ) →+ ℤ) := fun j =>
        match j with
        | none =>
          { toFun := fun x => ∑ a : Fin (n + 1), x (Sum.inr a.succ)
            map_zero' := by simp
            map_add' := fun x y => by
              simp only [Pi.add_apply, Finset.sum_add_distrib] }
        | some j => finiteTermCoordinateHom i 0 j
      have hleft (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 0 = finiteSumCoordinateInput i x := by
        rw [coordinateAdditionInputs_sum]
        change Function.update (finiteTermCoordinateInput i 0 x) i
          (finiteTermCoordinateInput i 0 x i + ∑ a : Fin (n + 1), x (Sum.inr a.succ)) = _
        simp only [finiteTermCoordinateInput, finiteSumCoordinateInput,
          Function.update_self, Function.update_idem]
        congr 1
        exact (Fin.sum_univ_succ (fun a : Fin (n + 2) => x (Sum.inr a))).symm
      have hfirst (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 1 = finiteTermCoordinateInput i 0 x := rfl
      have htail (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 2 =
            finiteSumCoordinateInput i (fun j => tailMap j x) := by
        rw [coordinateAdditionInputs_right]
        change Function.update (finiteTermCoordinateInput i 0 x) i
          (∑ a : Fin (n + 1), x (Sum.inr a.succ)) = _
        simp only [finiteTermCoordinateInput, finiteSumCoordinateInput, Function.update_idem]
        rfl
      have E₀ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) r
          (fun k x => W.eval k (finiteSumCoordinateInput i x))
          (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
            W.eval a.1 (finiteTermCoordinateInput i 0 x) *
              W.eval a.2 (finiteSumCoordinateInput i (fun j => tailMap j x))) := by
        have E := ((hadd W i).linearPullbackHom addMap).mono hBr
        simpa only [coordinateSumVector, coordinateTensorVector, hleft, hfirst, htail] using E
      have Efirst := ((hself W).linearPullbackHom
        (finiteTermCoordinateHom i (0 : Fin (n + 2)))).mono hDr
      have Etail := ((hprevious W i).linearPullbackHom tailMap).mono hAr
      have E₂ := htensor hr Efirst Etail
      have hunit (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          ∑ a : Fin W.outputDim × Fin W.outputDim,
            ‖W.eval a.1 (finiteTermCoordinateInput i 0 x) *
              W.eval a.2 (finiteSumCoordinateInput i (fun j => tailMap j x))‖ ^ 2 = 1 := by
        simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum,
          W.unit_eval, mul_one]
      have H := htrans (add_nonneg hr ht) (E₀.mono (le_add_of_nonneg_right ht))
        (E₂.mono (le_add_of_nonneg_left hr)) hunit
      have hdim : (Fintype.card (Fin (n + 2) → Fin W.outputDim) : ℝ) ≤
          Real.exp ((p + C) ^ C) := by
        simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        calc
          _ ≤ Real.exp p ^ (n + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
          _ = Real.exp ((n + 2 : ℕ) * p) := (Real.exp_nat_mul p (n + 2)).symm
          _ ≤ _ := Real.exp_le_exp.mpr hnC
      apply H.of_coordinate_maps _ _ id (fun a => (a 0, fun j => a j.succ))
        (fun _ _ => rfl) _ _ hdim hqC
      · intro a x
        rw [Fin.prod_univ_succ]
        rfl
      · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

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

theorem exists_finite_assignment_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (n : ℕ) (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k (x : (Fin (n + 1) × σ) → ℤ) => W.eval k (finiteChoiceCoordinateInput l x))
        (finiteChoiceExpansion W.eval l) := by
  induction l with
  | nil =>
      obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
      refine ⟨C, hC, ?_⟩
      intro p W _
      have E := (hself W).coordinatePullback (fun j => ((0 : Fin (n + 1)), j))
      apply E.of_coordinate_maps _ _ id (fun a => a Fin.elim0)
        (fun _ _ => rfl) _ E.left_dimension _ le_rfl
      · intro a x
        change (∏ v : Fin 0 → Fin (n + 1), W.eval (a v) (fun j => x (0, j))) =
          W.eval (a Fin.elim0) (fun j => x (0, j))
        rw [Fintype.prod_unique]
        exact congrArg (fun v => W.eval (a v) (fun j => x (0, j))) (by
          funext j
          exact Fin.elim0 j)
      · simpa only [Fintype.card_fun, Fintype.card_fin, List.length_nil, pow_zero, pow_one]
          using E.right_dimension
  | cons i l ih =>
      obtain ⟨A, _, hprevious⟩ := ih
      obtain ⟨B, _, hstep⟩ := exists_finite_sum_coordinate_equivalence (σ := σ) n
      obtain ⟨D, _, hproduct⟩ := NativeIntegerVectorEquivalence.exists_fin_product_budget (n + 1)
      obtain ⟨F, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
      let X : Polynomial ℕ := Polynomial.X
      let Q := (X + Polynomial.C A) ^ A
      let T := (Q + Polynomial.C D) ^ D
      let R := (X + Polynomial.C B) ^ B + T
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        ((R + Polynomial.C F) ^ F + Polynomial.C ((n + 1) ^ (l.length + 1)) * X + X)
      refine ⟨C, hC, ?_⟩
      intro p W hl
      have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
      let q := (p + A) ^ A
      let t := (q + D) ^ D
      let r := (p + B) ^ B + t
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hB : 0 ≤ (p + B) ^ B := by positivity
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
      have htr : t ≤ r := by dsimp [r]; linarith
      have hsum : (r + F) ^ F + ((n + 1) ^ (l.length + 1) : ℕ) * p + p ≤ (p + C) ^ C := by
        simpa [X, Q, T, R, q, t, r, Polynomial.eval₂_pow] using hbudget p hp
      have hpow : 0 ≤ (r + F) ^ F := by positivity
      have hnp : 0 ≤ ((n + 1) ^ (l.length + 1) : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hFC : (r + F) ^ F ≤ (p + C) ^ C := by linarith
      have hpC : p ≤ (p + C) ^ C := by linarith
      have hnC : ((n + 1) ^ (l.length + 1) : ℕ) * p ≤ (p + C) ^ C := by linarith
      let P : (σ ⊕ Fin (n + 1)) → (((Fin (n + 1) × σ) → ℤ) →+ ℤ) := fun j =>
        match j with
        | Sum.inl j => finiteChoiceCoordinateHom l j
        | Sum.inr a =>
          { toFun := fun x => x (a, i)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
      have hleft (x : (Fin (n + 1) × σ) → ℤ) :
          finiteSumCoordinateInput i (fun j => P j x) = finiteChoiceCoordinateInput (i :: l) x := by
        change Function.update (finiteChoiceCoordinateInput l x) i
          (∑ a : Fin (n + 1), x (a, i)) = _
        exact (finiteChoiceCoordinateInput_cons l i x).symm
      have hright (a : Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) :
          finiteTermCoordinateInput i a (fun j => P j x) =
            finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i a x) := by
        change Function.update (finiteChoiceCoordinateInput l x) i (x (a, i)) = _
        exact (finiteChoiceCoordinateInput_replace l i (List.nodup_cons.mp hl).1 a x).symm
      have E₀ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + B) ^ B)
          (fun k x => W.eval k (finiteChoiceCoordinateInput (i :: l) x))
          (fun a : Fin (n + 1) → Fin W.outputDim => fun x => ∏ j,
            W.eval (a j) (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))) := by
        have E := (hstep W i).linearPullbackHom P
        simpa only [hleft, hright] using E
      have E := hprevious W hl.tail
      have E₁ := hproduct
        (fun j k x => W.eval k (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x)))
        (fun j a x => finiteChoiceExpansion W.eval l a (finiteChoiceReplaceInput i j x))
        hq E.left_dimension E.right_dimension
        (fun j => E.coordinatePullback (finiteChoiceReplaceIndex i j))
      have hunit (x : (Fin (n + 1) × σ) → ℤ) :
          ∑ a : Fin (n + 1) → Fin W.outputDim,
            ‖∏ j, W.eval (a j) (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))‖ ^ 2 = 1 := by
        simp only [norm_prod, ← Finset.prod_pow]
        calc
          _ = ∏ j : Fin (n + 1), ∑ k : Fin W.outputDim,
              ‖W.eval k (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))‖ ^ 2 :=
            (Fintype.prod_sum _).symm
          _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]
      have H := htrans hr (E₀.mono hBr) (E₁.mono htr) hunit
      have hdim : (Fintype.card ((Fin (i :: l).length → Fin (n + 1)) → Fin W.outputDim) : ℝ) ≤
          Real.exp ((p + C) ^ C) := by
        simp only [Fintype.card_fun, Fintype.card_fin, List.length_cons, Nat.cast_pow]
        calc
          _ ≤ Real.exp p ^ ((n + 1) ^ (l.length + 1)) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
          _ = Real.exp (((n + 1) ^ (l.length + 1) : ℕ) * p) :=
            (Real.exp_nat_mul p ((n + 1) ^ (l.length + 1))).symm
          _ ≤ _ := Real.exp_le_exp.mpr hnC
      apply H.of_coordinate_maps _ _ id (fun a j v => a (Fin.cons j v))
        (fun _ _ => rfl) _ _ hdim hFC
      · intro a x
        exact finiteChoiceExpansion_cons W.eval l i a x
      · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultidegreeDilation
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_dilation_family {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (hpos : 1 ≤ ∑ j, bound j) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ R : NativeIntegerModelFamily (fun _ : σ => 1) ((∑ j, bound j) - 1)
        ((p + C) ^ C) (dilationTensorCrossProduct W.eval q (∑ j, bound j)),
        R.dim ≤ 2 * W.dim := by
  obtain ⟨C, hC, hcontrol⟩ := exists_controlled_dilation_family ((∑ j, bound j) - 1) q
  exact ⟨C, hC, fun W => hcontrol W.model W.multi rfl (Nat.sub_add_cancel hpos).symm
    W.complexity W.vertical W.orbit⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (d : Fin 2) (c : ℤ) (k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.eval k (Function.update (fun _ => c) d (x ())))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (mixedCorrelationDegree 1)
  refine ⟨C, hC, ?_⟩
  intro p W d c k
  classical
  let A : Fin 2 → ℤ := fun j => if j = d then 1 else 0
  let b : Fin 2 → ℤ := fun j => if j = d then 0 else c
  obtain ⟨E, _⟩ := hfreeze W {d} A b k (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [A, hj])
  have hdegree : (∑ j ∈ ({d} : Finset (Fin 2)), mixedCorrelationDegree 1 j) = 1 := by
    simp only [Finset.sum_singleton]
    fin_cases d <;> rfl
  have heq : (fun x : Unit → ℤ => W.eval k (fun j => b j + A j * x ())) =
      (fun x => W.eval k (Function.update (fun _ => c) d (x ()))) := by
    funext x
    apply congrArg (W.eval k)
    funext j
    by_cases hj : j = d
    · subst j
      simp [A, b]
    · simp [A, b, hj]
  exact ⟨by simpa only [hdegree, heq] using E⟩

theorem exists_antisymmetric_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (d : Fin 2) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => let z := Function.update (fun _ => c) d (x ())
          W.antisymmetricKernel i j (z 0) (z 1))) := by
  obtain ⟨A, _, hslice⟩ := exists_mixed_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hslice W d c i
  obtain ⟨F⟩ := hslice W d.rev c j
  obtain ⟨G⟩ := hmul (by positivity : 0 ≤ (p + A) ^ A) E.conjugate F
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have heq : (fun x : Unit → ℤ => star (W.eval i (Function.update (fun _ => c) d (x ()))) *
      W.eval j (Function.update (fun _ => c) d.rev (x ()))) =
      (fun x => let z := Function.update (fun _ => c) d (x ())
        W.antisymmetricKernel i j (z 0) (z 1)) := by
    funext x
    unfold antisymmetricKernel
    congr 1
    · congr 1
      apply congrArg (W.eval i)
      funext l
      fin_cases l <;> rfl
    · apply congrArg (W.eval j)
      funext l
      fin_cases d <;> fin_cases l <;> rfl
  exact ⟨by simpa only [heq] using G.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRootDegreeEquivalence
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_dilation_degree_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (hpos : 1 ≤ ∑ j, bound j) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (integerDilationVector W.eval q) (signedTensorVector W.eval (q ^ ∑ j, bound j)) := by
  obtain ⟨a, _, hfamily⟩ := exists_dilation_family bound hpos q
  let n := (q ^ ∑ j, bound j).natAbs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (n + 1) * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb : (p + a) ^ a + (n + 1 : ℝ) * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  have hnpr : (n : ℝ) * p ≤ (p + C) ^ C := by nlinarith
  have har : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  obtain ⟨R, _⟩ := hfamily W
  exact NativeIntegerVectorEquivalence.of_dilation_family W.eval q (∑ j, bound j) R
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr hnpr har

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
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

theorem horizontal_frequency (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, Fin 4 → W.rank.filtration.HigherHorizontal (d j).val)
    (hv : ∀ j, v j ∈ D.horizontal (d j)) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 0)) +
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 1)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 2)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 3)) = 0 := by
  obtain ⟨t, ht⟩ := D.nonempty
  apply (R.interval ⟨t, D.subset ht⟩).refilteredHorizontalImage_frequency
    (D.witness t ht).index (D.witness t ht).subalgebra (fun j => (d j).val) a hd hr
    ((D.witness t ht).bracket n (fun j => (d j).val) a hd hr) v
  intro j
  rw [D.horizontalImage_eq t ht (d j)]
  exact hv j

theorem sunflower_bracket (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, W.rank.filtration.HigherHorizontal (d j).val)
    (hv : ∀ j, v j ∈ fourFirstProjection (D.horizontal (d j)))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ fourDependentProjection (D.horizontal (d j)))
    (hvk : v k ∈ fourDependentProjection (D.horizontal (d k))) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a)
    (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a)
    (fun u j hj hu => W.rank.filtration.horizontalTreeValue_zero_of_leaf
      (fun j => (d j).val) a u (i := j) hj hu)
    W.vertical.frequency (map_zero _) (fun j => D.horizontal (d j))
    (D.horizontal_frequency n d a hd hr) v hv j k hjk hj hk hvj hvk

theorem sunflower_representatives (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, W.rank.filtration.layer (d j).val 1)
    (hv : ∀ j, W.rank.filtration.higherHorizontalMk (d j).val (v j) ∈
      fourFirstProjection (D.horizontal (d j)))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : W.rank.filtration.higherHorizontalMk (d j).val (v j) ∈
      fourDependentProjection (D.horizontal (d j)))
    (hvk : W.rank.filtration.higherHorizontalMk (d k).val (v k) ∈
      fourDependentProjection (D.horizontal (d k))) :
    W.vertical.frequency (lieTreeEval (fun j => (v j).val) a) = 0 := by
  have h := D.sunflower_bracket n d a hd hr
    (fun j => W.rank.filtration.higherHorizontalMk (d j).val (v j)) hv j k hjk hj hk hvj hvk
  rwa [W.rank.filtration.horizontalTreeValue_mk (fun j => (d j).val) a hd hr v] at h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficient_sunflower (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : Fin n → W.L) (hv : ∀ j, v j ∈ D.commonCoefficientSpace (d j))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentCoefficientSpace (d j))
    (hvk : v k ∈ D.dependentCoefficientSpace (d k)) :
    W.vertical.frequency (lieTreeEval v a) = 0 := by
  let u (i : Fin n) : W.rank.filtration.layer (d i).val 1 :=
    ⟨v i, D.commonCoefficientSpace_le (d i) (hv i)⟩
  exact D.sunflower_representatives n d a hd hr u
    (fun i => (W.rank.filtration.mem_horizontalPreimage _ _ (u i)).mp (hv i))
    j k hjk hj hk
    ((W.rank.filtration.mem_horizontalPreimage _ _ (u j)).mp hvj)
    ((W.rank.filtration.mem_horizontalPreimage _ _ (u k)).mp hvk)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficientFreeSpan_le_layer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 :=
  sup_le (D.commonFreeSpan_le_layer d) (D.dependentFreeSpan_le_layer d)

end Erdos3.NativeRankRelation.CommonData

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

theorem coefficientFreeGenerator_mem_combined (x : D.CoefficientAlphabet) :
    D.coefficientFreeGenerator x ∈ D.coefficientFreeSpan (D.coefficientLayerIndex x) := by
  cases x with
  | inl x => exact D.commonFreeSpan_le_coefficientFreeSpan x.1 (Submodule.subset_span ⟨x.2, rfl⟩)
  | inr x => exact D.dependentFreeSpan_le_coefficientFreeSpan x.1 (Submodule.subset_span ⟨x.2, rfl⟩)

theorem coefficientFreeGenerator_mem_dependent (x : D.CoefficientAlphabet)
    (hx : D.coefficientIsDependent x = true) :
    D.coefficientFreeGenerator x ∈ D.dependentFreeSpan (D.coefficientLayerIndex x) := by
  cases x with
  | inl x => cases hx
  | inr x => exact Submodule.subset_span ⟨x.2, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonDependentPolynomialIntersections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def dependentPolynomialLayer (d k l : ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra) :=
  markedPolynomialLayer D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent d k l

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
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

noncomputable def markedQuotientMultidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2)
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) (mixedCorrelationDegree s) :=
  markedShiftMultidegree D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedUnitOrbit
namespace OAI


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

noncomputable def localAffineMarkedBase (j : Fin s) : (D.coefficientFreeSpan j).baseChange ℝ :=
  ⟨(x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val,
    Submodule.add_mem _ (x j).property (Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.baseChange_mono ℝ
        (D.dependentFreeSpan_le_coefficientFreeSpan j) (y j i).property)))⟩

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def scaledLocalAffineCorrectingElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  ⟨realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))⟩

end Erdos3.NativeRankRelation.CommonData


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LocalMarkedLatticeCorrection
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem scaledLocalAffineCorrectingElement_mem_realLattice
    {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) {d : ℕ}
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (hm : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice) (h : ZMod N) :
    D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ E.realLattice := by
  exact markedDirection_mem_realLattice_of_smul D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t E (m : ℚ)
    (fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))
    (hm (fun i => -affineCyclicTorusCarry u c h₀ h i))

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def localPhaseMarkedSmallElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)

theorem scaledLocalAffineCorrectingElement_eq_parameter (h : ZMod N) :
    D.scaledLocalAffineCorrectingElement t u c h₀ m h =
      realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t
          (fun i => -(m : ℝ) * (affineCyclicTorusCarry u c h₀ h i : ℝ)) := by
  apply NilpotentLieBCHGroup.ext
  have he := realMarkedParameterDirection_rat D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t
      ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))
  change realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t _ =
      realMarkedParameterDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t _
  simpa only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_neg, Rat.cast_natCast,
    Rat.cast_intCast, Int.cast_neg, mul_neg, neg_mul] using he.symm

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)

variable (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

theorem localPhaseMarkedSmallElement_inv (h : ZMod N) :
    (D.localPhaseMarkedSmallElement t u c h₀ m h)⁻¹ =
      realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t
          (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) := by
  apply (realMarkedParameterElement_inv D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)).trans
  apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
  funext i
  simp only [Pi.neg_apply, neg_mul, neg_neg]

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonInducedCorrelation
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_induced_marked_observable_explicit (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]
      (E : RationalFilteredNilmanifold (L ⧸ J) u e)
      (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
        (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (t : ℝ) ≤ p → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr
        (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ V : E.Space → ℂ, (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      letI := D.metricSpace
      ∃ G : D.Space → ℂ,
        LipschitzWith (inducedMarkedLipschitzBound s d u e p
          ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩) G ∧
        (∀ g : D.RealGroup,
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
          G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g) ∧
        ∀ x, ‖G x‖ ≤ 2 := by
  obtain ⟨C, hC, hrepresentatives⟩ := exists_marked_phase_band_representatives s hs
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r d t m e u F v w marked hw hv hm _ _ _ _ D J hJ _ _ _ _ E hmap p hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  let φ := normalizedMarkedPhase F v w marked t m
  let R : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩
  let K : ℝ≥0 := ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
  let H := ⌈Real.exp p⌉₊
  let A := markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩
  let f := markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V
  have hR : 1 ≤ R := Real.one_le_exp (by positivity)
  have norm_iff (z : Fin t → ℝ) : ‖z‖ ≤ 1 / 4 ↔ ∀ i, |z i| ≤ 1 / 4 := by
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) (x := z))
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hct (i j k) : RationalHeightLE (lieStructureConstants E.basis i j k) H :=
    rationalHeightLE_ceil_exp (hE.2.2.1 i j k)
  have hrep (g : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4) :
      ∃ x : D.RealGroup, (QuotientGroup.mk x : D.Space) = QuotientGroup.mk g ∧
        torusPhaseLinear φ x.coord = torusPhaseLinear φ g.coord ∧
        ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ R :=
    hrepresentatives F v w marked hw hv D hp hD ht hm hmp hdir hphase hint hlat g ((norm_iff _).mp hg)
  have hdist (g h : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
      (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
      dist (f g) (f h) ≤ phaseBandQuotientConstant (s + 1) d H R K A *
        dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h) := by
    apply phase_band_quotient_dist_le D φ hint hc R K A hR
      (torusPhaseLinear_group_lipschitz_exp D φ hp hD.1 ht hphase) hrep f
      (fun x => markedLocalCoefficientValue_norm_le F v w marked hw hv t m hm D J hJ E hmap V hnorm x)
      (fun x y hx hy hxy => markedLocalCoefficientValue_eq_on_small_cosets
        F v w marked hw hv t m hm D J hJ E hmap hint V x y ((norm_iff _).mp hx) ((norm_iff _).mp hy) hxy)
      (fun x y hx hy => ?_) g h hg hh
    exact markedLocalCoefficientValue_coordinate_dist_le F v w marked hw hv t m hm D J hJ E hmap
      hp hD.1 ht hmp hdir hphase heval hc hct (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩
      (le_add_of_nonneg_left (by positivity)) V hV x y hx hy
  let X := {g : D.RealGroup // ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4}
  obtain ⟨G, hG, hGeq, hGnorm⟩ := exists_complex_extension_along_map
    (fun x : X => (QuotientGroup.mk x.val : D.Space)) (fun x : X => f x.val)
    (phaseBandQuotientConstant (s + 1) d H R K A) 1
    (fun x y => hdist x.val y.val x.property y.property)
    (fun x => markedLocalCoefficientValue_norm_le F v w marked hw hv t m hm D J hJ E hmap V hnorm x.val)
  refine ⟨G, hG, ?_, ?_⟩
  · intro g hg
    exact hGeq ⟨g, (norm_iff _).mpr hg⟩
  · intro x
    simpa only [NNReal.coe_one, mul_one] using hGnorm x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedMarkedLattice
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d) (m : ℕ)

theorem normalizedMarkedLattice_direction (hm : 0 < m) (a : Fin t → ℤ)
    (ha : (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
      D.filtration.Group) ∈ D.lattice) :
    (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
      D.filtration.Group) ∈ normalizedMarkedLattice F v w marked t D m := by
  refine ⟨ha, ?_⟩
  change IntegralVector (normalizedMarkedPhase F v w marked t m
    ((m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))))
  rw [normalizedMarkedPhase_scaled_direction F v w marked t m hm]
  exact ⟨a, fun _ => rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_normalized_marked_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap J (b j)) i) ≤ p) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              (∀ i j, rationalLogHeight
                (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
                  (p + C) ^ C) ∧
              (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤
                (p + C) ^ C) ∧
              (∀ i j, rationalLogHeight
                (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
                  (p + C) ^ C) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice →
                (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
              (∀ z : D.RealGroup, z ∈ D.realLattice →
                (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
                  E.realLattice) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice →
                IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
              ∀ a : Fin t → ℤ,
                (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                  D.filtration.Group) ∈ D.lattice := by
  obtain ⟨a, ha, hmodel⟩ := exists_compatible_marked_evaluation_model s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (2 * P₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro I ι L _ _ _ _ r t e u F b ω hF hω v w marked hw hv J hJ E p hp hn ht hc hgen hE hcoef
  let P := (p + a) ^ a
  let Q := (2 * P + 3) ^ 5
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpP : p ≤ P := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  have hTQ : 2 * P + 1 ≤ Q := by
    simpa only [show 2 * P + 1 + 2 = 2 * P + 3 by ring] using
      le_power_budget (by linarith : 0 ≤ 2 * P + 1) (by decide : 1 ≤ 5)
  have htotal : P + Q ≤ (p + C) ^ C := by
    simpa [X, P₀, P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := (le_add_of_nonneg_right hQ).trans htotal
  have hQC : Q ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  obtain ⟨q, hqdim, D, M, hMF, hM, _, hdir, hphase, heval, hmap, _, hrealmap,
      m, hm, hmb, hmlattice⟩ := hmodel F b ω hF hω v w marked hw hv J hJ E hp hn ht hc hgen hE hcoef
  obtain ⟨N, hN, hin, hout, _, hM'⟩ := exists_normalizedMarkedLattice_model F v w marked t D m M
    hP hM (ht.trans hpP) hm hmb hphase
  let Λ := normalizedMarkedLattice F v w marked t D m
  let D' := D.withLattice Λ N hN hin hout
  let M' := M.withLattice Λ N hN hin hout
  have hlatR : D'.realLattice ≤ D.realLattice :=
    Subgroup.map_mono (normalizedMarkedLattice_le F v w marked t D m)
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hPC), q, hqdim, D', M', hMF,
    hM'.mono M' hQC, (fun i j => (hdir i j).trans hPC), ?_,
    (fun i j => (heval i j).trans hPC), ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (normalizedMarkedPhase_height F v w marked t m hm hP hmb (D.basis j) i
      (hphase i j)).trans (hTQ.trans hQC)
  · intro z hz
    exact hmap z hz.1
  · intro z hz
    exact hrealmap z (hlatR hz)
  · exact normalizedMarkedLattice_integral F v w marked t D m
  · exact fun a => normalizedMarkedLattice_direction F v w marked t D m hm a (hmlattice a)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_induced_marked_observable (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m e : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]
      (E : RationalFilteredNilmanifold (L ⧸ J) u e)
      (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
        (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (t : ℝ) ≤ p → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr
        (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ V : E.Space → ℂ, (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      letI := D.metricSpace
      ∃ G : D.Space → ℂ,
        LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ G ∧
        (∀ g : D.RealGroup,
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
          G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g) ∧
        ∀ x, ‖G x‖ ≤ 2 := by
  obtain ⟨A, _, hext⟩ := exists_induced_marked_observable_explicit s hs
  obtain ⟨C, hC, hbound⟩ := exists_inducedMarkedLipschitzBound_exp_bound s u A
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r d t m e F v w marked hw hv hm _ _ _ _ D J hJ _ _ _ _ E hmap p hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  let := D.metricSpace
  obtain ⟨G, hG, hGeq, hGnorm⟩ := hext F v w marked hw hv hm D J hJ E hmap
    hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  refine ⟨G, hG.weaken ?_, hGeq, hGnorm⟩
  change (inducedMarkedLipschitzBound s d u e p
    ⟨Real.exp ((p + A) ^ A), Real.exp_nonneg _⟩ : ℝ) ≤ Real.exp ((p + C) ^ C)
  exact hbound d e p ⟨Real.exp ((p + A) ^ A), Real.exp_nonneg _⟩ hp hD.1 hE.1 le_rfl

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_induced_marked_model (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι J L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (Q : LieIdeal ℚ L) (hQ : markedLieSpan v w marked 0 2 0 ≤ Q.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ Q))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ Q))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ Q))] [T2Space (ℝ ⊗[ℚ] (L ⧸ Q))]
      (E : RationalFilteredNilmanifold (L ⧸ Q) u e) (V : J → E.Space → ℂ) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap Q (b j)) i) ≤ p) →
      (∀ i x, ‖V i x‖ ≤ 1) →
      (letI := E.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i)) →
      ∃ (m : ℕ) (hm : 0 < m), (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              ∃ hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
                  (⟨(markedBaseEvaluation F v w marked t Q hQ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice,
                (∀ z : D.filtration.Group, z ∈ D.lattice →
                  IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
                (∀ a : Fin t → ℤ,
                  (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                    D.filtration.Group) ∈ D.lattice) ∧
                (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
                 letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
                   IsModuleTopology.topologicalAddGroup ℝ _
                 letI := realification_moduleTopology_t2 D.basis
                 letI := D.metricSpace
                 ∃ G : J → D.Space → ℂ,
                   (∀ i x, ‖G i x‖ ≤ 2) ∧
                   (∀ i, LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ (G i)) ∧
                   ∀ i (g : D.RealGroup),
                     (∀ j, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord j| ≤ 1 / 4) →
                     G i (QuotientGroup.mk g) =
                       markedLocalCoefficientValue F v w marked hw hv t m hm D Q hQ E hmap (V i) g) := by
  classical
  obtain ⟨A, hA, hmodel⟩ := exists_normalized_marked_model s
  obtain ⟨B, _, hext⟩ := exists_induced_marked_observable s u hs
  let P₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I ι J L _ _ _ _ r t e F b ω hF hω v w marked hw hv Q hQ _ _ _ _ E V p hp hd ht hc hgen hE hproj hVnorm hV
  let P := (p + A) ^ A
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p ≤ P := by
    apply (le_power_budget hp (a := A) (by omega)).trans
    change (p + 2) ^ A ≤ (p + A) ^ A
    exact pow_le_pow_left₀ (by linarith) (add_le_add le_rfl (by exact_mod_cast hA)) A
  have htotal : P + (P + B) ^ B ≤ (p + C) ^ C := by
    simpa [P₀, P, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hEC : (P + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  obtain ⟨m, hm, hmp, d, hdim, D, M, hMF, hM, hdir, hphase, heval, _, hmap, hint, hlat⟩ :=
    hmodel F b ω hF hω v w marked hw hv Q hQ E hp hd ht hc hgen hE hproj
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hPC), d, hdim, D, M, hMF,
    hM.mono M hPC, hmap, hint, hlat, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  let := E.metricSpace
  have hchoose (i : J) := hext F v w marked hw hv hm D Q hQ E hmap hP hM.1
    (hE.mono E hpP) (ht.trans hpP) hmp hdir hphase heval hint hlat (V i) (hVnorm i)
    ((hV i).weaken (show (⟨Real.exp p, Real.exp_nonneg p⟩ : ℝ≥0) ≤
      ⟨Real.exp P, Real.exp_nonneg P⟩ from Real.exp_le_exp.mpr hpP))
  choose G hG hGeq hGnorm using hchoose
  refine ⟨G, hGnorm, ?_, hGeq⟩
  intro i
  exact (hG i).weaken (show (⟨Real.exp ((P + B) ^ B), Real.exp_nonneg _⟩ : ℝ≥0) ≤
    ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hEC)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_induced_marked_model (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J L : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L] {r t e n : ℕ}
      (F : DegreeRankLieFiltration L s r) (A : RationalFilteredNilmanifold L s n)
      (_hFA : F.associatedDegree = A.filtration) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (Q : LieIdeal ℚ L) (hQ : markedLieSpan v w marked 0 2 0 ≤ Q.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ Q))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ Q))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ Q))] [T2Space (ℝ ⊗[ℚ] (L ⧸ Q))]
      (E : RationalFilteredNilmanifold (L ⧸ Q) u e) (V : J → E.Space → ℂ) {p : ℝ},
      0 ≤ p → A.GeometryComplexityLE p → (t : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (A.basis.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap Q (A.basis j)) i) ≤ p) →
      (∀ i x, ‖V i x‖ ≤ 1) →
      (letI := E.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i)) →
      ∃ (m : ℕ) (hm : 0 < m), (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ n * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              ∃ hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
                  (⟨(markedBaseEvaluation F v w marked t Q hQ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice,
                (∀ z : D.filtration.Group, z ∈ D.lattice →
                  IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
                (∀ a : Fin t → ℤ,
                  (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                    D.filtration.Group) ∈ D.lattice) ∧
                (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
                 letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
                   IsModuleTopology.topologicalAddGroup ℝ _
                 letI := realification_moduleTopology_t2 D.basis
                 letI := D.metricSpace
                 ∃ G : J → D.Space → ℂ,
                   (∀ i x, ‖G i x‖ ≤ 2) ∧
                   (∀ i, LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ (G i)) ∧
                   ∀ i (g : D.RealGroup),
                     (∀ j, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord j| ≤ 1 / 4) →
                     G i (QuotientGroup.mk g) =
                       markedLocalCoefficientValue F v w marked hw hv t m hm D Q hQ E hmap (V i) g) := by
  obtain ⟨B, _, hmodel⟩ := exists_induced_marked_model s u hs
  let X : Polynomial ℕ := Polynomial.X + (Polynomial.X + 3) ^ 11 + 1
  let P₀ := X + (X + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I J L _ _ _ r t e n F A hFA v w marked hw hv Q hQ _ _ _ _ E V p hp hA ht hgen hE hproj hVnorm hV
  obtain ⟨b, ω, N, _, _, hfil, hb, hbinv, hbc, _, _, _, _⟩ := A.exists_controlled_adapted_basis hp hA
  have hFb : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}) := by
    simpa only [hFA] using hfil
  have hω := F.associatedDegree.adaptedBasis_weight_le_step b ω hFb
  let x := p + (p + 3) ^ 11 + 1
  let P := x + (x + 2) ^ 4
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpx : p ≤ x := by dsimp [x]; linarith [pow_nonneg (by linarith : 0 ≤ p + 3) 11]
  have hpx1 : p + 1 ≤ x := by dsimp [x]; linarith [pow_nonneg (by linarith : 0 ≤ p + 3) 11]
  have hxP : x ≤ P := le_add_of_nonneg_right (by positivity)
  have hpP : p ≤ P := hpx.trans hxP
  have hpowP : (x + 2) ^ 4 ≤ P := by dsimp [P]; linarith
  have h5x : (p + 3) ^ 5 ≤ x := by
    have hh := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 5 ≤ 11)
    dsimp [x]
    linarith
  have h11P : (p + 3) ^ 11 ≤ P := by
    apply le_trans ?_ hxP
    dsimp [x]
    linarith
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ P := by
    rw [Fintype.card_fin, finrank_eq_card_basis A.basis, Fintype.card_fin]
    exact hA.1.trans hpP
  have hdimx : (Fintype.card (Fin n) : ℝ) ≤ x := by simpa only [Fintype.card_fin] using hA.1.trans hpx
  have hgenb (i j) : rationalLogHeight (b.repr (v i) j) ≤ P := by
    have hh := linearMap_coordinate_logHeight A.basis b (LinearMap.id : L →ₗ[ℚ] L) hx hdimx
      (fun a c => (hbinv a c).trans h5x) (v i) (fun a => (hgen i a).trans hpx) j
    exact hh.trans hpowP
  have hprojb (i j) : rationalLogHeight (E.basis.repr (lieQuotientMap Q (b j)) i) ≤ P := by
    exact (linearMap_coordinate_logHeight A.basis E.basis (lieQuotientMap Q).toLinearMap hx hdimx
      (fun a c => (hproj c a).trans hpx) (b j) (fun a => (hb j a).trans hpx1) i).trans hpowP
  have htotal : P + (P + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P₀, P, x, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : (P + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  let := E.metricSpace
  obtain ⟨m, hm, hmp, d, hdimd, D, M, hMF, hM, hmap, hint, hlat, hobs⟩ :=
    hmodel F b ω hFb hω v w marked hw hv Q hQ E V hP hdim (ht.trans hpP)
      (fun i j k => (hbc i j k).trans h11P) hgenb (hE.mono E hpP) hprojb hVnorm
      (fun i => (hV i).weaken (show (⟨Real.exp p, Real.exp_nonneg p⟩ : ℝ≥0) ≤
        ⟨Real.exp P, Real.exp_nonneg P⟩ from Real.exp_le_exp.mpr hpP))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbound), d, ?_, D, M, hMF,
    hM.mono M hbound, hmap, hint, hlat, ?_⟩
  · simpa only [Fintype.card_fin, finrank_eq_card_basis A.basis] using hdimd
  · let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    let := realification_moduleTopology_t2 D.basis
    let := D.metricSpace
    obtain ⟨G, hGn, hGL, hGe⟩ := hobs
    refine ⟨G, hGn, ?_, hGe⟩
    intro i
    exact (hGL i).weaken (show (⟨Real.exp ((P + B) ^ B), Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hbound)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_quadratic_diagonal_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        (fun k : (Fin W.outputDim × Fin W.outputDim) ×
            (Fin W.outputDim × Fin W.outputDim) => fun x =>
          (W.eval k.1.1 (fun _ => x 1) * W.eval k.1.2 (correlationInput (x 1) (x 0))) *
            (W.eval k.2.1 (correlationInput (x 0) (x 1)) * W.eval k.2.2 (fun _ => x 0))) := by
  have hbound : mixedCorrelationDegree 1 = (fun _ : Fin 2 => 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hbound]
  obtain ⟨C, hC, hexpand⟩ := exists_translation_expansion_equivalence ([0, 1] : List (Fin 2))
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Option (Fin 2) → Fin 2 := fun j => match j with
    | none => 0
    | some _ => 1
  have E := (hexpand W (by decide)).coordinatePullback a
  have hleft (k : Fin W.outputDim) (x : Fin 2 → ℤ) :
      W.eval k (coordinateTranslatedInput [0, 1] (fun j => x (a j))) =
        W.eval k (fun _ => x 1 + x 0) := by
    apply congrArg (W.eval k)
    funext i
    fin_cases i <;> simp [coordinateTranslatedInput, a]
  have hright (k : (Fin W.outputDim × Fin W.outputDim) ×
      (Fin W.outputDim × Fin W.outputDim)) (x : Fin 2 → ℤ) :
      coordinateTranslationExpansion W.eval [0, 1] k (fun j => x (a j)) =
      (W.eval k.1.1 (fun _ => x 1) * W.eval k.1.2 (correlationInput (x 1) (x 0))) *
        (W.eval k.2.1 (correlationInput (x 0) (x 1)) * W.eval k.2.2 (fun _ => x 0)) := by
    simp only [coordinateTranslationExpansion]
    apply congrArg₂ (fun z w : ℂ => z * w)
    · apply congrArg₂ (fun z w : ℂ => z * w)
      · rfl
      · apply congrArg (W.eval k.1.2)
        funext i
        fin_cases i <;> rfl
    · apply congrArg₂ (fun z w : ℂ => z * w)
      · apply congrArg (W.eval k.2.1)
        funext i
        fin_cases i <;> rfl
      · apply congrArg (W.eval k.2.2)
        funext i
        fin_cases i <;> rfl
  refine ⟨E.left_dimension, E.right_dimension, ?_⟩
  intro k l
  obtain ⟨F⟩ := E.expansion k l
  exact ⟨by simpa only [Fintype.card_fin, Nat.reduceSub, hleft, hright] using F⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem exists_quadratic_diagonal_derivative_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        W.quadraticDiagonalDerivative W.quadraticMixedTriple := by
  obtain ⟨A, _, hdiag⟩ := exists_quadratic_diagonal_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 3 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + 3 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hthree : 3 * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdim2 := card_product_le_exp_two hdim hdim
  have hdim3 : (Fintype.card (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) : ℝ) ≤
      Real.exp (3 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    apply (mul_le_mul hdim hdim2 (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨hdim2.trans (Real.exp_le_exp.mpr htwo),
    hdim3.trans (Real.exp_le_exp.mpr hthree), ?_⟩
  intro a b
  obtain ⟨F⟩ := (hdiag W).expansion a.2 ((a.1, b.1), (b.2.1, b.2.2))
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star ((W.eval a.1 (fun _ => x 1) * W.eval b.1 (correlationInput (x 1) (x 0))) *
        (W.eval b.2.1 (correlationInput (x 0) (x 1)) * W.eval b.2.2 (fun _ => x 0))))) =
      (fun x => W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple b x)) := by
    funext x
    simp only [quadraticDiagonalDerivative, quadraticMixedTriple, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_explicit_quadratic_root_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C) W.eval
        (tensorVector ((W.rationalDilation (1 / 2)).tensorPower 2).eval 2) := by
  have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
  have hpos : 1 ≤ ∑ i, mixedCorrelationDegree 1 i := by rw [hsum]; norm_num
  obtain ⟨A, _, hdilation⟩ := exists_dilation_degree_equivalence (mixedCorrelationDegree 1) hpos 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 6 * (X + 1) + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hbound : (p + A) ^ A + 6 * (p + 1) + p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith
  have hAr : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hdimBound : 2 * tensorPowerBudget 2 p ≤ (p + C) ^ C := by
    norm_num [tensorPowerBudget]
    linarith
  let V := W.rationalDilation (1 / 2)
  let R := V.tensorPower 2
  have hleft (i : Fin W.outputDim) (x : Fin 2 → ℤ) :
      W.eval i x = integerDilationVector V.eval 2 i x :=
    (W.rationalDilation_eval_rescaled (1 / 2) 2 (by norm_num) i x).symm
  have hright (b : Fin 2 → Fin R.outputDim) (x : Fin 2 → ℤ) :
      tensorVector R.eval 2 b x =
        signedTensorVector V.eval ((2 : ℤ) ^ ∑ j, mixedCorrelationDegree 1 j)
          (rootTensorIndex W.outputDim 2 (∑ j, mixedCorrelationDegree 1 j) hpos b) x := by
    exact V.tensorPower_tensor_eval 2 (∑ j, mixedCorrelationDegree 1 j) hpos b x
  have hdim : (Fintype.card (Fin 2 → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 2 p) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp (2 * tensorPowerBudget 2 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 2 p) 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have E := (hdilation V).of_coordinate_maps W.eval (tensorVector R.eval 2) id
    (rootTensorIndex W.outputDim 2 (∑ j, mixedCorrelationDegree 1 j) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr
  simpa only [hsum, Nat.reduceSub] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

theorem exists_diagonalSquareCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
        ((p + q + C) ^ C) (W.diagonalSquareCorrection G a b)) := by
  obtain ⟨A, _, hdiag⟩ := exists_quadratic_diagonal_derivative_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B + X)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let r := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := add_nonneg hp hq
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have hAr : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; linarith
  have hcost : (r + B) ^ B + p ≤ (p + q + C) ^ C := by
    have hh : (r + B) ^ B + v ≤ (p + q + C) ^ C := by
      simpa [X, R, r, v, Polynomial.eval₂_pow] using hbudget v hv
    dsimp [v] at hh
    linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _j : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterm (j : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((r + B) ^ B)
        (fun x => (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
          star (G b.1 j x))) :=
    hmul hr ((Classical.choice ((hdiag W).expansion a (j, b.2))).mono hAr)
      ((Classical.choice (hG b.1 j)).conjugate.mono hqr)
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (hterm j))
    (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hcost
  change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => ∑ j, (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
      star (G b.1 j x)))
  exact ⟨by simpa only [one_mul] using E⟩

theorem exists_cyclicExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + e + C) ^ C)
        (W.cyclicDiagonalCorrection N δ (W.diagonalSquareCorrection G) a b)) := by
  obtain ⟨A, _, hdiag⟩ := exists_diagonalSquareCorrection_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_cyclicDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + (X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : (p + q + A) ^ A ≤ (p + q + e + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (p + (p + q + A) ^ A + e + B) ^ B ≤ (p + q + e + C) ^ C := by
    have hh : (p + q + e + (p + q + e + A) ^ A + B) ^ B ≤ (p + q + e + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget (p + q + e) (by positivity)
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by positivity)
    linarith
  obtain ⟨E⟩ := hcyclic W N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.diagonalSquareCorrection G) (hdiag W hq G hG) a b
  exact ⟨E.mono hb⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem exists_rootCyclicCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + e + C) ^ C)
        (W.rootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_explicit_half_root_exchange_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_cyclicExchangeCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget 2 p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : (3 * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num only [tensorPowerBudget, Nat.cast_ofNat] at *
    dsimp [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.quadraticRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.rootExchangeCorrection G) (hroot W hq G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeMixedCoordinateSlices
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_mixed_frozen_affine_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : (MixedReplicatedIndex (n + 1)) => 1) p)
      (d : (MixedReplicatedIndex (n + 1))) (A : (MixedReplicatedIndex (n + 1)) → Fin (n + 2) → ℤ)
      (b : (MixedReplicatedIndex (n + 1)) → ℤ) (out : Fin W.outputDim),
      (∀ k, A d k = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.eval out (integerAffineMap A b x))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest (fun _ : (MixedReplicatedIndex (n + 1)) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W d A b out hA
  classical
  let S : Finset (MixedReplicatedIndex (n + 1)) := Finset.univ.erase d
  have hcard : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 :=
    replicatedMixed_card (n + 1)
  have hdegree : (∑ j ∈ S, (1 : ℕ)) = n + 1 := by simp [S, hcard]
  obtain ⟨t, dim, ht, _hdim, D, hD⟩ := hfreeze W S b out
  have ht3 : t = n + 1 := ht.trans hdegree
  rcases ht3 with rfl
  let K := W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _hTnorm, hT, _hzero, heval⟩ := hD
  let U := T.affinePullback (fun j k => A j.val k) (fun j => b j.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hvalue (x : Fin (n + 2) → ℤ) : U.eval x = W.eval out (integerAffineMap A b x) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    apply congrArg (W.eval out)
    funext j
    by_cases hj : j ∈ S
    · simp [freezeCoordinates, hj, integerAffineMap]
    · have hjd : j = d := by simpa [S] using hj
      subst j
      simp [freezeCoordinates, hj, integerAffineMap, hA]
  let E : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C) U.eval :=
    NativeIntegerExpansion.ofTest U hU (fun _ => rfl)
  have heq : U.eval = (fun x => W.eval out (integerAffineMap A b x)) := funext hvalue
  exact ⟨heq ▸ E⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_diagonal_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        W.mixedDiagonalTensor := by
  let : Nonempty (MixedReplicatedIndex (s + 2)) := replicatedMixed_nonempty (s + 2)
  obtain ⟨C, hC, hexpand⟩ := exists_finite_assignment_equivalence 1 (mixedAllCoordinates s)
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Fin 2 × MixedReplicatedIndex (s + 2) → Fin 2 := fun j => j.1.rev
  have hA (x : Fin 2 → ℤ) : (fun j => x (a j)) = mixedDiagonalChoiceInput x := rfl
  have E := (hexpand W (mixedAllCoordinates_nodup s)).coordinatePullback a
  have H : NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
      (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
      (fun b : (Fin (mixedAllCoordinates s).length → Fin 2) → Fin W.outputDim =>
        fun x => ∏ v, W.eval (b v) (mixedDiagonalCorner (mixedCornerAssignmentEquiv s v) x)) := by
    simpa only [hA, finiteChoiceExpansion, mixedDiagonalChoice_sum, mixedDiagonalChoice_leaf,
      replicatedMixed_card, Nat.add_sub_cancel] using E
  have hdim : (Fintype.card ((Fin (s + 3) → Fin 2) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, mixedAllCoordinates_length]
      using H.right_dimension
  apply H.of_coordinate_maps _ W.mixedDiagonalTensor id
    (fun b v => b (mixedCornerAssignmentEquiv s v)) (fun _ _ => rfl) _
    H.left_dimension hdim le_rfl
  intro b x
  exact ((mixedCornerAssignmentEquiv s).prod_comp
    (fun v => W.eval (b v) (mixedDiagonalCorner v x))).symm

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixed_diagonal_derivative_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
        W.mixedDiagonalDerivative W.mixedNonconstantTensor := by
  obtain ⟨A, _, hdiag⟩ := exists_mixed_diagonal_expansion s
  let m : ℕ := 2 ^ (s + 3) - 1
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C m * X + 2 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + (m : ℝ) * p + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hm : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hnonconstant : (m : ℝ) * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdimNonconstant : (Fintype.card (MixedNonconstantCorner s → Fin W.outputDim) : ℝ) ≤
      Real.exp ((m : ℝ) * p) := by
    simp only [Fintype.card_fun, mixedNonconstantCorner_card, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound m
      _ = _ := (Real.exp_nat_mul p m).symm
  refine ⟨(card_product_le_exp_two hdim hdim).trans (Real.exp_le_exp.mpr htwo),
    hdimNonconstant.trans (Real.exp_le_exp.mpr hnonconstant), ?_⟩
  intro a b
  let full : (Fin (s + 3) → Fin 2) → Fin W.outputDim := fun v =>
    if h : v = fun _ => 0 then a.1 else b ⟨v, h⟩
  obtain ⟨F⟩ := (hdiag W).expansion a.2 full
  have htensor (x : Fin 2 → ℤ) : W.mixedDiagonalTensor full x =
      W.eval a.1 (fun _ => x 1) *
        ∏ v : MixedNonconstantCorner s, W.eval (b v) (mixedDiagonalCorner v.val x) := by
    rw [mixedDiagonalTensor, Fintype.prod_eq_mul_prod_subtype_ne _ (fun _ => 0)]
    have hzero : full (fun _ => 0) = a.1 := by simp only [full, dif_pos rfl]
    have hfull (v : MixedNonconstantCorner s) : full v.val = b v := by
      simp only [full, dif_neg v.property]
    simp only [hzero, mixedDiagonalCorner_zero, hfull]
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star (W.mixedDiagonalTensor full x))) =
      (fun x => W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor b x)) := by
    funext x
    rw [htensor]
    simp only [mixedDiagonalDerivative, mixedNonconstantTensor, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_integration_root_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        W.eval (tensorVector W.mixedIntegrationRoot.eval (d + 3)) := by
  obtain ⟨a, _, hdilation⟩ := exists_uniform_dilation_degree_equivalence (d + 2) ((d + 3 : ℕ) : ℤ)
  let n := (d + 3) ^ (d + 2)
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C (n + 1) * (X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (d + 4) * B + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + a) ^ a := by positivity
  have hB : 0 ≤ tensorPowerBudget n p := by unfold tensorPowerBudget; positivity
  have hqB : 0 ≤ (d + 3 : ℝ) * tensorPowerBudget n p := by positivity
  have hb : (p + a) ^ a + (d + 4 : ℝ) * tensorPowerBudget n p + p + 2 ≤ (p + C) ^ C := by
    simpa [X, B, tensorPowerBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith
  have hAr : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith
  have hdimBound : (d + 3 : ℝ) * tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  let V := W.rationalDilation (((d + 3 : ℕ) : ℚ)⁻¹)
  let R := V.tensorPower n
  have hscale : (((d + 3 : ℕ) : ℚ)⁻¹) * (((d + 3 : ℕ) : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  have hleft (i : Fin W.outputDim) (x : MixedReplicatedIndex (d + 2) → ℤ) :
      W.eval i x = integerDilationVector V.eval ((d + 3 : ℕ) : ℤ) i x :=
    (W.rationalDilation_eval_rescaled _ _ hscale i x).symm
  have hpos : 1 ≤ d + 3 := by omega
  have hright (b : Fin (d + 3) → Fin R.outputDim) (x : MixedReplicatedIndex (d + 2) → ℤ) :
      tensorVector R.eval (d + 3) b x = signedTensorVector V.eval (((d + 3 : ℕ) : ℤ) ^ (d + 3))
        (rootTensorIndex W.outputDim (d + 3) (d + 3) hpos b) x := by
    exact V.tensorPower_tensor_eval (d + 3) (d + 3) hpos b x
  have hdim : (Fintype.card (Fin (d + 3) → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ (d + 3) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp ((d + 3 : ℝ) * tensorPowerBudget n p) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget n p) (d + 3)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have hs : (∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ)) = d + 3 :=
    mixedReplicated_totalDegree (d + 1)
  exact (hdilation _ hs V).of_coordinate_maps W.eval (tensorVector R.eval (d + 3)) id
    (rootTensorIndex W.outputDim (d + 3) (d + 3) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_original_mixed_root_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      NativeIntegerVectorEquivalence (d + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C) M.eval
        (fun a (x : Fin 2 → ℤ) => tensorVector W.mixedIntegrationRoot.eval (d + 3) a (fun j => x j.1)) := by
  obtain ⟨a, _, hroot⟩ := exists_mixed_integration_root_equivalence d
  obtain ⟨b, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p M W E
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + a) ^ a + p
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_left (by positivity)
  have hAt : (p + a) ^ a ≤ t := le_add_of_nonneg_right hp
  have F := (hroot W).coordinatePullback (fun j : MixedReplicatedIndex (d + 2) => j.1)
  have H := htrans ht (E.mono hpt) (F.mono hAt) (fun x => W.unit_eval _)
  have hcost : (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

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

theorem exists_mixed_permuted_diagonal_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + r + C) ^ C)
        (W.mixedPermutedDiagonalCorrection G a b)) := by
  obtain ⟨A, _, hderivative⟩ := exists_mixed_diagonal_derivative_equivalence s
  obtain ⟨B, _, hseven⟩ := exists_mixed_corner_product_expansion s
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D + Polynomial.C (mixedCornerCount s) * X)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + r + A) ^ A + (p + q + r + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + r + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hterm (c : MixedNonconstantCorner s → Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((t + D) ^ D)
        (fun x => (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
          W.mixedCornerExchangeProduct G c b x)) := by
    exact hmul ht (Classical.choice (((hderivative W).mono hAt).expansion a c))
      ((Classical.choice (hseven W G hq hr hG hperm c b)).mono hBt)
  have hdim : (Fintype.card (MixedNonconstantCorner s → Fin W.outputDim) : ℝ) ≤ Real.exp ((mixedCornerCount s) * p) := by
    simp only [Fintype.card_fun, mixedNonconstantCorner_card_eq, Fintype.card_fin, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound (mixedCornerCount s)).trans_eq
      (Real.exp_nat_mul p (mixedCornerCount s)).symm
  have hcoeff : (∑ _ : MixedNonconstantCorner s → Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp ((mixedCornerCount s) * p) := by
    simpa using hdim
  have H := NativeIntegerExpansion.weightedSum (fun c => Classical.choice (hterm c))
    (fun _ => 1) (by positivity : 0 ≤ (mixedCornerCount s) * p) hdim hcoeff
  have hcost : (t + D) ^ D + (mixedCornerCount s) * p ≤ (p + q + r + C) ^ C := by
    have hb : (t + D) ^ D + (mixedCornerCount s) * (p + q + r) ≤ (p + q + r + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q + r) (by positivity)
    have hmono : (mixedCornerCount s : ℝ) * p ≤ (mixedCornerCount s : ℝ) * (p + q + r) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + r + C) ^ C)
    (fun x => ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
      (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
        W.mixedCornerExchangeProduct G c b x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixedRootCornerCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (s + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (s + 2)) a).symm j)) = W.eval i x) →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.mixedRootCornerCorrection G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_mixedRootExchangeCorrection_expansion s
  obtain ⟨B, _, hperm⟩ := exists_mixed_root_last_slots_equivalence s
  obtain ⟨D, _, hdiagonal⟩ := exists_mixed_permuted_diagonal_expansion s
  let n := (s + 3) ^ (s + 2)
  let X : Polynomial ℕ := Polynomial.X
  let T := Polynomial.C (n + 1) * (X + 1) + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hdiagonal W.mixedIntegrationRoot (W.mixedRootExchangeCorrection G)
    (by positivity : 0 ≤ (p + q + A) ^ A) (by positivity : 0 ≤ (p + B) ^ B)
    (hroot W hq G hG) (hperm W hsymm) a b
  have hcost : (tensorPowerBudget n p + (p + q + A) ^ A + (p + B) ^ B + D) ^ D ≤
      (p + q + C) ^ C := by
    have hmono : (p + B) ^ B ≤ (p + q + B) ^ B :=
      pow_le_pow_left₀ (by positivity) (by linarith) B
    have hbase : tensorPowerBudget n p ≤ (n + 1 : ℝ) * (p + q + 1) := by
      unfold tensorPowerBudget
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hbound : ((n + 1 : ℝ) * (p + q + 1) + (p + q + A) ^ A + (p + q + B) ^ B + D) ^ D ≤
        (p + q + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
    apply le_trans _ hbound
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    linarith
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_original_mixed_first_tensor_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C) M.eval W.mixedIntegrationRoot.mixedFirstTensor := by
  obtain ⟨C, hC, h⟩ := exists_original_mixed_root_equivalence s
  refine ⟨C, hC, ?_⟩
  intro p M W E
  exact h M W E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixedOriginalWeightCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      NativeIntegerVectorEquivalence (s + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      ∀ F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
        (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (F a b))) →
      ∀ a i b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (M.mixedOriginalWeightCorrection W F a i b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_original_mixed_first_tensor_equivalence s
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let n := (s + 3) ^ (s + 2)
  let K := (s + 3) * (n + 1)
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C B) ^ B + Polynomial.C K * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q M W hq E F hF a i b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v] at *
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hterm (d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((t + B) ^ B)
        (fun x => (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) *
          F a (mixedGroupedWeightMerge d b) x)) :=
    hmul ht ((Classical.choice ((hcompare M W E).expansion i d)).mono hAt)
      ((Classical.choice (hF a (mixedGroupedWeightMerge d b))).mono hqt)
  have hcard : (Fintype.card (Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim) : ℝ) ≤
      Real.exp ((K : ℝ) * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ (s + 3) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.mixedIntegrationRoot.output_bound _
      _ = Real.exp (((s + 3 : ℕ) : ℝ) * tensorPowerBudget n p) :=
        (Real.exp_nat_mul (tensorPowerBudget n p) (s + 3)).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have heq : (((s + 3 : ℕ) : ℝ) * tensorPowerBudget n p) = (K : ℝ) * (p + 1) := by
          simp only [K, tensorPowerBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by dsimp [v]; linarith) (Nat.cast_nonneg _)
  have hcoeff : (∑ _ : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim, ‖(1 : ℂ)‖) ≤
      Real.exp ((K : ℝ) * (v + 1)) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun d => Classical.choice (hterm d))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ (K : ℝ) * (v + 1)) hcard hcoeff
  have hcost : (t + B) ^ B + (K : ℝ) * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
    (fun x => ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
      (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) * F a (mixedGroupedWeightMerge d b) x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_middle_factor_row_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (h : ℤ) (k : Fin (s + 1)) (a : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C)
        (fun x => W.eval a (mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()]))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (fun _ : MixedReplicatedIndex (s + 2) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W h k a
  classical
  let S : Finset (MixedReplicatedIndex (s + 2)) :=
    Finset.univ.image (fun i : Fin (s + 1) => mixedReplica i.succ)
  let A : MixedReplicatedIndex (s + 2) → ℤ :=
    fun j => if (mixedInputCoordinate (s + 1) j).val < k.val + 2 then 0 else 1
  let b : MixedReplicatedIndex (s + 2) → ℤ :=
    fun j => if (mixedInputCoordinate (s + 1) j).val < k.val + 2 then h else 0
  have hA : ∀ j, j ∉ S → A j = 0 := by
    intro j hj
    rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
    · change (if (0 : ℕ) < k.val + 2 then (0 : ℤ) else 1) = 0
      simp
    · revert hj
      refine Fin.cases ?_ (fun i => ?_) i
      · intro _
        change (if (1 : ℕ) < k.val + 2 then (0 : ℤ) else 1) = 0
        split_ifs <;> omega
      · intro hj
        exact False.elim (hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hi : Function.Injective (fun i : Fin (s + 1) => mixedReplica i.succ) := by
    intro i j hij
    exact Fin.succ_injective _ (mixedReplica_injective _ hij)
  have hc : S.card = s + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hi]
    simp
  have hdegree : (∑ i ∈ S, (fun _ : MixedReplicatedIndex (s + 2) => 1) i) = s + 1 := by
    simpa using hc
  obtain ⟨E, _⟩ := hfreeze W S A b a hA
  have hin (x : Unit → ℤ) : (fun j => b j + A j * x ()) =
      mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()] := by
    rw [← mixedSampledInput_coordinates]
    funext j
    simp only [A, b, mixedWeightSample, Fin.val_succ, Fin.val_castSucc, Nat.add_assoc]
    split_ifs <;> simp
  have heq : (fun x : Unit → ℤ => W.eval a (fun j => b j + A j * x ())) =
      (fun x => W.eval a (mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()])) := by
    funext x
    rw [hin]
  rw [hdegree, heq] at E
  exact ⟨E⟩

theorem exists_mixedMiddleTensor_row_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (h : ℤ) (b : MixedMiddleCorner s → Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C)
        (fun x => W.mixedMiddleTensor b ![h, x ()])) := by
  obtain ⟨A, _, hfactor⟩ := exists_mixed_middle_factor_row_expansion s
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (Fintype.card (MixedMiddleCorner s))
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W h b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let e := (Fintype.equivFin (MixedMiddleCorner s)).symm
  obtain ⟨F⟩ := hprod
    (fun i (x : Unit → ℤ) => W.eval (b (e i))
      (mixedSampledInput (mixedWeightSample s (e i).1.castSucc.succ) ![h, x ()]))
    (by positivity : 0 ≤ (p + A) ^ A) (fun i => hfactor W h (e i).1 (b (e i)))
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have heq : (fun x : Unit → ℤ => ∏ i, W.eval (b (e i))
      (mixedSampledInput (mixedWeightSample s (e i).1.castSucc.succ) ![h, x ()])) =
      (fun x => W.mixedMiddleTensor b ![h, x ()]) := by
    funext x
    exact e.prod_comp (fun z => W.eval (b z)
      (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) ![h, x ()]))
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

namespace NativeUnitVerticalData

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} {V : NativeVerticalDerivativeData B}
  (U : NativeUnitVerticalData B V q)

theorem test_zero_correlation (h : ZMod N) (hh : h ∈ B.shifts) :
    Real.exp (-(p + 1)) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star ((U.test 0 h).evalCyclic N (fun _ => x))‖ := by
  have heq :
      (𝔼 x, multiplicativeDerivative f h x * star ((U.test 0 h).evalCyclic N (fun _ => x))) =
      (𝔼 x, multiplicativeDerivative f h x * star ((B.test h).evalCyclic N (fun _ => x))) / 2 := by
    simp only [U.test_zero_evalCyclic, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div]
  rw [heq, norm_div]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  have hsmall : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
  exact hsmall.trans (div_le_div_of_nonneg_right (B.correlation h hh) (by norm_num))

end NativeUnitVerticalData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankFamilyConstruction
namespace OAI

section

namespace Erdos3.NativeDegreeRankDerivativeData

open scoped BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

theorem toFamily_correlation (hpq : p ≤ q) (h : ZMod N) (hh : h ∈ B.shifts) :
    Real.exp (-(p + 1)) ≤
      ‖𝔼 x, multiplicativeDerivative f h x *
        star ((W.toFamily hpq).evalCyclic N (0 : Fin (W.unit.tailDim + 1)) h x)‖ := by
  simp only [W.toFamily_evalCyclic]
  exact W.unit.test_zero_correlation h hh

end Erdos3.NativeDegreeRankDerivativeData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_antisymmetric_anchor_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (a : Fin 2 → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (boxAnchorFactor (W.antisymmetricKernel i j) a)) := by
  obtain ⟨A, _, hslice⟩ := exists_antisymmetric_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := Q + (Q + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j a
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  let r := q + (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := le_add_of_nonneg_right (by positivity)
  have hbr : (q + B) ^ B ≤ r := le_add_of_nonneg_left hq
  obtain ⟨Ex⟩ := hslice W i j 0 (a 1)
  obtain ⟨Ey⟩ := hslice W i j 1 (a 0)
  change NativeIntegerExpansion (fun _ : Unit => 1) 1 q
    (fun x => W.antisymmetricKernel i j (x ()) (a 1)) at Ex
  change NativeIntegerExpansion (fun _ : Unit => 1) 1 q
    (fun x => W.antisymmetricKernel i j (a 0) (x ())) at Ey
  let Ex' := Ex.linearPullbackHom (fun _ : Unit =>
    ({ toFun := fun z : Fin 2 → ℤ => z 0, map_zero' := rfl, map_add' := fun _ _ => rfl }))
  let Ey' := Ey.linearPullbackHom (fun _ : Unit =>
    ({ toFun := fun z : Fin 2 → ℤ => z 1, map_zero' := rfl, map_add' := fun _ _ => rfl }))
  have Ec : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q
      (fun _ => W.antisymmetricKernel i j (a 0) (a 1)) := by
    simpa [integerAffineMap] using Ex.affinePullback
      (fun (_ : Unit) (_ : Fin 2) => (0 : ℤ)) (fun _ => a 0)
  obtain ⟨E⟩ := hmul hq Ey'.conjugate Ex'.conjugate
  obtain ⟨F⟩ := hmul hr (E.mono hbr) (Ec.mono hqr)
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [R, Q, X, r, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedInverseIntervals
namespace OAI

section

namespace Erdos3.NativeDegreeRankDerivativeData

open scoped BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def toCorrelationStructure (hcor : p + 1 ≤ q) (hq : 2 ≤ q) :
    NativeCorrelationStructure s r N q f := by
  have hpq : p ≤ q := by linarith
  have hq0 : 0 ≤ q := by linarith
  refine {
    shifts := B.shifts
    nonempty := B.nonempty
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans B.density
    mixed := NativeMultidegreeNilcharacter.constOne (mixedCorrelationDegree s) hq0
    family := W.toFamily hpq
    correlation := ?_
  }
  intro h hh
  apply NativeVectorCorrelation.exists_of_mean (s - 1) N _ hq
  refine ⟨((0 : Fin 1), (0 : Fin (W.unit.tailDim + 1))), ?_⟩
  have hc := (Real.exp_le_exp.mpr (neg_le_neg hcor)).trans (W.toFamily_correlation hpq h hh)
  simpa only [nativeCorrelationResidual, NativeMultidegreeNilcharacter.constOne_evalCyclic,
    star_one, mul_one] using hc

end Erdos3.NativeDegreeRankDerivativeData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootCyclicComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixedRootCyclicCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (s + 2))) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (s + 2)) a).symm j)) = W.eval k x) →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + e + C) ^ C)
        (W.mixedRootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_mixedRootCornerCorrection_expansion s
  obtain ⟨B, _, hcyclic⟩ := exists_mixedCyclicDiagonalCorrection_expansion s
  let n := mixedRootTensorExponent s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.C (n + 1) * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget n p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : ((n + 1 : ℝ) * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    have hb : tensorPowerBudget n p ≤ (n + 1 : ℝ) * (v + 1) := by
      unfold tensorPowerBudget
      exact mul_le_mul_of_nonneg_left (by dsimp [v]; linarith) (by positivity)
    dsimp only [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.mixedIntegrationRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.mixedRootCornerCorrection G) (hroot W hq hsymm G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {d : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

theorem mixedPrimitiveFactor_norm {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (i : Fin W.outputDim) (n : ZMod N) :
    ‖W.mixedPrimitiveFactor f i n‖ ≤ 1 := by
  rw [mixedPrimitiveFactor, norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)).trans (by
    simpa only [one_mul] using W.norm_eval _ _)

theorem mixedPrimitiveFactor_cross {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (h n : ZMod N) :
    multiplicativeDerivative f h n * W.mixedCyclicDiagonalDerivative a ![h, n] =
      W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h)) := by
  simp only [multiplicativeDerivative, mixedCyclicDiagonalDerivative, mixedPrimitiveFactor,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_mul]
  rw [add_comm h n]
  ring

end NativeMultidegreeNilcharacter

namespace NativeMixedCorrelation

variable {d : ℕ} {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation (d + 2) N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedPrimitiveRow (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) : ℂ :=
  (W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h))) *
    W.mixedMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)] *
      star (M.residualMultiplier h (fun _ => (n.val : ℤ)))

theorem mixedPrimitiveRow_eq (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) :
    M.mixedPrimitiveRow W a b h n = M.normalizedResidualRow h n *
      (W.mixedCyclicDiagonalDerivative a ![h, n] *
        W.mixedMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)]) := by
  rw [mixedPrimitiveRow, M.normalizedResidualRow_factor, ← W.mixedPrimitiveFactor_cross f a h n]
  ring

end NativeMixedCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

variable {d : ℕ} {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation (d + 2) N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

theorem mixedPrimitiveRow_cross_residual (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) :
    M.mixedPrimitiveRow W a b h n =
      (W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h))) *
        star (M.mixedResidualRowFactor W b h (fun _ => (n.val : ℤ))) := by
  simp only [mixedPrimitiveRow, mixedResidualRowFactor, star_mul, star_star]
  ring

theorem exists_mixedResidualRowFactor_expansion (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
      (M : NativeMixedCorrelation (d + 2) N m f)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
      (b : (MixedMiddleCorner d → Fin W.outputDim)) (h : ZMod N),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (d + 1) ((m + p + C) ^ C)
        (M.mixedResidualRowFactor W b h)) := by
  obtain ⟨A, _, hmiddle⟩ := NativeMultidegreeNilcharacter.exists_mixedMiddleTensor_row_expansion d
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro m p N _ f M W b h
  have hm : 0 ≤ m := (Nat.cast_nonneg M.mixed.dim).trans M.mixed.complexity.1.1
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := m + p + (m + p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hmt : m ≤ t := by
    have hpow : 0 ≤ (m + p + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ m + p + A by linarith) A).trans
    exact le_add_of_nonneg_left (add_nonneg hm hp)
  obtain ⟨F⟩ := hmul ht ((Classical.choice (M.residualMultiplier_expansion h)).mono hmt)
    ((Classical.choice (hmiddle W h.val b)).conjugate.mono hAt)
  have hcost : (t + B) ^ B ≤ (m + p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (m + p) (add_nonneg hm hp)
  exact ⟨F.mono hcost⟩

end NativeMixedCorrelation

end Erdos3

end

end OAI
end


