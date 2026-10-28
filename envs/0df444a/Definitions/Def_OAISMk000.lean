-- Prove2me | Definitions.Def_OAISMk000
-- name    : OAISMk000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:38:48.668996+00:00
-- url     : https://prove2.me/theorems/e6afdca6-2e0d-4032-9959-47afb5cd9725
-- title:
--   Definitions bundle OAISMk000 of the split of OpenAI, Nontrivial Markov Type Forces Superreflexivity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm`, carved from OpenAI's openai/math development (OpenAI, *Nontrivial Markov Type Forces Superreflexivity*, OpenAI Math Release, September 23, 2026, result family 327, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 847 declarations of OpenAI's Lean: 345 definitions, 13 inductive types or structures, 22 instances and 467 theorems. The definitions and types are `OAI.MarkovSuperreflexivity.AmbientJConvex`, `OAI.MarkovSuperreflexivity.ApproximateTailSystem`, `OAI.MarkovSuperreflexivity.ApproximateTailSystem.exactHalf`, `OAI.MarkovSuperreflexivity.C00`, `OAI.MarkovSuperreflexivity.C00.SupportedBelow`, `OAI.MarkovSuperreflexivity.C00.alternating`, `OAI.MarkovSuperreflexivity.C00.alternatingArray`, `OAI.MarkovSuperreflexivity.C00.alternatingEven`, `OAI.MarkovSuperreflexivity.C00.alternatingOdd`, `OAI.MarkovSuperreflexivity.C00.alternatingPlacement`, `OAI.MarkovSuperreflexivity.C00.arrayLinear`, `OAI.MarkovSuperreflexivity.C00.basis`, `OAI.MarkovSuperreflexivity.C00.blockIndex`, `OAI.MarkovSuperreflexivity.C00.blockOffset`, `OAI.MarkovSuperreflexivity.C00.collapseAtPair`, `OAI.MarkovSuperreflexivity.C00.collapseTail`, `OAI.MarkovSuperreflexivity.C00.endpointAlternating`, `OAI.MarkovSuperreflexivity.C00.jColumn`, `OAI.MarkovSuperreflexivity.C00.l1Mass`, `OAI.MarkovSuperreflexivity.C00.mergeAt`, `OAI.MarkovSuperreflexivity.C00.mergeIndex`, `OAI.MarkovSuperreflexivity.C00.ofArray`, `OAI.MarkovSuperreflexivity.C00.pairLinear`, `OAI.MarkovSuperreflexivity.C00.place`, `OAI.MarkovSuperreflexivity.C00.placeLinear`, `OAI.MarkovSuperreflexivity.C00.shift`, `OAI.MarkovSuperreflexivity.C00.skipAfter`, `OAI.MarkovSuperreflexivity.C00.subdivide`, `OAI.MarkovSuperreflexivity.C00.uniformArrayMap`, `OAI.MarkovSuperreflexivity.C00.uniformBlockLift`, `OAI.MarkovSuperreflexivity.C00.uniformSubdivision`, `OAI.MarkovSuperreflexivity.CancelPair`, `OAI.MarkovSuperreflexivity.CanonicallyReflexive`, `OAI.MarkovSuperreflexivity.Chart`, `OAI.MarkovSuperreflexivity.Chart.Good`, `OAI.MarkovSuperreflexivity.CoefficientBasic`, `OAI.MarkovSuperreflexivity.CoefficientMonotone`, `OAI.MarkovSuperreflexivity.CoordinateSpace`, `OAI.MarkovSuperreflexivity.CoordinateSpace.coefficients`, `OAI.MarkovSuperreflexivity.CoordinatesRepresentable` and 318 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/MarkovType, in whole or in part: `MarkovType_AlternatingNorm`, `MarkovType_AntitoneSeminormLimit`, `MarkovType_C00FiniteCoordinates`, `MarkovType_ChartPathProbability`, `MarkovType_ChartTransport`, `MarkovType_CoefficientBasic`, `MarkovType_CoefficientConsecutiveBlocks`, `MarkovType_CoefficientGrid`, `MarkovType_CoefficientSequenceOps`, `MarkovType_CubeNotJConvex`, `MarkovType_DyadicBellman`, `MarkovType_DyadicBlockCoordinates`, `MarkovType_DyadicConvexPotential`, `MarkovType_DyadicIndependentBlocks`, `MarkovType_DyadicInterpolation`, `MarkovType_DyadicSmoothRenorming`, `MarkovType_DyadicTree`, `MarkovType_DyadicTreeMartingale`, `MarkovType_DyadicWeakAmplification`, `MarkovType_DyadicWeakMaxDefinition`, `MarkovType_DyadicWeakType`, `MarkovType_EndNorm`, `MarkovType_FailureJApproximation`, `MarkovType_FailureJTriangular`, `MarkovType_FiniteBoundedEnergy`, `MarkovType_FiniteCharts`, `MarkovType_FiniteConditionalAverage`, `MarkovType_FiniteConditionalMartingale`, `MarkovType_FiniteCoupling`, `MarkovType_FiniteDyadicMartingale`, `MarkovType_FiniteDyadicProbability`, `MarkovType_FiniteFirstCrossing`, `MarkovType_FiniteGeometricBands`, `MarkovType_FiniteGoldstine`, `MarkovType_FiniteIndependentCopies`, `MarkovType_FiniteL2CoefficientAdapter`, `MarkovType_FiniteMarcinkiewicz`, `MarkovType_FiniteMartingaleBasic`, `MarkovType_FiniteMartingaleTransport`, `MarkovType_FiniteMatching`, `MarkovType_FinitePowerIntegrals`, `MarkovType_FinitePredictableSelection`, `MarkovType_FinitePredictableTransform`, `MarkovType_FiniteProbability`, `MarkovType_FiniteRamsey`, `MarkovType_FiniteSelectionCompression`, `MarkovType_FiniteSelectionCounter`, `MarkovType_FiniteSeparation`, `MarkovType_FiniteSmoothMoments`, `MarkovType_FiniteStoppingTime`, `MarkovType_FiniteTailCorrection`, `MarkovType_FiniteWalkCoordinates`, `MarkovType_FiniteWalkWitness`, `MarkovType_FinitelyRepresentable`, `MarkovType_FourLetters`, `MarkovType_HomogeneousPotential`, `MarkovType_IntegerCocycle`, `MarkovType_InterleavedCuts`, `MarkovType_JConvexityBasic`, `MarkovType_LatticeCubes`, `MarkovType_LatticeLift`, `MarkovType_LatticePaths`, `MarkovType_MarkedChains`, `MarkovType_MarkedLetters`, `MarkovType_MarkedPaths`, `MarkovType_MarkovTransport`, `MarkovType_MidpointPotential`, `MarkovType_NormCompression`, `MarkovType_NormedC00`, `MarkovType_OrbitDisplacement`, `MarkovType_OrderedBoundedCubes`, `MarkovType_OrderedCoordinates`, `MarkovType_OrderedJColumns`, `MarkovType_OrderedNorm`, `MarkovType_OrderedSequences`, `MarkovType_PeriodicArcs`, `MarkovType_PeriodicOrderIso`, `MarkovType_PowerRenormingFromDyadic`, `MarkovType_PrefixBlocks`, `MarkovType_PrefixIndicators`, `MarkovType_Renormed`, `MarkovType_RenormingBasic`, `MarkovType_ReversibleMartingales`, `MarkovType_ScalarUltralimit`, `MarkovType_SelectedRows`, `MarkovType_SeminormUltralimit`, `MarkovType_SequenceL2JConvex`, `MarkovType_SmoothnessBounds`, `MarkovType_SpreadingLimit`, `MarkovType_SpreadingLimitReal`, `MarkovType_SpreadingModel`, `MarkovType_SubdivisionAverage`, `MarkovType_SubdivisionInvariantBlocks`, `MarkovType_SubdivisionLimit`, `MarkovType_SubdivisionMergeConvex`, `MarkovType_SubdivisionMergeCoordinates`, `MarkovType_SubdivisionNearIsometry`, `MarkovType_SubdivisionOperators`, `MarkovType_SubdivisionOrderedNorm`, `MarkovType_SubdivisionProfileDefs`, `MarkovType_SubdivisionProfileExpansion`, `MarkovType_SubdivisionProfiles`, `MarkovType_SubdivisionSameSign`, `MarkovType_SubdivisionSpreading`, `MarkovType_TriangularArrays`, `MarkovType_TriangularBasic`, `MarkovType_TriangularCompletion`, `MarkovType_TriangularLimitSeminorm`, `MarkovType_TriangularPrefix`, `MarkovType_TriangularTransport`, `MarkovType_WalkDrift`, `MarkovType_WalkLandmarks`, `MarkovType_WalkMarkedDisplacement`, `MarkovType_WalkParameters`, `MarkovType_WalkTransport`, `MarkovType_WeightedEvents`, `MarkovType_WordAction`, `MarkovType_WordReduction`.
--
--   **Imports.** It imports the published bundle `Def_MarkovType`.
--
--   **Imported by** (directly, in this split): the bundle `OAISMk002`; the statements `OAI.MarkovSuperreflexivity.FiniteTriangularObstruction.sequenceL2`, `OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable`, `OAI.MarkovSuperreflexivity.exists_power_smooth_equivalentNorm`, `OAI.MarkovSuperreflexivity.finiteTriangularObstruction_of_hasEquivalentUCNorm` and `OAI.MarkovSuperreflexivity.hasEquivalentUCNorm_of_finiteTriangularObstruction`.
-- source:
--   OpenAI, Nontrivial Markov Type Forces Superreflexivity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 327; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/MarkovType at commit adc7f12

import Mathlib
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType

section
-- module Solutions.OAIS_Markov.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

abbrev C00 := ℕ →₀ ℝ

namespace C00

def basis (i : ℕ) : C00 := Finsupp.single i 1

def place {m : ℕ} (ι : Fin m → ℕ) (a : Fin m → ℝ) : C00 :=
  ∑ i, Finsupp.single (ι i) (a i)

def ofArray {m : ℕ} (a : Fin m → ℝ) : C00 := place Fin.val a

def placeLinear {m : ℕ} (ι : Fin m → ℕ) : (Fin m → ℝ) →ₗ[ℝ] C00 where
  toFun := place ι
  map_add' a b := by
    simp only [place, Pi.add_apply, Finsupp.single_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [place, Pi.smul_apply, Finset.smul_sum, Finsupp.smul_single, RingHom.id_apply]

def arrayLinear (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] C00 := placeLinear Fin.val

@[simp] theorem placeLinear_apply {m : ℕ} (ι : Fin m → ℕ) (a : Fin m → ℝ) :
    placeLinear ι a = place ι a := rfl

@[simp] theorem arrayLinear_apply {m : ℕ} (a : Fin m → ℝ) :
    arrayLinear m a = ofArray a := rfl

@[simp] theorem ofArray_apply {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    ofArray a i.val = a i := by
  classical
  simp only [ofArray, place, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hval]
  · simp

theorem ofArray_injective (m : ℕ) : Function.Injective (@ofArray m) := by
  intro a b h
  funext i
  simpa only [ofArray_apply] using congrArg (fun x : C00 => x i.val) h

def mergeIndex (i j : ℕ) : ℕ := if j ≤ i then j else j - 1

def mergeAt (i : ℕ) (x : C00) : C00 := Finsupp.mapDomain (mergeIndex i) x

@[simp] theorem mergeAt_zero (i : ℕ) : mergeAt i 0 = 0 := by
  simp [mergeAt]

@[simp] theorem mergeAt_single (i j : ℕ) (a : ℝ) :
    mergeAt i (Finsupp.single j a) = Finsupp.single (mergeIndex i j) a := by
  exact Finsupp.mapDomain_single

end C00

def prefixCut (x : C00) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, x i

@[simp] theorem prefixCut_zero (x : C00) : prefixCut x 0 = 0 := by
  simp [prefixCut]

theorem prefixCut_succ (x : C00) (k : ℕ) :
    prefixCut x (k + 1) = prefixCut x k + x k := by
  exact Finset.sum_range_succ (fun i => x i) k

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

structure OrderedNorm where
  toSeminorm : Seminorm ℝ C00
  definite : ∀ x, toSeminorm x = 0 → x = 0
  spreading : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
    ∀ a : Fin m → ℝ, toSeminorm (C00.place ι a) = toSeminorm (C00.ofArray a)
  merge_le : ∀ (i : ℕ) (x : C00), toSeminorm (C00.mergeAt i x) ≤ toSeminorm x

namespace OrderedNorm

instance instCoeFunForallC00Real : CoeFun OrderedNorm (fun _ => C00 → ℝ) := ⟨fun N => N.toSeminorm⟩

@[simp] theorem coe_toSeminorm (N : OrderedNorm) (x : C00) :
    N.toSeminorm x = N x := rfl

@[simp] theorem map_zero (N : OrderedNorm) : N 0 = 0 :=
  N.toSeminorm.map_zero'

theorem nonneg (N : OrderedNorm) (x : C00) : 0 ≤ N x :=
  apply_nonneg N.toSeminorm x

@[simp] theorem eq_zero_iff (N : OrderedNorm) (x : C00) : N x = 0 ↔ x = 0 :=
  ⟨N.definite x, fun h => h ▸ N.map_zero⟩

theorem add_le (N : OrderedNorm) (x y : C00) : N (x + y) ≤ N x + N y :=
  N.toSeminorm.add_le' x y

@[simp] theorem neg (N : OrderedNorm) (x : C00) : N (-x) = N x :=
  N.toSeminorm.neg' x

@[simp] theorem smul (N : OrderedNorm) (r : ℝ) (x : C00) :
    N (r • x) = |r| * N x := by

  rw [map_smul_eq_mul, Real.norm_eq_abs]

end OrderedNorm

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

def CoordinatesRepresentable (N : OrderedNorm) : Prop :=
  ∀ (m : ℕ) (ε : ℝ), 0 < ε →
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
      N (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + ε) * N (C00.ofArray a)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_AlternatingNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def alternating (k : ℕ) : C00 :=
  ∑ j ∈ Finset.range k, (basis (2 * j) - basis (2 * j + 1))

def alternatingArray (k : ℕ) (i : Fin (2 * k)) : ℝ := (-1) ^ i.val

def alternatingEven {k : ℕ} (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

def alternatingOdd {k : ℕ} (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩

@[simp] theorem alternating_zero : alternating 0 = 0 := by
  simp [alternating]

@[simp] theorem alternating_one : alternating 1 = basis 0 - basis 1 := by
  simp [alternating]

@[simp] theorem alternatingArray_even {k : ℕ} (j : Fin k) :
    alternatingArray k (alternatingEven j) = 1 := by
  simp [alternatingArray, alternatingEven, pow_mul]

@[simp] theorem alternatingArray_odd {k : ℕ} (j : Fin k) :
    alternatingArray k (alternatingOdd j) = -1 := by
  simp [alternatingArray, alternatingOdd, pow_add, pow_mul]

def shift (t : ℕ) (x : C00) : C00 :=
  Finsupp.mapDomain.addMonoidHom (fun i => t + i) x

@[simp] theorem shift_zero (t : ℕ) : shift t 0 = 0 := by
  exact map_zero (Finsupp.mapDomain.addMonoidHom (fun i => t + i))

@[simp] theorem shift_basis (t i : ℕ) : shift t (basis i) = basis (t + i) := by
  simp [shift, basis]

def alternatingPlacement {k : ℕ} (lo hi : Fin k → ℕ)
    (i : Fin (2 * k)) : ℕ :=
  if i.val % 2 = 0 then
    lo ⟨i.val / 2, by have := i.isLt; omega⟩
  else
    hi ⟨i.val / 2, by have := i.isLt; omega⟩

@[simp] theorem alternatingPlacement_even {k : ℕ} (lo hi : Fin k → ℕ)
    (j : Fin k) :
    alternatingPlacement lo hi (alternatingEven j) = lo j := by
  have hbound : 2 * j.val / 2 < k := by
    have := j.isLt
    omega
  change (if 2 * j.val % 2 = 0 then
    lo ⟨2 * j.val / 2, hbound⟩ else
    hi ⟨2 * j.val / 2, hbound⟩) = lo j
  calc
    _ = lo ⟨2 * j.val / 2, hbound⟩ := ite_eq_left (by omega)
    _ = lo j := by
      apply congrArg lo
      apply Fin.ext
      change 2 * j.val / 2 = j.val
      omega

@[simp] theorem alternatingPlacement_odd {k : ℕ} (lo hi : Fin k → ℕ)
    (j : Fin k) :
    alternatingPlacement lo hi (alternatingOdd j) = hi j := by
  have hbound : (2 * j.val + 1) / 2 < k := by
    have := j.isLt
    omega
  change (if (2 * j.val + 1) % 2 = 0 then
    lo ⟨(2 * j.val + 1) / 2, hbound⟩ else
    hi ⟨(2 * j.val + 1) / 2, hbound⟩) = hi j
  calc
    _ = hi ⟨(2 * j.val + 1) / 2, hbound⟩ := ite_eq_right (by omega)
    _ = hi j := by
      apply congrArg hi
      apply Fin.ext
      change (2 * j.val + 1) / 2 = j.val
      omega

end C00

namespace OrderedNorm

def alternatingNorm (N : OrderedNorm) (k : ℕ) : ℝ := N (C00.alternating k)

@[simp] theorem alternatingNorm_zero (N : OrderedNorm) :
    N.alternatingNorm 0 = 0 := by
  simp [alternatingNorm]

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_AntitoneSeminormLimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity.SeminormLimit

def value (p : ℕ → Seminorm ℝ C00) (x : C00) : ℝ := ⨅ n, p n x

theorem boundedBelow (p : ℕ → Seminorm ℝ C00) (x : C00) :
    BddBelow (Set.range fun n => p n x) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact apply_nonneg (p n) x

theorem tendsto_value (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) :
    Tendsto (fun n => p n x) atTop (𝓝 (value p x)) :=
  tendsto_atTop_ciInf (ha x) (boundedBelow p x)

def seminorm (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) : Seminorm ℝ C00 :=
  Seminorm.of (value p)
    (fun x y => le_of_tendsto_of_tendsto'
      (tendsto_value p ha (x + y))
      ((tendsto_value p ha x).add (tendsto_value p ha y))
      (fun n => (p n).add_le' x y))
    (fun r x => tendsto_nhds_unique
      (tendsto_value p ha (r • x))
      (by
        simpa only [map_smul_eq_mul] using
          (tendsto_const_nhds.mul (tendsto_value p ha x) :
            Tendsto (fun n => ‖r‖ * p n x) atTop (𝓝 (‖r‖ * value p x)))))

@[simp] theorem seminorm_apply (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) :
    seminorm p ha x = value p x := rfl

theorem seminorm_le (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) (n : ℕ) :
    seminorm p ha x ≤ p n x :=
  ciInf_le (boundedBelow p x) n

theorem lower_bound (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) {b : ℝ}
    (h : ∀ n, b ≤ p n x) : b ≤ seminorm p ha x :=
  ge_of_tendsto' (tendsto_value p ha x) h

theorem upper_bound (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) {b : ℝ}
    (h : ∀ n, p n x ≤ b) : seminorm p ha x ≤ b :=
  le_of_tendsto' (tendsto_value p ha x) h

theorem spreading (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x)
    (hs : ∀ n, ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a, p n (C00.place ι a) = p n (C00.ofArray a))
    {m : ℕ} (ι : Fin m → ℕ) (hι : StrictMono ι) (a : Fin m → ℝ) :
    seminorm p ha (C00.place ι a) = seminorm p ha (C00.ofArray a) := by
  change (⨅ n, p n (C00.place ι a)) = ⨅ n, p n (C00.ofArray a)
  congr 1
  funext n
  exact hs n ι hι a

theorem prefix_lower (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (d : ℝ)
    (hl : ∀ n x k, d * |prefixCut x k| ≤ p n x) (x : C00) (k : ℕ) :
    d * |prefixCut x k| ≤ seminorm p ha x :=
  lower_bound p ha x (fun n => hl n x k)

theorem definite (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) {d : ℝ} (hd : 0 < d)
    (hl : ∀ n x k, d * |prefixCut x k| ≤ p n x)
    (x : C00) (hx : seminorm p ha x = 0) : x = 0 := by
  have hp (k : ℕ) : prefixCut x k = 0 := by
    have h := prefix_lower p ha d hl x k
    rw [hx] at h
    have hz : |prefixCut x k| ≤ 0 := by nlinarith
    exact abs_nonpos_iff.mp hz
  ext i
  have h := prefixCut_succ x i
  rw [hp (i + 1), hp i] at h
  simpa only [zero_add, Finsupp.zero_apply] using h.symm

end MarkovSuperreflexivity.SeminormLimit

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_C00FiniteCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem ofArray_apply_of_ge {m : ℕ} (a : Fin m → ℝ) (j : ℕ) (hj : m ≤ j) :
    ofArray a j = 0 := by
  classical
  simp only [ofArray, place, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hne : i.val ≠ j := Nat.ne_of_lt (lt_of_lt_of_le i.isLt hj)
  simp only [Finsupp.single_apply, ite_eq_right hne]

theorem ofArray_of_vanishes (x : C00) (B : ℕ)
    (hx : ∀ k, B ≤ k → x k = 0) :
    ofArray (fun i : Fin B => x i.val) = x := by
  ext k
  by_cases hk : k < B
  · exact ofArray_apply (fun i : Fin B => x i.val) ⟨k, hk⟩
  · have hBk : B ≤ k := Nat.le_of_not_gt hk
    rw [ofArray_apply_of_ge _ k hBk, hx k hBk]

theorem exists_ofArray (x : C00) :
    ∃ m : ℕ, ∃ a : Fin m → ℝ, ofArray a = x := by
  classical
  let m := (x.support.sup id).succ
  refine ⟨m, (fun i => x i.val), ?_⟩
  ext j
  by_cases hj : j < m
  · exact ofArray_apply (fun i : Fin m => x i.val) ⟨j, hj⟩
  · have hmj : m ≤ j := Nat.le_of_not_gt hj
    rw [ofArray_apply_of_ge _ j hmj]
    symm
    apply Finsupp.notMem_support_iff.mp
    intro hs
    have hlt : j < m :=
      Finset.mem_range.mp (Finset.subset_range_sup_succ x.support hs)
    exact hj hlt

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

structure FiniteCoupling {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) where
  weight : A → B → ℝ
  nonneg : ∀ a b, 0 ≤ weight a b
  row_sum : ∀ a, ∑ b, weight a b = p a
  col_sum : ∀ b, ∑ a, weight a b = q b

namespace FiniteCoupling

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable {p : A → ℝ} {q : B → ℝ}

theorem weight_le_row (k : FiniteCoupling p q) (a : A) (b : B) :
    k.weight a b ≤ p a := by
  rw [← k.row_sum a]
  exact Finset.single_le_sum (fun j _ => k.nonneg a j) (Finset.mem_univ b)

theorem weight_le_col (k : FiniteCoupling p q) (a : A) (b : B) :
    k.weight a b ≤ q b := by
  rw [← k.col_sum b]
  exact Finset.single_le_sum (fun i _ => k.nonneg i b) (Finset.mem_univ a)

theorem weight_eq_zero_of_row (k : FiniteCoupling p q) {a : A}
    (h : p a = 0) (b : B) : k.weight a b = 0 :=
  le_antisymm (h ▸ k.weight_le_row a b) (k.nonneg a b)

theorem weight_eq_zero_of_col (k : FiniteCoupling p q) (a : A) {b : B}
    (h : q b = 0) : k.weight a b = 0 :=
  le_antisymm (h ▸ k.weight_le_col a b) (k.nonneg a b)

def transpose (k : FiniteCoupling p q) : FiniteCoupling q p where
  weight b a := k.weight a b
  nonneg b a := k.nonneg a b
  row_sum := k.col_sum
  col_sum := k.row_sum

def average (k l : FiniteCoupling p q) : FiniteCoupling p q where
  weight a b := (k.weight a b + l.weight a b) / 2
  nonneg a b := div_nonneg (add_nonneg (k.nonneg a b) (l.nonneg a b)) (by norm_num)
  row_sum a := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, k.row_sum, l.row_sum]
    ring
  col_sum b := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, k.col_sum, l.col_sum]
    ring

end FiniteCoupling

def finitePushforward {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (t : T) : ℝ :=
  ∑ a, if f a = t then p a else 0

theorem finitePushforward_nonneg {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (t : T) :
    0 ≤ finitePushforward p f t := by
  classical
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

theorem finitePushforward_sum {A : Type u} {T : Type v} [Fintype A] [Fintype T]
    (p : A → ℝ) (f : A → T) : ∑ t, finitePushforward p f t = ∑ a, p a := by
  classical
  simp only [finitePushforward]
  rw [Finset.sum_comm]
  simp

theorem weight_le_finitePushforward {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (a : A) :
    p a ≤ finitePushforward p f (f a) := by
  classical
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun b => if f b = f a then p b else 0)
    (fun b _ => by
      change 0 ≤ if f b = f a then p b else 0
      split_ifs
      · exact hp b
      · exact le_rfl) (Finset.mem_univ a)
  simpa [finitePushforward] using h

def finiteTotalVariation {A : Type u} [Fintype A] (p q : A → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

def finiteOverlap {A : Type u} (p q : A → ℝ) (a : A) : ℝ := min (p a) (q a)

def finiteResidualMass {A : Type u} [Fintype A] (p q : A → ℝ) : ℝ :=
  1 - ∑ a, finiteOverlap p q a

theorem residual_left_sum {A : Type u} [Fintype A] (p q : A → ℝ)
    (hp : ∑ a, p a = 1) :
    ∑ a, (p a - finiteOverlap p q a) = finiteResidualMass p q := by
  rw [Finset.sum_sub_distrib, hp]
  rfl

theorem residual_right_sum {A : Type u} [Fintype A] (p q : A → ℝ)
    (hq : ∑ a, q a = 1) :
    ∑ a, (q a - finiteOverlap p q a) = finiteResidualMass p q := by
  rw [Finset.sum_sub_distrib, hq]
  rfl

theorem finiteResidualMass_nonneg {A : Type u} [Fintype A] (p q : A → ℝ)
    (hp : ∑ a, p a = 1) : 0 ≤ finiteResidualMass p q := by
  rw [← residual_left_sum p q hp]
  exact Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (min_le_left _ _))

def maximalFiniteCouplingWeight {A : Type u} [Fintype A]
    (p q : A → ℝ) (a b : A) : ℝ :=
  (if a = b then finiteOverlap p q a else 0) +
    (p a - finiteOverlap p q a) * (q b - finiteOverlap p q b) /
      finiteResidualMass p q

theorem maximalFiniteCouplingWeight_nonneg {A : Type u} [Fintype A]
    {p q : A → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (a b : A) :
    0 ≤ maximalFiniteCouplingWeight p q a b := by
  classical
  apply add_nonneg
  · split_ifs
    · exact le_min (hp a) (hq a)
    · exact le_rfl
  · exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
        (sub_nonneg.mpr (min_le_right _ _)))
      (finiteResidualMass_nonneg p q hpsum)

theorem maximalFiniteCouplingWeight_row {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) (a : A) :
    ∑ b, maximalFiniteCouplingWeight p q a b = p a := by
  classical
  have hrow : ∑ b, maximalFiniteCouplingWeight p q a b =
      finiteOverlap p q a + (p a - finiteOverlap p q a) *
        finiteResidualMass p q / finiteResidualMass p q := by
    simp only [maximalFiniteCouplingWeight, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.mul_sum, residual_right_sum p q hq]
    simp
  rw [hrow]
  by_cases hd : finiteResidualMass p q = 0
  · have ha : p a - finiteOverlap p q a = 0 := by
      apply le_antisymm _ (sub_nonneg.mpr (min_le_left _ _))
      have hle := Finset.single_le_sum
        (fun b (_ : b ∈ (Finset.univ : Finset A)) =>
          sub_nonneg.mpr (min_le_left (p b) (q b))) (Finset.mem_univ a)
      change p a - finiteOverlap p q a ≤ ∑ b, (p b - finiteOverlap p q b) at hle
      rw [residual_left_sum p q hp, hd] at hle
      exact hle
    rw [hd]
    simp only [mul_zero, zero_div, add_zero]
    linarith
  · rw [mul_div_cancel_right₀ _ hd]
    ring

theorem maximalFiniteCouplingWeight_transpose {A : Type u} [Fintype A]
    (p q : A → ℝ) (a b : A) :
    maximalFiniteCouplingWeight q p b a = maximalFiniteCouplingWeight p q a b := by
  classical
  have hover : finiteResidualMass q p = finiteResidualMass p q := by
    simp only [finiteResidualMass, finiteOverlap, min_comm]
  simp only [maximalFiniteCouplingWeight, hover, finiteOverlap]
  by_cases hab : a = b
  · subst b
    simp only [min_comm]
    ring
  · simp only [ite_eq_right hab, ite_eq_right (Ne.symm hab), min_comm, zero_add]
    ring

def maximalFiniteCoupling {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) : FiniteCoupling p q where
  weight := maximalFiniteCouplingWeight p q
  nonneg := maximalFiniteCouplingWeight_nonneg hp hq hpsum
  row_sum := maximalFiniteCouplingWeight_row p q hpsum hqsum
  col_sum b := by
    simp_rw [← maximalFiniteCouplingWeight_transpose p q]
    exact maximalFiniteCouplingWeight_row q p hqsum hpsum b

def finiteConditional {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (t : T) (a : A) : ℝ :=
  if finitePushforward p f t = 0 then p a
  else if f a = t then p a / finitePushforward p f t else 0

theorem finiteConditional_nonneg {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (t : T) (a : A) :
    0 ≤ finiteConditional p f t a := by
  classical
  unfold finiteConditional
  split_ifs
  · exact hp a
  · exact div_nonneg (hp a) (finitePushforward_nonneg hp f t)
  · exact le_rfl

theorem finiteConditional_sum {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (hpsum : ∑ a, p a = 1) (t : T) :
    ∑ a, finiteConditional p f t a = 1 := by
  classical
  by_cases ht : finitePushforward p f t = 0
  · simpa [finiteConditional, ht] using hpsum
  · simp only [finiteConditional, ht, ite_false]
    have hterm (a : A) :
        (if f a = t then p a / finitePushforward p f t else 0) =
        (if f a = t then p a else 0) / finitePushforward p f t := by
      split_ifs <;> simp
    simp_rw [hterm]
    rw [← Finset.sum_div]
    exact div_self ht

theorem finiteConditional_weighted {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (t : T) (a : A) :
    finitePushforward p f t * finiteConditional p f t a =
      if f a = t then p a else 0 := by
  classical
  by_cases ht : finitePushforward p f t = 0
  · have hzero : f a = t → p a = 0 := by
      intro ha
      have hle := weight_le_finitePushforward hp f a
      rw [ha, ht] at hle
      exact le_antisymm hle (hp a)
    by_cases ha : f a = t
    · simp [finiteConditional, ht, ha, hzero ha]
    · simp [finiteConditional, ht, ha]
  · by_cases ha : f a = t
    · simp only [finiteConditional, ht, ite_false, ite_eq_left ha]
      field_simp
    · simp [finiteConditional, ht, ha]

theorem finiteConditional_reconstruct {A : Type u} {T : Type v}
    [Fintype A] [Fintype T] {p : A → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → T) (a : A) :
    ∑ t, finitePushforward p f t * finiteConditional p f t a = p a := by
  classical
  simp_rw [finiteConditional_weighted hp]
  simp

def liftFiniteCouplingWeight {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g))
    (a : A) (b : B) : ℝ :=
  ∑ t, ∑ u, k.weight t u * finiteConditional p f t a * finiteConditional q g u b

def liftFiniteCoupling {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g)) :
    FiniteCoupling p q where
  weight := liftFiniteCouplingWeight p q f g k
  nonneg a b := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun u _ =>
    mul_nonneg (mul_nonneg (k.nonneg t u) (finiteConditional_nonneg hp f t a))
      (finiteConditional_nonneg hq g u b)
  row_sum a := by
    unfold liftFiniteCouplingWeight
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, ∑ u, ∑ b,
          k.weight t u * finiteConditional p f t a * finiteConditional q g u b := by
        apply Finset.sum_congr rfl
        intro t _
        exact Finset.sum_comm
      _ = ∑ t, ∑ u, k.weight t u * finiteConditional p f t a := by
        simp_rw [← Finset.mul_sum, finiteConditional_sum q g hqsum, mul_one]
      _ = ∑ t, finitePushforward p f t * finiteConditional p f t a := by
        simp_rw [← Finset.sum_mul, k.row_sum]
      _ = p a := finiteConditional_reconstruct hp f a
  col_sum b := by
    unfold liftFiniteCouplingWeight
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, ∑ u, ∑ a,
          k.weight t u * finiteConditional p f t a * finiteConditional q g u b := by
        apply Finset.sum_congr rfl
        intro t _
        exact Finset.sum_comm
      _ = ∑ t, ∑ u, k.weight t u * finiteConditional q g u b := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum,
          finiteConditional_sum p f hpsum, mul_one]
      _ = ∑ u, ∑ t, k.weight t u * finiteConditional q g u b := Finset.sum_comm
      _ = ∑ u, finitePushforward q g u * finiteConditional q g u b := by
        simp_rw [← Finset.sum_mul, k.col_sum]
      _ = q b := finiteConditional_reconstruct hq g b

def maximalFeatureCoupling {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1) : FiniteCoupling p q :=
  liftFiniteCoupling p q f g hp hq hpsum hqsum
    (maximalFiniteCoupling (finitePushforward p f) (finitePushforward q g)
      (finitePushforward_nonneg hp f) (finitePushforward_nonneg hq g)
      ((finitePushforward_sum p f).trans hpsum) ((finitePushforward_sum q g).trans hqsum))

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {ι κ : Type*} [sectionFintypeι : Fintype ι] [Fintype κ]

def finiteL1 (x : ι → ℝ) : ℝ := ∑ i, |x i|

@[simp] theorem finiteL1_zero : finiteL1 (0 : ι → ℝ) = 0 := by
  simp [finiteL1]

@[simp] theorem finiteL1_single [DecidableEq ι] (i : ι) (a : ℝ) :
    finiteL1 (Pi.single i a) = |a| := by
  classical
  unfold finiteL1
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [Pi.single_eq_of_ne hji]

def finiteMixtures (v : κ → ι → ℝ) : Set (ι → ℝ) :=
  {x | ∃ w : κ → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
    ∀ i, x i = ∑ j, w j * v j i}

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

abbrev Chart (Λ : Finset ℝ) (B : ℕ) := ↥Λ ↪o Fin B

noncomputable instance chartFintype (Λ : Finset ℝ) (B : ℕ) :
    Fintype (Chart Λ B) := by
  classical
  exact Fintype.ofInjective (fun C : Chart Λ B => (C : ↥Λ → Fin B))
    (by intro C D h; apply DFunLike.ext; intro x; exact congrFun h x)

namespace Chart

variable {Λ : Finset ℝ} {B : ℕ}

def Good (h : ℝ ≃o ℝ) (C C' : Chart Λ B) : Prop :=
  ∀ (x : ↥Λ) (hx : h (x : ℝ) ∈ Λ), C' x = C ⟨h (x : ℝ), hx⟩

end Chart

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteRamsey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

def FiniteRamseyBound.{u, v} {κ : Type v} (r : ℕ) (targets : κ → ℕ) (B : ℕ) : Prop :=
  ∀ (α : Type u) [DecidableEq α] (S : Finset α), B ≤ S.card →
    ∀ χ : Finset α → κ,
      ∃ i : κ, ∃ H : Finset α,
        H ⊆ S ∧ H.card = targets i ∧
          ∀ A : Finset α, A ⊆ H → A.card = r → χ A = i

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  sum_mass : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def expect (μ : FiniteLaw Ω) (F : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * F ω

def prob (μ : FiniteLaw Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then μ.mass ω else 0

def vexpect {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (μ : FiniteLaw Ω) (F : Ω → V) : V :=
  ∑ ω, μ.mass ω • F ω

@[simp] theorem expect_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.sum_mass, one_mul]

end FiniteLaw

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

structure FiniteMarkedChain (S E : Type*) [Fintype S] [Fintype E] where
  π : S → ℝ
  π_nonneg : ∀ s, 0 ≤ π s
  sum_π : ∑ s, π s = 1
  src : E → S
  tgt : E → S
  rev : E → E
  rev_rev : Function.Involutive rev
  src_rev : ∀ e, src (rev e) = tgt e
  tgt_rev : ∀ e, tgt (rev e) = src e
  q : E → ℝ
  q_nonneg : ∀ e, 0 ≤ q e
  sum_q : ∀ s, ∑ e, (if src e = s then q e else 0) = 1
  balance : ∀ e, π (src e) * q e = π (tgt e) * q (rev e)

abbrev MarkedPath (S E : Type*) (n : ℕ) := S × (Fin n → E)

def markedState {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) {n : ℕ} (ω : MarkedPath S E n)
    (i : Fin (n + 1)) : S :=
  if h : i = 0 then ω.1 else C.tgt (ω.2 (i.pred h))

def markedValid {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) {n : ℕ} (ω : MarkedPath S E n) : Prop :=
  ∀ i : Fin n, C.src (ω.2 i) = markedState C ω i.castSucc

def markedPathWeight {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) (n : ℕ) (ω : MarkedPath S E n) : ℝ := by
  classical
  exact if markedValid C ω then C.π ω.1 * ∏ i : Fin n, C.q (ω.2 i) else 0

def markedExpect {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) (n : ℕ) (F : MarkedPath S E n → ℝ) : ℝ :=
  ∑ ω, markedPathWeight C n ω * F ω

def markedProb {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) (n : ℕ) (A : MarkedPath S E n → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then markedPathWeight C n ω else 0

def edgeSum {S E V : Type*} [AddCommMonoid V] {n : ℕ}
    (g : E → V) (ω : MarkedPath S E n) : V :=
  ∑ i : Fin n, g (ω.2 i)

def OddLabel {S E V : Type*} [Fintype S] [Fintype E] [Neg V]
    (C : FiniteMarkedChain S E) (g : E → V) : Prop :=
  ∀ e, g (C.rev e) = -g e

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ChartTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

universe u v

namespace FiniteCoupling

variable {A : Type u} [Fintype A] {p : A → ℝ}

def eventMass (k : FiniteCoupling p p) (G : A → A → Prop) : ℝ :=
  ∑ a, ∑ b, if G a b then k.weight a b else 0

end FiniteCoupling

def symmetrizeFiniteCouplings {A : Type u} {L : Type v} [Fintype A]
    {p : A → ℝ} (inv : L → L) (Γ : ∀ _s : L, FiniteCoupling p p)
    (s : L) : FiniteCoupling p p :=
  (Γ s).average (Γ (inv s)).transpose

theorem symmetrizeFiniteCouplings_reverse {A : Type u} {L : Type v} [Fintype A]
    {p : A → ℝ} (inv : L → L) (hinv : Function.Involutive inv)
    (Γ : ∀ _s : L, FiniteCoupling p p) (s : L) (a b : A) :
    (symmetrizeFiniteCouplings inv Γ (inv s)).weight b a =
      (symmetrizeFiniteCouplings inv Γ s).weight a b := by
  simp only [symmetrizeFiniteCouplings, FiniteCoupling.average,
    FiniteCoupling.transpose, hinv s, add_comm]

def chartTransportDomain (Λ : Finset ℝ) (h : ℝ ≃o ℝ) : Finset ℝ :=
  Λ.filter (fun x => h x ∈ Λ)

def chartTransportDomainSource (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    ↥(chartTransportDomain Λ h) ↪o ↥Λ where
  toFun x := ⟨h (x : ℝ), (Finset.mem_filter.mp x.property).2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact h.injective (congrArg Subtype.val hxy)
  map_rel_iff' := by
    intro x y
    exact h.le_iff_le

def chartTransportDomainTarget (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    ↥(chartTransportDomain Λ h) ↪o ↥Λ where
  toFun x := ⟨(x : ℝ), (Finset.mem_filter.mp x.property).1⟩
  inj' := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : ↥Λ => (z : ℝ)) hxy)
  map_rel_iff' := Iff.rfl

def chartTransportSourceTuple (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    Fin (chartTransportDomain Λ h).card ↪o ↥Λ :=
  ((chartTransportDomain Λ h).orderIsoOfFin rfl).toOrderEmbedding.trans
    (chartTransportDomainSource Λ h)

def chartTransportTargetTuple (Λ : Finset ℝ) (h : ℝ ≃o ℝ) :
    Fin (chartTransportDomain Λ h).card ↪o ↥Λ :=
  ((chartTransportDomain Λ h).orderIsoOfFin rfl).toOrderEmbedding.trans
    (chartTransportDomainTarget Λ h)

def preliminaryChartCoupling {Λ : Finset ℝ} {B : ℕ}
    (ν : FiniteLaw (Chart Λ B)) (h : ℝ ≃o ℝ) :
    FiniteCoupling ν.mass ν.mass :=
  maximalFeatureCoupling ν.mass ν.mass
    (fun C => (chartTransportSourceTuple Λ h).trans C)
    (fun C => (chartTransportTargetTuple Λ h).trans C)
    ν.mass_nonneg ν.mass_nonneg ν.sum_mass ν.sum_mass

abbrev PositiveMassSupport {A : Type u} [Fintype A] (ν : FiniteLaw A) :=
  {a : A // 0 < ν.mass a}

theorem mass_zero_outside_positive_support {A : Type u} [Fintype A]
    (ν : FiniteLaw A) {a : A} (ha : ¬ 0 < ν.mass a) : ν.mass a = 0 :=
  le_antisymm (le_of_not_gt ha) (ν.mass_nonneg a)

theorem sum_positive_support {A : Type u} [Fintype A] (ν : FiniteLaw A)
    (f : A → ℝ) (hf : ∀ a, ¬ 0 < ν.mass a → f a = 0) :
    ∑ a : PositiveMassSupport ν, f a = ∑ a, f a := by
  exact (Finset.sum_congr_set {a | 0 < ν.mass a} f (fun a => f a)
    (fun _ _ => rfl) hf).symm

def positiveSupportLaw {A : Type u} [Fintype A] (ν : FiniteLaw A) :
    FiniteLaw (PositiveMassSupport ν) where
  mass a := ν.mass a
  mass_nonneg a := ν.mass_nonneg a
  sum_mass := by
    rw [sum_positive_support ν ν.mass (fun a ha => mass_zero_outside_positive_support ν ha)]
    exact ν.sum_mass

def restrictPositiveCoupling {A : Type u} [Fintype A] (ν : FiniteLaw A)
    (k : FiniteCoupling ν.mass ν.mass) :
    FiniteCoupling (positiveSupportLaw ν).mass (positiveSupportLaw ν).mass where
  weight a b := k.weight a b
  nonneg a b := k.nonneg a b
  row_sum a := by
    rw [sum_positive_support ν (fun b => k.weight a b)
      (fun b hb => k.weight_eq_zero_of_col a (mass_zero_outside_positive_support ν hb))]
    exact k.row_sum a
  col_sum b := by
    rw [sum_positive_support ν (fun a => k.weight a b)
      (fun a ha => k.weight_eq_zero_of_row (mass_zero_outside_positive_support ν ha) b)]
    exact k.col_sum b

abbrev UniformCouplingEdge (A : Type u) (L : Type v) := A × L × A

def uniformCouplingChain {A : Type u} {L : Type v} [Fintype A] [Fintype L]
    [Nonempty L] (ν : FiniteLaw A) (hν : ∀ a, 0 < ν.mass a)
    (inv : L → L) (hinv : Function.Involutive inv)
    (couplings : ∀ _s : L, FiniteCoupling ν.mass ν.mass)
    (hrev : ∀ s a b, (couplings (inv s)).weight b a = (couplings s).weight a b) :
    FiniteMarkedChain A (UniformCouplingEdge A L) where
  π := ν.mass
  π_nonneg := ν.mass_nonneg
  sum_π := ν.sum_mass
  src e := e.1
  tgt e := e.2.2
  rev e := (e.2.2, inv e.2.1, e.1)
  rev_rev e := by rcases e with ⟨a,s,b⟩; simp only [hinv s]
  src_rev _ := rfl
  tgt_rev _ := rfl
  q e := (couplings e.2.1).weight e.1 e.2.2 / ((Fintype.card L : ℝ) * ν.mass e.1)
  q_nonneg e := div_nonneg ((couplings e.2.1).nonneg e.1 e.2.2)
    (mul_nonneg (Nat.cast_nonneg _) (ν.mass_nonneg e.1))
  sum_q a := by
    have hcard : (Fintype.card L : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card L ≠ 0)
    have ha : ν.mass a ≠ 0 := ne_of_gt (hν a)
    simp only [Fintype.sum_prod_type]
    simp_rw [Finset.sum_ite_irrel]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
    simp_rw [← Finset.sum_div, (couplings _).row_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  balance e := by
    rcases e with ⟨a,s,b⟩
    have ha : ν.mass a ≠ 0 := ne_of_gt (hν a)
    have hb : ν.mass b ≠ 0 := ne_of_gt (hν b)
    rw [hrev s a b]
    field_simp

def reversibleChartCoupling {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    (ν : FiniteLaw (Chart Λ B)) (inv : L → L) (h : L → ℝ ≃o ℝ)
    (s : L) : FiniteCoupling ν.mass ν.mass :=
  symmetrizeFiniteCouplings inv (fun t => preliminaryChartCoupling ν (h t)) s

def chartTransportChain {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ) :
    FiniteMarkedChain (PositiveMassSupport ν) (UniformCouplingEdge (PositiveMassSupport ν) L) :=
  uniformCouplingChain (positiveSupportLaw ν) (fun C => C.property) inv hinv
    (fun s => restrictPositiveCoupling ν (reversibleChartCoupling ν inv h s))
    (fun s C C' => symmetrizeFiniteCouplings_reverse inv hinv
      (fun t => preliminaryChartCoupling ν (h t)) s C C')

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E]

def markedTransition (C : FiniteMarkedChain S E) (s t : S) : ℝ := by
  classical
  exact ∑ e, if C.src e = s ∧ C.tgt e = t then C.q e else 0

theorem markedTransition_nonneg (C : FiniteMarkedChain S E) (s t : S) :
    0 ≤ markedTransition C s t := by
  classical
  exact Finset.sum_nonneg fun e _ => by
    split_ifs
    · exact C.q_nonneg e
    · exact le_rfl

theorem sum_markedTransition (C : FiniteMarkedChain S E) (s : S) :
    ∑ t, markedTransition C s t = 1 := by
  classical
  unfold markedTransition
  rw [Finset.sum_comm]
  have h (e : E) :
      (∑ t, if C.src e = s ∧ C.tgt e = t then C.q e else 0) =
        if C.src e = s then C.q e else 0 := by
    by_cases hs : C.src e = s <;> simp [hs]
  simp_rw [h]
  exact C.sum_q s

theorem markedTransition_balance (C : FiniteMarkedChain S E) (s t : S) :
    C.π s * markedTransition C s t = C.π t * markedTransition C t s := by
  classical
  unfold markedTransition
  simp only [Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.ofBijective C.rev C.rev_rev.bijective)
  intro e
  change C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) =
    C.π t * (if C.src (C.rev e) = t ∧ C.tgt (C.rev e) = s then C.q (C.rev e) else 0)
  rw [C.src_rev, C.tgt_rev]
  by_cases hs : C.src e = s
  · by_cases ht : C.tgt e = t
    · simpa [hs, ht] using C.balance e
    · simp [hs, ht]
  · simp [hs]

def FiniteMarkedChain.toStateChain (C : FiniteMarkedChain S E) :
    FiniteReversibleChain S where
  π := C.π
  P := markedTransition C
  π_nonneg := C.π_nonneg
  sum_π := C.sum_π
  P_nonneg := markedTransition_nonneg C
  sum_P := sum_markedTransition C
  balance := markedTransition_balance C

@[simp] theorem markedState_zero (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) : markedState C ω 0 = ω.1 := by
  simp [markedState]

@[simp] theorem markedState_succ (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (i : Fin n) :
    markedState C ω i.succ = C.tgt (ω.2 i) := by
  simp [markedState]

def markedSnoc {n : ℕ} (ω : MarkedPath S E n) (e : E) : MarkedPath S E (n + 1) :=
  (ω.1, Fin.snoc ω.2 e)

theorem markedState_snoc_castSucc (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) (i : Fin (n + 1)) :
    markedState C (markedSnoc ω e) i.castSucc = markedState C ω i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [markedSnoc]
  · rw [← Fin.succ_castSucc]
    simp [markedSnoc]

theorem markedValid_snoc (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) :
    markedValid C (markedSnoc ω e) ↔
      markedValid C ω ∧ C.src e = markedState C ω (Fin.last n) := by
  constructor
  · intro h
    constructor
    · intro i
      have hi := h i.castSucc
      rw [markedState_snoc_castSucc] at hi
      simpa only [markedSnoc, Fin.snoc_castSucc] using hi
    · have hi := h (Fin.last n)
      rw [markedState_snoc_castSucc] at hi
      simpa only [markedSnoc, Fin.snoc_last] using hi
  · rintro ⟨h, he⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [markedState_snoc_castSucc]
      simpa only [markedSnoc, Fin.snoc_last] using he
    · rw [markedState_snoc_castSucc]
      simpa only [markedSnoc, Fin.snoc_castSucc] using h j

theorem markedPathWeight_of_valid (C : FiniteMarkedChain S E) {n : ℕ}
    (ω : MarkedPath S E n) (h : markedValid C ω) :
    markedPathWeight C n ω = C.π ω.1 * ∏ i, C.q (ω.2 i) := by
  simp [markedPathWeight, h]

theorem markedPathWeight_snoc (C : FiniteMarkedChain S E) (n : ℕ)
    (ω : MarkedPath S E n) (e : E) :
    markedPathWeight C (n + 1) (markedSnoc ω e) =
      markedPathWeight C n ω *
        (if C.src e = markedState C ω (Fin.last n) then C.q e else 0) := by
  classical
  by_cases hv : markedValid C ω
  · by_cases he : C.src e = markedState C ω (Fin.last n)
    · have hve : markedValid C (markedSnoc ω e) := (markedValid_snoc C ω e).2 ⟨hv, he⟩
      rw [markedPathWeight_of_valid C (markedSnoc ω e) hve,
        markedPathWeight_of_valid C ω hv, ite_eq_left he]
      simp [markedSnoc, Fin.prod_univ_castSucc, mul_assoc]
    · simp [markedPathWeight, markedValid_snoc, hv, he]
  · simp [markedPathWeight, markedValid_snoc, hv]

theorem markedExpect_snoc (C : FiniteMarkedChain S E) (n : ℕ)
    (F : MarkedPath S E (n + 1) → ℝ) :
    markedExpect C (n + 1) F =
      ∑ ω : MarkedPath S E n, ∑ e,
        (markedPathWeight C n ω *
          (if C.src e = markedState C ω (Fin.last n) then C.q e else 0)) *
          F (markedSnoc ω e) := by
  classical
  unfold markedExpect
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => E)).sum_comp
    (fun w => markedPathWeight C (n + 1) (s, w) * F (s, w))]
  change (∑ z : E × (Fin n → E),
    markedPathWeight C (n + 1) (markedSnoc (s, z.2) z.1) *
      F (markedSnoc (s, z.2) z.1)) = _
  simp only [Fintype.sum_prod_type, markedPathWeight_snoc]
  exact Finset.sum_comm

theorem sum_markedPathWeight (C : FiniteMarkedChain S E) (n : ℕ) :
    ∑ ω : MarkedPath S E n, markedPathWeight C n ω = 1 := by
  classical
  induction n with
  | zero =>
      simpa [markedPathWeight, markedValid, Fintype.sum_prod_type] using C.sum_π
  | succ n ih =>
      have h := markedExpect_snoc C n (fun _ => 1)
      simp only [markedExpect, mul_one] at h
      rw [h]
      simp_rw [← Finset.mul_sum, C.sum_q, mul_one]
      exact ih

def markedTake {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (ω : MarkedPath S E n) : MarkedPath S E k :=
  (ω.1, fun i => ω.2 (Fin.castLE hk i))

omit sectionFintypeS sectionFintypeE in
@[simp] theorem markedTake_self [Fintype S] [Fintype E] {n : ℕ} (ω : MarkedPath S E n) :
    markedTake n le_rfl ω = ω := by
  apply Prod.ext rfl
  funext i
  rfl

omit sectionFintypeS sectionFintypeE in
@[simp] theorem markedTake_snoc [Fintype S] [Fintype E] {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (ω : MarkedPath S E n) (e : E) :
    markedTake k (Nat.le_trans hk (Nat.le_succ n)) (markedSnoc ω e) =
      markedTake k hk ω := by
  apply Prod.ext
  · rfl
  · funext i
    change Fin.snoc (α := fun _ : Fin (n + 1) => E) ω.2 e (Fin.castLE hk i).castSucc = _
    exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => E) e ω.2 (Fin.castLE hk i)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedLetters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E A : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E] [sectionFintypeA : Fintype A]

@[simp] theorem markedExpect_const (C : FiniteMarkedChain S E) (n : ℕ) (a : ℝ) :
    markedExpect C n (fun _ => a) = a := by
  simp only [markedExpect, ← Finset.sum_mul, sum_markedPathWeight, one_mul]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FourLetters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

abbrev Letter := Fin 2 × Bool

namespace Letter

def inv (s : Letter) : Letter := (s.1, !s.2)

@[simp] theorem inv_inv (s : Letter) : s.inv.inv = s := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

@[simp] theorem inv_ne_self (s : Letter) : s.inv ≠ s := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [inv]

end Letter

@[simp] theorem card_letter : Fintype.card Letter = 4 := by
  simp [Letter]

def positiveCount (w : List Letter) : ℕ := w.countP (fun s => s.2)

def negativeCount (w : List Letter) : ℕ := w.countP (fun s => !s.2)

@[simp] theorem positiveCount_nil : positiveCount [] = 0 := rfl

@[simp] theorem negativeCount_nil : negativeCount [] = 0 := rfl

@[simp] theorem positiveCount_cons (s : Letter) (w : List Letter) :
    positiveCount (s :: w) = positiveCount w + (if s.2 then 1 else 0) :=
  List.countP_cons

@[simp] theorem negativeCount_cons (s : Letter) (w : List Letter) :
    negativeCount (s :: w) = negativeCount w + (if !s.2 then 1 else 0) :=
  List.countP_cons

@[simp] theorem positiveCount_append (v w : List Letter) :
    positiveCount (v ++ w) = positiveCount v + positiveCount w :=
  List.countP_append

@[simp] theorem negativeCount_append (v w : List Letter) :
    negativeCount (v ++ w) = negativeCount v + negativeCount w :=
  List.countP_append

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PeriodicOrderIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def periodicLiftFun (e : ℝ ≃o ℝ) (x : ℝ) : ℝ :=
  (⌊x⌋ : ℝ) + e (Int.fract x)

theorem periodicLiftFun_range (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : 0 ≤ e (Int.fract x) ∧ e (Int.fract x) < 1 := by
  constructor
  · simpa only [h0] using e.monotone (Int.fract_nonneg x)
  · simpa only [h1] using e.strictMono (Int.fract_lt_one x)

theorem periodicLiftFun_floor (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : ⌊periodicLiftFun e x⌋ = ⌊x⌋ := by
  apply Int.floor_eq_iff.mpr
  have hr := periodicLiftFun_range e h0 h1 x
  dsimp only [periodicLiftFun]
  constructor <;> linarith

theorem periodicLiftFun_fract (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : Int.fract (periodicLiftFun e x) = e (Int.fract x) := by
  rw [Int.fract, periodicLiftFun_floor e h0 h1]
  dsimp only [periodicLiftFun]
  ring

theorem periodicLiftFun_strictMono (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) :
    StrictMono (periodicLiftFun e) := by
  intro x y hxy
  have hfloor : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy.le
  rcases hfloor.eq_or_lt with heq | hlt
  · have hfrac : Int.fract x < Int.fract y := by
      dsimp only [Int.fract]
      rw [heq]
      linarith
    have he := e.strictMono hfrac
    dsimp only [periodicLiftFun]
    rw [heq]
    linarith
  · have hgap : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    have hx := (periodicLiftFun_range e h0 h1 x).2
    have hy := (periodicLiftFun_range e h0 h1 y).1
    dsimp only [periodicLiftFun]
    linarith

theorem periodicLiftFun_rightInverse (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) :
    Function.RightInverse (periodicLiftFun e.symm) (periodicLiftFun e) := by
  have h0' : e.symm 0 = 0 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact h0.symm
  have h1' : e.symm 1 = 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact h1.symm
  intro x
  unfold periodicLiftFun
  rw [show ⌊(⌊x⌋ : ℝ) + e.symm (Int.fract x)⌋ = ⌊x⌋ from
    periodicLiftFun_floor e.symm h0' h1' x]
  rw [show Int.fract ((⌊x⌋ : ℝ) + e.symm (Int.fract x)) = e.symm (Int.fract x) from
    periodicLiftFun_fract e.symm h0' h1' x]
  rw [e.apply_symm_apply, Int.floor_add_fract]

def unitPeriodicOrderIso (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfRightInverse (periodicLiftFun e)
    (periodicLiftFun_strictMono e h0 h1) (periodicLiftFun e.symm)
    (periodicLiftFun_rightInverse e h0 h1)

@[simp] theorem unitPeriodicOrderIso_apply (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : unitPeriodicOrderIso e h0 h1 x = periodicLiftFun e x := rfl

@[simp] theorem unitPeriodicOrderIso_symm_apply (e : ℝ ≃o ℝ)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (x : ℝ) :
    (unitPeriodicOrderIso e h0 h1).symm x = periodicLiftFun e.symm x := rfl

def twoSlope (x : ℝ) : ℝ := if x ≤ 1 / 9 then 8 * x else (x + 7) / 8

def twoSlopeInverse (x : ℝ) : ℝ := if x ≤ 8 / 9 then x / 8 else 8 * x - 7

theorem twoSlope_strictMono : StrictMono twoSlope := by
  intro x y hxy
  unfold twoSlope
  split_ifs <;> linarith

theorem twoSlope_rightInverse : Function.RightInverse twoSlopeInverse twoSlope := by
  intro x
  by_cases hx : x ≤ 8 / 9
  · have hb : x / 8 ≤ 1 / 9 := by linarith
    simp only [twoSlopeInverse, ite_eq_left hx, twoSlope, ite_eq_left hb]
    ring
  · have hb : ¬8 * x - 7 ≤ 1 / 9 := by linarith
    simp only [twoSlopeInverse, ite_eq_right hx, twoSlope, ite_eq_right hb]
    ring

def twoSlopeOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfRightInverse twoSlope twoSlope_strictMono
    twoSlopeInverse twoSlope_rightInverse

@[simp] theorem twoSlopeOrderIso_apply (x : ℝ) : twoSlopeOrderIso x = twoSlope x := rfl

@[simp] theorem twoSlopeOrderIso_symm_apply (x : ℝ) :
    twoSlopeOrderIso.symm x = twoSlopeInverse x := rfl

@[simp] theorem twoSlopeOrderIso_zero : twoSlopeOrderIso 0 = 0 := by
  norm_num [twoSlopeOrderIso_apply, twoSlope]

@[simp] theorem twoSlopeOrderIso_one : twoSlopeOrderIso 1 = 1 := by
  norm_num [twoSlopeOrderIso_apply, twoSlope]

def periodicBend : ℝ ≃o ℝ :=
  unitPeriodicOrderIso twoSlopeOrderIso twoSlopeOrderIso_zero twoSlopeOrderIso_one

theorem periodicBend_apply (x : ℝ) :
    periodicBend x = (⌊x⌋ : ℝ) + twoSlope (Int.fract x) := rfl

def translatedPeriodicOrderIso (a c : ℝ) : ℝ ≃o ℝ where
  toFun x := c + periodicBend (x - a)
  invFun y := a + periodicBend.symm (y - c)
  left_inv x := by simp only [add_sub_cancel_left, periodicBend.symm_apply_apply]; ring
  right_inv y := by simp only [add_sub_cancel_left, periodicBend.apply_symm_apply]; ring
  map_rel_iff' := by
    intro x y
    change c + periodicBend (x - a) ≤ c + periodicBend (y - a) ↔ x ≤ y
    simp only [add_le_add_iff_left, periodicBend.le_iff_le, sub_le_sub_iff_right]

theorem translatedPeriodicOrderIso_apply (a c x : ℝ) :
    translatedPeriodicOrderIso a c x = c + periodicBend (x - a) := rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PeriodicArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def periodicIco (a b : ℝ) : Set ℝ := {x | ∃ j : ℤ, a + j ≤ x ∧ x < b + j}

def periodicIcc (a b : ℝ) : Set ℝ := {x | ∃ j : ℤ, a + j ≤ x ∧ x ≤ b + j}

def arcRank (s : Letter) : ℕ := s.1.val + if s.2 then 0 else 2

def alpha (s : Letter) : ℝ := (2 * (arcRank s : ℝ) + 1) / 9

def beta (s : Letter) : ℝ := alpha s + 1 / 9

def arc (s : Letter) : Set ℝ := periodicIco (alpha s) (beta s)

def closedArc (s : Letter) : Set ℝ := periodicIcc (alpha s) (beta s)

def positiveOrderIso (g : Fin 2) : ℝ ≃o ℝ :=
  translatedPeriodicOrderIso (alpha (g, false)) (beta (g, true) - 1)

def letterOrderIso (s : Letter) : ℝ ≃o ℝ :=
  if s.2 then positiveOrderIso s.1 else (positiveOrderIso s.1).symm

def letterPeriodShift (s : Letter) : ℤ := if s.2 then 0 else 1

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WeightedEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {Ω : Type*} [Fintype Ω]

noncomputable def eventMass (μ : Ω → ℝ) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then μ ω else 0

noncomputable def weightedMean (μ X : Ω → ℝ) : ℝ := ∑ ω, μ ω * X ω

end MarkovSuperreflexivity.FiniteWalkDrift

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WordReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

def step (s : Letter) : List Letter → List Letter
  | [] => [s]
  | a :: r => if s = a.inv then r else s :: a :: r

def scanWord (w r : List Letter) : List Letter :=
  w.foldl (fun stack s => step s stack) r

def reduceWord (w : List Letter) : List Letter := (scanWord w []).reverse

def reducedLength (w : List Letter) : ℕ := (reduceWord w).length

def ReducedWord (w : List Letter) : Prop :=
  List.IsChain (fun a b => b ≠ a.inv) w

@[simp] theorem step_nil (s : Letter) : step s [] = [s] := rfl

@[simp] theorem step_cancel (a : Letter) (r : List Letter) :
    step a.inv (a :: r) = r := by simp [step]

@[simp] theorem scanWord_nil (r : List Letter) : scanWord [] r = r := rfl

@[simp] theorem reduceWord_nil : reduceWord [] = [] := rfl

@[simp] theorem reducedWord_nil : ReducedWord [] := List.isChain_nil

@[simp] theorem reducedWord_singleton (s : Letter) : ReducedWord [s] :=
  List.isChain_singleton s

inductive CancelPair : List Letter → List Letter → Prop
  | erase (u v : List Letter) (s : Letter) :
      CancelPair (u ++ s :: s.inv :: v) (u ++ v)

abbrev WordReduction : List Letter → List Letter → Prop :=
  Relation.ReflTransGen CancelPair

@[simp] theorem reducedLength_nil : reducedLength [] = 0 := rfl

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {A : Type*} [sectionFintypeA : Fintype A]

noncomputable def uniformWordMean (n : ℕ) (F : (Fin n → A) → ℝ) : ℝ :=
  ((4 : ℝ)⁻¹) ^ n * ∑ w, F w

end MarkovSuperreflexivity.FiniteWalkDrift

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

def walkWindowLength (n : ℕ) : ℕ := 8 * (n + 1)

@[simp] theorem walkWindowLength_pos (n : ℕ) : 0 < walkWindowLength n := by
  simp [walkWindowLength]

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ChartPathProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {S E : Type*} [Fintype S] [Fintype E]

variable {Λ : Finset ℝ} {B : ℕ}

abbrev ConcreteChartState (ν : FiniteLaw (Chart Λ B)) := PositiveMassSupport ν

abbrev ConcreteChartEdge (ν : FiniteLaw (Chart Λ B)) :=
  UniformCouplingEdge (ConcreteChartState ν) Letter

def concreteChartChain (ν : FiniteLaw (Chart Λ B)) :
    FiniteMarkedChain (ConcreteChartState ν) (ConcreteChartEdge ν) :=
  chartTransportChain ν Letter.inv Letter.inv_inv letterOrderIso

def concreteChartGood {ν : FiniteLaw (Chart Λ B)} (e : ConcreteChartEdge ν) : Prop :=
  Chart.Good (letterOrderIso e.2.1) e.1.val e.2.2.val

def concreteChartGoodMass (ν : FiniteLaw (Chart Λ B)) : ℝ :=
  ∑ e : ConcreteChartEdge ν, if concreteChartGood e then
    (concreteChartChain ν).π e.1 * (concreteChartChain ν).q e else 0

def concreteChartPathLetters {ν : FiniteLaw (Chart Λ B)} {n : ℕ}
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n) : Fin n → Letter :=
  fun i => (ω.2 i).2.1

end MarkovSuperreflexivity.FiniteWalkDrift

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

def CoefficientBasic (K : ℝ) (x : Fin n → E) : Prop :=
  ∀ a : Fin n → ℝ, ∀ k : ℕ, k ≤ n →
    ‖∑ i : Fin n, if i.val < k then a i • x i else 0‖ ≤
      K * ‖∑ i : Fin n, a i • x i‖

abbrev CoefficientMonotone (x : Fin n → E) : Prop := CoefficientBasic 1 x

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientSequenceOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]
variable {n m k : ℕ}

def equalBlock (x : Fin (m * k) → E) (j : Fin m) (i : Fin k) : E :=
  x (finProdFinEquiv (j, i))

def equalBlocks (x : Fin (m * k) → E) (j : Fin m) : E :=
  ∑ i : Fin k, equalBlock x j i

def equalBlockOrderEmbedding (j : Fin m) : Fin k ↪o Fin (m * k) :=
  OrderEmbedding.ofStrictMono (fun i => finProdFinEquiv (j, i)) (by
    intro i l hil
    change i.val + k * j.val < l.val + k * j.val
    exact Nat.add_lt_add_right hil _)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientConsecutiveBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

def consecutiveBlocks (x : Fin n → E) (cuts : Fin (m + 1) → ℕ) (j : Fin m) : E :=
  ∑ i : Fin n, if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then x i else 0

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

noncomputable section

def coefficientGridValue (k : ℕ) (j : Fin (2 * k ^ 2 + 1)) : ℝ :=
  (j.val : ℝ) / (k : ℝ) ^ 2 - 1

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_RenormingBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {X}

namespace EquivalentNorm

@[simp] theorem eq_zero_iff (N : EquivalentNorm X) (x : X) : N.p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hlow := N.lower_bound x
    have hn := norm_nonneg x
    have he : ‖x‖ = 0 := by nlinarith [N.lower_pos]
    exact norm_eq_zero.mp he
  · rintro rfl
    exact map_zero N.p

end EquivalentNorm

def UniformSmooth (p : Seminorm ℝ X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, 0 < t → t < δ → ∀ x y : X, p x = 1 → p y = 1 →
      (p (x + t • y) + p (x - t • y)) / 2 ≤ 1 + ε * t

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JConvexityBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def cutSign {n : ℕ} (r j : Fin n) : ℝ := if j < r then 1 else -1

def cutSum {n : ℕ} (x : Fin n → X) (r : Fin n) : X :=
  ∑ j, cutSign r j • x j

@[simp] theorem abs_cutSign {n : ℕ} (r j : Fin n) : |cutSign r j| = 1 := by
  unfold cutSign
  split <;> norm_num

@[simp] theorem norm_cutSign {n : ℕ} (r j : Fin n) : ‖cutSign r j‖ = 1 := by
  simpa only [Real.norm_eq_abs] using abs_cutSign r j

@[simp] theorem cutSum_two_zero (x : Fin 2 → X) :
    cutSum x (0 : Fin 2) = -(x 0 + x 1) := by
  simp [cutSum, Fin.sum_univ_two, cutSign]

@[simp] theorem cutSum_two_one (x : Fin 2 → X) :
    cutSum x (1 : Fin 2) = x 0 - x 1 := by
  simp [cutSum, Fin.sum_univ_two, cutSign, sub_eq_add_neg]

def JConvexWitness (p : Seminorm ℝ X) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ x : Fin n → X, (∀ j, p (x j) ≤ 1) →
    ∃ r : Fin n, p (cutSum x r) ≤ (n : ℝ) * (1 - δ)

def JConvex (p : Seminorm ℝ X) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ JConvexWitness p n δ

def UniformlyNonsquare (p : Seminorm ℝ X) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ x y : X, p x ≤ 1 → p y ≤ 1 →
      p (x + y) ≤ 2 * (1 - δ) ∨ p (x - y) ≤ 2 * (1 - δ)

def AmbientJConvex (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  JConvex (normSeminorm ℝ X)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CubeNotJConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cutSignColumn {n : ℕ} (j : Fin n) : Fin n → ℝ := fun r => cutSign r j

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u

inductive DyadicTree (X : Type u) where
  | leaf : X → DyadicTree X
  | node : DyadicTree X → DyadicTree X → DyadicTree X

namespace DyadicTree

variable {X : Type u}

noncomputable def terminal (t : DyadicTree X) (f : X → ℝ) : ℝ :=
  match t with
  | leaf x => f x
  | node t s => (terminal t f + terminal s f) / 2

@[simp] theorem terminal_leaf (x : X) (f : X → ℝ) :
    terminal (leaf x) f = f x := rfl

@[simp] theorem terminal_node (t s : DyadicTree X) (f : X → ℝ) :
    terminal (node t s) f = (terminal t f + terminal s f) / 2 := rfl

theorem terminal_mono (t : DyadicTree X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    terminal t f ≤ terminal t g := by
  induction t with
  | leaf x => exact h x
  | node t s ht hs => simp only [terminal_node]; linarith

@[simp] theorem terminal_const (t : DyadicTree X) (c : ℝ) :
    terminal t (fun _ => c) = c := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [terminal_node, ht, hs]; ring

theorem terminal_linear (t : DyadicTree X) (f g : X → ℝ) (a b : ℝ) :
    terminal t (fun x => a * f x + b * g x) =
      a * terminal t f + b * terminal t g := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [terminal_node, ht, hs]; ring

def height : DyadicTree X → ℕ
  | leaf _ => 0
  | node t s => max (height t) (height s) + 1

def Full : ℕ → DyadicTree X → Prop
  | 0, leaf _ => True
  | 0, node _ _ => False
  | _ + 1, leaf _ => False
  | n + 1, node t s => Full n t ∧ Full n s

def pad : ℕ → DyadicTree X → DyadicTree X
  | 0, t => t
  | n + 1, leaf x => node (pad n (leaf x)) (pad n (leaf x))
  | n + 1, node t s => node (pad n t) (pad n s)

@[simp] theorem terminal_pad (n : ℕ) (t : DyadicTree X) (f : X → ℝ) :
    terminal (pad n t) f = terminal t f := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases t with
      | leaf x => simp only [pad, terminal_node, ih]; ring
      | node t s => simp only [pad, terminal_node, ih]

variable [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

noncomputable def root : DyadicTree X → X
  | leaf x => x
  | node t s => (2 : ℝ)⁻¹ • (root t + root s)

@[simp] theorem root_leaf (x : X) : root (leaf x) = x := rfl

@[simp] theorem root_node (t s : DyadicTree X) :
    root (node t s) = (2 : ℝ)⁻¹ • (root t + root s) := rfl

noncomputable def moment (p : ℝ) (t : DyadicTree X) : ℝ :=
  terminal t (fun x => ‖x‖ ^ p)

omit sectionNormedSpaceℝX in
@[simp] theorem moment_leaf [NormedSpace ℝ X] (p : ℝ) (x : X) : moment p (leaf x) = ‖x‖ ^ p := rfl

omit sectionNormedSpaceℝX in
@[simp] theorem moment_node [NormedSpace ℝ X] (p : ℝ) (t s : DyadicTree X) :
    moment p (node t s) = (moment p t + moment p s) / 2 := rfl

noncomputable def energy (p : ℝ) : DyadicTree X → ℝ
  | leaf _ => 0
  | node t s => (energy p t + energy p s) / 2 +
      ‖(2 : ℝ)⁻¹ • (root t - root s)‖ ^ p

@[simp] theorem energy_leaf (p : ℝ) (x : X) : energy p (leaf x) = 0 := rfl

@[simp] theorem energy_node (p : ℝ) (t s : DyadicTree X) :
    energy p (node t s) = (energy p t + energy p s) / 2 +
      ‖(2 : ℝ)⁻¹ • (root t - root s)‖ ^ p := rfl

def translate (a : X) : DyadicTree X → DyadicTree X
  | leaf x => leaf (a + x)
  | node t s => node (translate a t) (translate a s)

def scale (a : ℝ) : DyadicTree X → DyadicTree X
  | leaf x => leaf (a • x)
  | node t s => node (scale a t) (scale a s)

@[simp] theorem root_translate (a : X) (t : DyadicTree X) :
    root (translate a t) = a + root t := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [translate, root_node, ht, hs]; module

@[simp] theorem root_scale (a : ℝ) (t : DyadicTree X) :
    root (scale a t) = a • root t := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [scale, root_node, ht, hs]; module

@[simp] theorem scale_scale (a b : ℝ) (t : DyadicTree X) :
    scale a (scale b t) = scale (a * b) t := by
  induction t with
  | leaf x => simp only [scale, smul_smul]
  | node t s ht hs => simp only [scale, ht, hs]

@[simp] theorem scale_one (t : DyadicTree X) : scale 1 t = t := by
  induction t with
  | leaf x => simp [scale]
  | node t s ht hs => simp only [scale, ht, hs]

omit sectionNormedSpaceℝX in
@[simp] theorem terminal_translate [NormedSpace ℝ X] (a : X) (t : DyadicTree X) (f : X → ℝ) :
    terminal (translate a t) f = terminal t (fun x => f (a + x)) := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [translate, terminal_node, ht, hs]

omit sectionNormedSpaceℝX in
@[simp] theorem translate_translate [NormedSpace ℝ X] (a b : X) (t : DyadicTree X) :
    translate a (translate b t) = translate (a + b) t := by
  induction t with
  | leaf x => simp [translate, add_assoc]
  | node t s ht hs => simp only [translate, ht, hs]

omit sectionNormedSpaceℝX in
@[simp] theorem translate_zero [NormedSpace ℝ X] (t : DyadicTree X) : translate 0 t = t := by
  induction t with
  | leaf x => simp [translate]
  | node t s ht hs => simp only [translate, ht, hs]

@[simp] theorem energy_translate (p : ℝ) (a : X) (t : DyadicTree X) :
    energy p (translate a t) = energy p t := by
  induction t with
  | leaf x => rfl
  | node t s ht hs =>
      simp only [translate, energy_node, root_translate, ht, hs,
        add_sub_add_left_eq_sub]

@[simp] theorem moment_scale (p a : ℝ) (t : DyadicTree X) :
    moment p (scale a t) = |a| ^ p * moment p t := by
  induction t with
  | leaf x =>
      simp only [scale, moment_leaf, norm_smul, Real.norm_eq_abs,
        Real.mul_rpow (abs_nonneg a) (norm_nonneg x)]
  | node t s ht hs => simp only [scale, moment_node, ht, hs]; ring

@[simp] theorem energy_scale (p a : ℝ) (t : DyadicTree X) :
    energy p (scale a t) = |a| ^ p * energy p t := by
  induction t with
  | leaf x => simp [scale]
  | node t s ht hs =>
      simp only [scale, energy_node, root_scale, ht, hs]
      have he : (2 : ℝ)⁻¹ • (a • root t - a • root s) =
          a • ((2 : ℝ)⁻¹ • (root t - root s)) := by module
      rw [he, norm_smul, Real.norm_eq_abs,
        Real.mul_rpow (abs_nonneg a) (norm_nonneg _)]
      ring

@[simp] theorem root_pad (n : ℕ) (t : DyadicTree X) : root (pad n t) = root t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases t with
      | leaf x => simp only [pad, root_node, ih]; module
      | node t s => simp only [pad, root_node, ih]

omit sectionNormedSpaceℝX in
@[simp] theorem moment_pad [NormedSpace ℝ X] (p : ℝ) (n : ℕ) (t : DyadicTree X) :
    moment p (pad n t) = moment p t := terminal_pad n t _

@[simp] theorem energy_pad {p : ℝ} (hp : 0 < p) (n : ℕ) (t : DyadicTree X) :
    energy p (pad n t) = energy p t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases t with
      | leaf x => simp [pad, energy_node, ih, Real.zero_rpow hp.ne']
      | node t s => simp only [pad, energy_node, ih, root_pad]

end DyadicTree
end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicBellman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

open Set DyadicTree

def FiniteDyadicUpperEstimate (p A K : ℝ) : Prop :=
  ∀ t : DyadicTree X, moment p t ≤ A * ‖root t‖ ^ p + K * energy p t

noncomputable def dyadicObjective (p K : ℝ) (t : DyadicTree X) : ℝ :=
  moment p t - K * energy p t

def bellmanValues (p K : ℝ) (x : X) : Set ℝ :=
  {v | ∃ t : DyadicTree X, root t = x ∧ v = dyadicObjective p K t}

noncomputable def bellmanPotential (p K : ℝ) (x : X) : ℝ :=
  sSup (bellmanValues p K x)

theorem bellmanValues_nonempty (p K : ℝ) (x : X) :
    (bellmanValues p K x).Nonempty := by
  refine ⟨‖x‖ ^ p, leaf x, rfl, ?_⟩
  simp [dyadicObjective]

theorem bellmanValues_bddAbove {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    BddAbove (bellmanValues p K x) := by
  refine ⟨A * ‖x‖ ^ p, ?_⟩
  rintro v ⟨t, ht, rfl⟩
  have h := hMT t
  rw [ht] at h
  dsimp [dyadicObjective]
  linarith

theorem dyadicObjective_le_bellman {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (t : DyadicTree X) :
    dyadicObjective p K t ≤ bellmanPotential p K (root t) :=
  le_csSup (bellmanValues_bddAbove hMT _) ⟨t, rfl, rfl⟩

theorem bellmanPotential_bounds {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    ‖x‖ ^ p ≤ bellmanPotential p K x ∧
      bellmanPotential p K x ≤ A * ‖x‖ ^ p := by
  constructor
  · simpa [dyadicObjective] using dyadicObjective_le_bellman hMT (leaf x)
  · apply csSup_le (bellmanValues_nonempty p K x)
    rintro v ⟨t, ht, rfl⟩
    have h := hMT t
    rw [ht] at h
    dsimp [dyadicObjective]
    linarith

theorem bellmanPotential_nonneg {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    0 ≤ bellmanPotential p K x :=
  (Real.rpow_nonneg (norm_nonneg x) p).trans (bellmanPotential_bounds hMT x).1

@[simp] theorem bellmanPotential_zero {p A K : ℝ} (hp : 0 < p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) :
    bellmanPotential p K (0 : X) = 0 := by
  have h := bellmanPotential_bounds hMT (0 : X)
  simp only [norm_zero, Real.zero_rpow hp.ne', mul_zero] at h
  exact le_antisymm h.2 h.1

@[simp] theorem dyadicObjective_scale (p K a : ℝ) (t : DyadicTree X) :
    dyadicObjective p K (scale a t) = |a| ^ p * dyadicObjective p K t := by
  simp only [dyadicObjective, moment_scale, energy_scale]
  ring

theorem bellmanPotential_smul {p A K : ℝ} (hp : 0 < p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (a : ℝ) (x : X) :
    bellmanPotential p K (a • x) = |a| ^ p * bellmanPotential p K x := by
  by_cases ha : a = 0
  · subst a
    simp [bellmanPotential_zero hp hMT, Real.zero_rpow hp.ne']
  have hk : 0 < |a| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr ha) p
  apply le_antisymm
  · apply csSup_le (bellmanValues_nonempty p K (a • x))
    rintro v ⟨t, ht, rfl⟩
    have hr : root (scale a⁻¹ t) = x := by
      rw [root_scale, ht, smul_smul, inv_mul_cancel₀ ha, one_smul]
    have hc := dyadicObjective_le_bellman hMT (scale a⁻¹ t)
    rw [hr] at hc
    have hm := mul_le_mul_of_nonneg_left hc hk.le
    rw [← dyadicObjective_scale, scale_scale, mul_inv_cancel₀ ha, scale_one] at hm
    exact hm
  · have hh : bellmanPotential p K x ≤ bellmanPotential p K (a • x) / (|a| ^ p) := by
      apply csSup_le (bellmanValues_nonempty p K x)
      rintro v ⟨t, ht, rfl⟩
      apply (le_div_iff₀ hk).2
      have hc := dyadicObjective_le_bellman hMT (scale a t)
      rw [root_scale, ht, dyadicObjective_scale] at hc
      simpa only [mul_comm] using hc
    have hh' := (le_div_iff₀ hk).1 hh
    simpa only [mul_comm] using hh'

theorem norm_rpow_convex {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : X => ‖x‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hn : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
  have hpow := (convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)).trans hpow

theorem moment_translate_convex {p : ℝ} (hp : 1 ≤ p) (t : DyadicTree X)
    (x y : X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    moment p (translate (a • x + b • y) t) ≤
      a * moment p (translate x t) + b * moment p (translate y t) := by
  change terminal (translate (a • x + b • y) t) (fun z => ‖z‖ ^ p) ≤ _
  rw [terminal_translate]
  calc
    terminal t (fun z => ‖a • x + b • y + z‖ ^ p) ≤
        terminal t (fun z => a * ‖x + z‖ ^ p + b * ‖y + z‖ ^ p) := by
      apply terminal_mono
      intro z
      have he : a • x + b • y + z = a • (x + z) + b • (y + z) := by
        calc
          _ = a • x + b • y + (a + b) • z := by rw [hab, one_smul]
          _ = _ := by module
      rw [he]
      exact (norm_rpow_convex hp).2 (mem_univ _) (mem_univ _) ha hb hab
    _ = a * moment p (translate x t) + b * moment p (translate y t) := by
      rw [terminal_linear]
      simp only [moment, terminal_translate]

theorem bellmanPotential_convex {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) :
    ConvexOn ℝ Set.univ (bellmanPotential (X := X) p K) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply csSup_le (bellmanValues_nonempty p K (a • x + b • y))
  rintro v ⟨t, ht, rfl⟩
  let z := a • x + b • y
  let u := translate (-z) t
  have hu : root u = 0 := by
    change root (translate (-z) t) = 0
    rw [root_translate, ht]
    exact neg_add_cancel z
  have huz : translate z u = t := by simp [u]
  have huE : energy p u = energy p t := by simp [u]
  have hm := moment_translate_convex hp u x y ha hb hab
  change moment p (translate z u) ≤ _ at hm
  rw [huz] at hm
  have hJ : dyadicObjective p K t ≤
      a * dyadicObjective p K (translate x u) +
        b * dyadicObjective p K (translate y u) := by
    have hweight : a * (K * energy p t) + b * (K * energy p t) =
        K * energy p t := by
      rw [← add_mul, hab, one_mul]
    simp only [dyadicObjective, energy_translate, huE]
    nlinarith only [hm, hweight]
  have hxJ := dyadicObjective_le_bellman hMT (translate x u)
  have hyJ := dyadicObjective_le_bellman hMT (translate y u)
  simp only [root_translate, hu, add_zero] at hxJ hyJ
  exact hJ.trans (add_le_add (mul_le_mul_of_nonneg_left hxJ ha)
    (mul_le_mul_of_nonneg_left hyJ hb))

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteIndependentCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def independentCopies (μ : FiniteLaw Ω) (m : ℕ) : FiniteLaw (Fin m → Ω) where
  mass x := ∏ i, μ.mass (x i)
  mass_nonneg x := Finset.prod_nonneg fun i _ => μ.mass_nonneg (x i)
  sum_mass := by
    rw [← Fintype.prod_sum]
    simp only [μ.sum_mass, Finset.prod_const_one]

@[simp]
theorem independentCopies_mass (μ : FiniteLaw Ω) (m : ℕ) (x : Fin m → Ω) :
    (μ.independentCopies m).mass x = ∏ i, μ.mass (x i) := rfl

@[simp]
theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.sum_mass]

@[simp]
theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

end FiniteLaw
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteStoppingTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

structure FinitePartitionFiltration (Ω : Type*) where
  part : ℕ → Setoid Ω
  refines : ∀ {m n : ℕ}, m ≤ n → ∀ {ω η : Ω},
    (part n).r ω η → (part m).r ω η

namespace FinitePartitionFiltration

variable {Ω : Type*} (F : FinitePartitionFiltration Ω)

def IsStoppingTime (τ : Ω → ℕ) : Prop :=
  ∀ n : ℕ, ∀ {ω η : Ω}, (F.part n).r ω η → (τ ω ≤ n ↔ τ η ≤ n)

def IsPredictableTime (τ : Ω → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ {ω η : Ω},
    (F.part (n - 1)).r ω η → (τ ω = n ↔ τ η = n)

def AdaptedAt {V : Type*} (n : ℕ) (f : Ω → V) : Prop :=
  ∀ {ω η : Ω}, (F.part n).r ω η → f ω = f η

theorem isStoppingTime_const (n : ℕ) : F.IsStoppingTime (fun _ => n) := by
  intro m ω η hωη
  rfl

theorem isStoppingTime_of_isPredictableTime {τ : Ω → ℕ}
    (hpos : ∀ ω, 0 < τ ω) (hτ : F.IsPredictableTime τ) :
    F.IsStoppingTime τ := by
  intro n ω η hωη
  constructor
  · intro hle
    have hrel : (F.part (τ ω - 1)).r ω η :=
      F.refines ((Nat.sub_le (τ ω) 1).trans hle) hωη
    have heq : τ η = τ ω := (hτ (τ ω) (hpos ω) hrel).mp rfl
    simpa only [heq] using hle
  · intro hle
    have hrel : (F.part (τ η - 1)).r η ω :=
      F.refines ((Nat.sub_le (τ η) 1).trans hle) ((F.part n).symm' hωη)
    have heq : τ ω = τ η := (hτ (τ η) (hpos η) hrel).mp rfl
    simpa only [heq] using hle

def stoppedSetoid (τ : Ω → ℕ) : Setoid Ω where
  r ω η := τ ω = τ η ∧ (F.part (τ ω)).r ω η
  iseqv := {
    refl := fun ω => ⟨rfl, (F.part (τ ω)).refl' ω⟩
    symm := by
      intro ω η h
      refine ⟨h.1.symm, ?_⟩
      rw [← h.1]
      exact (F.part (τ ω)).symm' h.2
    trans := by
      intro ω η ξ hωη hηξ
      refine ⟨hωη.1.trans hηξ.1, ?_⟩
      have hηξ' : (F.part (τ ω)).r η ξ := by
        rw [hωη.1]
        exact hηξ.2
      exact (F.part (τ ω)).trans' hωη.2 hηξ' }

theorem stopped_rel_of_rel_of_le {τ : Ω → ℕ} (hτ : F.IsStoppingTime τ)
    {n : ℕ} {ω η : Ω} (hωη : (F.part n).r ω η) (hω : τ ω ≤ n) :
    (F.stoppedSetoid τ).r ω η := by
  have hη : τ η ≤ n := (hτ n hωη).mp hω
  have hrelω : (F.part (τ ω)).r ω η := F.refines hω hωη
  have hrelη : (F.part (τ η)).r ω η := F.refines hη hωη
  have hηω : τ η ≤ τ ω := (hτ (τ ω) hrelω).mp le_rfl
  have hωηtime : τ ω ≤ τ η := (hτ (τ η) hrelη).mpr le_rfl
  exact ⟨Nat.le_antisymm hωηtime hηω, hrelω⟩

theorem stoppedSetoid_refines {τ σ : Ω → ℕ} (hτ : F.IsStoppingTime τ)
    (hle : ∀ ω, τ ω ≤ σ ω) {ω η : Ω}
    (hωη : (F.stoppedSetoid σ).r ω η) :
    (F.stoppedSetoid τ).r ω η :=
  F.stopped_rel_of_rel_of_le hτ hωη.2 (hle ω)

end FinitePartitionFiltration

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteDyadicProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

abbrev DyadicWord (N : ℕ) := Fin N → Bool

def fairBitLaw : FiniteLaw Bool where
  mass _ := (2 : ℝ)⁻¹
  mass_nonneg _ := by norm_num
  sum_mass := by norm_num [Fintype.sum_bool]

def dyadicLaw (N : ℕ) : FiniteLaw (DyadicWord N) := fairBitLaw.independentCopies N

@[simp] theorem dyadicLaw_mass (N : ℕ) (ω : DyadicWord N) :
    (dyadicLaw N).mass ω = (2 : ℝ)⁻¹ ^ N := by
  simp [dyadicLaw, FiniteLaw.independentCopies_mass, fairBitLaw]

@[simp] theorem fairBitLaw_prob_eq (b : Bool) :
    fairBitLaw.prob (fun c => c = b) = (2 : ℝ)⁻¹ := by
  cases b <;> norm_num [FiniteLaw.prob, fairBitLaw, Fintype.sum_bool]

def dyadicFiltration (N : ℕ) : FinitePartitionFiltration (DyadicWord N) where
  part n := {
    r := fun ω η => ∀ i : Fin N, i.val < n → ω i = η i
    iseqv := {
      refl := fun ω i _ => rfl
      symm := fun h i hi => (h i hi).symm
      trans := fun h₁ h₂ i hi => (h₁ i hi).trans (h₂ i hi) } }
  refines := by
    intro m n hmn ω η hωη i hi
    exact hωη i (hi.trans_le hmn)

def dyadicPrefix {N : ℕ} (ω : DyadicWord N) (j : ℕ) (hj : j ≤ N) : DyadicWord j :=
  fun i => ω ⟨i.val, i.is_lt.trans_le hj⟩

def dyadicFlip {N : ℕ} (i : Fin N) (ω : DyadicWord N) : DyadicWord N :=
  Function.update ω i (!(ω i))

@[simp] theorem dyadicFlip_at {N : ℕ} (i : Fin N) (ω : DyadicWord N) :
    dyadicFlip i ω i = !(ω i) := by simp [dyadicFlip]

theorem dyadicFlip_of_ne {N : ℕ} (i j : Fin N) (ω : DyadicWord N) (hji : j ≠ i) :
    dyadicFlip i ω j = ω j := by simp [dyadicFlip, hji]

theorem dyadicFlip_involutive {N : ℕ} (i : Fin N) : Function.Involutive (dyadicFlip i) := by
  intro ω
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · rw [dyadicFlip_of_ne i j _ hji, dyadicFlip_of_ne i j _ hji]

def dyadicFlipEquiv {N : ℕ} (i : Fin N) : DyadicWord N ≃ DyadicWord N where
  toFun := dyadicFlip i
  invFun := dyadicFlip i
  left_inv := dyadicFlip_involutive i
  right_inv := dyadicFlip_involutive i

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicBlockCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def dyadicBlockEquiv (m N : ℕ) : DyadicWord (m * N) ≃ (Fin m → DyadicWord N) where
  toFun ω b i := ω (finProdFinEquiv (b, i))
  invFun f j := f ((finProdFinEquiv (m := m) (n := N)).symm j).1
    ((finProdFinEquiv (m := m) (n := N)).symm j).2
  left_inv ω := by
    funext j
    exact congrArg ω ((finProdFinEquiv (m := m) (n := N)).apply_symm_apply j)
  right_inv f := by
    funext b i
    exact congrArg (fun z : Fin m × Fin N => f z.1 z.2)
      ((finProdFinEquiv (m := m) (n := N)).symm_apply_apply (b, i))

@[simp] theorem dyadicBlockEquiv_apply {m N : ℕ} (ω : DyadicWord (m * N))
    (b : Fin m) (i : Fin N) :
    dyadicBlockEquiv m N ω b i = ω (finProdFinEquiv (b, i)) := rfl

@[simp] theorem dyadicBlockEquiv_symm_apply {m N : ℕ}
    (f : Fin m → DyadicWord N) (j : Fin (m * N)) :
    (dyadicBlockEquiv m N).symm f j =
      f ((finProdFinEquiv (m := m) (n := N)).symm j).1
        ((finProdFinEquiv (m := m) (n := N)).symm j).2 := rfl

theorem dyadicBlockIndex_symm_val {m N : ℕ} (j : Fin (m * N)) :
    ((finProdFinEquiv (m := m) (n := N)).symm j).2.val +
      N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val = j.val :=
  congrArg Fin.val ((finProdFinEquiv (m := m) (n := N)).apply_symm_apply j)

def dyadicBlockPrefix {m N : ℕ} (j : Fin (m * N)) (α : DyadicWord j.val) :
    DyadicWord (((finProdFinEquiv (m := m) (n := N)).symm j).2.val) :=
  fun k => α ⟨k.val + N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val, by
    calc
      k.val + N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val <
          ((finProdFinEquiv (m := m) (n := N)).symm j).2.val +
            N * ((finProdFinEquiv (m := m) (n := N)).symm j).1.val :=
        Nat.add_lt_add_right k.is_lt _
      _ = j.val := dyadicBlockIndex_symm_val j⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_HomogeneousPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {E : Type*} [sectionNormedAddCommGroupE : NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem subadditive_of_convex_unit_sublevel (N : E → ℝ)
    (hN : ∀ x, 0 ≤ N x)
    (hsmul : ∀ (a : ℝ) x, N (a • x) = ‖a‖ * N x)
    (hconv : Convex ℝ {x | N x ≤ 1}) (x y : E) :
    N (x + y) ≤ N x + N y := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      N (x + y) ≤ N x + N y + 2 * ε := by
    let a := N x + ε
    let b := N y + ε
    have ha : 0 < a := add_pos_of_nonneg_of_pos (hN x) hε
    have hb : 0 < b := add_pos_of_nonneg_of_pos (hN y) hε
    have hs : 0 < a + b := add_pos ha hb
    have hu : N (a⁻¹ • x) ≤ 1 := by
      calc
        N (a⁻¹ • x) = N x / a := by
          rw [hsmul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha),
            div_eq_mul_inv, mul_comm]
        _ ≤ 1 := (div_le_one ha).mpr (le_add_of_nonneg_right hε.le)
    have hv : N (b⁻¹ • y) ≤ 1 := by
      calc
        N (b⁻¹ • y) = N y / b := by
          rw [hsmul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb),
            div_eq_mul_inv, mul_comm]
        _ ≤ 1 := (div_le_one hb).mpr (le_add_of_nonneg_right hε.le)
    have hweights : a / (a + b) + b / (a + b) = 1 := by
      rw [← add_div, div_self hs.ne']
    have hc := hconv hu hv (div_nonneg ha.le hs.le)
      (div_nonneg hb.le hs.le) hweights
    change N ((a / (a + b)) • (a⁻¹ • x) +
      (b / (a + b)) • (b⁻¹ • y)) ≤ 1 at hc
    have hca : (a / (a + b)) * a⁻¹ = (a + b)⁻¹ := by
      field_simp [ha.ne', hs.ne']
    have hcb : (b / (a + b)) * b⁻¹ = (a + b)⁻¹ := by
      field_simp [hb.ne', hs.ne']
    have hvec : (a / (a + b)) • (a⁻¹ • x) +
        (b / (a + b)) • (b⁻¹ • y) = (a + b)⁻¹ • (x + y) := by
      simp only [smul_smul, hca, hcb, smul_add]
    rw [hvec, hsmul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at hc
    have hquot : N (x + y) / (a + b) ≤ 1 := by
      simpa only [div_eq_mul_inv, mul_comm] using hc
    have hbound := (div_le_one hs).mp hquot
    dsimp [a, b] at hbound
    linarith only [hbound]
  by_contra h
  have hgap : 0 < N (x + y) - (N x + N y) := sub_pos.mpr (lt_of_not_ge h)
  have hε : 0 < (N (x + y) - (N x + N y)) / 4 := by
    linarith only [hgap]
  have hbound := happrox ((N (x + y) - (N x + N y)) / 4) hε
  linarith only [hbound, hgap]

noncomputable def potentialRoot (q : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  F x ^ (1 / q)

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
theorem potentialRoot_nonneg [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℝ) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) : 0 ≤ potentialRoot q F x :=
  Real.rpow_nonneg (hF x) _

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
theorem potentialRoot_rpow [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) : (potentialRoot q F x) ^ q = F x := by
  have hexp : (1 / q) * q = (1 : ℝ) := by field_simp [hq.ne']
  rw [potentialRoot, ← Real.rpow_mul (hF x), hexp, Real.rpow_one]

theorem potentialRoot_smul (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (a : ℝ) (x : E) : potentialRoot q F (a • x) = ‖a‖ * potentialRoot q F x := by
  have hexp : q * (1 / q) = (1 : ℝ) := by field_simp [hq.ne']
  simp only [potentialRoot, hhom]
  rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg a) q) (hF x),
    ← Real.rpow_mul (norm_nonneg a), hexp, Real.rpow_one]

theorem potentialRoot_le_iff (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) (b : ℝ) (hb : 0 ≤ b) :
    potentialRoot q F x ≤ b ↔ F x ≤ b ^ q := by
  rw [← Real.rpow_le_rpow_iff (potentialRoot_nonneg q F hF x) hb hq,
    potentialRoot_rpow q hq F hF x]

theorem le_potentialRoot_iff (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) (b : ℝ) (hb : 0 ≤ b) :
    b ≤ potentialRoot q F x ↔ b ^ q ≤ F x := by
  rw [← Real.rpow_le_rpow_iff hb (potentialRoot_nonneg q F hF x) hq,
    potentialRoot_rpow q hq F hF x]

theorem potentialRoot_unit_sublevel_convex
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hconv : ConvexOn ℝ Set.univ F) :
    Convex ℝ {x | potentialRoot q F x ≤ 1} := by
  intro x hx y hy a b ha hb hab
  have hxF : F x ≤ 1 := by
    simpa only [Real.one_rpow] using
      (potentialRoot_le_iff q hq F hF x 1 zero_le_one).mp hx
  have hyF : F y ≤ 1 := by
    simpa only [Real.one_rpow] using
      (potentialRoot_le_iff q hq F hF y 1 zero_le_one).mp hy
  have hFcombo : F (a • x + b • y) ≤ 1 := by
    calc
      F (a • x + b • y) ≤ a * F x + b * F y := by
        simpa only [smul_eq_mul] using
          hconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hxF ha) (mul_le_mul_of_nonneg_left hyF hb)
      _ = 1 := by simpa only [mul_one] using hab
  exact (potentialRoot_le_iff q hq F hF (a • x + b • y) 1 zero_le_one).mpr
    (by simpa only [Real.one_rpow] using hFcombo)

noncomputable def potentialSeminorm
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) : Seminorm ℝ E :=
  Seminorm.of (potentialRoot q F)
    (subadditive_of_convex_unit_sublevel (potentialRoot q F)
      (potentialRoot_nonneg q F hF) (potentialRoot_smul q hq F hF hhom)
      (potentialRoot_unit_sublevel_convex q hq F hF hconv))
    (potentialRoot_smul q hq F hF hhom)

@[simp] theorem potentialSeminorm_apply
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) (x : E) :
    potentialSeminorm q hq F hF hhom hconv x = F x ^ (1 / q) := rfl

theorem potentialSeminorm_rpow
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) (x : E) :
    (potentialSeminorm q hq F hF hhom hconv x) ^ q = F x :=
  potentialRoot_rpow q hq F hF x

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MidpointPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem nonpos_on_unit_interval_of_midpoint
    (g : ℝ → ℝ)
    (hmid : ∀ s t, g ((s + t) / 2) ≤ (g s + g t) / 2)
    (hzero : g 0 ≤ 0) (hone : g 1 ≤ 0)
    (M : ℝ) (hbound : ∀ t, 0 ≤ t → t ≤ 1 → g t ≤ M)
    (t : ℝ) (htzero : 0 ≤ t) (htone : t ≤ 1) : g t ≤ 0 := by
  by_contra h
  have hpos : 0 < g t := lt_of_not_ge h
  have hstep (s : ℝ) (hszero : 0 ≤ s) (hsone : s ≤ 1) :
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 2 * g s ≤ g u := by
    by_cases hs : s ≤ 1 / 2
    · have hm := hmid 0 (2 * s)
      have he : (0 + 2 * s) / 2 = s := by ring
      rw [he] at hm
      refine ⟨2 * s, by linarith, by linarith, ?_⟩
      linarith only [hm, hzero]
    · have hm := hmid (2 * s - 1) 1
      have he : (2 * s - 1 + 1) / 2 = s := by ring
      rw [he] at hm
      refine ⟨2 * s - 1, by linarith, by linarith, ?_⟩
      linarith only [hm, hone]
  have hgrowth (n : ℕ) :
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (n : ℝ) * g t + g t ≤ g s := by
    induction n with
    | zero => exact ⟨t, htzero, htone, by simp⟩
    | succ n ih =>
        obtain ⟨s, hs0, hs1, hvalue⟩ := ih
        obtain ⟨u, hu0, hu1, hdouble⟩ := hstep s hs0 hs1
        have hn : 0 ≤ (n : ℝ) * g t := mul_nonneg (Nat.cast_nonneg n) hpos.le
        refine ⟨u, hu0, hu1, ?_⟩
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith only [hn, hvalue, hdouble]
  obtain ⟨n, hn⟩ := exists_nat_gt (M / g t)
  have hlarge : M < (n : ℝ) * g t := (div_lt_iff₀ hpos).mp hn
  obtain ⟨s, hs0, hs1, hvalue⟩ := hgrowth n
  have hsmall := hbound s hs0 hs1
  linarith only [hlarge, hsmall, hvalue, hpos]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_of_midpoint_norm_power_bound
    (q : ℝ) (hq : 0 ≤ q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (hbound : ∀ x, F x ≤ ‖x‖ ^ q)
    (hmid : ∀ x y, F ((2 : ℝ)⁻¹ • (x + y)) ≤ (F x + F y) / 2) :
    ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let g : ℝ → ℝ := fun t =>
    F ((1 - t) • x + t • y) - ((1 - t) * F x + t * F y)
  have hgmid (s t : ℝ) : g ((s + t) / 2) ≤ (g s + g t) / 2 := by
    have he : (2 : ℝ)⁻¹ •
        (((1 - s) • x + s • y) + ((1 - t) • x + t • y)) =
        (1 - (s + t) / 2) • x + ((s + t) / 2) • y := by module
    have hm := hmid ((1 - s) • x + s • y) ((1 - t) • x + t • y)
    rw [he] at hm
    dsimp [g]
    nlinarith only [hm]
  have hgzero : g 0 ≤ 0 := by simp [g]
  have hgone : g 1 ≤ 0 := by simp [g]
  have hgBound (t : ℝ) (htzero : 0 ≤ t) (htone : t ≤ 1) :
      g t ≤ (‖x‖ + ‖y‖) ^ q := by
    have hleft : 0 ≤ 1 - t := sub_nonneg.mpr htone
    have hnorm : ‖(1 - t) • x + t • y‖ ≤ ‖x‖ + ‖y‖ := by
      calc
        ‖(1 - t) • x + t • y‖ ≤ ‖(1 - t) • x‖ + ‖t • y‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖y‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hleft,
            abs_of_nonneg htzero]
        _ ≤ ‖x‖ + ‖y‖ := add_le_add
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 htzero) (norm_nonneg x))
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right htone (norm_nonneg y))
    have hupper := (hbound ((1 - t) • x + t • y)).trans
      (Real.rpow_le_rpow (norm_nonneg _) hnorm hq)
    have hlinear : 0 ≤ (1 - t) * F x + t * F y :=
      add_nonneg (mul_nonneg hleft (hF x)) (mul_nonneg htzero (hF y))
    dsimp [g]
    linarith only [hupper, hlinear]
  have hbone : b ≤ 1 := by linarith only [ha, hab]
  have hvalue := nonpos_on_unit_interval_of_midpoint g hgmid hgzero hgone
    ((‖x‖ + ‖y‖) ^ q) hgBound b hb hbone
  have hae : a = 1 - b := by linarith only [hab]
  rw [hae]
  change F ((1 - b) • x + b • y) ≤ (1 - b) * F x + b * F y
  exact sub_nonpos.mp hvalue

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicConvexPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def FiniteDyadicCotype (q A : ℝ) : Prop :=
  ∀ t : DyadicTree E, DyadicTree.root t = 0 →
    DyadicTree.energy q t ≤ A * DyadicTree.moment q t

variable {E}

namespace DyadicConvex

open DyadicTree

noncomputable def cost (q β : ℝ) (t : DyadicTree E) : ℝ :=
  moment q t - β * energy q t

def values (q β : ℝ) (x : E) : Set ℝ :=
  {z | ∃ t : DyadicTree E, root t = x ∧ cost q β t = z}

noncomputable def potential (q β : ℝ) (x : E) : ℝ :=
  sInf (values q β x)

theorem values_nonempty (q β : ℝ) (x : E) : (values q β x).Nonempty :=
  ⟨cost q β (leaf x), leaf x, rfl, rfl⟩

theorem cost_leaf (q β : ℝ) (x : E) : cost q β (leaf x) = ‖x‖ ^ q := by
  simp only [cost, moment_leaf, energy_leaf, mul_zero, sub_zero]

theorem cost_node (q β : ℝ) (t u : DyadicTree E) :
    cost q β (node t u) = (cost q β t + cost q β u) / 2 -
      β * ‖(2 : ℝ)⁻¹ • (root t - root u)‖ ^ q := by
  simp only [cost, moment_node, energy_node]
  ring

theorem cost_scale (q β a : ℝ) (t : DyadicTree E) :
    cost q β (scale a t) = ‖a‖ ^ q * cost q β t := by
  simp only [cost, moment_scale, energy_scale, Real.norm_eq_abs]
  ring

theorem root_add_energy_le {q A : ℝ} (hc : FiniteDyadicCotype E q A)
    (t : DyadicTree E) : ‖root t‖ ^ q + energy q t ≤ A * moment q t := by
  have hr : root (node t (scale (-1 : ℝ) t)) = 0 := by
    rw [root_node, root_scale]
    simp only [neg_one_smul, add_neg_cancel, smul_zero]
  have h := hc (node t (scale (-1 : ℝ) t)) hr
  simp only [energy_node, moment_node, energy_scale, moment_scale, root_scale,
    abs_neg, abs_one, Real.one_rpow, one_mul, neg_one_smul] at h
  have he : (2 : ℝ)⁻¹ • (root t - -root t) = root t := by module
  rw [he] at h
  nlinarith only [h]

theorem cost_lower {q A : ℝ} (hA : 0 < A) (hc : FiniteDyadicCotype E q A)
    (t : DyadicTree E) : A⁻¹ * ‖root t‖ ^ q ≤ cost q A⁻¹ t := by
  have h := mul_le_mul_of_nonneg_left (root_add_energy_le hc t)
    (inv_nonneg.mpr hA.le)
  have h' : A⁻¹ * ‖root t‖ ^ q + A⁻¹ * energy q t ≤ moment q t := by
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] using h
  unfold cost
  linarith only [h']

theorem values_bddBelow {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) : BddBelow (values q A⁻¹ x) := by
  refine ⟨A⁻¹ * ‖x‖ ^ q, ?_⟩
  rintro z ⟨t, ht, rfl⟩
  simpa only [ht] using cost_lower hA hc t

theorem potential_lower {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    A⁻¹ * ‖x‖ ^ q ≤ potential q A⁻¹ x := by
  apply le_csInf (values_nonempty q A⁻¹ x)
  rintro z ⟨t, ht, rfl⟩
  simpa only [ht] using cost_lower hA hc t

theorem potential_le_cost {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (t : DyadicTree E) {x : E}
    (ht : root t = x) : potential q A⁻¹ x ≤ cost q A⁻¹ t :=
  csInf_le (values_bddBelow hA hc x) ⟨t, ht, rfl⟩

theorem potential_upper {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    potential q A⁻¹ x ≤ ‖x‖ ^ q := by
  simpa only [cost_leaf] using potential_le_cost hA hc (leaf x) (x := x) rfl

theorem potential_nonneg {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) : 0 ≤ potential q A⁻¹ x :=
  (mul_nonneg (inv_nonneg.mpr hA.le) (Real.rpow_nonneg (norm_nonneg x) q)).trans
    (potential_lower hA hc x)

theorem potential_zero {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : potential q A⁻¹ (0 : E) = 0 := by
  apply le_antisymm _ (potential_nonneg hA hc 0)
  simpa only [norm_zero, Real.zero_rpow hq.ne'] using potential_upper hA hc (0 : E)

theorem exists_cost_lt (q β : ℝ) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : DyadicTree E, root t = x ∧ cost q β t < potential q β x + ε := by
  have hlt : potential q β x < potential q β x + ε := lt_add_of_pos_right _ hε
  obtain ⟨z, ⟨t, ht, hz⟩, hzt⟩ :=
    exists_lt_of_csInf_lt (values_nonempty q β x) hlt
  exact ⟨t, ht, by simpa only [hz] using hzt⟩

theorem potential_midpoint {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x y : E) :
    potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
        A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q ≤
      (potential q A⁻¹ x + potential q A⁻¹ y) / 2 := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
          A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q ≤
        (potential q A⁻¹ x + potential q A⁻¹ y) / 2 + ε := by
    obtain ⟨t, ht, hcostt⟩ := exists_cost_lt q A⁻¹ x ε hε
    obtain ⟨u, hu, hcostu⟩ := exists_cost_lt q A⁻¹ y ε hε
    have hroot : root (node t u) = (2 : ℝ)⁻¹ • (x + y) := by
      rw [root_node, ht, hu]
    have hcost := potential_le_cost hA hc (node t u) hroot
    rw [cost_node, ht, hu] at hcost
    linarith only [hcost, hcostt, hcostu]
  by_contra h
  have hgap : 0 < potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
      A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q -
      (potential q A⁻¹ x + potential q A⁻¹ y) / 2 := sub_pos.mpr (lt_of_not_ge h)
  have hε := happrox
    ((potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
      A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q -
      (potential q A⁻¹ x + potential q A⁻¹ y) / 2) / 2)
    (half_pos hgap)
  linarith only [hε, hgap]

theorem potential_convex {q A : ℝ} (hq : 0 ≤ q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : ConvexOn ℝ Set.univ (potential q A⁻¹ : E → ℝ) := by
  apply convexOn_of_midpoint_norm_power_bound q hq (potential q A⁻¹)
    (potential_nonneg hA hc) (potential_upper hA hc)
  intro x y
  have h := potential_midpoint hA hc x y
  have hterm : 0 ≤ A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q :=
    mul_nonneg (inv_nonneg.mpr hA.le) (Real.rpow_nonneg (norm_nonneg _) q)
  linarith only [h, hterm]

theorem potential_scale_le {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (a : ℝ) (ha : a ≠ 0) (x : E) :
    potential q A⁻¹ (a • x) ≤ ‖a‖ ^ q * potential q A⁻¹ x := by
  have hpos : 0 < ‖a‖ ^ q := Real.rpow_pos_of_pos (norm_pos_iff.mpr ha) q
  have hquot : potential q A⁻¹ (a • x) / (‖a‖ ^ q) ≤ potential q A⁻¹ x := by
    apply le_csInf (values_nonempty q A⁻¹ x)
    rintro z ⟨t, ht, rfl⟩
    apply (div_le_iff₀ hpos).mpr
    have hroot : root (scale a t) = a • x := by rw [root_scale, ht]
    have h := potential_le_cost hA hc (scale a t) hroot
    simpa only [cost_scale, mul_comm] using h
  simpa only [mul_comm] using (div_le_iff₀ hpos).mp hquot

theorem potential_homogeneous {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (a : ℝ) (x : E) :
    potential q A⁻¹ (a • x) = ‖a‖ ^ q * potential q A⁻¹ x := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, potential_zero hq hA hc, norm_zero,
      Real.zero_rpow hq.ne', zero_mul]
  · apply le_antisymm (potential_scale_le hA hc a ha x)
    have h := potential_scale_le hA hc a⁻¹ (inv_ne_zero ha) (a • x)
    have he : a⁻¹ • (a • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [he, norm_inv, Real.inv_rpow (norm_nonneg a)] at h
    have hpos : 0 < ‖a‖ ^ q := Real.rpow_pos_of_pos (norm_pos_iff.mpr ha) q
    have hm := mul_le_mul_of_nonneg_left h hpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] using hm

noncomputable def seminorm {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : Seminorm ℝ E :=
  potentialSeminorm q hq (potential q A⁻¹) (potential_nonneg hA hc)
    (potential_homogeneous hq hA hc) (potential_convex hq.le hA hc)

theorem seminorm_upper {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) : seminorm hq hA hc x ≤ ‖x‖ :=
  (potentialRoot_le_iff q hq (potential q A⁻¹) (potential_nonneg hA hc)
    x ‖x‖ (norm_nonneg x)).mpr (potential_upper hA hc x)

theorem seminorm_lower {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    (A⁻¹ ^ (1 / q)) * ‖x‖ ≤ seminorm hq hA hc x := by
  have hβ : 0 ≤ A⁻¹ := inv_nonneg.mpr hA.le
  apply (le_potentialRoot_iff q hq (potential q A⁻¹) (potential_nonneg hA hc)
    x ((A⁻¹ ^ (1 / q)) * ‖x‖)
    (mul_nonneg (Real.rpow_nonneg hβ _) (norm_nonneg x))).mpr
  rw [Real.mul_rpow (Real.rpow_nonneg hβ _) (norm_nonneg x), one_div,
    Real.rpow_inv_rpow hβ hq.ne']
  exact potential_lower hA hc x

noncomputable def equivalentNorm {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : EquivalentNorm E where
  p := seminorm hq hA hc
  lower := A⁻¹ ^ (1 / q)
  upper := 1
  lower_pos := Real.rpow_pos_of_pos (inv_pos.mpr hA) _
  upper_pos := zero_lt_one
  lower_bound := seminorm_lower hq hA hc
  upper_bound x := by simpa only [one_mul] using seminorm_upper hq hA hc x

end DyadicConvex

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePowerIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace MarkovSuperreflexivity

noncomputable def lowerPowerKernel (s r t : ℝ) : ℝ :=
  if 0 < t ∧ t < r then t ^ (s - 1) else 0

noncomputable def upperPowerKernel (s r t : ℝ) : ℝ :=
  if 0 < t ∧ r ≤ t then t ^ (-s - 1) else 0

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMarcinkiewicz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace MarkovSuperreflexivity

variable {I Ω E F : Type*} [sectionFintypeI : Fintype I] [Fintype Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

noncomputable def finiteMoment (w : I → ℝ) (p : ℝ) (φ : I → E) : ℝ :=
  ∑ i, w i * ‖φ i‖ ^ p

noncomputable def finiteTail (ν : Ω → ℝ) (f : Ω → F) (t : ℝ) : ℝ :=
  ∑ ω, if t < ‖f ω‖ then ν ω else 0

noncomputable def largeCut (φ : I → E) (t : ℝ) : I → E :=
  fun i => if t < ‖φ i‖ then φ i else 0

section Linear

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

def FiniteWeakType (w : I → ℝ) (ν : Ω → ℝ)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) (p A : ℝ) : Prop :=
  ∀ (φ : I → E) (t : ℝ), 0 < t →
    finiteTail ν (T φ) t ≤ (A / t) ^ p * finiteMoment w p φ

end Linear

noncomputable def largeMomentKernel (p q r t : ℝ) : ℝ :=
  r ^ q * lowerPowerKernel (p - q) r t

noncomputable def smallMomentKernel (p q r t : ℝ) : ℝ :=
  r ^ q * upperPowerKernel (q - p) r t

noncomputable def finiteLayerKernel (ν : Ω → ℝ) (p : ℝ) (f : Ω → F) (t : ℝ) : ℝ :=
  p * ∑ ω, ν ω * lowerPowerKernel p ‖f ω‖ t

noncomputable def finiteLargeKernel (w : I → ℝ) (p q : ℝ) (φ : I → E) (t : ℝ) : ℝ :=
  ∑ i, w i * largeMomentKernel p q ‖φ i‖ t

noncomputable def finiteSmallKernel (w : I → ℝ) (p q : ℝ) (φ : I → E) (t : ℝ) : ℝ :=
  ∑ i, w i * smallMomentKernel p q ‖φ i‖ t

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def finiteDifference (M : ℕ → Ω → E) (j : ℕ) : Ω → E :=
  if j = 0 then M 0 else fun ω => M j ω - M (j - 1) ω

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem finiteDifference_zero [Fintype Ω] [NormedSpace ℝ E] (M : ℕ → Ω → E) :
    finiteDifference M 0 = M 0 := by
  simp [finiteDifference]

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem finiteDifference_succ [Fintype Ω] [NormedSpace ℝ E] (M : ℕ → Ω → E) (j : ℕ) (ω : Ω) :
    finiteDifference M (j + 1) ω = M (j + 1) ω - M j ω := by
  simp [finiteDifference]

def HasZeroConditionalSum (μ : FiniteLaw Ω) (P : Setoid Ω) (f : Ω → E) : Prop :=
  ∀ a : Ω, ∑ ω, (if P.r ω a then μ.mass ω • f ω else 0) = 0

namespace FinitePartitionFiltration

def IsMartingaleUpTo (F : FinitePartitionFiltration Ω) (μ : FiniteLaw Ω)
    (M : ℕ → Ω → E) (N : ℕ) : Prop :=
  (∀ j : ℕ, j ≤ N → F.AdaptedAt j (M j)) ∧
  ∀ j : ℕ, 0 < j → j ≤ N →
    HasZeroConditionalSum μ (F.part (j - 1)) (finiteDifference M j)

end FinitePartitionFiltration

def finiteL2Norm (μ : FiniteLaw Ω) (f : Ω → E) : ℝ :=
  Real.sqrt (μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)))

omit sectionNormedSpaceℝE in
@[simp] theorem finiteL2Norm_zero [NormedSpace ℝ E] (μ : FiniteLaw Ω) :
    finiteL2Norm μ (fun _ => (0 : E)) = 0 := by
  simp [finiteL2Norm, FiniteLaw.expect]

def FiniteUpperL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r χ : ℝ) : Prop :=
  ∀ m : ℕ, ∀ μ : FiniteLaw (Fin m),
  ∀ F : FinitePartitionFiltration (Fin m), ∀ M : ℕ → Fin m → E,
  ∀ N : ℕ, ∀ B : ℝ, 0 ≤ B → F.IsMartingaleUpTo μ M N →
    (∀ j : ℕ, j ≤ N → finiteL2Norm μ (finiteDifference M j) ≤ B) →
    finiteL2Norm μ (M N) ≤ χ * (N + 1 : ℝ) ^ (1 / r) * B

def FiniteLowerL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s χ : ℝ) : Prop :=
  ∀ m : ℕ, ∀ μ : FiniteLaw (Fin m),
  ∀ F : FinitePartitionFiltration (Fin m), ∀ M : ℕ → Fin m → E,
  ∀ N : ℕ, F.IsMartingaleUpTo μ M N →
    (∑ j ∈ Finset.range (N + 1), finiteL2Norm μ (finiteDifference M j)) ≤
      χ * (N + 1 : ℝ) ^ (1 - 1 / s) * finiteL2Norm μ (M N)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteDyadicMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

abbrev DyadicAtom (N : ℕ) := Unit ⊕ (Σ j : Fin N, DyadicWord j.val)

def dyadicInputWeight {N : ℕ} : DyadicAtom N → ℝ
  | .inl _ => 1
  | .inr ⟨j, α⟩ => (dyadicLaw j.val).mass α

def dyadicRoot {N : ℕ} (φ : DyadicAtom N → E) : E := φ (.inl ())

def dyadicCoefficient {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N)
    (α : DyadicWord j.val) : E := φ (.inr ⟨j, α⟩)

def dyadicSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem dyadicSign_not (b : Bool) : dyadicSign (!b) = -dyadicSign b := by
  cases b <;> norm_num [dyadicSign]

def dyadicIncrement {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N)
    (ω : DyadicWord N) : E :=
  dyadicSign (ω j) • dyadicCoefficient φ j
    (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))

@[simp] theorem norm_dyadicIncrement {N : ℕ} (φ : DyadicAtom N → E)
    (j : Fin N) (ω : DyadicWord N) :
    ‖dyadicIncrement φ j ω‖ =
      ‖dyadicCoefficient φ j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))‖ := by
  cases h : ω j <;> simp [dyadicIncrement, dyadicSign, h]

def dyadicProcess {N : ℕ} (φ : DyadicAtom N → E) : ℕ → DyadicWord N → E
  | 0 => fun _ => dyadicRoot φ
  | n + 1 => fun ω => dyadicProcess φ n ω +
      if hn : n < N then dyadicIncrement φ ⟨n, hn⟩ ω else 0

@[simp] theorem dyadicProcess_zero {N : ℕ} (φ : DyadicAtom N → E) (ω : DyadicWord N) :
    dyadicProcess φ 0 ω = dyadicRoot φ := rfl

theorem dyadicProcess_add {N : ℕ} (φ ψ : DyadicAtom N → E) (n : ℕ) (ω : DyadicWord N) :
    dyadicProcess (φ + ψ) n ω = dyadicProcess φ n ω + dyadicProcess ψ n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hn : n < N
      · simp only [dyadicProcess, dite_eq_left hn, ih, dyadicIncrement, dyadicCoefficient,
          Pi.add_apply, smul_add]
        abel
      · simp only [dyadicProcess, dite_eq_right hn, ih, add_zero]

theorem dyadicProcess_smul {N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (n : ℕ) (ω : DyadicWord N) :
    dyadicProcess (c • φ) n ω = c • dyadicProcess φ n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hn : n < N
      · simp only [dyadicProcess, dite_eq_left hn, ih, dyadicIncrement, dyadicCoefficient,
          Pi.smul_apply]
        module
      · simp only [dyadicProcess, dite_eq_right hn, ih, add_zero]

def dyadicSynthesis (N : ℕ) : (DyadicAtom N → E) →ₗ[ℝ] (DyadicWord N → E) where
  toFun φ := dyadicProcess φ N
  map_add' φ ψ := funext (dyadicProcess_add φ ψ N)
  map_smul' c φ := funext (dyadicProcess_smul c φ N)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicIndependentBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dyadicIndependentBlocks {N : ℕ} (m : ℕ) (c : ℝ) (φ : DyadicAtom N → E) :
    DyadicAtom (m * N) → E
  | .inl _ => 0
  | .inr ⟨j, α⟩ => c • dyadicCoefficient φ (finProdFinEquiv.symm j).2
      (dyadicBlockPrefix j α)

@[simp] theorem dyadicIndependentBlocks_root {N : ℕ} (m : ℕ) (c : ℝ)
    (φ : DyadicAtom N → E) : dyadicRoot (dyadicIndependentBlocks m c φ) = 0 := rfl

def dyadicCopyScale (m : ℕ) (p : ℝ) : ℝ := ((m : ℝ) ^ (1 / p))⁻¹

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicTreeMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [sectionNormedAddCommGroupE : NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

namespace DyadicTree

def branch : DyadicTree E → Bool → DyadicTree E
  | leaf x, _ => leaf x
  | node t s, b => if b then t else s

def splitCoefficient : DyadicTree E → E
  | leaf _ => 0
  | node t s => (2 : ℝ)⁻¹ • (root t - root s)

def descendant (t : DyadicTree E) : (n : ℕ) → DyadicWord n → DyadicTree E
  | 0, _ => t
  | n + 1, α => branch (descendant t n (Fin.init α)) (α (Fin.last n))

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
@[simp] theorem descendant_zero [NormedAddCommGroup E] [NormedSpace ℝ E] (t : DyadicTree E) (α : DyadicWord 0) :
    descendant t 0 α = t := rfl

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
@[simp] theorem descendant_snoc [NormedAddCommGroup E] [NormedSpace ℝ E] (t : DyadicTree E) (n : ℕ)
    (α : DyadicWord n) (b : Bool) :
    descendant t (n + 1) (Fin.snoc α b) = branch (descendant t n α) b := by
  simp only [descendant, Fin.init_snoc, Fin.snoc_last]

def coefficients (N : ℕ) (t : DyadicTree E) : DyadicAtom N → E
  | .inl _ => root t
  | .inr ⟨j, α⟩ => splitCoefficient (descendant t j.val α)

@[simp] theorem coefficients_root (N : ℕ) (t : DyadicTree E) :
    dyadicRoot (coefficients N t) = root t := rfl

@[simp] theorem coefficients_prefix (N : ℕ) (t : DyadicTree E) (j : Fin N)
    (α : DyadicWord j.val) :
    dyadicCoefficient (coefficients N t) j α = splitCoefficient (descendant t j.val α) := rfl

end DyadicTree
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicWeakMaxDefinition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def DyadicNormalizedWeakMax (a A : ℝ) : Prop :=
  ∀ (N : ℕ) (φ : DyadicAtom N → E), dyadicRoot φ = 0 →
    finiteMoment dyadicInputWeight a φ ≤ 1 →
    ∀ t : ℝ, 0 < t →
      (dyadicLaw N).prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖dyadicProcess φ j ω‖) ≤
        A / t ^ (a / 2)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicWeakAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dyadicAmplificationThreshold (a A : ℝ) : ℝ := (2 * A) ^ (2 / a)
def dyadicAmplificationRadius (a A : ℝ) : ℝ := 2 * dyadicAmplificationThreshold a A
def dyadicZeroWeakConstant (a A : ℝ) : ℝ := 2 * (dyadicAmplificationRadius a A) ^ a

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicWeakType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def dyadicCenter {N : ℕ} (φ : DyadicAtom N → E) : DyadicAtom N → E
  | .inl _ => 0
  | .inr z => φ (.inr z)

omit sectionNormedSpaceℝE in
@[simp] theorem dyadicRoot_center [NormedSpace ℝ E] {N : ℕ} (φ : DyadicAtom N → E) :
    dyadicRoot (dyadicCenter φ) = 0 := rfl

omit sectionNormedSpaceℝE in
@[simp] theorem dyadicCoefficient_center [NormedSpace ℝ E] {N : ℕ} (φ : DyadicAtom N → E)
    (j : Fin N) (α : DyadicWord j.val) :
    dyadicCoefficient (dyadicCenter φ) j α = dyadicCoefficient φ j α := rfl

def dyadicWeakConstant (a A : ℝ) : ℝ := (2 : ℝ) ^ a * dyadicZeroWeakConstant a A

def dyadicWeakNorm (a A : ℝ) : ℝ := dyadicWeakConstant a A ^ (1 / a)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dyadicInterpolationConstant (a₀ p a₁ B₀ B₁ : ℝ) : ℝ :=
  p * ((2 * B₀) ^ a₀ / (p - a₀) + (2 * B₁) ^ a₁ / (a₁ - p))

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SmoothnessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

def SymmetricPowerSmooth (p : Seminorm ℝ X) (q A : ℝ) : Prop :=
  ∀ x y : X, (p (x + y) ^ q + p (x - y) ^ q) / 2 ≤
    p x ^ q + A * p y ^ q

def PowerSmooth (p : Seminorm ℝ X) (q C : ℝ) : Prop :=
  ∀ x y : X, p x = 1 → p y = 1 → ∀ t : ℝ, 0 ≤ t →
    (p (x + t • y) + p (x - t • y)) / 2 ≤ 1 + C * t ^ q

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicSmoothRenorming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

noncomputable def dyadicPowerSeminorm {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) : Seminorm ℝ X :=
  potentialSeminorm p (lt_of_lt_of_le zero_lt_one hp) (bellmanPotential p K)
    (bellmanPotential_nonneg hMT)
    (fun a x => by
      simpa only [Real.norm_eq_abs] using
        bellmanPotential_smul (lt_of_lt_of_le zero_lt_one hp) hMT a x)
    (bellmanPotential_convex hp hMT)

@[simp] theorem dyadicPowerSeminorm_apply {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    dyadicPowerSeminorm hp hMT x = bellmanPotential p K x ^ (1 / p) := rfl

theorem dyadicPowerSeminorm_rpow {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    (dyadicPowerSeminorm hp hMT x) ^ p = bellmanPotential p K x :=
  potentialSeminorm_rpow _ _ _ _ _ _ _

theorem norm_le_dyadicPowerSeminorm {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    ‖x‖ ≤ dyadicPowerSeminorm hp hMT x := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg x)
    (apply_nonneg (dyadicPowerSeminorm hp hMT) x)
    (lt_of_lt_of_le zero_lt_one hp)).1
  rw [dyadicPowerSeminorm_rpow]
  exact (bellmanPotential_bounds hMT x).1

theorem dyadicPowerSeminorm_le_mul_norm {p A K L : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K)
    (hL : 0 ≤ L) (hA : A ≤ L ^ p) (x : X) :
    dyadicPowerSeminorm hp hMT x ≤ L * ‖x‖ := by
  apply (Real.rpow_le_rpow_iff (apply_nonneg (dyadicPowerSeminorm hp hMT) x)
    (mul_nonneg hL (norm_nonneg x)) (lt_of_lt_of_le zero_lt_one hp)).1
  rw [dyadicPowerSeminorm_rpow, Real.mul_rpow hL (norm_nonneg x)]
  exact (bellmanPotential_bounds hMT x).2.trans
    (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (norm_nonneg x) p))

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_NormCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def SupportedBelow (x : C00) (B : ℕ) : Prop := ∀ i, B ≤ i → x i = 0

def skipAfter (i j : ℕ) : ℕ := if j ≤ i then j else j + 1

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PrefixBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem prefixBlocks_prefixCut_add (x y : C00) (k : ℕ) :
    prefixCut (x + y) k = prefixCut x k + prefixCut y k := by
  simp only [prefixCut, Finsupp.add_apply, Finset.sum_add_distrib]

theorem prefixBlocks_prefixCut_smul (a : ℝ) (x : C00) (k : ℕ) :
    prefixCut (a • x) k = a * prefixCut x k := by
  simp only [prefixCut, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]

@[simp] theorem prefixCut_single (i : ℕ) (a : ℝ) (k : ℕ) :
    prefixCut (Finsupp.single i a) k = if i < k then a else 0 := by
  classical
  unfold prefixCut
  by_cases hi : i < k
  · rw [ite_eq_left hi, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact Finsupp.single_eq_of_ne hji
    · simp [Finset.mem_range, hi]
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finsupp.single_eq_of_ne
    have hjk := Finset.mem_range.mp hj
    omega

def blockIndex {r : ℕ} (c : Fin (r + 1) → ℕ) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin r => c j.succ ≤ i).card

def prefixBlockCoeffs {r : ℕ} (c : Fin (r + 1) → ℕ) :
    C00 →ₗ[ℝ] (Fin r → ℝ) where
  toFun x j := prefixCut x (c j.succ) - prefixCut x (c j.castSucc)
  map_add' x y := by
    funext j
    simp only [prefixBlocks_prefixCut_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext j
    simp only [prefixBlocks_prefixCut_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def prefixBlocksLinear {r : ℕ} (c : Fin (r + 1) → ℕ) : C00 →ₗ[ℝ] C00 :=
  (C00.arrayLinear r).comp (prefixBlockCoeffs c)

@[simp] theorem prefixBlocksLinear_apply {r : ℕ} (c : Fin (r + 1) → ℕ) (x : C00) :
    prefixBlocksLinear c x =
      C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
        prefixCut x (c j.castSucc)) := rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PrefixIndicators
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

@[simp] theorem prefixCut_add (x y : C00) (k : ℕ) :
    prefixCut (x + y) k = prefixCut x k + prefixCut y k := by
  simp only [prefixCut, Finsupp.add_apply, Finset.sum_add_distrib]

@[simp] theorem prefixCut_sub (x y : C00) (k : ℕ) :
    prefixCut (x - y) k = prefixCut x k - prefixCut y k := by
  simp only [prefixCut, Finsupp.sub_apply, Finset.sum_sub_distrib]

@[simp] theorem prefixCut_neg (x : C00) (k : ℕ) :
    prefixCut (-x) k = -prefixCut x k := by
  simp only [prefixCut, Finsupp.neg_apply, Finset.sum_neg_distrib]

@[simp] theorem prefixCut_smul (r : ℝ) (x : C00) (k : ℕ) :
    prefixCut (r • x) k = r * prefixCut x k := by
  simp only [prefixCut, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]

@[simp] theorem prefixCut_basis (i k : ℕ) :
    prefixCut (C00.basis i) k = if i < k then (1 : ℝ) else 0 := by
  classical
  simp [prefixCut, C00.basis, Finsupp.single_apply, Finset.mem_range]

namespace PrefixIndicators

def halfOpen (a b y : ℝ) : ℝ := if a ≤ y ∧ y < b then 1 else 0

def periodic (a b y : ℝ) : ℝ := by
  classical
  exact if ∃ j : ℤ, a + (j : ℝ) ≤ y ∧ y < b + (j : ℝ) then 1 else 0

end PrefixIndicators

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_EndNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def endpointAlternating (M : ℕ) (ell V : ℝ) : C00 :=
  V • (basis 0 - basis (2 * M + 1)) + ell • shift 1 (alternating M)

def collapseTail (i : ℕ) : ℕ := if i = 0 then 0 else 1

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitelyRepresentable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u v w

def FinitelyRepresentable (Y : Type v) (X : Type u)
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (E : Submodule ℝ Y) [FiniteDimensional ℝ E] (η : ℝ), 0 < η →
    ∃ T : E →ₗ[ℝ] X, ∀ z : E,
      ‖z‖ ≤ ‖T z‖ ∧ ‖T z‖ ≤ (1 + η) * ‖z‖

def CanonicallyReflexive (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure TriangularSystem (n : ℕ) (θ : ℝ) where
  vectors : Fin n → X
  functionals : Fin n → StrongDual ℝ X
  vectors_bound : ∀ i, ‖vectors i‖ ≤ 1
  functionals_bound : ∀ j, ‖functionals j‖ ≤ 1
  pairing : ∀ i j, functionals j (vectors i) = if j ≤ i then θ else 0

def FiniteTriangularObstruction : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ n : ℕ, 0 < n ∧ ¬ Nonempty (TriangularSystem X n θ)

variable {X}

namespace TriangularSystem

variable {n m : ℕ} {θ : ℝ}

def restrict (s : TriangularSystem X n θ) (h : m ≤ n) : TriangularSystem X m θ where
  vectors i := s.vectors (Fin.castLE h i)
  functionals j := s.functionals (Fin.castLE h j)
  vectors_bound i := s.vectors_bound (Fin.castLE h i)
  functionals_bound j := s.functionals_bound (Fin.castLE h j)
  pairing i j := by
    have hle : (Fin.castLE h j ≤ Fin.castLE h i) ↔ j ≤ i := Iff.rfl
    simpa only [hle] using s.pairing (Fin.castLE h i) (Fin.castLE h j)

end TriangularSystem

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FailureJApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure ApproximateTailSystem (n : ℕ) (η : ℝ) where
  vectors : Fin n → X
  functionals : Fin n → StrongDual ℝ X
  vectors_bound : ∀ i, ‖vectors i‖ ≤ 1
  functionals_bound : ∀ j, ‖functionals j‖ ≤ 1
  pairing_error : ∀ i j,
    |functionals j (vectors i) - (if j ≤ i then (1 : ℝ) else 0)| ≤ η

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteTailCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

def finiteCoefficientTail {n : ℕ} (a : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, if j ≤ i then a i else 0

noncomputable def finiteTailLinear (n : ℕ) (j : Fin n) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun a := finiteCoefficientTail a j
  map_add' a b := by
    change (∑ i, if j ≤ i then a i + b i else 0) =
      (∑ i, if j ≤ i then a i else 0) + ∑ i, if j ≤ i then b i else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hji : j ≤ i <;> simp only [hji, ite_true, ite_false, add_zero]
  map_smul' c a := by
    change (∑ i, if j ≤ i then c * a i else 0) =
      c * ∑ i, if j ≤ i then a i else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hji : j ≤ i <;> simp only [hji, ite_true, ite_false, mul_zero]

@[simp] theorem finiteTailLinear_apply (n : ℕ) (j : Fin n) (a : Fin n → ℝ) :
    finiteTailLinear n j a = finiteCoefficientTail a j := rfl

@[simp] theorem finiteTail_zero {n : ℕ} (j : Fin n) :
    finiteCoefficientTail (0 : Fin n → ℝ) j = 0 := by
  simp [finiteCoefficientTail]

@[simp] theorem finiteTail_single {n : ℕ} (i j : Fin n) (a : ℝ) :
    finiteCoefficientTail (Pi.single i a) j = if j ≤ i then a else 0 := by
  classical
  unfold finiteCoefficientTail
  calc
    (∑ k, if j ≤ k then (Pi.single i a : Fin n → ℝ) k else 0) =
        if j ≤ i then (Pi.single i a : Fin n → ℝ) i else 0 := by
      apply Fintype.sum_eq_single i
      intro k hki
      simp only [Pi.single_eq_of_ne hki, ite_self]
    _ = if j ≤ i then a else 0 := by rw [Pi.single_eq_same]

theorem finiteTail_sub_next {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hnext : i.val + 1 < n) :
    finiteCoefficientTail a i - finiteCoefficientTail a ⟨i.val + 1, hnext⟩ = a i := by
  classical
  unfold finiteCoefficientTail
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin n, ((if i ≤ j then a j else 0) -
        (if (⟨i.val + 1, hnext⟩ : Fin n) ≤ j then a j else 0))) =
        ∑ j : Fin n, if j = i then a j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        have hnot : ¬ (⟨i.val + 1, hnext⟩ : Fin n) ≤ i := by
          change ¬ i.val + 1 ≤ i.val
          omega
        simp only [le_refl, ite_true, hnot, ite_false, sub_zero]
      · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
        have hle : (i ≤ j) ↔ ((⟨i.val + 1, hnext⟩ : Fin n) ≤ j) := by
          change (i.val ≤ j.val) ↔ (i.val + 1 ≤ j.val)
          omega
        simp only [hle, hji, ite_false, sub_self]
    _ = a i := by simp

theorem eq_finiteTail_sub_next {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hnext : i.val + 1 < n) :
    a i = finiteCoefficientTail a i - finiteCoefficientTail a ⟨i.val + 1, hnext⟩ :=
  (finiteTail_sub_next a i hnext).symm

theorem finiteTail_eq_of_last {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hlast : i.val + 1 = n) : finiteCoefficientTail a i = a i := by
  classical
  unfold finiteCoefficientTail
  calc
    (∑ j : Fin n, if i ≤ j then a j else 0) =
        ∑ j : Fin n, if j = i then a j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      have hle : (i ≤ j) ↔ j = i := by
        constructor
        · intro hij
          apply Fin.ext
          change i.val ≤ j.val at hij
          have hjn := j.isLt
          omega
        · intro hji
          subst j
          exact le_rfl
      simp only [hle]
    _ = a i := by simp

@[simp] theorem finiteTail_last {n : ℕ} (a : Fin (n + 1) → ℝ) :
    finiteCoefficientTail a (Fin.last n) = a (Fin.last n) :=
  finiteTail_eq_of_last a (Fin.last n) rfl

theorem abs_le_two_mul_of_finiteTail_le {n : ℕ} (a : Fin n → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ j, |finiteCoefficientTail a j| ≤ M) (i : Fin n) :
    |a i| ≤ 2 * M := by
  by_cases hnext : i.val + 1 < n
  · rw [eq_finiteTail_sub_next a i hnext]
    calc
      |finiteCoefficientTail a i - finiteCoefficientTail a ⟨i.val + 1, hnext⟩| ≤
          |finiteCoefficientTail a i| + |finiteCoefficientTail a ⟨i.val + 1, hnext⟩| := abs_sub _ _
      _ ≤ M + M := add_le_add (h i) (h ⟨i.val + 1, hnext⟩)
      _ = 2 * M := by ring
  · have hlast : i.val + 1 = n := by
      have hin := i.isLt
      omega
    have hi : |a i| ≤ M := by
      rw [← finiteTail_eq_of_last a i hlast]
      exact h i
    linarith

theorem sum_abs_le_two_mul_card_mul_of_finiteTail_le {n : ℕ}
    (a : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j, |finiteCoefficientTail a j| ≤ M) :
    (∑ i, |a i|) ≤ 2 * (n : ℝ) * M := by
  calc
    (∑ i, |a i|) ≤ ∑ _i : Fin n, 2 * M := by
      exact Finset.sum_le_sum (fun i _ => abs_le_two_mul_of_finiteTail_le a hM h i)
    _ = 2 * (n : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem eq_zero_of_finiteTail_eq_zero {n : ℕ} (a : Fin n → ℝ)
    (h : ∀ j, finiteCoefficientTail a j = 0) : a = 0 := by
  have hbound : ∀ j, |finiteCoefficientTail a j| ≤ (0 : ℝ) := by
    intro j
    simpa only [h j, abs_zero] using (le_refl (0 : ℝ))
  funext i
  have hi := abs_le_two_mul_of_finiteTail_le a (le_refl 0) hbound i
  have habs : |a i| = 0 := le_antisymm (by simpa only [mul_zero] using hi) (abs_nonneg _)
  exact abs_eq_zero.mp habs

theorem exists_finiteTail_abs_max {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) :
    ∃ j : Fin n, ∀ i : Fin n, |finiteCoefficientTail a i| ≤ |finiteCoefficientTail a j| := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => |finiteCoefficientTail a i|) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩

theorem finiteTail_le_two_norm_of_approx {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] X) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : 2 * (n : ℝ) * η ≤ (1 / 2 : ℝ))
    (happrox : ∀ (a : Fin n → ℝ) (j : Fin n),
      |finiteCoefficientTail a j| ≤ ‖A a‖ + η * ∑ i, |a i|) :
    ∀ (a : Fin n → ℝ) (j : Fin n), |finiteCoefficientTail a j| ≤ 2 * ‖A a‖ := by
  intro a j
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  obtain ⟨jmax, hmax⟩ := exists_finiteTail_abs_max a hn
  have hM : 0 ≤ |finiteCoefficientTail a jmax| := abs_nonneg _
  have hsum := sum_abs_le_two_mul_card_mul_of_finiteTail_le a hM hmax
  have herror : η * (∑ i, |a i|) ≤ (1 / 2 : ℝ) * |finiteCoefficientTail a jmax| := by
    calc
      η * (∑ i, |a i|) ≤ η * (2 * (n : ℝ) * |finiteCoefficientTail a jmax|) :=
        mul_le_mul_of_nonneg_left hsum hη
      _ = (2 * (n : ℝ) * η) * |finiteCoefficientTail a jmax| := by ring
      _ ≤ (1 / 2 : ℝ) * |finiteCoefficientTail a jmax| :=
        mul_le_mul_of_nonneg_right hsmall hM
  have hmaxnorm : |finiteCoefficientTail a jmax| ≤ 2 * ‖A a‖ := by
    have hpair := happrox a jmax
    linarith
  exact (hmax j).trans hmaxnorm

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FailureJTriangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def finiteArrayRealize {n : ℕ} (x : Fin n → X) : (Fin n → ℝ) →ₗ[ℝ] X where
  toFun a := ∑ i, a i • x i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp] theorem finiteArrayRealize_apply {n : ℕ} (x : Fin n → X) (a : Fin n → ℝ) :
    finiteArrayRealize x a = ∑ i, a i • x i := rfl

@[simp] theorem finiteArrayRealize_single {n : ℕ} (x : Fin n → X) (i : Fin n) :
    finiteArrayRealize x (Pi.single i 1) = x i := by
  classical
  simp [finiteArrayRealize, Pi.single_apply]

namespace ApproximateTailSystem

variable {n : ℕ} {η : ℝ}

theorem realization_pairing_error (s : ApproximateTailSystem X n η)
    (a : Fin n → ℝ) (j : Fin n) :
    |s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j| ≤
      η * ∑ i, |a i| := by
  classical
  have heq : s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j =
      ∑ i, a i * (s.functionals j (s.vectors i) - if j ≤ i then 1 else 0) := by
    simp only [finiteArrayRealize_apply, map_sum, map_smul, smul_eq_mul, finiteCoefficientTail]
    simp_rw [mul_sub, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_sub_distrib]
  rw [heq]
  calc
    |∑ i, a i * (s.functionals j (s.vectors i) - if j ≤ i then 1 else 0)|
        ≤ ∑ i, |a i * (s.functionals j (s.vectors i) - if j ≤ i then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * η := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (s.pairing_error i j) (abs_nonneg _)
    _ = η * ∑ i, |a i| := by rw [← Finset.sum_mul]; ring

theorem finiteTail_le_realization_add_error (s : ApproximateTailSystem X n η)
    (a : Fin n → ℝ) (j : Fin n) :
    |finiteCoefficientTail a j| ≤ ‖finiteArrayRealize s.vectors a‖ + η * ∑ i, |a i| := by
  have hf : |s.functionals j (finiteArrayRealize s.vectors a)| ≤
      ‖finiteArrayRealize s.vectors a‖ := by
    rw [← Real.norm_eq_abs]
    exact ((s.functionals j).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (s.functionals_bound j) (norm_nonneg _)).trans_eq
        (one_mul _))
  have ht : |finiteCoefficientTail a j| ≤
      |s.functionals j (finiteArrayRealize s.vectors a)| +
        |s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j| := by
    calc
      |finiteCoefficientTail a j| =
          |s.functionals j (finiteArrayRealize s.vectors a) -
            (s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j)| := by
        congr 1
        ring
      _ ≤ _ := abs_sub _ _
  exact ht.trans (add_le_add hf (s.realization_pairing_error a j))

def exactHalf (s : ApproximateTailSystem X n η) (hη : 0 ≤ η)
    (hsmall : 2 * (n : ℝ) * η ≤ 1 / 2) : TriangularSystem X n (1 / 2) := by
  classical
  let A : (Fin n → ℝ) →ₗ[ℝ] X := finiteArrayRealize s.vectors
  have htail (a : Fin n → ℝ) (j : Fin n) : |finiteCoefficientTail a j| ≤ 2 * ‖A a‖ :=
    finiteTail_le_two_norm_of_approx A hη hsmall
      (fun a j => s.finiteTail_le_realization_add_error a j) a j
  have hz (a : Fin n → ℝ) (ha : A a = 0) : a = 0 := by
    apply eq_zero_of_finiteTail_eq_zero
    intro j
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa only [ha, norm_zero, mul_zero] using htail a j
  have hA : Function.Injective A := by
    intro a b hab
    have hab0 : A (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hz (a - b) hab0)
  let E : Submodule ℝ X := LinearMap.range A
  let e : (Fin n → ℝ) ≃ₗ[ℝ] E := LinearEquiv.ofInjective A hA
  have hAinv (z : E) : A (e.symm z) = (z : X) :=
    LinearEquiv.ofInjective_symm_apply A z
  let tailOnImage (j : Fin n) : E →ₗ[ℝ] ℝ :=
    (1 / 2 : ℝ) • ((finiteTailLinear n j).comp e.symm.toLinearMap)
  have htailOnImage (j : Fin n) (z : E) : ‖tailOnImage j z‖ ≤ 1 * ‖z‖ := by
    change ‖(1 / 2 : ℝ) * finiteCoefficientTail (e.symm z) j‖ ≤ 1 * ‖z‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have ht := htail (e.symm z) j
    rw [hAinv] at ht
    change |finiteCoefficientTail (e.symm z) j| ≤ 2 * ‖z‖ at ht
    nlinarith
  let f (j : Fin n) : StrongDual ℝ E :=
    (tailOnImage j).mkContinuous 1 (htailOnImage j)
  have hfnorm (j : Fin n) : ‖f j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    exact htailOnImage j
  have hext (j : Fin n) : ∃ F : StrongDual ℝ X,
      (∀ z : E, F (z : X) = f j z) ∧ ‖F‖ ≤ 1 := by
    obtain ⟨F, hF, hFnorm⟩ := exists_extension_norm_eq E (f j)
    exact ⟨F, hF, hFnorm.trans_le (hfnorm j)⟩
  let F (j : Fin n) : StrongDual ℝ X := Classical.choose (hext j)
  have hF (j : Fin n) : ∀ z : E, F j (z : X) = f j z :=
    (Classical.choose_spec (hext j)).1
  have hFnorm (j : Fin n) : ‖F j‖ ≤ 1 := (Classical.choose_spec (hext j)).2
  refine {
    vectors := s.vectors
    functionals := F
    vectors_bound := s.vectors_bound
    functionals_bound := hFnorm
    pairing := ?_ }
  intro i j
  have hf := hF j (e (Pi.single i 1))
  change F j (A (Pi.single i 1)) =
    (1 / 2 : ℝ) * finiteCoefficientTail (e.symm (e (Pi.single i 1))) j at hf
  rw [e.symm_apply_apply] at hf
  simpa only [A, finiteArrayRealize_single, finiteTail_single,
    mul_ite, mul_one, mul_zero] using hf

end ApproximateTailSystem

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteGeometricBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

def dyadicMagnitudeBand (k : ℕ) (z : ℝ) : Prop :=
  (1 / 2 : ℝ) ^ (k + 1) < z ∧ z ≤ (1 / 2 : ℝ) ^ k

def bandGeometricRatio (a r : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 / r) * (1 / 2 : ℝ) ^ (1 / a)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

universe u v w

namespace MarkovSuperreflexivity

variable {Ω : Type u} {Ξ : Type v} [sectionFintypeΩ : Fintype Ω] [sectionFintypeΞ : Fintype Ξ]

namespace FiniteLaw

def reindex (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) : FiniteLaw Ξ where
  mass ξ := μ.mass (e ξ)
  mass_nonneg ξ := μ.mass_nonneg (e ξ)
  sum_mass := (e.sum_comp μ.mass).trans μ.sum_mass

@[simp] theorem reindex_mass (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (ξ : Ξ) :
    (μ.reindex e).mass ξ = μ.mass (e ξ) := rfl

@[simp] theorem expect_reindex (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (f : Ω → ℝ) :
    (μ.reindex e).expect (f ∘ e) = μ.expect f :=
  e.sum_comp (fun ω => μ.mass ω * f ω)

@[simp] theorem vexpect_reindex {V : Type w} [AddCommMonoid V] [Module ℝ V]
    (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (f : Ω → V) :
    (μ.reindex e).vexpect (f ∘ e) = μ.vexpect f :=
  e.sum_comp (fun ω => μ.mass ω • f ω)

@[simp] theorem prob_reindex (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (A : Ω → Prop) :
    (μ.reindex e).prob (A ∘ e) = μ.prob A := by
  classical
  exact e.sum_comp (fun ω => if A ω then μ.mass ω else 0)

end FiniteLaw

namespace FinitePartitionFiltration

def reindex (F : FinitePartitionFiltration Ω) (e : Ξ ≃ Ω) :
    FinitePartitionFiltration Ξ where
  part n := Setoid.comap e (F.part n)
  refines := by
    intro m n hmn ξ η hξη
    exact F.refines hmn hξη

end FinitePartitionFiltration

variable {E : Type w} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

omit sectionFintypeΩ sectionFintypeΞ sectionNormedSpaceℝE in
@[simp] theorem finiteDifference_comp_equiv [Fintype Ω] [Fintype Ξ] [NormedSpace ℝ E] (M : ℕ → Ω → E) (e : Ξ ≃ Ω)
    (j : ℕ) :
    finiteDifference (fun n => M n ∘ e) j = finiteDifference M j ∘ e := by
  funext ξ
  by_cases hj : j = 0 <;> simp only [finiteDifference, hj, Function.comp_apply,
    ite_true, ite_false]

omit sectionNormedSpaceℝE in
@[simp] theorem finiteL2Norm_reindex [NormedSpace ℝ E] (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (f : Ω → E) :
    finiteL2Norm (μ.reindex e) (f ∘ e) = finiteL2Norm μ f := by
  change Real.sqrt ((μ.reindex e).expect ((fun ω => ‖f ω‖ ^ (2 : ℕ)) ∘ e)) =
    Real.sqrt (μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)))
  rw [μ.expect_reindex]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSmoothMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def SymmetricPowerSmoothWith (q D : ℝ) (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ x y : X, ‖x + y‖ ^ q + ‖x - y‖ ^ q ≤
    2 * ‖x‖ ^ q + 2 * D * ‖y‖ ^ q

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteConditionalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteLaw

variable {Ω K J : Type*} [Fintype Ω] [DecidableEq K] [DecidableEq J]

def fiberWeight (μ : FiniteLaw Ω) (key : Ω → K) (a : K) (ω : Ω) : ℝ :=
  if key ω = a then μ.mass ω else 0

def fiberMass (μ : FiniteLaw Ω) (key : Ω → K) (a : K) : ℝ :=
  ∑ ω, μ.fiberWeight key a ω

def normalizedFiberWeight (μ : FiniteLaw Ω) (key : Ω → K) (a : K) (ω : Ω) : ℝ :=
  (μ.fiberMass key a)⁻¹ * μ.fiberWeight key a ω

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

def fiberSum (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) (a : K) : E :=
  ∑ ω, μ.fiberWeight key a ω • F ω

def conditionalMean (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) (a : K) : E :=
  (μ.fiberMass key a)⁻¹ • μ.fiberSum key F a

def conditionalAverage (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) (ω : Ω) : E :=
  μ.conditionalMean key F (key ω)

end Module

end MarkovSuperreflexivity.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePredictableSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def finiteSelectedValue (N : ℕ) (d : ℕ → Ω → E) (σ : Ω → ℕ) (ω : Ω) : E :=
  if σ ω ≤ N then d (σ ω) ω else 0

namespace FinitePartitionFiltration

def selectedFiltration (F : FinitePartitionFiltration Ω) (τ : ℕ → Ω → ℕ)
    (hstop : ∀ i, F.IsStoppingTime (τ i))
    (hmono : ∀ ω, Monotone (fun i => τ i ω)) : FinitePartitionFiltration Ω where
  part i := F.stoppedSetoid (τ i)
  refines := by
    intro i j hij ω η hωη
    exact F.stoppedSetoid_refines (hstop i) (fun ω => hmono ω hij) hωη

end FinitePartitionFiltration

def finiteSelectedProcess (N : ℕ) (d : ℕ → Ω → E) (τ : ℕ → Ω → ℕ)
    (j : ℕ) (ω : Ω) : E :=
  ∑ i ∈ Finset.range j, finiteSelectedValue N d (τ (i + 1)) ω

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem finiteSelectedProcess_zero [Fintype Ω] [NormedSpace ℝ E] (N : ℕ) (d : ℕ → Ω → E)
    (τ : ℕ → Ω → ℕ) (ω : Ω) : finiteSelectedProcess N d τ 0 ω = 0 := by
  simp [finiteSelectedProcess]

@[simp] theorem finiteDifference_selectedProcess_succ (N : ℕ) (d : ℕ → Ω → E)
    (τ : ℕ → Ω → ℕ) (j : ℕ) (ω : Ω) :
    finiteDifference (finiteSelectedProcess N d τ) (j + 1) ω =
      finiteSelectedValue N d (τ (j + 1)) ω := by
  rw [finiteDifference_succ]
  simp only [finiteSelectedProcess, Finset.sum_range_succ]
  abel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSelectionCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω : Type*}

def selectionPredicate (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) (n : ℕ) : Prop :=
  0 < n ∧ n ≤ N ∧ B n ω

def selectionCount (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) : ℕ :=
  Nat.count (selectionPredicate N B ω) (N + 1)

def selectionSlot (N : ℕ) (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) : ℕ :=
  if i < selectionCount N B ω then Nat.nth (selectionPredicate N B ω) i else N + 1

def selectionTime (N : ℕ) (B : ℕ → Ω → Prop) : ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | i + 1 => selectionSlot N B i

@[simp] theorem selectionTime_zero (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionTime N B 0 ω = 0 := rfl

@[simp] theorem selectionTime_succ (N : ℕ) (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) :
    selectionTime N B (i + 1) ω = selectionSlot N B i ω := rfl

theorem selectionSlot_mem {N i : ℕ} {B : ℕ → Ω → Prop} {ω : Ω}
    (hi : i < selectionCount N B ω) :
    selectionPredicate N B ω (selectionSlot N B i ω) := by
  rw [selectionSlot, ite_eq_left hi]
  exact Nat.nth_mem i (fun hf => hi.trans_le (Nat.count_le_card hf (N + 1)))

theorem selectionSlot_rank {N i : ℕ} {B : ℕ → Ω → Prop} {ω : Ω}
    (hi : i < selectionCount N B ω) :
    Nat.count (selectionPredicate N B ω) (selectionSlot N B i ω) = i := by
  rw [selectionSlot, ite_eq_left hi]
  exact Nat.count_nth (fun hf => hi.trans_le (Nat.count_le_card hf (N + 1)))

theorem selectionSlot_pos (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    0 < selectionSlot N B i ω := by
  by_cases hi : i < selectionCount N B ω
  · exact (selectionSlot_mem hi).1
  · simp only [selectionSlot, ite_eq_right hi]
    exact Nat.succ_pos N

theorem selectionSlot_le (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionSlot N B i ω ≤ N + 1 := by
  by_cases hi : i < selectionCount N B ω
  · exact (selectionSlot_mem hi).2.1.trans (Nat.le_succ N)
  · simp only [selectionSlot, ite_eq_right hi, le_refl]

theorem selectionSlot_le_horizon_iff (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionSlot N B i ω ≤ N ↔ i < selectionCount N B ω := by
  by_cases hi : i < selectionCount N B ω
  · exact ⟨fun _ => hi, fun _ => (selectionSlot_mem hi).2.1⟩
  · simp [selectionSlot, hi]

theorem selectionSlot_eq_sentinel_iff (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionSlot N B i ω = N + 1 ↔ selectionCount N B ω ≤ i := by
  by_cases hi : i < selectionCount N B ω
  · have hle := (selectionSlot_mem hi).2.1
    have hne : selectionSlot N B i ω ≠ N + 1 := by omega
    simp [hne, Nat.not_le.mpr hi]
  · simp [selectionSlot, hi, Nat.le_of_not_gt hi]

theorem selectionSlot_eq_iff {N i n : ℕ} (B : ℕ → Ω → Prop) (ω : Ω)
    (hn : n ≤ N) :
    selectionSlot N B i ω = n ↔
      selectionPredicate N B ω n ∧ Nat.count (selectionPredicate N B ω) n = i := by
  constructor
  · intro h
    have hi : i < selectionCount N B ω :=
      (selectionSlot_le_horizon_iff N i B ω).mp (h.symm ▸ hn)
    exact ⟨h ▸ selectionSlot_mem hi, h ▸ selectionSlot_rank hi⟩
  · rintro ⟨hp, hrank⟩
    have hi : i < selectionCount N B ω := by
      rw [← hrank]
      exact Nat.count_strict_mono hp (Nat.lt_succ_of_le hn)
    rw [selectionSlot, ite_eq_left hi, ← hrank, Nat.nth_count hp]

theorem selectionSlot_monotone (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    Monotone (fun i => selectionSlot N B i ω) := by
  intro i j hij
  by_cases hj : j < selectionCount N B ω
  · have hi := hij.trans_lt hj
    simp only [selectionSlot, ite_eq_left hi, ite_eq_left hj]
    exact Nat.nth_le_nth' hij (fun hf => hj.trans_le (Nat.count_le_card hf (N + 1)))
  · calc
      selectionSlot N B i ω ≤ N + 1 := selectionSlot_le N i B ω
      _ = selectionSlot N B j ω := by simp only [selectionSlot, ite_eq_right hj]

theorem selectionTime_monotone (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    Monotone (fun i => selectionTime N B i ω) := by
  intro i j hij
  cases i with
  | zero => exact Nat.zero_le _
  | succ i =>
    cases j with
    | zero => omega
    | succ j => exact selectionSlot_monotone N B ω (Nat.succ_le_succ_iff.mp hij)

theorem count_congr_below (P Q : ℕ → Prop) (n : ℕ)
    (h : ∀ j, j < n → (P j ↔ Q j)) : Nat.count P n = Nat.count Q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun hj => h j hj)

theorem selectionCount_before_congr (F : FinitePartitionFiltration Ω)
    (N : ℕ) (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    {n : ℕ} {ω η : Ω} (hωη : (F.part (n - 1)).r ω η) :
    Nat.count (selectionPredicate N B ω) n = Nat.count (selectionPredicate N B η) n := by
  apply count_congr_below
  intro j hj
  by_cases hjpos : 0 < j
  · by_cases hjN : j ≤ N
    · have hrel : (F.part (j - 1)).r ω η :=
        F.refines (Nat.sub_le_sub_right (Nat.le_of_lt hj) 1) hωη
      simp only [selectionPredicate, hjpos, hjN, true_and]
      exact hB j hjpos hjN hrel
    · simp only [selectionPredicate, hjN, false_and, and_false]
  · simp only [selectionPredicate, hjpos, false_and]

theorem selectionSlot_predictable (F : FinitePartitionFiltration Ω)
    (N : ℕ) (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    (i : ℕ) : F.IsPredictableTime (selectionSlot N B i) := by
  intro n hn ω η hωη
  by_cases hnN : n ≤ N
  · rw [selectionSlot_eq_iff B ω hnN, selectionSlot_eq_iff B η hnN,
      selectionCount_before_congr F N B hB hωη]
    have hBn := hB n hn hnN hωη
    simp only [selectionPredicate, hn, hnN, true_and, hBn]
  · by_cases hnSent : n = N + 1
    · subst n
      rw [selectionSlot_eq_sentinel_iff, selectionSlot_eq_sentinel_iff]
      have hc := selectionCount_before_congr F N B hB (n := N + 1) hωη
      change Nat.count (selectionPredicate N B ω) (N + 1) ≤ i ↔
        Nat.count (selectionPredicate N B η) (N + 1) ≤ i
      rw [hc]
    · have hω := selectionSlot_le N i B ω
      have hη := selectionSlot_le N i B η
      have hneω : selectionSlot N B i ω ≠ n := by omega
      have hneη : selectionSlot N B i η ≠ n := by omega
      simp only [hneω, hneη]

theorem selectionTime_stopping (F : FinitePartitionFiltration Ω)
    (N : ℕ) (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    (i : ℕ) : F.IsStoppingTime (selectionTime N B i) := by
  cases i with
  | zero => exact F.isStoppingTime_const 0
  | succ i =>
    exact F.isStoppingTime_of_isPredictableTime
      (selectionSlot_pos N i B) (selectionSlot_predictable F N B hB i)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSelectionCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def selectionProcess (N : ℕ) (B : ℕ → Ω → Prop) (d : ℕ → Ω → E) : ℕ → Ω → E :=
  finiteSelectedProcess N d (selectionTime N B)

@[simp] theorem selectionProcess_zero (N : ℕ) (B : ℕ → Ω → Prop)
    (d : ℕ → Ω → E) (ω : Ω) : selectionProcess N B d 0 ω = 0 := by
  exact finiteSelectedProcess_zero N d (selectionTime N B) ω

@[simp] theorem finiteDifference_selectionProcess_succ (N : ℕ)
    (B : ℕ → Ω → Prop) (d : ℕ → Ω → E) (i : ℕ) (ω : Ω) :
    finiteDifference (selectionProcess N B d) (i + 1) ω =
      if selectionSlot N B i ω ≤ N then d (selectionSlot N B i ω) ω else 0 := by
  exact finiteDifference_selectedProcess_succ N d (selectionTime N B) i ω

namespace FinitePartitionFiltration

def selectionFiltration (F : FinitePartitionFiltration Ω) (N : ℕ)
    (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η)) : FinitePartitionFiltration Ω :=
  F.selectedFiltration (selectionTime N B)
    (selectionTime_stopping F N B hB) (selectionTime_monotone N B)

end FinitePartitionFiltration

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteBoundedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def boundedEnergyConstant (a r χ : ℝ) : ℝ :=
  (χ * (2 : ℝ) ^ (1 / r)) / (1 - bandGeometricRatio a r)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteConditionalMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity
namespace FinitePartitionFiltration

variable {Ω : Type*} (F : FinitePartitionFiltration Ω)

def quotientCoarsening {i j : ℕ} (hij : i ≤ j) :
    Quotient (F.part j) → Quotient (F.part i) :=
  Quotient.lift (Quotient.mk (F.part i))
    (fun _ _ h => Quotient.sound (F.refines hij h))

@[simp] theorem quotientCoarsening_mk {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    F.quotientCoarsening hij (Quotient.mk (F.part j) ω) =
      Quotient.mk (F.part i) ω := rfl

variable [Fintype Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) : Ω → E :=
  μ.conditionalAverage (Quotient.mk (F.part j)) f

end FinitePartitionFiltration
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteFirstCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity
namespace FinitePartitionFiltration

variable {Ω E : Type*} [SeminormedAddCommGroup E]

attribute [local instance] Classical.propDecidable

def firstCrossing (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω) : ℕ :=
  if h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖ then Nat.find h else N

end FinitePartitionFiltration
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteGoldstine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem finite_coordinate_expansion {m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] ℝ) (z : Fin m → ℝ) :
    L z = ∑ i : Fin m, L (Pi.single i 1) * z i := by
  calc
    L z = L (∑ i : Fin m, Pi.single i (z i)) :=
      congrArg L (Finset.univ_sum_single z).symm
    _ = ∑ i : Fin m, L (Pi.single i (z i)) := map_sum L _ _
    _ = ∑ i : Fin m, L (Pi.single i 1) * z i := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : (Pi.single i (z i) : Fin m → ℝ) =
          z i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
        simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i (z i) (1 : ℝ)
      rw [hi, L.map_smul, smul_eq_mul, mul_comm]

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem finite_goldstine
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {m : ℕ} (f : Fin m → (Y →L[ℝ] ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Y, ‖y‖ ≤ 1 ∧ ∀ i, |f i y - v (f i)| < ε := by
  classical
  let T : Y →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun y i => f i y
      map_add' := by
        intro y z
        funext i
        exact (f i).map_add y z
      map_smul' := by
        intro c y
        funext i
        exact (f i).map_smul c y }
  let a : Fin m → ℝ := fun i => v (f i)
  have hconv : Convex ℝ (T '' Metric.closedBall (0 : Y) 1) :=
    (convex_closedBall (0 : Y) (1 : ℝ)).linear_image T
  have ha : a ∈ closure (T '' Metric.closedBall (0 : Y) 1) := by
    by_contra hnot
    obtain ⟨L, c, hLc, hca⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hnot
    let F : Y →L[ℝ] ℝ := ∑ i : Fin m, L (Pi.single i 1) • f i
    have hFy (y : Y) : F y = L (T y) := by
      calc
        F y = ∑ i : Fin m, L (Pi.single i 1) * f i y := by
          simp only [F, sum_apply,
            smul_apply, smul_eq_mul]
        _ = L (T y) := (finite_coordinate_expansion L (T y)).symm
    have hFa : L a = v F := by
      calc
        L a = ∑ i : Fin m, L (Pi.single i 1) * v (f i) :=
          finite_coordinate_expansion L a
        _ = v F := by simp only [F, map_sum, map_smul, smul_eq_mul]
    have hFlt (y : Y) (hy : ‖y‖ ≤ 1) : F y < c := by
      rw [hFy]
      apply hLc
      apply subset_closure
      refine ⟨y, ?_, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    have hc : 0 < c := by
      simpa only [map_zero] using hFlt 0 (by simp)
    have hFnorm : ‖F‖ ≤ c := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm hc.le
      intro y hy
      have hu : F y < c := hFlt y hy.le
      have hl : -F y < c := by
        simpa only [map_neg] using
          hFlt (-y) (by simpa only [norm_neg] using hy.le)
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith only [hl], hu.le⟩
    have hvF : v F ≤ ‖F‖ := by
      apply (le_abs_self (v F)).trans
      simpa only [Real.norm_eq_abs, one_mul] using v.le_of_opNorm_le hv F
    have hcF : c < v F := by simpa only [hFa] using hca
    exact (not_lt_of_ge (hvF.trans hFnorm)) hcF
  obtain ⟨z, hz, haz⟩ := Metric.mem_closure_iff.mp ha ε hε
  rcases hz with ⟨y, hy, rfl⟩
  refine ⟨y, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  · intro i
    have hnorm : ‖a - T y‖ < ε := by
      simpa only [dist_eq_norm] using haz
    have hi : ‖(a - T y) i‖ < ε :=
      lt_of_le_of_lt (norm_le_pi_norm (a - T y) i) hnorm
    have hi' : |v (f i) - f i y| < ε := by
      change ‖v (f i) - f i y‖ < ε at hi
      simpa only [Real.norm_eq_abs] using hi
    simpa only [abs_sub_comm] using hi'

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SequenceL2JConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators ENNReal

universe u

variable (X : Type u) [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

instance sequenceL2ExponentAtLeastOne : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

abbrev SequenceL2 := lp (fun _ : ℕ => X) (2 : ℝ≥0∞)

variable {X}

@[simp] theorem sequenceL2_cutSum_apply {n : ℕ} (f : Fin n → SequenceL2 X)
    (r : Fin n) (k : ℕ) :
    (cutSum f r) k = cutSum (fun j => f j k) r := by
  let ev : SequenceL2 X →+ X :=
    { toFun := fun x => x k
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ j : Fin n, cutSign r j • f j) =
    ∑ j : Fin n, cutSign r j • f j k
  exact (map_sum ev (fun j : Fin n => cutSign r j • f j) Finset.univ).trans
    (Finset.sum_congr rfl (fun _ _ => rfl))

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteL2CoefficientAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators ENNReal

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def finiteL2ToSequence {m : ℕ} (μ : FiniteLaw (Fin m)) :
    (Fin m → E) →ₗ[ℝ] SequenceL2 E where
  toFun f := ∑ i : Fin m,
    lp.single (2 : ℝ≥0∞) i.val (Real.sqrt (μ.mass i) • f i)
  map_add' f g := by
    simp only [Pi.add_apply, smul_add, lp.single_add, Finset.sum_add_distrib]
  map_smul' c f := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change lp.single (E := fun _ : ℕ => E) (2 : ℝ≥0∞) i.val
      (Real.sqrt (μ.mass i) • (c • f i)) = _
    rw [smul_comm (Real.sqrt (μ.mass i)) c, lp.single_smul, RingHom.id_apply]

section FiniteProcess

variable {Ω : Type*} [sectionFintypeΩ : Fintype Ω]

def finiteCoefficientProcess {N : ℕ} (M : ℕ → Ω → E) (a : Fin (N + 1) → ℝ)
    (t : ℕ) (ω : Ω) : E :=
  ∑ i : Fin (N + 1), if i.val ≤ t then a i • finiteDifference M i.val ω else 0

end FiniteProcess

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMatching
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u v

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_continuous_range_section
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (T : Y →ₗ[ℝ] F) :
    ∃ S : LinearMap.range T →L[ℝ] Y,
      ∀ z : LinearMap.range T, T (S z) = (z : F) := by
  classical
  let R : Submodule ℝ F := LinearMap.range T
  let b := Module.finBasis ℝ R
  let y : Fin (Module.finrank ℝ R) → Y := fun i => Classical.choose (b i).property
  have hy (i : Fin (Module.finrank ℝ R)) : T (y i) = (b i : F) :=
    Classical.choose_spec (b i).property
  let S₀ : R →ₗ[ℝ] Y := b.constr ℝ y
  have hcomp : T.comp S₀ = R.subtype := by
    apply b.ext
    intro i
    change T (S₀ (b i)) = (b i : F)
    rw [show S₀ (b i) = y i from b.constr_basis ℝ y i]
    exact hy i
  let S : R →L[ℝ] Y := ⟨S₀, S₀.continuous_of_finiteDimensional⟩
  refine ⟨S, ?_⟩
  intro z
  exact congrArg (fun L : R →ₗ[ℝ] F => L z) hcomp

theorem finite_matching_unit
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {m : ℕ} (f : Fin m → (Y →L[ℝ] ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Y, ‖y‖ ≤ 1 + ε ∧ ∀ i, f i y = v (f i) := by
  classical
  let T : Y →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun y i => f i y
      map_add' := by
        intro y z
        funext i
        exact (f i).map_add y z
      map_smul' := by
        intro c y
        funext i
        exact (f i).map_smul c y }
  let a : Fin m → ℝ := fun i => v (f i)
  let R : Submodule ℝ (Fin m → ℝ) := LinearMap.range T
  have hclosed : IsClosed (R : Set (Fin m → ℝ)) := R.closed_of_finiteDimensional
  have ha : a ∈ R := by
    change a ∈ (R : Set (Fin m → ℝ))
    rw [← hclosed.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨y, _, hy⟩ := finite_goldstine v hv f hδ
    refine ⟨T y, ⟨y, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    change ‖a i - (T y) i‖ < δ
    rw [Real.norm_eq_abs]
    change |v (f i) - f i y| < δ
    rw [abs_sub_comm]
    exact hy i
  obtain ⟨S, hS⟩ := exists_continuous_range_section T
  have hSpos : 0 < ‖S‖ + 1 := by linarith [norm_nonneg S]
  let δ : ℝ := ε / (‖S‖ + 1)
  have hδ : 0 < δ := div_pos hε hSpos
  obtain ⟨y, hy, hfy⟩ := finite_goldstine v hv f hδ
  let e : R := ⟨a - T y, R.sub_mem ha ⟨y, rfl⟩⟩
  have he : ‖e‖ < δ := by
    change ‖a - T y‖ < δ
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    change ‖a i - (T y) i‖ < δ
    rw [Real.norm_eq_abs]
    change |v (f i) - f i y| < δ
    rw [abs_sub_comm]
    exact hfy i
  have hcorrection : ‖S e‖ ≤ ε := by
    calc
      ‖S e‖ ≤ ‖S‖ * ‖e‖ := S.le_opNorm e
      _ ≤ ‖S‖ * δ := mul_le_mul_of_nonneg_left he.le (norm_nonneg S)
      _ ≤ (‖S‖ + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = δ * (‖S‖ + 1) := mul_comm _ _
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hSpos)
  refine ⟨y + S e, (norm_add_le _ _).trans (add_le_add hy hcorrection), ?_⟩
  intro i
  have heval : T (y + S e) = a := by
    rw [map_add, hS e]
    change T y + (a - T y) = a
    rw [add_comm, sub_add_cancel]
  exact congrFun heval i

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePredictableTransform
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def partialSumProcess (d : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  ∑ j ∈ Finset.range n, d (j + 1) ω

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem partialSumProcess_zero [Fintype Ω] [NormedSpace ℝ E] (d : ℕ → Ω → E) (ω : Ω) :
    partialSumProcess d 0 ω = 0 := by
  simp [partialSumProcess]

@[simp] theorem difference_partialSumProcess_succ (d : ℕ → Ω → E)
    (n : ℕ) (ω : Ω) :
    finiteDifference (partialSumProcess d) (n + 1) ω = d (n + 1) ω := by
  simp only [finiteDifference_succ, partialSumProcess, Finset.sum_range_succ]
  abel

def cumulativeCost (w : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, w (j + 1) ω

omit sectionFintypeΩ in
@[simp] theorem cumulativeCost_zero [Fintype Ω] (w : ℕ → Ω → ℝ) (ω : Ω) :
    cumulativeCost w 0 ω = 0 := by simp [cumulativeCost]

def budgetCoefficient (w : ℕ → Ω → ℝ) (S : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  if cumulativeCost w j ω ≤ S then 1 else 0

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteWalkWitness
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

structure FiniteWalkWitness (N : OrderedNorm) (n : ℕ) where
  State : Type
  Edge : Type
  stateFintype : Fintype State
  edgeFintype : Fintype Edge
  chain : @FiniteMarkedChain State Edge stateFintype edgeFintype
  coordinateBound : ℕ
  label : Edge → C00
  odd : ∀ e, label (chain.rev e) = -label e
  support_bound : ∀ e k, coordinateBound ≤ k → label e k = 0
  unit : ∀ e, N (label e) = 1
  escape : (3 : ℝ) / 20 ≤
    @markedProb State Edge stateFintype edgeFintype chain n
      (fun ω => (n : ℝ) / 24 ≤ N (edgeSum label ω))

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def CoordinateSpace (_N : OrderedNorm) (m : ℕ) := Fin m → ℝ

namespace CoordinateSpace

variable (N : OrderedNorm) (m : ℕ)

instance instAddCommGroup : AddCommGroup (CoordinateSpace N m) :=
  inferInstanceAs (AddCommGroup (Fin m → ℝ))

instance instModuleReal : Module ℝ (CoordinateSpace N m) :=
  inferInstanceAs (Module ℝ (Fin m → ℝ))

instance instFiniteDimensionalReal : FiniteDimensional ℝ (CoordinateSpace N m) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin m → ℝ))

instance instNorm : Norm (CoordinateSpace N m) := ⟨fun a => N (C00.ofArray a)⟩

theorem normCore : NormedSpace.Core ℝ (CoordinateSpace N m) where
  norm_nonneg a := N.nonneg (C00.ofArray a)
  norm_smul r a := by
    change Fin m → ℝ at a
    change N (C00.arrayLinear m (r • a)) = ‖r‖ * N (C00.arrayLinear m a)
    rw [map_smul, N.smul, Real.norm_eq_abs]
  norm_triangle a b := by
    change Fin m → ℝ at a b
    change N (C00.arrayLinear m (a + b)) ≤
      N (C00.arrayLinear m a) + N (C00.arrayLinear m b)
    rw [map_add]
    exact N.add_le _ _
  norm_eq_zero_iff a := by
    change N (C00.ofArray a) = 0 ↔ a = 0
    rw [N.eq_zero_iff]
    constructor
    · intro h
      apply C00.ofArray_injective m
      exact h.trans ((C00.arrayLinear m).map_zero).symm
    · rintro rfl
      exact (C00.arrayLinear m).map_zero

instance instNormedAddCommGroup : NormedAddCommGroup (CoordinateSpace N m) :=
  NormedAddCommGroup.ofCore (normCore N m)

instance instNormedSpaceReal : NormedSpace ℝ (CoordinateSpace N m) :=
  NormedSpace.ofCore (normCore N m)

def coefficients : CoordinateSpace N m ≃ₗ[ℝ] (Fin m → ℝ) :=
  LinearEquiv.refl ℝ _

@[simp] theorem norm_eq (a : CoordinateSpace N m) :
    ‖a‖ = N (C00.ofArray a) := rfl

end CoordinateSpace

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteWalkCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

attribute [local instance] FiniteWalkWitness.stateFintype FiniteWalkWitness.edgeFintype

namespace FiniteWalkWitness

variable {N : OrderedNorm} {n : ℕ}

def coordinateLabel (W : FiniteWalkWitness N n) (e : W.Edge) :
    CoordinateSpace N W.coordinateBound :=
  fun i => W.label e i.val

end FiniteWalkWitness

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WordAction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

noncomputable def wordMap : List Letter → ℝ ≃o ℝ
  | [] => OrderIso.refl ℝ
  | s :: w => (wordMap w).trans (letterOrderIso s)

@[simp] theorem wordMap_nil : wordMap [] = OrderIso.refl ℝ := rfl

@[simp] theorem wordMap_nil_apply (x : ℝ) : wordMap [] x = x := rfl

@[simp] theorem wordMap_nil_symm (x : ℝ) : (wordMap []).symm x = x := rfl

@[simp] theorem wordMap_cons (s : Letter) (w : List Letter) (x : ℝ) :
    wordMap (s :: w) x = letterOrderIso s (wordMap w x) := rfl

@[simp] theorem wordMap_cons_symm (s : Letter) (w : List Letter) (x : ℝ) :
    (wordMap (s :: w)).symm x = (wordMap w).symm ((letterOrderIso s).symm x) :=
  rfl

@[simp] theorem wordMap_singleton (s : Letter) (x : ℝ) :
    wordMap [s] x = letterOrderIso s x := rfl

def inverseWord (w : List Letter) : List Letter := w.reverse.map Letter.inv

@[simp] theorem inverseWord_nil : inverseWord [] = [] := rfl

@[simp] theorem inverseWord_cons (s : Letter) (w : List Letter) :
    inverseWord (s :: w) = inverseWord w ++ [s.inv] := by
  simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]

@[simp] theorem inverseWord_length (w : List Letter) :
    (inverseWord w).length = w.length := by
  simp only [inverseWord, List.length_map, List.length_reverse]

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_IntegerCocycle
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

noncomputable section

def arcIndicator (s : Letter) (y : ℝ) : ℤ := by
  classical
  exact if y ∈ arc s then 1 else 0

def negativeIndicator (s : Letter) : ℤ := if s.2 then 0 else 1

def chi (s : Letter) (y : ℝ) : ℤ := arcIndicator s y - negativeIndicator s

def wordCocycle : List Letter → ℝ → ℤ
  | [], _ => 0
  | s :: w, y => chi s y + wordCocycle w ((letterOrderIso s).symm y)

@[simp] theorem wordCocycle_nil (y : ℝ) : wordCocycle [] y = 0 := rfl

@[simp] theorem wordCocycle_cons (s : Letter) (w : List Letter) (y : ℝ) :
    wordCocycle (s :: w) y =
      chi s y + wordCocycle w ((letterOrderIso s).symm y) := rfl

def pullbackPoint (w : List Letter) (k : ℕ) (y : ℝ) : ℝ :=
  (wordMap (w.take k)).symm y

@[simp] theorem pullbackPoint_zero (w : List Letter) (y : ℝ) :
    pullbackPoint w 0 y = y := rfl

@[simp] theorem pullbackPoint_nil (k : ℕ) (y : ℝ) :
    pullbackPoint [] k y = y := by
  simp only [pullbackPoint, List.take_nil, wordMap_nil_symm]

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_InterleavedCuts
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def interleavedCuts {M : ℕ} (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ)
    (B : ℕ) (i : Fin (2 * M + 2 + 1)) : ℕ :=
  if h0 : i.val = 0 then 0
  else if hlast : i.val = 2 * M + 2 then B
  else if hodd : i.val % 2 = 1 then
    r ⟨i.val / 2, by have := i.isLt; omega⟩
  else
    t ⟨i.val / 2 - 1, by have := i.isLt; omega⟩

@[simp] theorem interleavedCuts_zero {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B : ℕ) :
    interleavedCuts r t B 0 = 0 := by
  simp [interleavedCuts]

@[simp] theorem interleavedCuts_last {M : ℕ}
    (r : Fin (M + 1) → ℕ) (t : Fin M → ℕ) (B : ℕ) :
    interleavedCuts r t B (Fin.last (2 * M + 2)) = B := by
  simp [interleavedCuts]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrbitDisplacement
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

def OrbitRep (C : FiniteMarkedChain S E) :=
  {e : E // (Fintype.equivFin E) e < (Fintype.equivFin E) (C.rev e)}

instance instFintypeOrbitRep (C : FiniteMarkedChain S E) : Fintype (OrbitRep C) := by
  classical
  unfold OrbitRep
  infer_instance

def orbitDisplacement (C : FiniteMarkedChain S E) (e : E)
    (j : OrbitRep C) : ℤ := by
  classical
  exact (if e = j.val then 1 else 0) -
    (if C.rev e = j.val then 1 else 0)

@[simp] theorem orbitDisplacement_rev (C : FiniteMarkedChain S E) (e : E) :
    orbitDisplacement C (C.rev e) = -orbitDisplacement C e := by
  classical
  funext j
  change ((if C.rev e = j.val then 1 else 0) -
    (if C.rev (C.rev e) = j.val then 1 else 0) : ℤ) =
      -((if e = j.val then 1 else 0) - (if C.rev e = j.val then 1 else 0))
  rw [C.rev_rev e]
  exact (neg_sub _ _).symm

theorem orbitDisplacement_bounds (C : FiniteMarkedChain S E)
    (e : E) (j : OrbitRep C) :
    -1 ≤ orbitDisplacement C e j ∧ orbitDisplacement C e j ≤ 1 := by
  classical
  unfold orbitDisplacement
  split_ifs <;> norm_num

@[simp] theorem orbitDisplacement_fixed (C : FiniteMarkedChain S E)
    {e : E} (he : C.rev e = e) : orbitDisplacement C e = 0 := by
  classical
  funext j
  simp [orbitDisplacement, he]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def labelLinear (C : FiniteMarkedChain S E) (g : E → V)
    (a : OrbitRep C → ℤ) : V :=
  ∑ j, (a j : ℝ) • g j.val

@[simp] theorem labelLinear_zero (C : FiniteMarkedChain S E) (g : E → V) :
    labelLinear C g 0 = 0 := by
  simp [labelLinear]

@[simp] theorem labelLinear_neg (C : FiniteMarkedChain S E) (g : E → V)
    (a : OrbitRep C → ℤ) :
    labelLinear C g (-a) = -labelLinear C g a := by
  simp [labelLinear, Int.cast_neg, neg_smul, Finset.sum_neg_distrib]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticeCubes
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

def LatticeCube (J : Type*) (R : ℕ) :=
  J → Set.Icc (-(R : ℤ)) (R : ℤ)

instance instFintypeLatticeCube {J : Type*} [Fintype J] (R : ℕ) : Fintype (LatticeCube J R) := by
  classical
  unfold LatticeCube
  infer_instance

def latticeCubeVal {J : Type*} {R : ℕ} (a : LatticeCube J R) : J → ℤ :=
  fun j => (a j).val

theorem latticeCubeVal_injective {J : Type*} {R : ℕ} :
    Function.Injective (@latticeCubeVal J R) := by
  intro a b hab
  funext j
  exact Subtype.ext (congrFun hab j)

def latticeCubeZero (J : Type*) (R : ℕ) : LatticeCube J R :=
  fun _ => ⟨0, by constructor <;> omega⟩

instance instNonemptyLatticeCube {J : Type*} (R : ℕ) : Nonempty (LatticeCube J R) :=
  ⟨latticeCubeZero J R⟩

@[simp] theorem latticeCubeVal_zero (J : Type*) (R : ℕ) :
    latticeCubeVal (latticeCubeZero J R) = 0 := rfl

theorem latticeCube_coordinate_bounds {J : Type*} {R : ℕ}
    (a : LatticeCube J R) (j : J) :
    -(R : ℤ) ≤ latticeCubeVal a j ∧ latticeCubeVal a j ≤ R :=
  (a j).property

theorem latticeCube_card_pos {J : Type*} [Fintype J] (R : ℕ) :
    0 < Fintype.card (LatticeCube J R) := Fintype.card_pos

theorem latticeCube_card_real_pos {J : Type*} [Fintype J] (R : ℕ) :
    0 < (Fintype.card (LatticeCube J R) : ℝ) := by
  exact_mod_cast latticeCube_card_pos (J := J) R

def latticeCubeInclusion {J : Type*} {R Q : ℕ} (hQR : Q ≤ R)
    (a : LatticeCube J Q) : LatticeCube J R := fun j =>
  ⟨(a j).val, by
    rcases (a j).property with ⟨hl, hu⟩
    constructor <;> omega⟩

@[simp] theorem latticeCubeVal_inclusion {J : Type*} {R Q : ℕ} (hQR : Q ≤ R)
    (a : LatticeCube J Q) :
    latticeCubeVal (latticeCubeInclusion hQR a) = latticeCubeVal a := rfl

def latticeDensity (J : Type*) [Fintype J] (n R : ℕ) : ℝ :=
  (Fintype.card (LatticeCube J (R - n)) : ℝ) /
    (Fintype.card (LatticeCube J R) : ℝ)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticeLift
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

abbrev LiftCube (C : FiniteMarkedChain S E) (R : ℕ) :=
  LatticeCube (OrbitRep C) R

def liftAccept (C : FiniteMarkedChain S E) (R : ℕ) (e : E)
    (a : LiftCube C R) : Prop :=
  ∀ j, -(R : ℤ) ≤ latticeCubeVal a j + orbitDisplacement C e j ∧
    latticeCubeVal a j + orbitDisplacement C e j ≤ R

def liftMove (C : FiniteMarkedChain S E) (R : ℕ) (e : E)
    (a : LiftCube C R) (h : liftAccept C R e a) : LiftCube C R :=
  fun j => ⟨latticeCubeVal a j + orbitDisplacement C e j, h j⟩

@[simp] theorem latticeCubeVal_liftMove (C : FiniteMarkedChain S E) (R : ℕ)
    (e : E) (a : LiftCube C R) (h : liftAccept C R e a) :
    latticeCubeVal (liftMove C R e a h) =
      latticeCubeVal a + orbitDisplacement C e := rfl

theorem liftAccept_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (e : E) (a : LiftCube C R) (h : liftAccept C R e a) :
    liftAccept C R (C.rev e) (liftMove C R e a h) := by
  intro j
  simpa only [liftAccept, latticeCubeVal_liftMove, Pi.add_apply,
    orbitDisplacement_rev, Pi.neg_apply, add_neg_cancel_right] using
    latticeCube_coordinate_bounds a j

@[simp] theorem liftMove_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (e : E) (a : LiftCube C R) (h : liftAccept C R e a)
    (h' : liftAccept C R (C.rev e) (liftMove C R e a h)) :
    liftMove C R (C.rev e) (liftMove C R e a h) h' = a := by
  apply latticeCubeVal_injective
  simp [orbitDisplacement_rev]

def liftSource (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) : S × LiftCube C R := (C.src x.1, x.2)

def liftTarget (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) : S × LiftCube C R := by
  classical
  exact if h : liftAccept C R x.1 x.2 then
    (C.tgt x.1, liftMove C R x.1 x.2 h) else (C.src x.1, x.2)

def liftReverse (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) : E × LiftCube C R := by
  classical
  exact if h : liftAccept C R x.1 x.2 then
    (C.rev x.1, liftMove C R x.1 x.2 h) else x

theorem liftReverse_involutive (C : FiniteMarkedChain S E) (R : ℕ) :
    Function.Involutive (liftReverse C R) := by
  classical
  rintro ⟨e, a⟩
  by_cases h : liftAccept C R e a
  · have h' := liftAccept_reverse C R e a h
    have hfirst : liftReverse C R (e, a) = (C.rev e, liftMove C R e a h) := by
      simp only [liftReverse, dite_eq_left h]
    rw [hfirst]
    simp only [liftReverse, dite_eq_left h']
    exact Prod.ext (C.rev_rev e) (liftMove_reverse C R e a h h')
  · simp [liftReverse, h]

theorem liftSource_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) :
    liftSource C R (liftReverse C R x) = liftTarget C R x := by
  classical
  rcases x with ⟨e, a⟩
  by_cases h : liftAccept C R e a
  · simp [liftSource, liftTarget, liftReverse, h, C.src_rev]
  · simp [liftSource, liftTarget, liftReverse, h]

theorem liftTarget_reverse (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) :
    liftTarget C R (liftReverse C R x) = liftSource C R x := by
  rw [← liftSource_reverse, liftReverse_involutive]

def liftMass (C : FiniteMarkedChain S E) (R : ℕ)
    (x : S × LiftCube C R) : ℝ :=
  C.π x.1 / (Fintype.card (LiftCube C R) : ℝ)

theorem liftMass_nonneg (C : FiniteMarkedChain S E) (R : ℕ)
    (x : S × LiftCube C R) : 0 ≤ liftMass C R x :=
  div_nonneg (C.π_nonneg x.1) (Nat.cast_nonneg _)

theorem sum_liftMass (C : FiniteMarkedChain S E) (R : ℕ) :
    ∑ x, liftMass C R x = 1 := by
  classical
  have hc : (Fintype.card (LiftCube C R) : ℝ) ≠ 0 :=
    ne_of_gt (latticeCube_card_real_pos R)
  have hsum (s : S) :
      (∑ _a : LiftCube C R, C.π s / (Fintype.card (LiftCube C R) : ℝ)) =
        C.π s := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hc]
  simpa only [liftMass, Fintype.sum_prod_type, hsum] using C.sum_π

theorem sum_liftOutgoing (C : FiniteMarkedChain S E) (R : ℕ)
    (x : S × LiftCube C R) :
    (∑ e : E × LiftCube C R, if liftSource C R e = x then C.q e.1 else 0) = 1 := by
  classical
  rcases x with ⟨s, a⟩
  rw [← C.sum_q s]
  simp only [liftSource, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : C.src e = s <;> simp [Prod.mk.injEq, h]

theorem lift_edge_balance (C : FiniteMarkedChain S E) (R : ℕ)
    (x : E × LiftCube C R) :
    liftMass C R (liftSource C R x) * C.q x.1 =
      liftMass C R (liftTarget C R x) * C.q (liftReverse C R x).1 := by
  classical
  rcases x with ⟨e, a⟩
  by_cases h : liftAccept C R e a
  · simp only [liftSource, liftTarget, liftReverse, h, dite_true, liftMass
      ]
    calc
      C.π (C.src e) / (Fintype.card (LiftCube C R) : ℝ) * C.q e =
          (C.π (C.src e) * C.q e) / (Fintype.card (LiftCube C R) : ℝ) := by ring
      _ = (C.π (C.tgt e) * C.q (C.rev e)) /
          (Fintype.card (LiftCube C R) : ℝ) := by rw [C.balance]
      _ = C.π (C.tgt e) / (Fintype.card (LiftCube C R) : ℝ) *
          C.q (C.rev e) := by ring
  · simp [liftSource, liftTarget, liftReverse, h]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticePaths
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

def prefixDisplacement (C : FiniteMarkedChain S E) {n : ℕ} (w : Fin n → E) :
    ℕ → (OrbitRep C → ℤ)
  | 0 => 0
  | k + 1 => prefixDisplacement C w k +
      if h : k < n then orbitDisplacement C (w ⟨k, h⟩) else 0

@[simp] theorem prefixDisplacement_zero (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) : prefixDisplacement C w 0 = 0 := rfl

theorem prefixDisplacement_bounds (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) (k : ℕ) (j : OrbitRep C) :
    -(k : ℤ) ≤ prefixDisplacement C w k j ∧
      prefixDisplacement C w k j ≤ (k : ℤ) := by
  induction k with
  | zero => simp [prefixDisplacement]
  | succ k ih =>
      by_cases hk : k < n
      · have hd := orbitDisplacement_bounds C (w ⟨k, hk⟩) j
        simp only [prefixDisplacement, hk, dite_true, Pi.add_apply]
        constructor <;> omega
      · simp only [prefixDisplacement, hk, dite_false, add_zero]
        constructor <;> omega

def centralPosition (C : FiniteMarkedChain S E) {n R : ℕ} (hnR : n ≤ R)
    (a : LatticeCube (OrbitRep C) (R - n)) (w : Fin n → E)
    (i : Fin (n + 1)) : LiftCube C R := fun j =>
  ⟨latticeCubeVal a j + prefixDisplacement C w i.val j, by
    have ha := latticeCube_coordinate_bounds a j
    have hd := prefixDisplacement_bounds C w i.val j
    have hi := i.isLt
    constructor <;> omega⟩

@[simp] theorem centralPosition_zero (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (w : Fin n → E) :
    centralPosition C hnR a w 0 = latticeCubeInclusion (Nat.sub_le R n) a := by
  apply latticeCubeVal_injective
  funext j
  simp [centralPosition, latticeCubeVal, latticeCubeInclusion]

def centralLiftPath (C : FiniteMarkedChain S E) {n R : ℕ} (hnR : n ≤ R)
    (a : LatticeCube (OrbitRep C) (R - n)) (ω : MarkedPath S E n) :
    MarkedPath (S × LiftCube C R) (E × LiftCube C R) n :=
  ((ω.1, centralPosition C hnR a ω.2 0),
    fun i => (ω.2 i, centralPosition C hnR a ω.2 i.castSucc))

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkovTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace FiniteReversibleChain

def reindex {S T : Type*} [Fintype S] [Fintype T]
    (C : FiniteReversibleChain S) (e : T ≃ S) : FiniteReversibleChain T where
  π t := C.π (e t)
  P t u := C.P (e t) (e u)
  π_nonneg t := C.π_nonneg (e t)
  sum_π := (e.sum_comp C.π).trans C.sum_π
  P_nonneg t u := C.P_nonneg (e t) (e u)
  sum_P t := (e.sum_comp (C.P (e t))).trans (C.sum_P (e t))
  balance t u := C.balance (e t) (e u)

end FiniteReversibleChain

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_NormedC00
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def NormedC00 (p : Seminorm ℝ C00) (_hp : ∀ x, p x = 0 → x = 0) := C00

namespace NormedC00

variable (p : Seminorm ℝ C00) (hp : ∀ x, p x = 0 → x = 0)

instance instAddCommGroup : AddCommGroup (NormedC00 p hp) := inferInstanceAs (AddCommGroup C00)

instance instModuleReal : Module ℝ (NormedC00 p hp) := inferInstanceAs (Module ℝ C00)

instance instNorm : Norm (NormedC00 p hp) := ⟨fun x => p x⟩

theorem normCore : NormedSpace.Core ℝ (NormedC00 p hp) where
  norm_nonneg x := apply_nonneg p x
  norm_smul r x := p.smul' r x
  norm_triangle x y := p.add_le' x y
  norm_eq_zero_iff x := by
    change p x = 0 ↔ x = 0
    exact ⟨hp x, fun h => h ▸ p.map_zero'⟩

instance instNormedAddCommGroup : NormedAddCommGroup (NormedC00 p hp) :=
  NormedAddCommGroup.ofCore (normCore p hp)

instance instNormedSpaceReal : NormedSpace ℝ (NormedC00 p hp) :=
  NormedSpace.ofCore (normCore p hp)

def coefficients : NormedC00 p hp ≃ₗ[ℝ] C00 := LinearEquiv.refl ℝ _

@[simp] theorem norm_eq (x : NormedC00 p hp) : ‖x‖ = p x := rfl

end NormedC00

abbrev OrderedSpace (N : OrderedNorm) := NormedC00 N.toSeminorm N.definite

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedBoundedCubes
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def pairLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] C00 where
  toFun a := ∑ i : Fin n, a i • (basis (2 * i.val) - basis (2 * i.val + 1))
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

def collapseAtPair (i k : ℕ) : ℕ := if k ≤ 2 * i then 0 else 1

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionProfileDefs
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

def ofList : List ℝ → C00 :=
  @List.ofFnRec ℝ (fun _ => C00) (fun _ a => C00.ofArray a)

@[simp] theorem ofList_ofFn {m : ℕ} (a : Fin m → ℝ) :
    ofList (List.ofFn a) = C00.ofArray a := by
  exact List.ofFnRec_ofFn (C := fun _ : List ℝ => C00)
    (fun _ a => C00.ofArray a) a

def pieces (blocks : List (ℝ × ℕ)) : List ℝ :=
  blocks.flatMap fun b => List.replicate b.2 (b.1 / (b.2 : ℝ))

@[simp] theorem pieces_nil : pieces [] = [] := rfl

@[simp] theorem pieces_cons (c : ℝ) (J : ℕ) (blocks : List (ℝ × ℕ)) :
    pieces ((c, J) :: blocks) = List.replicate J (c / (J : ℝ)) ++ pieces blocks := rfl

def finiteSubdivision {m : ℕ} (a : Fin m → ℝ) (J : Fin m → ℕ) : C00 :=
  ofList (pieces (List.ofFn fun i => (a i, J i)))

end MarkovSuperreflexivity.Subdivision

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionProfileExpansion
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.Subdivision

theorem ofList_append (left right : List ℝ) :
    ofList (left ++ right) = ofList left +
      Finsupp.mapDomain (fun i => left.length + i) (ofList right) := by
  classical
  induction left using List.ofFnRec with
  | h l left =>
      induction right using List.ofFnRec with
      | h r right =>
          rw [← List.ofFn_fin_append]
          simp only [ofList_ofFn, List.length_ofFn, C00.ofArray, C00.place,
            Fin.sum_univ_add, Fin.append_left, Fin.append_right,
            Fin.val_castAdd, Fin.val_natAdd,
            Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

theorem ofList_replicate (J : ℕ) (c : ℝ) :
    ofList (List.replicate J c) = ∑ j : Fin J, Finsupp.single j.val c := by
  rw [← List.ofFn_const, ofList_ofFn]
  rfl

theorem pieces_ofFn_eq {m : ℕ} (a : Fin m → ℝ) (J : ℕ → ℕ) :
    ofList (pieces (List.ofFn fun i => (a i, J i.val))) =
      ∑ i : Fin m, ∑ t : Fin (J i.val),
        Finsupp.single ((∑ k ∈ Finset.range i.val, J k) + t.val)
          (a i / (J i.val : ℝ)) := by
  classical
  induction m generalizing J with
  | zero =>
      simp only [List.ofFn_zero, pieces_nil, Fin.sum_univ_zero]
      exact ofList_ofFn (fun i : Fin 0 => Fin.elim0 i)
  | succ m ih =>
      rw [List.ofFn_succ, pieces_cons, ofList_append, ofList_replicate,
        List.length_replicate]
      simp only [Fin.val_succ]
      rw [ih (fun i => a i.succ) (fun k => J (k + 1))]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Finset.range_zero, Finset.sum_empty,
        zero_add, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [Finset.sum_range_succ']
      omega

theorem finiteSubdivision_eq {m : ℕ} (a : Fin m → ℝ) (J : ℕ → ℕ) :
    finiteSubdivision a (fun i => J i.val) =
      ∑ i : Fin m, ∑ t : Fin (J i.val),
        Finsupp.single ((∑ k ∈ Finset.range i.val, J k) + t.val)
          (a i / (J i.val : ℝ)) :=
  pieces_ofFn_eq a J

end MarkovSuperreflexivity.Subdivision

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionOperators
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.C00

def blockOffset (J : ℕ → ℕ) (i : ℕ) : ℕ := ∑ k ∈ Finset.range i, J k

@[simp] theorem blockOffset_zero (J : ℕ → ℕ) : blockOffset J 0 = 0 := by
  simp [blockOffset]

theorem blockOffset_succ (J : ℕ → ℕ) (i : ℕ) :
    blockOffset J (i + 1) = blockOffset J i + J i :=
  Finset.sum_range_succ J i

theorem blockOffset_mono (J : ℕ → ℕ) : Monotone (blockOffset J) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [blockOffset_succ]
  exact Nat.le_add_right _ _

theorem le_blockOffset (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (i : ℕ) :
    i ≤ blockOffset J i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [blockOffset_succ]
      have hi := hJ i
      omega

@[simp] theorem blockOffset_const (q i : ℕ) :
    blockOffset (fun _ => q) i = q * i := by
  simp [blockOffset, Nat.mul_comm]

theorem blockOffset_mul (r : ℕ) (J : ℕ → ℕ) (i : ℕ) :
    blockOffset (fun k => r * J k) i = r * blockOffset J i := by
  simp only [blockOffset, Finset.mul_sum]

theorem sum_range_blockOffset {A : Type*} [AddCommMonoid A]
    (J : ℕ → ℕ) (m : ℕ) (f : ℕ → A) :
    (∑ k ∈ Finset.range (blockOffset J m), f k) =
      ∑ i : Fin m, ∑ t : Fin (J i.val), f (blockOffset J i.val + t.val) := by
  have h (m : ℕ) :
      (∑ k ∈ Finset.range (blockOffset J m), f k) =
        ∑ i ∈ Finset.range m, ∑ t ∈ Finset.range (J i), f (blockOffset J i + t) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [blockOffset_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]
  calc
    _ = ∑ i ∈ Finset.range m, ∑ t ∈ Finset.range (J i),
        f (blockOffset J i + t) := h m
    _ = _ := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_range (fun t => f (blockOffset J i.val + t))

def blockIndex (J : ℕ → ℕ) (t : Σ i : ℕ, Fin (J i)) : ℕ :=
  blockOffset J t.1 + t.2.val

theorem blockOffset_le_blockIndex (J : ℕ → ℕ) (t : Σ i : ℕ, Fin (J i)) :
    blockOffset J t.1 ≤ blockIndex J t :=
  Nat.le_add_right _ _

theorem blockIndex_lt_blockOffset_succ (J : ℕ → ℕ) (t : Σ i : ℕ, Fin (J i)) :
    blockIndex J t < blockOffset J (t.1 + 1) := by
  rw [blockOffset_succ]
  exact Nat.add_lt_add_left t.2.isLt _

theorem blockIndex_injective (J : ℕ → ℕ) : Function.Injective (blockIndex J) := by
  rintro ⟨i, t⟩ ⟨j, u⟩ he
  have hi : i = j := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have hlt : blockIndex J ⟨i, t⟩ < blockIndex J ⟨j, u⟩ := by
        calc
          _ < blockOffset J (i + 1) := blockIndex_lt_blockOffset_succ J ⟨i, t⟩
          _ ≤ blockOffset J j := blockOffset_mono J (Nat.succ_le_of_lt hij)
          _ ≤ _ := blockOffset_le_blockIndex J ⟨j, u⟩
      exact False.elim ((ne_of_lt hlt) he)
    · exact hij
    · have hlt : blockIndex J ⟨j, u⟩ < blockIndex J ⟨i, t⟩ := by
        calc
          _ < blockOffset J (j + 1) := blockIndex_lt_blockOffset_succ J ⟨j, u⟩
          _ ≤ blockOffset J i := blockOffset_mono J (Nat.succ_le_of_lt hji)
          _ ≤ _ := blockOffset_le_blockIndex J ⟨i, t⟩
      exact False.elim ((ne_of_lt hlt) he.symm)
  subst j
  change blockOffset J i + t.val = blockOffset J i + u.val at he
  have htu : t = u := Fin.ext (Nat.add_left_cancel he)
  subst u
  rfl

theorem exists_blockInterval (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (n : ℕ) :
    ∃ i, blockOffset J i ≤ n ∧ n < blockOffset J (i + 1) := by
  have hex : ∃ i, n < blockOffset J (i + 1) :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (le_blockOffset J hJ (n + 1))⟩
  let i := Nat.find hex
  have hupper : n < blockOffset J (i + 1) := Nat.find_spec hex
  have hlower : blockOffset J i ≤ n := by
    by_cases hi : i = 0
    · simp [hi]
    · have hpred : i - 1 < Nat.find hex := by
        change i - 1 < i
        omega
      have hnot := Nat.find_min hex hpred
      have hsucc : i - 1 + 1 = i := by omega
      rw [hsucc] at hnot
      omega
  exact ⟨i, hlower, hupper⟩

theorem blockIndex_surjective (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) :
    Function.Surjective (blockIndex J) := by
  intro n
  obtain ⟨i, hlower, hupper⟩ := exists_blockInterval J hJ n
  rw [blockOffset_succ] at hupper
  have ht : n - blockOffset J i < J i := by omega
  refine ⟨⟨i, ⟨n - blockOffset J i, ht⟩⟩, ?_⟩
  change blockOffset J i + (n - blockOffset J i) = n
  omega

def uniformBlockLift (q : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  q * f (n / q) + n % q

theorem uniformBlockLift_apply (q : ℕ) (f : ℕ → ℕ) (hq : 0 < q)
    (i t : ℕ) (ht : t < q) :
    uniformBlockLift q f (q * i + t) = q * f i + t := by
  have hqr : (q * i + t) / q = i ∧ (q * i + t) % q = t :=
    (Nat.div_mod_unique hq).2 ⟨Nat.add_comm _ _, ht⟩
  simp only [uniformBlockLift, hqr.1, hqr.2]

theorem uniformBlockLift_strictMono (q : ℕ) (f : ℕ → ℕ) (hq : 0 < q)
    (hf : StrictMono f) : StrictMono (uniformBlockLift q f) := by
  intro a b hab
  have hdiv : a / q ≤ b / q := Nat.div_le_div_right hab.le
  by_cases he : a / q = b / q
  · have ha := Nat.div_add_mod a q
    have hb := Nat.div_add_mod b q
    rw [he] at ha
    have hrem : a % q < b % q := by omega
    simp only [uniformBlockLift, he]
    exact Nat.add_lt_add_left hrem _
  · have hstrict : a / q < b / q := lt_of_le_of_ne hdiv he
    have hstep : f (a / q) + 1 ≤ f (b / q) := hf hstrict
    change q * f (a / q) + a % q < q * f (b / q) + b % q
    calc
      _ < q * f (a / q) + q := Nat.add_lt_add_left (Nat.mod_lt a hq) _
      _ = q * (f (a / q) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ q * f (b / q) := Nat.mul_le_mul_left q hstep
      _ ≤ _ := Nat.le_add_right _ _

def subdivide (J : ℕ → ℕ) : C00 →ₗ[ℝ] C00 :=
  Finsupp.linearCombination ℝ fun i =>
    ∑ t : Fin (J i), Finsupp.single (blockOffset J i + t.val) ((J i : ℝ)⁻¹)

def uniformSubdivision (q : ℕ) : C00 →ₗ[ℝ] C00 := subdivide (fun _ => q)

@[simp] theorem subdivide_single (J : ℕ → ℕ) (i : ℕ) (a : ℝ) :
    subdivide J (Finsupp.single i a) =
      ∑ t : Fin (J i), Finsupp.single (blockOffset J i + t.val) (a / (J i : ℝ)) := by
  simp [subdivide, Finset.smul_sum, Finsupp.smul_single, div_eq_mul_inv]

@[simp] theorem uniformSubdivision_single (q i : ℕ) (a : ℝ) :
    uniformSubdivision q (Finsupp.single i a) =
      ∑ t : Fin q, Finsupp.single (q * i + t.val) (a / (q : ℝ)) := by
  simp [uniformSubdivision, blockOffset, Nat.mul_comm]

theorem subdivide_ofArray (J : ℕ → ℕ) {m : ℕ} (a : Fin m → ℝ) :
    subdivide J (ofArray a) =
      ∑ i : Fin m, ∑ t : Fin (J i.val),
        Finsupp.single (blockOffset J i.val + t.val) (a i / (J i.val : ℝ)) := by
  simp only [ofArray, place, map_sum, subdivide_single]

theorem subdivide_ofArray_eq_finiteSubdivision (J : ℕ → ℕ) {m : ℕ}
    (a : Fin m → ℝ) :
    subdivide J (ofArray a) = Subdivision.finiteSubdivision a (fun i => J i.val) := by
  simp only [subdivide_ofArray, Subdivision.finiteSubdivision_eq, blockOffset]

theorem subdivide_single_apply_block (J : ℕ → ℕ) (i j : ℕ)
    (t : Fin (J i)) (a : ℝ) :
    subdivide J (Finsupp.single j a) (blockOffset J i + t.val) =
      (Finsupp.single j a i) / (J i : ℝ) := by
  classical
  rw [subdivide_single]
  by_cases hji : j = i
  · subst j
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single t]
    · simp
    · intro u _ hut
      have hne : blockOffset J i + u.val ≠ blockOffset J i + t.val := by
        intro h
        exact hut (Fin.ext (Nat.add_left_cancel h))
      simp only [Finsupp.single_apply, ite_eq_right hne]
    · simp
  · have hne (u : Fin (J j)) :
        blockOffset J j + u.val ≠ blockOffset J i + t.val := by
      intro h
      have he : (⟨j, u⟩ : Σ k, Fin (J k)) = ⟨i, t⟩ := blockIndex_injective J h
      exact hji (congrArg Sigma.fst he)
    simp [Finsupp.finsetSum_apply, hne, hji]

theorem subdivide_apply_block (J : ℕ → ℕ) (x : C00) (i : ℕ) (t : Fin (J i)) :
    subdivide J x (blockOffset J i + t.val) = x i / (J i : ℝ) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_div]
  | single j a => exact subdivide_single_apply_block J i j t a

theorem sum_subdivide_block (J : ℕ → ℕ) (x : C00) (i : ℕ) (hi : 0 < J i) :
    (∑ t : Fin (J i), subdivide J x (blockOffset J i + t.val)) = x i := by
  have hne : (J i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  simp only [subdivide_apply_block, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel₀ (x i) hne

theorem prefixCut_subdivide (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (x : C00) (k : ℕ) :
    prefixCut (subdivide J x) (blockOffset J k) = prefixCut x k := by
  rw [prefixCut, sum_range_blockOffset]
  simp_rw [sum_subdivide_block J x _ (hJ _)]
  simpa only [prefixCut] using (Fin.sum_univ_eq_sum_range (fun i => x i) k)

theorem subdivide_ofArray_apply_of_ge (J : ℕ → ℕ) {m : ℕ} (a : Fin m → ℝ)
    (k : ℕ) (hk : blockOffset J m ≤ k) : subdivide J (ofArray a) k = 0 := by
  classical
  rw [subdivide_ofArray]
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro t _
  have hlt : blockOffset J i.val + t.val < blockOffset J m := by
    calc
      blockOffset J i.val + t.val < blockOffset J i.val + J i.val :=
        Nat.add_lt_add_left t.isLt _
      _ = blockOffset J (i.val + 1) := (blockOffset_succ J i.val).symm
      _ ≤ blockOffset J m := blockOffset_mono J (Nat.succ_le_of_lt i.isLt)
  have hne : blockOffset J i.val + t.val ≠ k := Nat.ne_of_lt (lt_of_lt_of_le hlt hk)
  simp [hne]

def l1Mass (x : C00) : ℝ := x.sum (fun _ a => |a|)

theorem l1Mass_eq_sum_range (x : C00) (m : ℕ) (h : ∀ k, m ≤ k → x k = 0) :
    l1Mass x = ∑ k ∈ Finset.range m, |x k| := by
  apply Finsupp.sum_of_support_subset x
  · intro k hk
    apply Finset.mem_range.mpr
    by_contra hkm
    have hx := h k (Nat.le_of_not_gt hkm)
    exact (Finsupp.mem_support_iff.mp hk) hx
  · intro _ _
    exact abs_zero

theorem l1Mass_ofArray {m : ℕ} (a : Fin m → ℝ) :
    l1Mass (ofArray a) = ∑ i : Fin m, |a i| := by
  rw [l1Mass_eq_sum_range (ofArray a) m (ofArray_apply_of_ge a)]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [ofArray_apply]

theorem l1Mass_subdivide (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (x : C00) :
    l1Mass (subdivide J x) = l1Mass x := by
  obtain ⟨m, a, rfl⟩ := exists_ofArray x
  rw [l1Mass_eq_sum_range _ (blockOffset J m)
    (subdivide_ofArray_apply_of_ge J a), sum_range_blockOffset, l1Mass_ofArray]
  apply Finset.sum_congr rfl
  intro i _
  simp only [subdivide_apply_block, ofArray_apply, abs_div,
    abs_of_nonneg (show 0 ≤ (J i.val : ℝ) from Nat.cast_nonneg _), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : (J i.val : ℝ) ≠ 0 := by exact_mod_cast (hJ i.val).ne'
  exact mul_div_cancel₀ |a i| hne

@[simp] theorem uniformSubdivision_apply (q : ℕ) (hq : 0 < q) (x : C00) (k : ℕ) :
    uniformSubdivision q x k = x (k / q) / (q : ℝ) := by
  have h := subdivide_apply_block (fun _ => q) x (k / q)
    ⟨k % q, Nat.mod_lt k hq⟩
  have hk : q * (k / q) + k % q = k := Nat.div_add_mod k q
  simpa only [uniformSubdivision, blockOffset_const, hk] using h

theorem uniformSubdivision_subdivide (r : ℕ) (hr : 0 < r) (J : ℕ → ℕ)
    (hJ : ∀ i, 0 < J i) (x : C00) :
    uniformSubdivision r (subdivide J x) = subdivide (fun i => r * J i) x := by
  ext k
  obtain ⟨⟨i, t⟩, rfl⟩ := blockIndex_surjective (fun i => r * J i)
    (fun i => Nat.mul_pos hr (hJ i)) k
  change uniformSubdivision r (subdivide J x)
      (blockOffset (fun i => r * J i) i + t.val) =
    subdivide (fun i => r * J i) x (blockOffset (fun i => r * J i) i + t.val)
  rw [subdivide_apply_block (fun i => r * J i) x i t,
    uniformSubdivision_apply r hr, blockOffset_mul]
  have ht : t.val / r < J i := by
    apply (Nat.div_lt_iff_lt_mul hr).mpr
    simpa only [Nat.mul_comm] using t.isLt
  have hdiv : (r * blockOffset J i + t.val) / r = blockOffset J i + t.val / r := by
    rw [Nat.add_comm (r * blockOffset J i) t.val, Nat.add_mul_div_left _ _ hr,
      Nat.add_comm]
  rw [hdiv, subdivide_apply_block J x i ⟨t.val / r, ht⟩]
  simp only [div_div, Nat.cast_mul, mul_comm]

theorem uniformSubdivision_mapDomain (q : ℕ) (hq : 0 < q)
    (f : ℕ → ℕ) (x : C00) :
    uniformSubdivision q (Finsupp.mapDomain f x) =
      Finsupp.mapDomain (uniformBlockLift q f) (uniformSubdivision q x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [Finsupp.mapDomain_zero]
  | add x y hx hy => simp only [Finsupp.mapDomain_add, map_add, hx, hy]
  | single i a =>
    rw [Finsupp.mapDomain_single, uniformSubdivision_single,
      uniformSubdivision_single, Finsupp.mapDomain_finsetSum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finsupp.mapDomain_single, uniformBlockLift_apply q f hq i t.val t.isLt]

@[simp] theorem prefixCut_uniformSubdivision (q : ℕ) (hq : 0 < q)
    (x : C00) (k : ℕ) :
    prefixCut (uniformSubdivision q x) (q * k) = prefixCut x k := by
  simpa only [uniformSubdivision, blockOffset_const] using
    prefixCut_subdivide (fun _ => q) (fun _ => hq) x k

@[simp] theorem l1Mass_uniformSubdivision (q : ℕ) (hq : 0 < q) (x : C00) :
    l1Mass (uniformSubdivision q x) = l1Mass x :=
  l1Mass_subdivide (fun _ => q) (fun _ => hq) x

end MarkovSuperreflexivity.C00

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_OrderedJColumns
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def jColumn (n m j : ℕ) : C00 :=
  ∑ t ∈ Finset.range m, (basis (2 * n * t + j) - basis (2 * n * t + n + j))

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PowerRenormingFromDyadic
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def dyadicPowerEquivalentNorm {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    EquivalentNorm X where
  p := dyadicPowerSeminorm hq.le hD
  lower := 1
  upper := T
  lower_pos := zero_lt_one
  upper_pos := lt_of_lt_of_le zero_lt_one hT
  lower_bound x := by
    simpa only [one_mul] using norm_le_dyadicPowerSeminorm hq.le hD x
  upper_bound x := dyadicPowerSeminorm_le_mul_norm hq.le hD
    (le_trans zero_le_one hT) le_rfl x

@[simp] theorem dyadicPowerEquivalentNorm_p {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    (dyadicPowerEquivalentNorm hq hT hD).p = dyadicPowerSeminorm hq.le hD := rfl

@[simp] theorem dyadicPowerEquivalentNorm_lower {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    (dyadicPowerEquivalentNorm hq hT hD).lower = 1 := rfl

@[simp] theorem dyadicPowerEquivalentNorm_upper {q T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hD : FiniteDyadicUpperEstimate (X := X) q (T ^ q) (T ^ q)) :
    (dyadicPowerEquivalentNorm hq hT hD).upper = T := rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_Renormed
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def Renormed (_N : EquivalentNorm X) : Type u := X

namespace Renormed

variable (N : EquivalentNorm X)

instance instAddCommGroup : AddCommGroup (Renormed N) := inferInstanceAs (AddCommGroup X)
instance instModuleReal : Module ℝ (Renormed N) := inferInstanceAs (Module ℝ X)

def ofOriginal (x : X) : Renormed N := x
def toOriginal (x : Renormed N) : X := x

@[simp] theorem toOriginal_ofOriginal (x : X) :
    toOriginal N (ofOriginal N x) = x := rfl

@[simp] theorem ofOriginal_toOriginal (x : Renormed N) :
    ofOriginal N (toOriginal N x) = x := rfl

instance instNorm : Norm (Renormed N) := ⟨fun x => N.p (toOriginal N x)⟩

theorem normCore : NormedSpace.Core ℝ (Renormed N) where
  norm_nonneg x := apply_nonneg N.p (toOriginal N x)
  norm_smul c x := map_smul_eq_mul N.p c (toOriginal N x)
  norm_triangle x y := map_add_le_add N.p (toOriginal N x) (toOriginal N y)
  norm_eq_zero_iff x := N.eq_zero_iff (toOriginal N x)

instance instNormedAddCommGroup : NormedAddCommGroup (Renormed N) := NormedAddCommGroup.ofCore (normCore N)
instance instNormedSpaceReal : NormedSpace ℝ (Renormed N) := NormedSpace.ofCore (normCore N)

@[simp] theorem norm_ofOriginal (x : X) : ‖ofOriginal N x‖ = N.p x := rfl

@[simp] theorem norm_eq (x : Renormed N) : ‖x‖ = N.p (toOriginal N x) := rfl

def linearEquiv : X ≃ₗ[ℝ] Renormed N where
  toFun := ofOriginal N
  invFun := toOriginal N
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofOriginalL : X →L[ℝ] Renormed N :=
  (linearEquiv N).toLinearMap.mkContinuous N.upper (fun x => N.upper_bound x)

def toOriginalL : Renormed N →L[ℝ] X :=
  (linearEquiv N).symm.toLinearMap.mkContinuous (1 / N.lower) (by
    intro x
    change ‖toOriginal N x‖ ≤ (1 / N.lower) * N.p (toOriginal N x)
    calc
      ‖toOriginal N x‖ ≤ N.p (toOriginal N x) / N.lower :=
        (le_div_iff₀ N.lower_pos).2 (by simpa only [mul_comm] using N.lower_bound (toOriginal N x))
      _ = (1 / N.lower) * N.p (toOriginal N x) := by ring)

@[simp] theorem ofOriginalL_apply (x : X) : ofOriginalL N x = ofOriginal N x := rfl

@[simp] theorem toOriginalL_apply (x : Renormed N) : toOriginalL N x = toOriginal N x := rfl

def continuousLinearEquiv : X ≃L[ℝ] Renormed N where
  toLinearEquiv := linearEquiv N
  continuous_toFun := (ofOriginalL N).continuous
  continuous_invFun := (toOriginalL N).continuous

end Renormed

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ReversibleMartingales
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S X : Type*} [Fintype S]
variable [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

local instance instDecidableEq_solutions : DecidableEq S := Classical.decEq S

def chainAverage (C : FiniteReversibleChain S) (f : S → X) (i : S) : X :=
  ∑ j, C.P i j • f j

def chainDrift (C : FiniteReversibleChain S) (f : S → X) (i : S) : X :=
  chainAverage C f i - f i

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ScalarUltralimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

def RealSeqBounded (f : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n, |f n| ≤ B

namespace RealSeqBounded

variable {f g : ℕ → ℝ}

theorem const (c : ℝ) : RealSeqBounded (fun _ : ℕ => c) :=
  ⟨|c|, fun _ => le_rfl⟩

theorem add (hf : RealSeqBounded f) (hg : RealSeqBounded g) :
    RealSeqBounded (fun n => f n + g n) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  exact ⟨B + C, fun n => (abs_add_le (f n) (g n)).trans (add_le_add (hB n) (hC n))⟩

theorem abs (hf : RealSeqBounded f) : RealSeqBounded (fun n => |f n|) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  simpa only [abs_abs] using hB n

end RealSeqBounded

def realULim (U : Ultrafilter ℕ) (f : ℕ → ℝ) : ℝ :=
  Filter.limUnder (U : Filter ℕ) f

variable {f g : ℕ → ℝ}

theorem tendsto_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    Tendsto f (U : Filter ℕ) (𝓝 (realULim U f)) := by
  obtain ⟨B, hB⟩ := hf
  have hmem : Set.Icc (-B) B ∈ Ultrafilter.map f U := by
    change ∀ᶠ n in (U : Filter ℕ), f n ∈ Set.Icc (-B) B
    exact Filter.Eventually.of_forall fun n => abs_le.mp (hB n)
  obtain ⟨a, _ha, hlim⟩ :=
    isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map f U) hmem
  have ha : Tendsto f (U : Filter ℕ) (𝓝 a) := hlim
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem realULim_eq_of_tendsto (U : Ultrafilter ℕ) {a : ℝ}
    (h : Tendsto f (U : Filter ℕ) (𝓝 a)) : realULim U f = a :=
  h.limUnder_eq

@[simp]
theorem realULim_const (U : Ultrafilter ℕ) (c : ℝ) :
    realULim U (fun _ : ℕ => c) = c :=
  realULim_eq_of_tendsto U tendsto_const_nhds

theorem realULim_add (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) :
    realULim U (fun n => f n + g n) = realULim U f + realULim U g :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).add (tendsto_realULim U hg))

theorem realULim_const_mul (U : Ultrafilter ℕ) (c : ℝ) (hf : RealSeqBounded f) :
    realULim U (fun n => c * f n) = c * realULim U f :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).const_mul c)

theorem realULim_le_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ g n) :
    realULim U f ≤ realULim U g :=
  le_of_tendsto_of_tendsto (tendsto_realULim U hf) (tendsto_realULim U hg) h

theorem le_realULim_of_eventually_le (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    {c : ℝ} (h : ∀ᶠ n in (U : Filter ℕ), c ≤ f n) : c ≤ realULim U f := by
  have hlim := realULim_le_realULim U (RealSeqBounded.const c) hf h
  simpa only [realULim_const] using hlim

def freeUltrafilter : Ultrafilter ℕ := Filter.hyperfilter ℕ

theorem freeUltrafilter_le_atTop : (freeUltrafilter : Filter ℕ) ≤ Filter.atTop :=
  Nat.hyperfilter_le_atTop

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularArrays
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

structure TriangularArray (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (d ε : ℝ) (M : ℕ) where
  y : Fin M → Y
  f : Fin M → (Y →L[ℝ] ℝ)
  y_norm_le : ∀ j, ‖y j‖ ≤ 1
  f_norm_le : ∀ i, ‖f i‖ ≤ 1
  lower_zero : ∀ i j, j < i → f i (y j) = 0
  upper_close : ∀ i j, i ≤ j → |f i (y j) - d| ≤ ε

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularPrefix
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def coefficientL1 {m : ℕ} (a : Fin m → ℝ) : ℝ := ∑ i, |a i|

def arrayPrefix {m : ℕ} (a : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if i.val < k then a i else 0

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SelectedRows
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]

structure SelectedRow (d : ℝ) (k : ℕ) where
  M : ℕ
  le_M : k ≤ M
  cubic_le_M : k ^ 3 ≤ M
  A : TriangularArray Y d (M : ℝ)⁻¹ M
  e : Fin k ↪o Fin M
  homogeneous : ∀ (m : ℕ) (_hm : m ≤ k) (a : Fin m → ℝ),
    (∀ i, |a i| ≤ 1) → ∀ s t : Fin m ↪o Fin k,
      |‖∑ i, a i • A.y (Fin.rev (e (s i)))‖ -
        ‖∑ i, a i • A.y (Fin.rev (e (t i)))‖| ≤ 3 / (k : ℝ)

variable {Y}

namespace SelectedRow

variable {d : ℝ} {k : ℕ}

def vector (R : SelectedRow Y d k) (i : Fin k) : Y := R.A.y (Fin.rev (R.e i))

def synthesis (R : SelectedRow Y d k) : C00 →ₗ[ℝ] Y :=
  Finsupp.linearCombination ℝ (fun j => if h : j < k then R.vector ⟨j, h⟩ else 0)

end SelectedRow

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SeminormUltralimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter

namespace MarkovSuperreflexivity

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

def seminormULim (U : Ultrafilter ℕ) (p : ℕ → Seminorm ℝ E)
    (hb : ∀ x : E, RealSeqBounded (fun n => p n x)) : Seminorm ℝ E :=
  Seminorm.of (fun x => realULim U (fun n => p n x))
    (by
      intro x y
      have h := realULim_le_realULim U (hb (x + y)) ((hb x).add (hb y))
        (Filter.Eventually.of_forall (fun n => map_add_le_add (p n) x y))
      simpa only [realULim_add U (hb x) (hb y)] using h)
    (by
      intro a x
      have he : (fun n => p n (a • x)) = (fun n => ‖a‖ * p n x) := by
        funext n
        exact map_smul_eq_mul (p n) a x
      change realULim U (fun n => p n (a • x)) =
        ‖a‖ * realULim U (fun n => p n x)
      rw [he, realULim_const_mul U ‖a‖ (hb x)])

@[simp] theorem seminormULim_apply (U : Ultrafilter ℕ) (p : ℕ → Seminorm ℝ E)
    (hb : ∀ x : E, RealSeqBounded (fun n => p n x)) (x : E) :
    seminormULim U p hb x = realULim U (fun n => p n x) := rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

namespace SpreadingLimit

section PointwiseLimit

variable {E Y : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (L : ℕ → E →ₗ[ℝ] Y)
  (hCauchy : ∀ x, CauchySeq (fun n => ‖L n x‖))

def normLimit (x : E) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete (hCauchy x))

theorem tendsto_normLimit (x : E) :
    Tendsto (fun n => ‖L n x‖) atTop (𝓝 (normLimit L hCauchy x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hCauchy x))

theorem normLimit_add_le (x y : E) :
    normLimit L hCauchy (x + y) ≤ normLimit L hCauchy x + normLimit L hCauchy y := by
  apply le_of_tendsto_of_tendsto' (tendsto_normLimit L hCauchy (x + y))
    ((tendsto_normLimit L hCauchy x).add (tendsto_normLimit L hCauchy y))
  intro n
  simpa only [map_add] using norm_add_le (L n x) (L n y)

theorem normLimit_smul (r : ℝ) (x : E) :
    normLimit L hCauchy (r • x) = ‖r‖ * normLimit L hCauchy x := by
  have h : Tendsto (fun n => ‖L n (r • x)‖) atTop
      (𝓝 (‖r‖ * normLimit L hCauchy x)) := by
    simpa only [map_smul, norm_smul] using
      (tendsto_const_nhds.mul (tendsto_normLimit L hCauchy x))
  exact tendsto_nhds_unique (tendsto_normLimit L hCauchy (r • x)) h

def limitSeminorm : Seminorm ℝ E :=
  Seminorm.of (normLimit L hCauchy) (normLimit_add_le L hCauchy)
    (normLimit_smul L hCauchy)

@[simp] theorem limitSeminorm_apply (x : E) :
    limitSeminorm L hCauchy x = normLimit L hCauchy x := rfl

end PointwiseLimit

end SpreadingLimit

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitReal
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

abbrev RationalCoefficients := Σ m : ℕ, Fin m → ℚ

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingModel
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

structure SpreadingModel (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  p : Seminorm ℝ C00
  d : ℝ
  d_pos : 0 < d
  prefix_lower : ∀ x r, d * |prefixCut x r| ≤ p x
  array_upper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|
  spreading : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
    ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a)
  embeddings : ∀ (m : ℕ) (η : ℝ), 0 < η →
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
      p (C00.ofArray a) ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p (C00.ofArray a)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionAverage
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.Subdivision

def skip (cut i : ℕ) : ℕ := if i < cut then i else i + 1

theorem strictMono_skip (cut : ℕ) : StrictMono (skip cut) := by
  intro i j hij
  simp only [skip]
  split_ifs <;> omega

def blockArray {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) : Fin (l + (J + r)) → ℝ :=
  Fin.append left (Fin.append (fun _ : Fin J => c / (J : ℝ)) right)

def blockVector {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) : C00 := C00.ofArray (blockArray left right J c)

theorem place_blockArray {l r : ℕ} (left : Fin l → ℝ)
    (right : Fin r → ℝ) (J : ℕ) (c : ℝ) (g : ℕ → ℕ) :
    C00.place (fun i => g i.val) (blockArray left right J c) =
      (∑ i : Fin l, Finsupp.single (g i.val) (left i)) +
      ((∑ j : Fin J, Finsupp.single (g (l + j.val)) (c / (J : ℝ))) +
        ∑ i : Fin r, Finsupp.single (g (l + (J + i.val))) (right i)) := by
  classical
  simp only [C00.place, blockArray, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]

theorem blockVector_eq {l r : ℕ} (left : Fin l → ℝ)
    (right : Fin r → ℝ) (J : ℕ) (c : ℝ) :
    blockVector left right J c =
      (∑ i : Fin l, Finsupp.single i.val (left i)) +
      ((∑ j : Fin J, Finsupp.single (l + j.val) (c / (J : ℝ))) +
        ∑ i : Fin r, Finsupp.single (l + (J + i.val)) (right i)) := by
  exact place_blockArray left right J c id

def sample {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) (t : Fin (J + 1)) : C00 :=
  C00.place (fun i => skip (l + t.val) i.val) (blockArray left right J c)

theorem skip_in_block {J l : ℕ} (t : Fin (J + 1)) (j : Fin J) :
    skip (l + t.val) (l + j.val) = l + (t.succAbove j).val := by
  by_cases h : j.val < t.val
  · have h' : j.castSucc < t := h
    rw [Fin.succAbove_of_castSucc_lt _ _ h']
    simp only [skip, Fin.val_castSucc]
    rw [ite_eq_left (Nat.add_lt_add_left h l)]
  · have h' : t ≤ j.castSucc := Nat.le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ h']
    simp only [skip, Fin.val_succ]
    rw [ite_eq_right (by omega)]
    omega

theorem sample_eq {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) (t : Fin (J + 1)) :
    sample left right J c t =
      (∑ i : Fin l, Finsupp.single i.val (left i)) +
      ((∑ j : Fin J,
        Finsupp.single (l + (t.succAbove j).val) (c / (J : ℝ))) +
        ∑ i : Fin r, Finsupp.single (l + (J + 1 + i.val)) (right i)) := by
  classical
  rw [sample, place_blockArray]
  have hl (i : Fin l) : skip (l + t.val) i.val = i.val := by
    apply ite_eq_left
    have hi := i.isLt
    omega
  have hr (i : Fin r) :
      skip (l + t.val) (l + (J + i.val)) = l + (J + 1 + i.val) := by
    have ht := t.isLt
    simp only [skip]
    rw [ite_eq_right (by omega)]
    omega
  simp only [hl, hr, skip_in_block]

theorem sum_deletions {A : Type*} [AddCommGroup A] (J : ℕ)
    (f : Fin (J + 1) → A) :
    (∑ t : Fin (J + 1), ∑ j : Fin J, f (t.succAbove j)) =
      J • ∑ t : Fin (J + 1), f t := by
  classical
  have hd (t : Fin (J + 1)) :
      (∑ j : Fin J, f (t.succAbove j)) = (∑ i, f i) - f t := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (Fin.sum_univ_succAbove f t).symm
  simp_rw [hd]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [add_nsmul, one_nsmul]
  abel

theorem block_nsmul {J l : ℕ} (hJ : 0 < J) (c : ℝ) :
    J • (∑ t : Fin (J + 1), Finsupp.single (l + t.val) (c / (J : ℝ))) =
      (J + 1) •
        (∑ t : Fin (J + 1), Finsupp.single (l + t.val) (c / ((J + 1 : ℕ) : ℝ))) := by
  classical
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  have hj' : ((J + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem sum_samples {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    {J : ℕ} (hJ : 0 < J) (c : ℝ) :
    (∑ t : Fin (J + 1), sample left right J c t) =
      (J + 1) • blockVector left right (J + 1) c := by
  classical
  simp_rw [sample_eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_deletions J (fun t : Fin (J + 1) =>
      Finsupp.single (l + t.val) (c / (J : ℝ)))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [block_nsmul hJ c, blockVector_eq]
  simp only [smul_add]

theorem seminorm_sum_le (p : Seminorm ℝ C00) {A : Type*}
    (s : Finset A) (f : A → C00) : p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_refl]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (p.add_le' _ _).trans (add_le_add le_rfl ih)

variable (p : Seminorm ℝ C00)
variable (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
  ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a))

include hspread

theorem sample_norm {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) (t : Fin (J + 1)) :
    p (sample left right J c t) = p (blockVector left right J c) := by
  apply hspread
  intro i j hij
  exact strictMono_skip (l + t.val) (show i.val < j.val from hij)

theorem block_succ_le {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    {J : ℕ} (hJ : 0 < J) (c : ℝ) :
    p (blockVector left right (J + 1) c) ≤ p (blockVector left right J c) := by
  classical
  have h := seminorm_sum_le p Finset.univ (sample left right J c)
  rw [sum_samples left right hJ c, ← Nat.cast_smul_eq_nsmul ℝ,
    map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at h
  simp_rw [sample_norm p hspread] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < ((J + 1 : ℕ) : ℝ))).mp h

theorem block_mono {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    {J M : ℕ} (hJ : 0 < J) (hJM : J ≤ M) (c : ℝ) :
    p (blockVector left right M c) ≤ p (blockVector left right J c) := by
  induction M, hJM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hJM ih =>
      exact (block_succ_le p hspread left right (by omega : 0 < M) c).trans ih

end MarkovSuperreflexivity.Subdivision

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionProfiles
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

variable (p : Seminorm ℝ C00)
variable (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
  ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a))

include hspread in
theorem list_block_mono (left right : List ℝ) {J M : ℕ}
    (hJ : 0 < J) (hJM : J ≤ M) (c : ℝ) :
    p (ofList (left ++ (List.replicate M (c / (M : ℝ)) ++ right))) ≤
      p (ofList (left ++ (List.replicate J (c / (J : ℝ)) ++ right))) := by
  induction left using List.ofFnRec with
  | h l left =>
      induction right using List.ofFnRec with
      | h r right =>
          have h := block_mono p hspread left right hJ hJM c
          simpa only [blockVector, ← ofList_ofFn, blockArray,
            List.ofFn_fin_append, List.ofFn_const] using h

def ProfileLE (a b : ℝ × ℕ) : Prop := a.1 = b.1 ∧ 0 < a.2 ∧ a.2 ≤ b.2

include hspread in
theorem pieces_mono_in_context {small large : List (ℝ × ℕ)}
    (h : List.Forall₂ ProfileLE small large) (left right : List ℝ) :
    p (ofList (left ++ (pieces large ++ right))) ≤
      p (ofList (left ++ (pieces small ++ right))) := by
  induction h generalizing left right with
  | nil => exact le_rfl
  | @cons a b small large hab htail ih =>
      rcases a with ⟨c, J⟩
      rcases b with ⟨d, M⟩
      rcases hab with ⟨hcd, hJ, hJM⟩
      change c = d at hcd
      subst d
      have htail' := ih (left ++ List.replicate M (c / (M : ℝ))) right
      simp only [List.append_assoc] at htail'
      have hhead := list_block_mono p hspread left (pieces small ++ right) hJ hJM c
      simpa only [pieces_cons, List.append_assoc] using htail'.trans hhead

theorem profiles_related : ∀ {m : ℕ} (a : Fin m → ℝ)
    (J M : Fin m → ℕ), (∀ i, 0 < J i) → (∀ i, J i ≤ M i) →
    List.Forall₂ ProfileLE (List.ofFn fun i => (a i, J i))
      (List.ofFn fun i => (a i, M i))
  | 0, a, J, M, _, _ => by simp only [List.ofFn_zero]; exact .nil
  | m + 1, a, J, M, hJ, hJM => by
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons ⟨rfl, hJ 0, hJM 0⟩
        (profiles_related (fun i => a i.succ) (fun i => J i.succ)
          (fun i => M i.succ) (fun i => hJ i.succ) (fun i => hJM i.succ))

include hspread in

theorem finiteSubdivision_mono {m : ℕ} (a : Fin m → ℝ) (J M : Fin m → ℕ)
    (hJ : ∀ i, 0 < J i) (hJM : ∀ i, J i ≤ M i) :
    p (finiteSubdivision a M) ≤ p (finiteSubdivision a J) := by
  have h := pieces_mono_in_context p hspread (profiles_related a J M hJ hJM) [] []
  simpa only [List.nil_append, List.append_nil, finiteSubdivision] using h

end MarkovSuperreflexivity.Subdivision

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionSpreading
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

def extendPlacement {m : ℕ} (ι : Fin m → ℕ) (i : ℕ) : ℕ :=
  if h : i < m then ι ⟨i, h⟩ else Finset.univ.sup ι + 1 + (i - m)

@[simp] theorem extendPlacement_apply {m : ℕ} (ι : Fin m → ℕ) (i : Fin m) :
    extendPlacement ι i.val = ι i := by
  simp only [extendPlacement, dite_eq_left i.isLt]

theorem strictMono_extendPlacement {m : ℕ} (ι : Fin m → ℕ)
    (hι : StrictMono ι) : StrictMono (extendPlacement ι) := by
  classical
  intro i j hij
  simp only [extendPlacement]
  split_ifs with hi hj
  · exact hι (show (⟨i, hi⟩ : Fin m) < ⟨j, hj⟩ from hij)
  · have hb : ι ⟨i, hi⟩ ≤ Finset.univ.sup ι :=
      Finset.le_sup (Finset.mem_univ (⟨i, hi⟩ : Fin m))
    omega
  · omega
  · omega

theorem mapDomain_ofArray (f : ℕ → ℕ) {m : ℕ} (a : Fin m → ℝ) :
    Finsupp.mapDomain f (C00.ofArray a) = C00.place (fun i => f i.val) a := by
  classical
  simp only [C00.ofArray, C00.place, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single]

theorem mapDomain_extendPlacement {m : ℕ} (ι : Fin m → ℕ) (a : Fin m → ℝ) :
    Finsupp.mapDomain (extendPlacement ι) (C00.ofArray a) = C00.place ι a := by
  rw [mapDomain_ofArray]
  simp only [extendPlacement_apply]

variable (p : Seminorm ℝ C00)
variable (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
  ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a))

include hspread in
theorem norm_mapDomain (f : ℕ → ℕ) (hf : StrictMono f) (x : C00) :
    p (Finsupp.mapDomain f x) = p x := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha, mapDomain_ofArray]
  apply hspread
  intro i j hij
  exact hf (show i.val < j.val from hij)

include hspread in

theorem uniform_spreading (q : ℕ) (hq : 0 < q) {m : ℕ}
    (ι : Fin m → ℕ) (hι : StrictMono ι) (a : Fin m → ℝ) :
    p (C00.uniformSubdivision q (C00.place ι a)) =
      p (C00.uniformSubdivision q (C00.ofArray a)) := by
  rw [← mapDomain_extendPlacement ι a, C00.uniformSubdivision_mapDomain q hq]
  exact norm_mapDomain p hspread _
    (C00.uniformBlockLift_strictMono q (extendPlacement ι) hq
      (strictMono_extendPlacement ι hι)) _

end MarkovSuperreflexivity.Subdivision

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionLimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

namespace Subdivision

theorem subdivide_le_ofArray (p : Seminorm ℝ C00)
    (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a, p (C00.place ι a) = p (C00.ofArray a))
    {m : ℕ} (a : Fin m → ℝ) (J M : ℕ → ℕ)
    (hJ : ∀ i : Fin m, 0 < J i.val) (hJM : ∀ i : Fin m, J i.val ≤ M i.val) :
    p (C00.subdivide M (C00.ofArray a)) ≤ p (C00.subdivide J (C00.ofArray a)) := by
  rw [C00.subdivide_ofArray_eq_finiteSubdivision, C00.subdivide_ofArray_eq_finiteSubdivision]
  exact finiteSubdivision_mono p hspread a _ _ hJ hJM

theorem subdivide_le (p : Seminorm ℝ C00)
    (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a, p (C00.place ι a) = p (C00.ofArray a))
    (J M : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (hJM : ∀ i, J i ≤ M i) (x : C00) :
    p (C00.subdivide M x) ≤ p (C00.subdivide J x) := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha]
  exact subdivide_le_ofArray p hspread a J M (fun i => hJ i.val) (fun i => hJM i.val)

end Subdivision

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def subdivisionFamily (S : SpreadingModel Y) (n : ℕ) : Seminorm ℝ C00 :=
  S.p.comp (C00.uniformSubdivision (n + 1))

theorem subdivisionFamily_antitone (S : SpreadingModel Y) (x : C00) :
    Antitone fun n => S.subdivisionFamily n x := by
  intro n m hnm
  exact Subdivision.subdivide_le S.p S.spreading (fun _ => n + 1) (fun _ => m + 1)
    (fun _ => Nat.succ_pos n) (fun _ => Nat.succ_le_succ hnm) x

def averagedSeminorm (S : SpreadingModel Y) : Seminorm ℝ C00 :=
  SeminormLimit.seminorm S.subdivisionFamily S.subdivisionFamily_antitone

theorem tendsto_averagedSeminorm (S : SpreadingModel Y) (x : C00) :
    Tendsto (fun n => S.p (C00.uniformSubdivision (n + 1) x)) atTop
      (𝓝 (S.averagedSeminorm x)) :=
  SeminormLimit.tendsto_value S.subdivisionFamily S.subdivisionFamily_antitone x

theorem averaged_le_uniform (S : SpreadingModel Y) (x : C00)
    (q : ℕ) (hq : 0 < q) :
    S.averagedSeminorm x ≤ S.p (C00.uniformSubdivision q x) := by
  unfold averagedSeminorm
  have h := SeminormLimit.seminorm_le S.subdivisionFamily
    S.subdivisionFamily_antitone x (q - 1)
  have he : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  simpa only [subdivisionFamily, Seminorm.comp_apply, he] using h

theorem p_le_l1Mass (S : SpreadingModel Y) (x : C00) : S.p x ≤ C00.l1Mass x := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha, C00.l1Mass_ofArray]
  exact S.array_upper a

theorem subdivisionFamily_upper (S : SpreadingModel Y) (n : ℕ) (x : C00) :
    S.subdivisionFamily n x ≤ C00.l1Mass x := by
  change S.p (C00.uniformSubdivision (n + 1) x) ≤ C00.l1Mass x
  have h := S.p_le_l1Mass (C00.uniformSubdivision (n + 1) x)
  simpa only [C00.l1Mass_uniformSubdivision (n + 1) (Nat.succ_pos n)] using h

theorem subdivisionFamily_prefix_lower (S : SpreadingModel Y) (n : ℕ)
    (x : C00) (k : ℕ) : S.d * |prefixCut x k| ≤ S.subdivisionFamily n x := by
  change S.d * |prefixCut x k| ≤ S.p (C00.uniformSubdivision (n + 1) x)
  have h := S.prefix_lower (C00.uniformSubdivision (n + 1) x) ((n + 1) * k)
  simpa only [C00.prefixCut_uniformSubdivision (n + 1) (Nat.succ_pos n)] using h

theorem averaged_array_upper (S : SpreadingModel Y) {m : ℕ} (a : Fin m → ℝ) :
    S.averagedSeminorm (C00.ofArray a) ≤ ∑ i, |a i| := by
  unfold averagedSeminorm
  have h := SeminormLimit.upper_bound S.subdivisionFamily S.subdivisionFamily_antitone
    (C00.ofArray a) (fun n => S.subdivisionFamily_upper n (C00.ofArray a))
  simpa only [C00.l1Mass_ofArray] using h

theorem averaged_definite (S : SpreadingModel Y) (x : C00) :
    S.averagedSeminorm x = 0 → x = 0 :=
  SeminormLimit.definite S.subdivisionFamily S.subdivisionFamily_antitone S.d_pos
    S.subdivisionFamily_prefix_lower x

theorem averaged_spreading (S : SpreadingModel Y) {m : ℕ}
    (ι : Fin m → ℕ) (hι : StrictMono ι) (a : Fin m → ℝ) :
    S.averagedSeminorm (C00.place ι a) = S.averagedSeminorm (C00.ofArray a) :=
  SeminormLimit.spreading S.subdivisionFamily S.subdivisionFamily_antitone
    (fun n => Subdivision.uniform_spreading S.p S.spreading (n + 1) (Nat.succ_pos n))
    ι hι a

theorem averaged_subdivide (S : SpreadingModel Y) (J : ℕ → ℕ)
    (hJ : ∀ i, 0 < J i) (x : C00) :
    S.averagedSeminorm (C00.subdivide J x) = S.averagedSeminorm x := by
  classical
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  subst x
  let K : ℕ := (∑ i : Fin m, J i.val) + 1
  have hK : 0 < K := Nat.succ_pos _
  have hJK (i : Fin m) : J i.val ≤ K := by
    have hle : J i.val ≤ ∑ j : Fin m, J j.val :=
      Finset.single_le_sum (f := fun j : Fin m => J j.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact hle.trans (Nat.le_succ _)
  have hlo (n : ℕ) : S.averagedSeminorm (C00.ofArray a) ≤
      S.p (C00.uniformSubdivision (n + 1) (C00.subdivide J (C00.ofArray a))) := by
    rw [C00.uniformSubdivision_subdivide (n + 1) (Nat.succ_pos n) J hJ]
    apply (S.averaged_le_uniform (C00.ofArray a) ((n + 1) * K)
      (Nat.mul_pos (Nat.succ_pos n) hK)).trans
    exact Subdivision.subdivide_le_ofArray S.p S.spreading a
      (fun i => (n + 1) * J i) (fun _ => (n + 1) * K)
      (fun i => Nat.mul_pos (Nat.succ_pos n) (hJ i.val))
      (fun i => Nat.mul_le_mul_left (n + 1) (hJK i))
  have hhi (n : ℕ) :
      S.p (C00.uniformSubdivision (n + 1) (C00.subdivide J (C00.ofArray a))) ≤
        S.p (C00.uniformSubdivision (n + 1) (C00.ofArray a)) := by
    rw [C00.uniformSubdivision_subdivide (n + 1) (Nat.succ_pos n) J hJ]
    apply Subdivision.subdivide_le_ofArray S.p S.spreading a
      (fun _ => n + 1) (fun i => (n + 1) * J i)
      (fun _ => Nat.succ_pos n)
    intro i
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (n + 1) (Nat.succ_le_of_lt (hJ i.val))
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto'
      (S.tendsto_averagedSeminorm (C00.subdivide J (C00.ofArray a)))
      (S.tendsto_averagedSeminorm (C00.ofArray a)) hhi
  · exact ge_of_tendsto'
      (S.tendsto_averagedSeminorm (C00.subdivide J (C00.ofArray a))) hlo

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionInvariantBlocks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

namespace Subdivision

theorem blockVector_eq_ofList {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) :
    blockVector left right J c =
      ofList (List.ofFn left ++ (List.replicate J (c / (J : ℝ)) ++ List.ofFn right)) := by
  rw [blockVector, ← ofList_ofFn]
  simp only [blockArray, List.ofFn_fin_append, List.ofFn_const]

theorem pieces_append (a b : List (ℝ × ℕ)) : pieces (a ++ b) = pieces a ++ pieces b := by
  simp only [pieces, List.flatMap_append]

theorem pieces_unit (a : List ℝ) : pieces (a.map fun c => (c, 1)) = a := by
  induction a with
  | nil => rfl
  | cons c a ih =>
      simp only [List.map_cons, pieces_cons, Nat.cast_one, div_one,
        List.replicate_one, List.singleton_append, ih]

end Subdivision

namespace SpreadingModel

open Subdivision

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_pieces (S : SpreadingModel Y) (blocks : List (ℝ × ℕ))
    (hpos : ∀ b ∈ blocks, 0 < b.2) :
    S.averagedSeminorm (ofList (pieces blocks)) =
      S.averagedSeminorm (ofList (blocks.map Prod.fst)) := by
  induction blocks using List.ofFnRec with
  | h m blocks =>
      let J : ℕ → ℕ := fun i => if h : i < m then (blocks ⟨i, h⟩).2 else 1
      have hJ (i : ℕ) : 0 < J i := by
        dsimp [J]
        split_ifs with hi
        · apply hpos
          exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩
        · exact Nat.one_pos
      have hJval (i : Fin m) : J i.val = (blocks i).2 := by
        simp only [J, dite_eq_left i.isLt]
      have h := S.averaged_subdivide J hJ (C00.ofArray fun i => (blocks i).1)
      rw [C00.subdivide_ofArray_eq_finiteSubdivision] at h
      simpa only [finiteSubdivision, hJval, List.map_ofFn, Function.comp_def,
        ofList_ofFn] using h

theorem averaged_block (S : SpreadingModel Y) (left right : List ℝ)
    (J : ℕ) (hJ : 0 < J) (c : ℝ) :
    S.averagedSeminorm (ofList (left ++ (List.replicate J (c / (J : ℝ)) ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([c] ++ right))) := by
  let blocks := (left.map fun a => (a, 1)) ++ (c, J) :: (right.map fun a => (a, 1))
  have hp : ∀ b ∈ blocks, 0 < b.2 := by
    intro b hb
    dsimp only [blocks] at hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      exact Nat.one_pos
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hJ
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
        exact Nat.one_pos
  have h := S.averaged_pieces blocks hp
  simpa only [blocks, pieces_append, pieces_unit, pieces_cons, List.map_append,
    List.map_cons, List.map_map, Function.comp_def, List.map_id, List.map_id',
    List.singleton_append] using h

theorem averaged_insert_zero (S : SpreadingModel Y) (left right : List ℝ) :
    S.averagedSeminorm (ofList (left ++ ([0] ++ right))) =
      S.averagedSeminorm (ofList (left ++ right)) := by
  induction left using List.ofFnRec with
  | h l left =>
      induction right using List.ofFnRec with
      | h r right =>
          have hs : sample left right 0 0 (0 : Fin 1) = blockVector left right 1 0 := by
            rw [sample_eq, blockVector_eq]
            simp
          have h := sample_norm S.averagedSeminorm S.averaged_spreading
            left right 0 0 (0 : Fin 1)
          rw [hs] at h
          simpa only [blockVector_eq_ofList, zero_div, List.replicate_one,
            List.replicate_zero, List.nil_append] using h

theorem averaged_split_positive_nats (S : SpreadingModel Y) (left right : List ℝ)
    {j k : ℕ} (hj : 0 < j) (hk : 0 < k) (s : ℝ) :
    S.averagedSeminorm
        (ofList (left ++ ([(j : ℝ) / ((j + k : ℕ) : ℝ) * s,
          (k : ℝ) / ((j + k : ℕ) : ℝ) * s] ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([s] ++ right))) := by
  let a : ℝ := (j : ℝ) / ((j + k : ℕ) : ℝ) * s
  let b : ℝ := (k : ℝ) / ((j + k : ℕ) : ℝ) * s
  have hjr : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have haj : a / (j : ℝ) = s / ((j + k : ℕ) : ℝ) := by
    dsimp [a]
    field_simp
  have hbk : b / (k : ℝ) = s / ((j + k : ℕ) : ℝ) := by
    dsimp [b]
    field_simp
  change S.averagedSeminorm (ofList (left ++ ([a, b] ++ right))) = _
  calc
    _ = S.averagedSeminorm
        (ofList (left ++ (List.replicate j (a / (j : ℝ)) ++ ([b] ++ right)))) := by
      exact (S.averaged_block left ([b] ++ right) j hj a).symm
    _ = S.averagedSeminorm
        (ofList (left ++ (List.replicate j (a / (j : ℝ)) ++
          (List.replicate k (b / (k : ℝ)) ++ right)))) := by
      simpa only [List.append_assoc] using
        (S.averaged_block (left ++ List.replicate j (a / (j : ℝ))) right k hk b).symm
    _ = S.averagedSeminorm
        (ofList (left ++ (List.replicate (j + k) (s / ((j + k : ℕ) : ℝ)) ++ right))) := by
      simp only [haj, hbk, List.replicate_add, List.append_assoc]
    _ = _ := S.averaged_block left right (j + k) (by omega) s

theorem averaged_split_natFraction (S : SpreadingModel Y) (left right : List ℝ)
    {n j : ℕ} (hn : 0 < n) (hjn : j ≤ n) (s : ℝ) :
    S.averagedSeminorm
        (ofList (left ++ ([(j : ℝ) / (n : ℝ) * s,
          (1 - (j : ℝ) / (n : ℝ)) * s] ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([s] ++ right))) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  by_cases hj0 : j = 0
  · subst j
    simpa using S.averaged_insert_zero left ([s] ++ right)
  by_cases hjn' : j = n
  · subst j
    simpa only [div_self hnr, one_mul, sub_self, zero_mul, List.append_assoc,
      List.cons_append, List.nil_append] using S.averaged_insert_zero (left ++ [s]) right
  have hj : 0 < j := Nat.pos_of_ne_zero hj0
  have hk : 0 < n - j := by omega
  have he : j + (n - j) = n := by omega
  have h := S.averaged_split_positive_nats left right hj hk s
  rw [he] at h
  have heq : ((n - j : ℕ) : ℝ) / (n : ℝ) * s =
      (1 - (j : ℝ) / (n : ℝ)) * s := by
    rw [Nat.cast_sub hjn]
    field_simp
  rwa [heq] at h

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionMergeConvex
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem convex_constant_Icc_min {f : ℝ → ℝ} {c : ℝ}
    (hf : ConvexOn ℝ Set.univ f)
    (hc : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = c) :
    ∀ t : ℝ, c ≤ f t := by
  have h0 : f 0 = c := hc 0 ⟨le_rfl, zero_le_one⟩
  have h1 : f 1 = c := hc 1 ⟨zero_le_one, le_rfl⟩
  intro t
  by_cases ht0 : t < 0
  · have h := hf.secant_mono_aux1 (x := t) (y := 0) (z := 1)
      (Set.mem_univ t) (Set.mem_univ 1) ht0 zero_lt_one
    rw [h0, h1] at h
    nlinarith only [h]
  · have h0t : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : t ≤ 1
    · exact (hc t ⟨h0t, ht1⟩).ge
    · have h1t : 1 < t := lt_of_not_ge ht1
      have h := hf.secant_mono_aux1 (x := 0) (y := 1) (z := t)
        (Set.mem_univ 0) (Set.mem_univ t) zero_lt_one h1t
      rw [h0, h1] at h
      nlinarith only [h]

namespace Subdivision

theorem ofList_singleton (a : ℝ) : ofList [a] = Finsupp.single 0 a := by
  simpa using ofList_replicate 1 a

theorem ofList_pair (a b : ℝ) :
    ofList [a, b] = Finsupp.single 0 a + Finsupp.single 1 b := by
  change ofList ([a] ++ [b]) = _
  rw [ofList_append, ofList_singleton, ofList_singleton]
  simp only [List.length_singleton, Finsupp.mapDomain_single, Nat.add_zero]

def pairBase (left right : List ℝ) : C00 :=
  ofList left + Finsupp.mapDomain (fun i => left.length + i)
    (Finsupp.mapDomain (fun i => 2 + i) (ofList right))

def singleBase (left right : List ℝ) : C00 :=
  ofList left + Finsupp.mapDomain (fun i => left.length + i)
    (Finsupp.mapDomain (fun i => 1 + i) (ofList right))

theorem pair_context_eq (left right : List ℝ) (a b : ℝ) :
    ofList (left ++ [a, b] ++ right) = pairBase left right +
      Finsupp.single left.length a + Finsupp.single (left.length + 1) b := by
  rw [List.append_assoc, ofList_append, ofList_append, ofList_pair]
  simp only [List.length_cons, List.length_nil, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, Nat.add_zero, pairBase]
  exact ((add_assoc (ofList left)
    (Finsupp.single left.length a + Finsupp.single (left.length + 1) b) _).symm.trans
      (add_right_comm _ _ _)).trans (add_assoc _ _ _).symm

theorem single_context_eq (left right : List ℝ) (a : ℝ) :
    ofList (left ++ [a] ++ right) = singleBase left right + Finsupp.single left.length a := by
  rw [List.append_assoc, ofList_append, ofList_append, ofList_singleton]
  simp only [List.length_singleton, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, Nat.add_zero, singleBase]
  exact (add_assoc (ofList left) (Finsupp.single left.length a) _).symm.trans
    (add_right_comm _ _ _)

theorem pair_context_affine (left right : List ℝ)
    (a b c d α β : ℝ) (hαβ : α + β = 1) :
    ofList (left ++ [α * a + β * c, α * b + β * d] ++ right) =
      α • ofList (left ++ [a, b] ++ right) + β • ofList (left ++ [c, d] ++ right) := by
  rw [pair_context_eq, pair_context_eq, pair_context_eq]
  calc
    pairBase left right + Finsupp.single left.length (α * a + β * c) +
        Finsupp.single (left.length + 1) (α * b + β * d) =
      (α + β) • pairBase left right + Finsupp.single left.length (α * a + β * c) +
        Finsupp.single (left.length + 1) (α * b + β * d) := by rw [hαβ, one_smul]
    _ = _ := by
      simp only [add_smul, smul_add, Finsupp.smul_single, smul_eq_mul, Finsupp.single_add]
      abel

theorem seminorm_single_le (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (k : ℕ) (c : ℝ) : p (Finsupp.single k c) ≤ |c| := by
  classical
  let a : Fin (k + 1) → ℝ := fun i => if i = Fin.last k then c else 0
  have ha : C00.ofArray a = Finsupp.single k c := by
    unfold C00.ofArray C00.place
    rw [Finset.sum_eq_single (Fin.last k)]
    · simp [a]
    · intro i _ hi
      simp [a, hi]
    · simp
  have h := hupper a
  rw [ha] at h
  simpa [a, abs_ite] using h

theorem pair_context_lipschitz (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (left right : List ℝ) (a b a' b' : ℝ) :
    |p (ofList (left ++ [a, b] ++ right)) - p (ofList (left ++ [a', b'] ++ right))| ≤
      |a - a'| + |b - b'| := by
  have hsub : ofList (left ++ [a, b] ++ right) - ofList (left ++ [a', b'] ++ right) =
      Finsupp.single left.length (a - a') + Finsupp.single (left.length + 1) (b - b') := by
    rw [pair_context_eq, pair_context_eq, Finsupp.single_sub, Finsupp.single_sub]
    abel
  calc
    |p (ofList (left ++ [a, b] ++ right)) - p (ofList (left ++ [a', b'] ++ right))|
        ≤ p (ofList (left ++ [a, b] ++ right) - ofList (left ++ [a', b'] ++ right)) :=
      abs_sub_map_le_sub p _ _
    _ = p (Finsupp.single left.length (a - a') +
        Finsupp.single (left.length + 1) (b - b')) := by rw [hsub]
    _ ≤ p (Finsupp.single left.length (a - a')) +
        p (Finsupp.single (left.length + 1) (b - b')) := map_add_le_add p _ _
    _ ≤ |a - a'| + |b - b'| := add_le_add
      (seminorm_single_le p hupper _ _) (seminorm_single_le p hupper _ _)

theorem single_context_lipschitz (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (left right : List ℝ) (a a' : ℝ) :
    |p (ofList (left ++ [a] ++ right)) - p (ofList (left ++ [a'] ++ right))| ≤ |a - a'| := by
  have hsub : ofList (left ++ [a] ++ right) - ofList (left ++ [a'] ++ right) =
      Finsupp.single left.length (a - a') := by
    rw [single_context_eq, single_context_eq, Finsupp.single_sub]
    abel
  calc
    |p (ofList (left ++ [a] ++ right)) - p (ofList (left ++ [a'] ++ right))|
        ≤ p (ofList (left ++ [a] ++ right) - ofList (left ++ [a'] ++ right)) :=
      abs_sub_map_le_sub p _ _
    _ = p (Finsupp.single left.length (a - a')) := by rw [hsub]
    _ ≤ |a - a'| := seminorm_single_le p hupper _ _

theorem merge_context_le_of_ne_zero (p : Seminorm ℝ C00)
    (left right : List ℝ)
    (hsame : ∀ s θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      p (ofList (left ++ [θ * s, (1 - θ) * s] ++ right)) =
        p (ofList (left ++ [s] ++ right)))
    (a b : ℝ) (hs : a + b ≠ 0) :
    p (ofList (left ++ [a + b] ++ right)) ≤ p (ofList (left ++ [a, b] ++ right)) := by
  let s := a + b
  let f : ℝ → ℝ := fun t => p (ofList (left ++ [t * s, (1 - t) * s] ++ right))
  have hf : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hαβ
    have heq : ofList (left ++ [(α * x + β * y) * s, (1 - (α * x + β * y)) * s] ++ right) =
        α • ofList (left ++ [x * s, (1 - x) * s] ++ right) +
          β • ofList (left ++ [y * s, (1 - y) * s] ++ right) := by
      have hsecond : (1 - (α * x + β * y)) * s = α * ((1 - x) * s) + β * ((1 - y) * s) := by
        calc
          (1 - (α * x + β * y)) * s = ((α + β) - (α * x + β * y)) * s := by rw [hαβ]
          _ = _ := by ring
      rw [show (α * x + β * y) * s = α * (x * s) + β * (y * s) by ring, hsecond]
      exact pair_context_affine left right _ _ _ _ α β hαβ
    change p (ofList (left ++ [(α * x + β * y) * s, (1 - (α * x + β * y)) * s] ++ right)) ≤ _
    rw [heq]
    exact p.convexOn.2 (Set.mem_univ _) (Set.mem_univ _) hα hβ hαβ
  have hmin := convex_constant_Icc_min hf
    (fun t ht => hsame s t ht.1 ht.2) (a / s)
  have hs' : s ≠ 0 := hs
  have hfirst : a / s * s = a := div_mul_cancel₀ a hs'
  have hsecond : (1 - a / s) * s = b := by
    rw [sub_mul, one_mul, hfirst]
    dsimp only [s]
    ring
  simpa only [f, hfirst, hsecond, s] using hmin

theorem merge_context_le (p : Seminorm ℝ C00)
    (hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|)
    (left right : List ℝ)
    (hsame : ∀ s θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      p (ofList (left ++ [θ * s, (1 - θ) * s] ++ right)) =
        p (ofList (left ++ [s] ++ right)))
    (a b : ℝ) :
    p (ofList (left ++ [a + b] ++ right)) ≤ p (ofList (left ++ [a, b] ++ right)) := by
  by_cases hs : a + b = 0
  · rw [hs]
    by_contra hbad
    have hgap : p (ofList (left ++ [a, b] ++ right)) < p (ofList (left ++ [0] ++ right)) :=
      lt_of_not_ge hbad
    let δ := (p (ofList (left ++ [0] ++ right)) - p (ofList (left ++ [a, b] ++ right))) / 4
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    have hsum : a + δ + b = δ := by linarith only [hs]
    have hnonzero : a + δ + b ≠ 0 := by rw [hsum]; exact ne_of_gt hδ
    have hmerge := merge_context_le_of_ne_zero p left right hsame (a + δ) b hnonzero
    rw [hsum] at hmerge
    have hsingle := single_context_lipschitz p hupper left right 0 δ
    have hpair := pair_context_lipschitz p hupper left right (a + δ) b a b
    have hsingle' : |p (ofList (left ++ [0] ++ right)) - p (ofList (left ++ [δ] ++ right))| ≤ δ := by
      simpa only [zero_sub, abs_neg, abs_of_pos hδ] using hsingle
    have hpair' : |p (ofList (left ++ [a + δ, b] ++ right)) - p (ofList (left ++ [a, b] ++ right))| ≤ δ := by
      simpa only [add_sub_cancel_left, sub_self, abs_zero, add_zero, abs_of_pos hδ] using hpair
    have h1 := (abs_le.mp hsingle').2
    have h2 := (abs_le.mp hpair').2
    dsimp only [δ] at hδ hmerge h1 h2
    linarith
  · exact merge_context_le_of_ne_zero p left right hsame a b hs

end Subdivision

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionMergeCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

theorem singleton_vector (a : ℝ) : ofList [a] = Finsupp.single 0 a := by
  simpa using ofList_replicate 1 a

theorem pair_vector (a b : ℝ) :
    ofList [a, b] = Finsupp.single 0 a + Finsupp.single 1 b := by
  change ofList ([a] ++ [b]) = _
  rw [ofList_append, singleton_vector, singleton_vector]
  simp only [List.length_singleton, Finsupp.mapDomain_single, Nat.add_zero]

theorem pair_context_vector (left right : List ℝ) (a b : ℝ) :
    ofList (left ++ ([a, b] ++ right)) =
      ofList left + Finsupp.single left.length a + Finsupp.single (left.length + 1) b +
        Finsupp.mapDomain (fun k => left.length + 2 + k) (ofList right) := by
  rw [ofList_append, ofList_append, pair_vector]
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    ← Finsupp.mapDomain_comp, Function.comp_def, List.length_cons, List.length_nil,
    Nat.add_zero, Nat.add_assoc]
  have hshift (k : ℕ) : 0 + (1 + (1 + k)) = 2 + k := by omega
  simp only [hshift, add_assoc]

theorem single_context_vector (left right : List ℝ) (a : ℝ) :
    ofList (left ++ ([a] ++ right)) =
      ofList left + Finsupp.single left.length a +
        Finsupp.mapDomain (fun k => left.length + 1 + k) (ofList right) := by
  rw [ofList_append, ofList_append, singleton_vector]
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    ← Finsupp.mapDomain_comp, Function.comp_def, List.length_singleton,
    Nat.add_zero, Nat.add_assoc]
  abel

theorem merge_left_context (left : List ℝ) :
    Finsupp.mapDomain (C00.mergeIndex left.length) (ofList left) = ofList left := by
  classical
  induction left using List.ofFnRec with
  | h m left =>
      simp only [List.length_ofFn, ofList_ofFn, C00.ofArray, C00.place,
        Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
      apply Finset.sum_congr rfl
      intro i _
      simp only [C00.mergeIndex, ite_eq_left (Nat.le_of_lt i.isLt)]

theorem mergeAt_context (left right : List ℝ) (a b : ℝ) :
    C00.mergeAt left.length (ofList (left ++ ([a, b] ++ right))) =
      ofList (left ++ ([a + b] ++ right)) := by
  classical
  rw [C00.mergeAt, pair_context_vector]
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  rw [merge_left_context]
  have h0 : C00.mergeIndex left.length left.length = left.length := by
    simp only [C00.mergeIndex, le_refl, ite_true]
  have h1 : C00.mergeIndex left.length (left.length + 1) = left.length := by
    simp only [C00.mergeIndex]
    rw [ite_eq_right (by omega)]
    omega
  have hr :
      Finsupp.mapDomain (C00.mergeIndex left.length)
        (Finsupp.mapDomain (fun k => left.length + 2 + k) (ofList right)) =
      Finsupp.mapDomain (fun k => left.length + 1 + k) (ofList right) := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext k
    simp only [Function.comp_def, C00.mergeIndex]
    rw [ite_eq_right (by omega)]
    omega
  rw [h0, h1, hr, single_context_vector, Finsupp.single_add]
  abel

theorem exists_context (x : C00) (i : ℕ) :
    ∃ left right : List ℝ, ∃ a b : ℝ,
      left.length = i ∧ ofList (left ++ ([a, b] ++ right)) = x := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  let B : ℕ := max m (i + 2)
  let L : List ℝ := List.ofFn fun j : Fin B => x j.val
  have hL : ofList L = x := by
    rw [ofList_ofFn]
    apply C00.ofArray_of_vanishes
    intro k hk
    rw [← ha]
    exact C00.ofArray_apply_of_ge a k ((le_max_left _ _).trans hk)
  have hi : i < L.length := by
    simp only [L, List.length_ofFn]
    have h := le_max_right m (i + 2)
    omega
  have hi1 : i + 1 < L.length := by
    simp only [L, List.length_ofFn]
    have h := le_max_right m (i + 2)
    omega
  have hdrop : L.drop i = L[i] :: L[i + 1] :: L.drop (i + 2) := by
    rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hi1]
  have hdec : L.take i ++ ([L[i], L[i + 1]] ++ L.drop (i + 2)) = L := by
    change L.take i ++ (L[i] :: L[i + 1] :: L.drop (i + 2)) = L
    rw [← hdrop]
    exact List.take_append_drop i L
  refine ⟨L.take i, L.drop (i + 2), L[i], L[i + 1], ?_, ?_⟩
  · simp only [List.length_take, min_eq_left hi.le]
  · rw [hdec]
    exact hL

end MarkovSuperreflexivity.Subdivision

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionNearIsometry
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal

namespace MarkovSuperreflexivity

namespace C00

def uniformArrayMap (q m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin (q * m) → ℝ) where
  toFun a i := uniformSubdivision q (ofArray a) i.val
  map_add' a b := by
    funext i
    change ((uniformSubdivision q).comp (arrayLinear m)) (a + b) i.val = _
    rw [map_add]
    rfl
  map_smul' c a := by
    funext i
    change ((uniformSubdivision q).comp (arrayLinear m)) (c • a) i.val = _
    rw [map_smul]
    rfl

end C00

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionSameSign
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

theorem exists_natFraction_close {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hε : 0 < ε) :
    ∃ n j : ℕ, 0 < n ∧ j ≤ n ∧ |θ - (j : ℝ) / (n : ℝ)| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℝ) / ε)
  have hnr : 0 < (n : ℝ) := (one_div_pos.mpr hε).trans hn
  have hn0 : 0 < n := by exact_mod_cast hnr
  let j : ℕ := ⌊(n : ℝ) * θ⌋₊
  have hjn : j ≤ n := by
    apply Nat.floor_le_of_le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hθ1 hnr.le
  have hjlo : (j : ℝ) ≤ (n : ℝ) * θ :=
    Nat.floor_le (mul_nonneg hnr.le hθ0)
  have hjhi : (n : ℝ) * θ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : (j : ℝ) / (n : ℝ) ≤ θ := by
    apply (div_le_iff₀ hnr).mpr
    simpa only [mul_comm] using hjlo
  have hgap : θ - (j : ℝ) / (n : ℝ) < 1 / (n : ℝ) := by
    apply (lt_div_iff₀ hnr).mpr
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hnr)]
    linarith
  have he : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnr).mpr
    have h := (div_lt_iff₀ hε).mp hn
    simpa only [mul_comm] using h
  exact ⟨n, j, hn0, hjn, by
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact hgap.trans he⟩

end MarkovSuperreflexivity.Subdivision

namespace MarkovSuperreflexivity.SpreadingModel

open Subdivision

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_sameSign_split (S : SpreadingModel Y) (left right : List ℝ)
    (s θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    S.averagedSeminorm (ofList (left ++ ([θ * s, (1 - θ) * s] ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([s] ++ right))) := by
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      |S.averagedSeminorm (ofList (left ++ ([θ * s, (1 - θ) * s] ++ right))) -
        S.averagedSeminorm (ofList (left ++ ([s] ++ right)))| < ε := by
    let δ : ℝ := ε / (2 * |s| + 1)
    have hden : 0 < 2 * |s| + 1 := by positivity
    have hδ : 0 < δ := div_pos hε hden
    obtain ⟨n, j, hn, hjn, hclose⟩ := exists_natFraction_close hθ0 hθ1 hδ
    let q : ℝ := (j : ℝ) / (n : ℝ)
    have hrat := S.averaged_split_natFraction left right hn hjn s
    have hlip := pair_context_lipschitz S.averagedSeminorm S.averaged_array_upper
      left right (θ * s) ((1 - θ) * s) (q * s) ((1 - q) * s)
    simp only [List.append_assoc] at hlip
    change S.averagedSeminorm (ofList (left ++ ([q * s, (1 - q) * s] ++ right))) = _
      at hrat
    rw [hrat] at hlip
    have he : |θ * s - q * s| + |(1 - θ) * s - (1 - q) * s| =
        2 * |θ - q| * |s| := by
      have h1 : θ * s - q * s = (θ - q) * s := by ring
      have h2 : (1 - θ) * s - (1 - q) * s = -((θ - q) * s) := by ring
      rw [h1, h2, abs_neg, abs_mul]
      ring
    rw [he] at hlip
    have hδε : δ * (2 * |s| + 1) = ε :=
      div_mul_cancel₀ ε (ne_of_gt hden)
    have heps : 2 * δ * |s| < ε := by nlinarith
    have hbound : 2 * |θ - q| * |s| ≤ 2 * δ * |s| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hclose.le (by norm_num)) (abs_nonneg s)
    exact hlip.trans_lt (hbound.trans_lt heps)
  by_contra hne
  have hpos : 0 <
      |S.averagedSeminorm (ofList (left ++ ([θ * s, (1 - θ) * s] ++ right))) -
        S.averagedSeminorm (ofList (left ++ ([s] ++ right)))| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  exact (lt_irrefl _) (hsmall _ hpos)

theorem averaged_merge_context (S : SpreadingModel Y) (left right : List ℝ)
    (a b : ℝ) :
    S.averagedSeminorm (ofList (left ++ ([a + b] ++ right))) ≤
      S.averagedSeminorm (ofList (left ++ ([a, b] ++ right))) := by
  simpa only [List.append_assoc] using
    merge_context_le S.averagedSeminorm S.averaged_array_upper left right
      (fun s θ h0 h1 => by
        simpa only [List.append_assoc] using S.averaged_sameSign_split left right s θ h0 h1)
      a b

end MarkovSuperreflexivity.SpreadingModel

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SubdivisionOrderedNorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_mergeAt (S : SpreadingModel Y) (i : ℕ) (x : C00) :
    S.averagedSeminorm (C00.mergeAt i x) ≤ S.averagedSeminorm x := by
  obtain ⟨left, right, a, b, hi, hx⟩ := Subdivision.exists_context x i
  calc
    S.averagedSeminorm (C00.mergeAt i x) =
        S.averagedSeminorm
          (C00.mergeAt left.length (Subdivision.ofList (left ++ ([a, b] ++ right)))) := by
      rw [hi, hx]
    _ = S.averagedSeminorm (Subdivision.ofList (left ++ ([a + b] ++ right))) := by
      rw [Subdivision.mergeAt_context]
    _ ≤ S.averagedSeminorm (Subdivision.ofList (left ++ ([a, b] ++ right))) :=
      S.averaged_merge_context left right a b
    _ = S.averagedSeminorm x := congrArg S.averagedSeminorm hx

def orderedNorm (S : SpreadingModel Y) : OrderedNorm where
  toSeminorm := S.averagedSeminorm
  definite := S.averaged_definite
  spreading := S.averaged_spreading
  merge_le := S.averaged_mergeAt

@[simp] theorem orderedNorm_apply (S : SpreadingModel Y) (x : C00) :
    S.orderedNorm x = S.averagedSeminorm x := rfl

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularLimitSeminorm
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.OrderedNorm.instCoeFunForallC00Real _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

def vectorAt (s : ∀ n : ℕ, TriangularSystem X n θ) (n i : ℕ) : X :=
  if hi : i < n then (s n).vectors ⟨i, hi⟩ else 0

theorem vectorAt_bound (s : ∀ n : ℕ, TriangularSystem X n θ) (n i : ℕ) :
    ‖vectorAt s n i‖ ≤ 1 := by
  classical
  by_cases hi : i < n
  · simpa only [vectorAt, dite_eq_left hi] using (s n).vectors_bound ⟨i, hi⟩
  · simp [vectorAt, hi]

def realize (s : ∀ n : ℕ, TriangularSystem X n θ) (n : ℕ) : C00 →ₗ[ℝ] X :=
  Finsupp.linearCombination ℝ (vectorAt s n)

def finiteSeminorm (s : ∀ n : ℕ, TriangularSystem X n θ) (n : ℕ) : Seminorm ℝ C00 :=
  (normSeminorm ℝ X).comp (realize s n)

@[simp] theorem finiteSeminorm_apply (s : ∀ n : ℕ, TriangularSystem X n θ)
    (n : ℕ) (a : C00) : finiteSeminorm s n a = ‖realize s n a‖ := rfl

theorem finiteSeminorm_le (s : ∀ n : ℕ, TriangularSystem X n θ) (n : ℕ) (a : C00) :
    finiteSeminorm s n a ≤ ∑ i ∈ a.support, |a i| := by
  classical
  change ‖∑ i ∈ a.support, a i • vectorAt s n i‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (vectorAt_bound s n i) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem bounded (s : ∀ n : ℕ, TriangularSystem X n θ) (a : C00) :
    RealSeqBounded (fun n => finiteSeminorm s n a) := by
  refine ⟨∑ i ∈ a.support, |a i|, fun n => ?_⟩
  rw [abs_of_nonneg (apply_nonneg (finiteSeminorm s n) a)]
  exact finiteSeminorm_le s n a

def limitNorm (s : ∀ n : ℕ, TriangularSystem X n θ) : Seminorm ℝ C00 :=
  seminormULim freeUltrafilter (finiteSeminorm s) (bounded s)

@[simp] theorem limitNorm_apply (s : ∀ n : ℕ, TriangularSystem X n θ) (a : C00) :
    limitNorm s a = realULim freeUltrafilter (fun n => finiteSeminorm s n a) := rfl

def tailForm (θ : ℝ) (j : ℕ) : C00 →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun i => if j ≤ i then θ else 0)

@[simp] theorem tailForm_single (j i : ℕ) (b : ℝ) :
    tailForm θ j (Finsupp.single i b) = b * (if j ≤ i then θ else 0) := by
  simp only [tailForm, Finsupp.linearCombination_single, smul_eq_mul]

theorem finite_pairing (s : ∀ n : ℕ, TriangularSystem X n θ)
    (a : C00) {n j : ℕ} (hj : j < n) (ha : ∀ i ∈ a.support, i < n) :
    (s n).functionals ⟨j, hj⟩ (realize s n a) = tailForm θ j a := by
  classical
  change (s n).functionals ⟨j, hj⟩ (∑ i ∈ a.support, a i • vectorAt s n i) =
    ∑ i ∈ a.support, a i • (if j ≤ i then θ else 0)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  congr 1
  rw [vectorAt, dite_eq_left (ha i hi), (s n).pairing]
  rfl

theorem tailForm_le_finite (s : ∀ n : ℕ, TriangularSystem X n θ)
    (a : C00) {n j : ℕ} (hj : j < n) (ha : ∀ i ∈ a.support, i < n) :
    |tailForm θ j a| ≤ finiteSeminorm s n a := by
  rw [← finite_pairing s a hj ha, ← Real.norm_eq_abs]
  calc
    ‖(s n).functionals ⟨j, hj⟩ (realize s n a)‖ ≤
        ‖(s n).functionals ⟨j, hj⟩‖ * ‖realize s n a‖ :=
      ((s n).functionals ⟨j, hj⟩).le_opNorm _
    _ ≤ 1 * ‖realize s n a‖ :=
      mul_le_mul_of_nonneg_right ((s n).functionals_bound _) (norm_nonneg _)
    _ = finiteSeminorm s n a := one_mul _

theorem tailForm_le (s : ∀ n : ℕ, TriangularSystem X n θ) (a : C00) (j : ℕ) :
    |tailForm θ j a| ≤ limitNorm s a := by
  apply le_realULim_of_eventually_le freeUltrafilter (bounded s a)
  apply freeUltrafilter_le_atTop
  filter_upwards [eventually_ge_atTop (max j (a.support.sup id) + 1)] with n hn
  apply tailForm_le_finite s a (by omega)
  intro i hi
  have his : i ≤ a.support.sup id := Finset.le_sup (f := id) hi
  omega

theorem tailForm_sub (a : C00) (j : ℕ) :
    tailForm θ j a - tailForm θ (j + 1) a = θ * a j := by
  classical
  have h : tailForm θ j - tailForm θ (j + 1) =
      θ • (Finsupp.lapply j : C00 →ₗ[ℝ] ℝ) := by
    apply Finsupp.lhom_ext
    intro i b
    by_cases hij : i = j
    · subst i
      simp [tailForm_single, mul_comm]
    · by_cases hji : j ≤ i
      · have hnext : j + 1 ≤ i := by omega
        simp [tailForm_single, hji, hnext, Ne.symm hij]
      · have hnext : ¬j + 1 ≤ i := by omega
        simp [tailForm_single, hji, hnext, Ne.symm hij]
  exact congrArg (fun T : C00 →ₗ[ℝ] ℝ => T a) h

theorem coordinate_bound (s : ∀ n : ℕ, TriangularSystem X n θ)
    (a : C00) (j : ℕ) : |θ * a j| ≤ 2 * limitNorm s a := by
  rw [← tailForm_sub a j]
  calc
    |tailForm θ j a - tailForm θ (j + 1) a| ≤
        |tailForm θ j a| + |tailForm θ (j + 1) a| := abs_sub _ _
    _ ≤ limitNorm s a + limitNorm s a := add_le_add (tailForm_le s a j)
      (tailForm_le s a (j + 1))
    _ = 2 * limitNorm s a := by ring

theorem definite (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    ∀ a : C00, limitNorm s a = 0 → a = 0 := by
  intro a ha
  ext j
  have hz : |θ * a j| = 0 := le_antisymm (by simpa [ha] using coordinate_bound s a j)
    (abs_nonneg _)
  have hp : θ * a j = 0 := abs_eq_zero.mp hz
  exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt hθ)

@[simp] theorem tailForm_basis (j i : ℕ) :
    tailForm θ j (C00.basis i) = if j ≤ i then θ else 0 := by
  simp only [C00.basis, tailForm_single, one_mul]

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularCompletion
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

abbrev PreSpace (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :=
  NormedC00 (limitNorm s) (definite s hθ)

abbrev Space (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :=
  UniformSpace.Completion (PreSpace s hθ)

def ofC00 (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    C00 →ₗ[ℝ] Space s hθ :=
  (UniformSpace.Completion.toComplₗᵢ : PreSpace s hθ →ₗᵢ[ℝ] Space s hθ).toLinearMap.comp
    (NormedC00.coefficients (limitNorm s) (definite s hθ)).symm.toLinearMap

@[simp] theorem norm_ofC00 (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (a : C00) : ‖ofC00 s hθ a‖ = limitNorm s a := by
  change ‖((NormedC00.coefficients (limitNorm s) (definite s hθ)).symm a :
    UniformSpace.Completion (PreSpace s hθ))‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

def basis (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (i : ℕ) : Space s hθ :=
  ofC00 s hθ (C00.basis i)

def preTail (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (j : ℕ) :
    StrongDual ℝ (PreSpace s hθ) :=
  ((tailForm θ j).comp
    (NormedC00.coefficients (limitNorm s) (definite s hθ)).toLinearMap).mkContinuous 1
      (by
        intro a
        change |tailForm θ j a| ≤ 1 * limitNorm s a
        simpa only [one_mul] using tailForm_le s a j)

def tail (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) (j : ℕ) :
    StrongDual ℝ (Space s hθ) :=
  (preTail s hθ j).extend
    (UniformSpace.Completion.toComplL : PreSpace s hθ →L[ℝ] Space s hθ)

@[simp] theorem tail_ofC00 (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (j : ℕ) (a : C00) : tail s hθ j (ofC00 s hθ a) = tailForm θ j a := by
  change (preTail s hθ j).extend _
    ((UniformSpace.Completion.toComplL : PreSpace s hθ →L[ℝ] Space s hθ)
      ((NormedC00.coefficients (limitNorm s) (definite s hθ)).symm a)) = _
  rw [ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _)]
  rfl

@[simp] theorem pairing (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (i j : ℕ) : tail s hθ j (basis s hθ i) = if j ≤ i then θ else 0 := by
  rw [basis, tail_ofC00, tailForm_basis]

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

namespace TriangularSystem

variable {n : ℕ} {θ η : ℝ}

def mapEquivOfBounds (s : TriangularSystem X n θ)
    (e : X ≃L[ℝ] Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x, a * ‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x, ‖e x‖ ≤ b * ‖x‖) :
    TriangularSystem Y n ((a / b) * θ) where
  vectors i := b⁻¹ • e (s.vectors i)
  functionals j := a • ((s.functionals j).comp e.symm.toContinuousLinearMap)
  vectors_bound i := by
    calc
      ‖b⁻¹ • e (s.vectors i)‖ = b⁻¹ * ‖e (s.vectors i)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
      _ ≤ b⁻¹ * (b * ‖s.vectors i‖) :=
        mul_le_mul_of_nonneg_left (hupper _) (inv_nonneg.mpr hb.le)
      _ = ‖s.vectors i‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hb), one_mul]
      _ ≤ 1 := s.vectors_bound i
  functionals_bound j := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    rw [one_mul]
    change ‖a • s.functionals j (e.symm y)‖ ≤ ‖y‖
    calc
      ‖a • s.functionals j (e.symm y)‖ = a * ‖s.functionals j (e.symm y)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * (‖s.functionals j‖ * ‖e.symm y‖) :=
        mul_le_mul_of_nonneg_left ((s.functionals j).le_opNorm _) ha.le
      _ ≤ a * (1 * ‖e.symm y‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (s.functionals_bound j) (norm_nonneg _)) ha.le
      _ = a * ‖e.symm y‖ := by rw [one_mul]
      _ ≤ ‖y‖ := by simpa only [e.apply_symm_apply] using hlower (e.symm y)
  pairing i j := by
    change a • s.functionals j (e.symm (b⁻¹ • e (s.vectors i))) = _
    rw [e.symm.map_smul, e.symm_apply_apply, (s.functionals j).map_smul, s.pairing]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, smul_eq_mul, div_eq_mul_inv, mul_assoc]
    · simp only [ite_eq_right hji, smul_zero]

def toDual (s : TriangularSystem X n θ) :
    TriangularSystem (StrongDual ℝ X) n θ where
  vectors i := s.functionals i.rev
  functionals j := NormedSpace.inclusionInDoubleDual ℝ X (s.vectors j.rev)
  vectors_bound i := s.functionals_bound i.rev
  functionals_bound j :=
    (NormedSpace.double_dual_bound ℝ X (s.vectors j.rev)).trans (s.vectors_bound j.rev)
  pairing i j := by
    change s.functionals i.rev (s.vectors j.rev) = if j ≤ i then θ else 0
    simpa only [Fin.rev_le_rev] using s.pairing j.rev i.rev

def ofDual (s : TriangularSystem (StrongDual ℝ X) n θ)
    {ε : ℝ} (hε : 0 < ε) : TriangularSystem X n (θ / (1 + ε)) := by
  classical
  have hmatch (j : Fin n) :
      ∃ x : X, ‖x‖ ≤ 1 + ε ∧ ∀ i, s.vectors i x = s.functionals j (s.vectors i) :=
    finite_matching_unit (s.functionals j) (s.functionals_bound j) s.vectors hε
  let x : Fin n → X := fun j => Classical.choose (hmatch j)
  have hx (j : Fin n) : ‖x j‖ ≤ 1 + ε := (Classical.choose_spec (hmatch j)).1
  have hpair (j i : Fin n) :
      s.vectors i (x j) = s.functionals j (s.vectors i) :=
    (Classical.choose_spec (hmatch j)).2 i
  have hc : 0 < 1 + ε := by linarith
  refine
    { vectors := fun i => (1 + ε)⁻¹ • x i.rev
      functionals := fun j => s.vectors j.rev
      vectors_bound := ?_
      functionals_bound := fun j => s.vectors_bound j.rev
      pairing := ?_ }
  · intro i
    calc
      ‖(1 + ε)⁻¹ • x i.rev‖ = (1 + ε)⁻¹ * ‖x i.rev‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      _ ≤ (1 + ε)⁻¹ * (1 + ε) :=
        mul_le_mul_of_nonneg_left (hx _) (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hc)
  · intro i j

    rw [(s.vectors j.rev).map_smul, hpair, s.pairing]
    simp only [Fin.rev_le_rev]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, smul_eq_mul, div_eq_mul_inv, mul_comm]
    · simp only [ite_eq_right hji, smul_zero]

end TriangularSystem

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkLandmarks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

abbrev WalkBoundedWord (n : ℕ) := Σ k : Fin (n + 1), Fin k.val → Letter

def WalkBoundedWord.toList {n : ℕ} (w : WalkBoundedWord n) : List Letter :=
  List.ofFn w.2

@[simp] theorem WalkBoundedWord.length_toList {n : ℕ} (w : WalkBoundedWord n) :
    w.toList.length = w.1.val := by
  simp [WalkBoundedWord.toList]

def WalkBoundedWord.ofList {n : ℕ} (w : List Letter) (hw : w.length ≤ n) :
    WalkBoundedWord n :=
  ⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩

@[simp] theorem WalkBoundedWord.toList_ofList {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) : (WalkBoundedWord.ofList w hw).toList = w := by
  exact List.ofFn_get w

noncomputable def walkLandmarkShifts (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(2 * (n : ℤ))) ((walkWindowLength n : ℤ) + 2 * (n : ℤ))

noncomputable def walkEndpointValue (n : ℕ)
    (p : Letter × (Fin (walkWindowLength n) × Bool)) : ℝ :=
  if p.2.2 then alpha p.1 + (p.2.1.val : ℝ)
  else beta p.1 + (p.2.1.val : ℝ)

noncomputable def walkEndpoints (n : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (walkEndpointValue n)

noncomputable def walkOrbitPoints (n : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.biUnion fun w : WalkBoundedWord n =>
    (walkLandmarkShifts n).image fun j : ℤ => wordMap w.toList 0 + (j : ℝ)

noncomputable def walkLandmarks (n : ℕ) : Finset ℝ := by
  classical
  exact walkEndpoints n ∪ walkOrbitPoints n

theorem alpha_shift_mem_walkLandmarks (n : ℕ) (s : Letter)
    (j : Fin (walkWindowLength n)) :
    alpha s + (j.val : ℝ) ∈ walkLandmarks n := by
  classical
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨(s, (j, true)), Finset.mem_univ _, ?_⟩
  simp [walkEndpointValue]

theorem beta_shift_mem_walkLandmarks (n : ℕ) (s : Letter)
    (j : Fin (walkWindowLength n)) :
    beta s + (j.val : ℝ) ∈ walkLandmarks n := by
  classical
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨(s, (j, false)), Finset.mem_univ _, ?_⟩
  simp [walkEndpointValue]

theorem orbit_shift_mem_walkLandmarks {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) (j : ℤ)
    (hjlo : -(2 * (n : ℤ)) ≤ j)
    (hjhi : j ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ)) :
    wordMap w 0 + (j : ℝ) ∈ walkLandmarks n := by
  classical
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨WalkBoundedWord.ofList w hw, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_Icc.mpr ⟨hjlo, hjhi⟩, ?_⟩
  simp only [WalkBoundedWord.toList_ofList]

theorem integer_mem_walkLandmarks {n : ℕ} (j : ℤ)
    (hjlo : -(2 * (n : ℤ)) ≤ j)
    (hjhi : j ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ)) :
    (j : ℝ) ∈ walkLandmarks n := by
  have h := orbit_shift_mem_walkLandmarks ([] : List Letter)
    (Nat.zero_le n) j hjlo hjhi
  simpa only [wordMap, OrderIso.refl_apply, zero_add] using h

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

def chartCut {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B) (x : ↥Λ) : ℕ :=
  (C x).val + 1

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkMarkedDisplacement
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

open FiniteWalkDrift

def chartPathFromArray {n B k : ℕ} (v : Fin k → Letter)
    (C : Fin (k + 1) → Chart (walkLandmarks n) B)
    (i : Fin ((List.ofFn v).length + 1)) : Chart (walkLandmarks n) B :=
  C ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

end MarkovSuperreflexivity

end

end OAI
end


