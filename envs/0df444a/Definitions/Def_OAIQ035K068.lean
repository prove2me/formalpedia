-- Prove2me | Definitions.Def_OAIQ035K068
-- name    : OAIQ035K068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:21:08.803662+00:00
-- url     : https://prove2.me/theorems/a9b07fdd-e9fd-4e93-92e7-3bfb9e38889a
-- title:
--   Definitions bundle OAIQ035K068 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 11 definitions and 25 theorems. The definitions and types are `OAI.MetricKMedian.Reduction.Enumeration.branches`, `OAI.MetricKMedian.Reduction.Enumeration.choices`, `OAI.MetricKMedian.Reduction.Program.branchList`, `OAI.MetricKMedian.Reduction.Program.completions`, `OAI.MetricKMedian.Reduction.Program.costData`, `OAI.MetricKMedian.Reduction.Program.diff`, `OAI.MetricKMedian.Reduction.Program.endpoints`, `OAI.MetricKMedian.Reduction.Program.nearestData`, `OAI.MetricKMedian.Reduction.Program.outcomes`, `OAI.MetricKMedian.Reduction.Program.union`, `OAI.MetricKMedian.Reduction.Program.values`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_RestrictionProgram`, `KMedian_Reduction_DeletionProgram`, `KMedian_Reduction_ReductionCostProgram`, `KMedian_Reduction_ReductionOutcomesProgram`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseBernoulliSupport`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparseOuterReal`, `KMedian_Sparse_SparseSignedFixed`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseSignedRounding`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K061`, `OAIQ035K062` and `OAIQ035K064` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K071` and `OAIQ035K072`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K061
import Definitions.Def_OAIQ035K062
import Definitions.Def_OAIQ035K064

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BoundedEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
@[fun_prop] theorem words_poly {α : Type} [Coding α] [Inhabited α] (c : ℕ) : Poly (@words α c) := by
  induction c with
  | zero => exact const [[]]
  | succ c ih =>
    change Poly (fun xs : List α => []::xs.flatMap (fun a => (words c xs).map (List.cons a)))
    have h : Poly (fun xs : List α => xs.flatMap (fun a => (words c xs).map (List.cons a))) := by
      apply list_flatMap
      · apply list_map
        · exact comp list_cons (pair (comp snd fst) snd)
        · exact comp ih fst
      · fun_prop
    have hh := comp (list_cons (α := List α)) (pair (const ([] : List α) : Poly (fun _ : List α => ([] : List α))) h)
    exact hh

 theorem words_map {α β : Type} (f : α → β) (c : ℕ) (xs : List α) :
    words c (xs.map f)=(words c xs).map (List.map f) := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [words,List.flatMap_map,List.map_cons,List.map_nil,List.map_flatMap,ih,List.map_map,Function.comp_def]

end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem pair_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (i j : Fin n) (hij : i≠j) :
    (run (d := 2) p hp n).moment (fun q => flag q i*flag q j)=p i*p j := by
  simpa only [prod_pair hij] using subset_moment p hp {i,j} (by simp [hij] : ({i,j} : Finset (Fin n)).card ≤ 2)

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

theorem terminal_mean (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) :
    (terminal u p hp).moment (fun q => point q i)=point p i := by
  rw [terminal,SparseIntegerLaw.map_moment]
  by_cases hi : u i<0
  · simp only [point_state,ite_eq_left hi,SparseIntegerLaw.moment_const]
  · simp only [point_state,ite_eq_right hi,SparseBernoulli.single_moment]

theorem terminal_pair (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i j : Fin n) (hij : i≠j) :
    (terminal u p hp).moment (fun q => point q i*point q j)=point p i*point p j := by
  rw [terminal,SparseIntegerLaw.map_moment]
  by_cases hi : u i<0 <;> by_cases hj : u j<0
  · simp only [point_state,ite_eq_left hi,ite_eq_left hj,SparseIntegerLaw.moment_const]
  · simp only [point_state,ite_eq_left hi,ite_eq_right hj,SparseIntegerLaw.moment_mul,SparseBernoulli.single_moment]
  · simp only [point_state,ite_eq_right hi,ite_eq_left hj,SparseIntegerLaw.moment_mul_right,SparseBernoulli.single_moment]
  · simp only [point_state,ite_eq_right hi,ite_eq_right hj,SparseBernoulli.pair_moment _ _ _ _ hij]

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

theorem round_mean (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) :
    (round u p hp).moment (fun q => point q i)=point p i := by
  have hh := ((SparseSignedPartial.run u p n).bindCompress_spec (kernel u p hp)
    features).2.2 (finSumFinEquiv (Sum.inl i))
  simp only [features_single,kernel,RationalSignedTerminal.terminal_mean] at hh
  exact hh.trans (SparseSignedPartial.run_mean u p n i)

theorem round_pair (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i j : Fin n) (hij : i ≠ j) :
    (round u p hp).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  have hh := ((SparseSignedPartial.run u p n).bindCompress_spec (kernel u p hp)
    features).2.2 (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair,kernel,RationalSignedTerminal.terminal_pair _ _ _ _ _ hij] at hh
  exact hh.trans_le (SparseSignedPartial.run_pair u p n i j hij)

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

theorem kernel_nominal (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e : Fin m) :
    (kernel D q hq).moment (fun z => SparseBernoulli.flag z.2.2 e)=point q e := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  simp only [SparseBernoulli.single_moment,SparseIntegerLaw.moment_const]

theorem kernel_nominal_pair (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e f : Fin m) (hef : e≠f) :
    (kernel D q hq).moment (fun z => SparseBernoulli.flag z.2.2 e*SparseBernoulli.flag z.2.2 f)=
      point q e*point q f := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  simp only [SparseBernoulli.pair_moment _ _ _ _ hef,SparseIntegerLaw.moment_const]

theorem nominal (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (e : Fin m) :
    (law D c p hp hc).moment (fun z => SparseBernoulli.flag z.2.2 e)=point p e := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_nominal]
  exact SparseSignedRounding.round_mean _ _ _ _

theorem nominal_pair (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e f : Fin m) (hef : e≠f) :
    (law D c p hp hc).moment (fun z => SparseBernoulli.flag z.2.2 e*SparseBernoulli.flag z.2.2 f) ≤
      point p e*point p f := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_nominal_pair _ _ _ _ _ hef]
  exact SparseSignedRounding.round_pair _ _ _ _ _ hef

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem nominal_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) :
    (law D c q hc hq).moment (fun z => SparseSignedPreparation.nominalCount (base q) z e)=q e := by
  unfold SparseSignedPreparation.nominalCount
  rw [SparseIntegerLaw.moment_add,
    SparseIntegerLaw.moment_const,SparseSignedPreparation.nominal,fraction_identity]

theorem nominal_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) :
    (law D c q hc hq).moment (fun z =>
      SparseSignedPreparation.nominalCount (base q) z e*SparseSignedPreparation.nominalCount (base q) z f) ≤ q e*q f := by
  have hh := SparseIntegerLaw.moment_affine_pair_le (law D c q hc hq)
    (fun z => SparseBernoulli.flag z.2.2 e) (fun z => SparseBernoulli.flag z.2.2 f)
    (base q e:ℚ) (base q f:ℚ) (point (fraction q) e) (point (fraction q) f)
    (SparseSignedPreparation.nominal _ _ _ _ _ e) (SparseSignedPreparation.nominal _ _ _ _ _ f)
    (SparseSignedPreparation.nominal_pair _ _ _ _ _ e f hef)
  simpa only [SparseSignedPreparation.nominalCount,fraction_identity] using hh

theorem activation_adjacent (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) :
    let b : ℚ := if i∈D e then (base q e:ℚ) else 0
    activation D q (law D c q hc hq).states[a.val] e i=b ∨
      activation D q (law D c q hc hq).states[a.val] e i=b+1 := by
  dsimp only [activation]
  split_ifs
  all_goals first | exact Or.inl (add_zero _) | exact Or.inr rfl

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features)
variable {n : ℕ}

theorem fixed (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (e : Fin n)
    (he : point p e=0 ∨ point p e=1) (a : Fin (round u p hp).length) :
    point (round u p hp).states[a.val] e=point p e := by
  rcases he with he | he
  · rw [he]
    apply SparseIntegerLaw.zero_nonnegative (round u p hp) (fun q => point q e)
      (fun i => ((round_invariants u p hp hu i).1 e).1)
      ((round_mean u p hp e).trans he) a (positive u p hp a)
  · have hh : (round u p hp).moment (fun q => 1-point q e)=0 := by
      rw [SparseIntegerLaw.moment_sub,SparseIntegerLaw.moment_const,round_mean,he,sub_self]
    have hz := SparseIntegerLaw.zero_nonnegative (round u p hp) (fun q => 1-point q e)
      (fun i => sub_nonneg.mpr ((round_invariants u p hp hu i).1 e).2)
      hh a (positive u p hp a)
    rw [he]
    linarith only [hz]

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem point_fixed (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m)
    (he : point (fraction q) e=0) : ∀ a : Fin (law D c q hc hq).length,
      point (law D c q hc hq).states[a.val].1 e=0 := by
  unfold law SparseSignedPreparation.law
  dsimp only
  apply SparseIntegerLaw.bindIndexed_property _ _ (fun z : State n m => point z.1 e=0)
  intro a
  unfold SparseSignedPreparation.kernel
  apply SparseIntegerLaw.prod_property _ _ _ (fun z : State n m => point z.1 e=0)
  intro b d
  exact (SparseSignedRounding.fixed (SparseSignedPreparation.signed D c) (fraction q)
    (SparseGridRounding.fraction_unit q hq)
    (fun j _ => (sub_le_self _ (Nat.cast_nonneg _)).trans (hc j).2) e (Or.inl he) a).trans he

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem outsideCount_le_at (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (L : ℕ)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (hL : q e ≤ L) :
    outsideCount q (law D c q hc hq).states[a.val] e ≤ L := by
  have hb : base q e ≤ L := by exact_mod_cast (Nat.floor_le (hq e)).trans hL
  by_cases hi : 0 < point (law D c q hc hq).states[a.val].1 e
  · have hl : base q e < L := by
      by_contra hn
      have heq : base q e = L := le_antisymm hb (le_of_not_gt hn)
      have hz : point (fraction q) e = 0 := by
        simp only [fraction, point, Vector.getElem_ofFn]
        have hh := Nat.floor_le (hq e)
        change (base q e : ℚ) ≤ q e at hh
        rw [heq] at hh ⊢
        linarith only [hh, hL]
      have hf := point_fixed D c q hc hq e hz a
      rw [hf] at hi
      exact (lt_irrefl 0) hi
    simpa only [outsideCount, ite_eq_left hi] using Nat.add_one_le_iff.mpr hl
  · simpa only [outsideCount, ite_eq_right hi, Nat.add_zero] using hb

theorem nominalMass_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ) (e : Fin m) :
    (law D c q hc hq).realIndex.expect
      (fun a => nominalMass q g (law D c q hc hq).states[a.val] e) = g * (q e : ℝ) := by
  simp only [nominalMass, FiniteLaw.expect_mul]
  rw [SparseIntegerLaw.realIndex_expect _ (fun z => SparseSignedPreparation.nominalCount (base q) z e), nominal_mean]

theorem nominalMass_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ)
    (e f : Fin m) (hef : e ≠ f) :
    (law D c q hc hq).realIndex.expect (fun a =>
      nominalMass q g (law D c q hc hq).states[a.val] e *
      nominalMass q g (law D c q hc hq).states[a.val] f) ≤
      (g * (q e : ℝ)) * (g * (q f : ℝ)) := by
  have he := (law D c q hc hq).realIndex_expect (fun z =>
    SparseSignedPreparation.nominalCount (base q) z e *
    SparseSignedPreparation.nominalCount (base q) z f)
  simp only [Rat.cast_mul] at he
  have hh : (law D c q hc hq).realIndex.expect (fun a =>
      (SparseSignedPreparation.nominalCount (base q) (law D c q hc hq).states[a.val] e : ℝ) *
      (SparseSignedPreparation.nominalCount (base q) (law D c q hc hq).states[a.val] f : ℝ)) ≤
      (q e : ℝ) * (q f : ℝ) := by
    rw [he, ← Rat.cast_mul]
    exact Rat.cast_le.mpr (nominal_pair D c q hc hq e f hef)
  have hf : ∀ x y : ℝ, (g*x)*(g*y) = g^2*(x*y) := by intros; ring
  simpa only [nominalMass, hf, FiniteLaw.expect_mul] using
    mul_le_mul_of_nonneg_left hh (sq_nonneg g)

end MetricKMedian.SparseOuterLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RestrictionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
def choices {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : List (Finset (Fin n)) :=
  (words c (List.ofFn (T.orderEmbOfFin rfl))).map List.toFinset

def branches (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) : List (Finset (Fin I.n)) :=
  (words a (pairs F)).map (fun ps => witnessedRestriction I F ps.toFinset)
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_ReductionCostProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MaskProgram

def nearestData (x : List ℚ × Row) : ℚ := LPBinary.minimum (selectedValues x)
@[fun_prop] theorem nearestData_poly : Poly nearestData := by
  have h : Poly LPBinary.minimum := ⟨LPBinary.Program.minimumProgram⟩
  unfold nearestData; fun_prop
 theorem nearestData_view (I : Instance) (j : Fin I.n) (U : Finset (Fin I.n)) :
    nearestData (List.ofFn (I.distance j),setView U)=rationalNearest I j U := by
  unfold nearestData rationalNearest
  split_ifs with h
  · exact LPBinary.minimum_eq_finset _ _ (h.image _) (selectedValues_mem (I.distance j) U)
  · have he : selectedValues (List.ofFn (I.distance j),setView U)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      obtain ⟨i,hi,_⟩ := mem_image.mp ((selectedValues_mem (I.distance j) U q).mp hq)
      exact h ⟨i,hi⟩
    rw [he]; rfl

def costData (x : Raw × Row) : ℚ :=
  ((indices x.1.1.1).map (fun j => if get x.1.1.1 j then nearestData (x.1.2.2[j]?.getD [],x.2) else 0)).sum
@[fun_prop] theorem costData_poly : Poly costData := by
  unfold costData
  apply comp rat_sum
  apply list_map <;> fun_prop

def diff (x : Row × Row) : Row := (x.1.zip x.2).map (fun z => z.1 && !z.2)
def union (x : Row × Row) : Row := (x.1.zip x.2).map (fun z => z.1 || z.2)
@[fun_prop] theorem diff_poly : Poly diff := by unfold diff; apply list_map <;> fun_prop
@[fun_prop] theorem union_poly : Poly union := by unfold union; apply list_map <;> fun_prop
 theorem union_view {n : ℕ} (S T : Finset (Fin n)) : union (setView S,setView T)=setView (S∪T) := by
  simp only [union,setView,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,mem_union,Bool.decide_or]
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase )
open Completion.Rational.BestProgram (card card_view)
open Enumeration

def values (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : List ℚ :=
  (choices T c).flatMap (fun D => (List.ofFn (T.orderEmbOfFin rfl)).map (fun i =>
    rationalCost I ((T\D).erase i)-rationalCost I (T\D)))

def endpoints (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : List (Finset (Fin I.n)) :=
  (0::values I T c).map (fun B => rationalHistory I B T c)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_ReductionOutcomesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open Enumeration

def completions (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) : List (Finset (Fin I.n)) :=
  (choices U b).flatMap (fun H => (choices F b).map (fun B => completionSet I F B (U\H) (rationalRadii I U) δ))

def outcomes (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) : List (Finset (Fin I.n)) :=
  T::(endpoints I T c).flatMap (fun U => U::completions I F U δ b)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def branchList (I : Instance) : List Branch := (branches I I.facilities a).map (fun F => ⟨I,F⟩)
end MetricKMedian.Reduction.Program
end

end OAI
end


