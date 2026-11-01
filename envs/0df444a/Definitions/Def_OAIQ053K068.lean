-- Prove2me | Definitions.Def_OAIQ053K068
-- name    : OAIQ053K068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:18:42.167456+00:00
-- url     : https://prove2.me/theorems/a7195f1e-066d-4a95-a4a6-e25e4d2c4f16
-- title:
--   Definitions bundle OAIQ053K068 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 26 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Machines_FiniteBoundaryPrograms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Machines/FiniteBoundaryPrograms.lean), [`KMedian_Machines_FiniteFilterProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Machines/FiniteFilterProgram.lean), [`KMedian_Projection_SeedCombinators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedCombinators.lean), [`KMedian_Sparse_SparseOuterCounts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseOuterCounts.lean), [`KMedian_Sparse_SparseOuterLaw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseOuterLaw.lean), [`KMedian_Sparse_SparseOuterMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseOuterMoments.lean), [`KMedian_Sparse_SparseOuterReal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseOuterReal.lean), [`KMedian_Sparse_SparseSignedPreparation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseSignedPreparation.lean), [`KMedian_Sparse_SparseStarActivation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseStarActivation.lean).
--
--   **Imports.** It imports the bundles `OAIQ053K058`, `OAIQ053K059`, `OAIQ053K060` and `OAIQ053K061` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K074`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K058
import Definitions.Def_OAIQ053K059
import Definitions.Def_OAIQ053K060
import Definitions.Def_OAIQ053K061

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteFilterProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteFilterProgram
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

lemma poly_finite_filter {X I : Type} [Coding X] [Fintype I] [Coding (Finset I)]
    (f : X→I→Prop) (h : ∀ i, Poly (fun x=>decide (f x i))) :
    Poly (fun x=>Finset.univ.filter (f x)) := by
  have hh := poly_coordinates (fun x i=>decide (f x i)) h
  have hc : Poly (fun g : I→Bool => Finset.univ.filter (fun i=>g i)) := hardcoded _
  apply poly_congr (hc.comp hh)
  intro x
  simp only [decide_eq_true_eq]
namespace FiniteList
variable {A X : Type} [Fintype A] [Coding A] [Hardcoded A] [Coding X] [Inhabited A]
lemma poly_getElem? : Poly (fun p : List A×ℕ => p.1[p.2]?) := by
  have hs : Poly (some : A→Option A) := hardcoded _
  have hm : Poly (fun p : List A×ℕ => p.1.map some) := Poly.list_map (hs.comp Poly.snd) Poly.fst
  apply poly_congr (Poly.list_getD_comp none hm Poly.snd)
  intro p
  simp only [List.getElem?_map]
  cases p.1[p.2]? <;> rfl
lemma poly_prefixCell (pref : X→List A) (bound : X→ℕ) (v : Option A)
    (hp : Poly pref) (hb : Poly bound) :
    Poly (fun p : X×ℕ=>decide (Tableau.prefixCell (pref p.1) (bound p.1) p.2 v)) := by
  have hg := poly_getElem?.comp (Poly.pair (hp.comp Poly.fst) Poly.snd)
  have he : Poly (fun a : Option A=>decide (v=a)) := hardcoded _
  have hv := he.comp hg
  have h1 : Poly (fun p : X×ℕ=>decide (p.2<(pref p.1).length)) := by fun_prop
  have h2 : Poly (fun p : X×ℕ=>decide ((pref p.1).length+bound p.1≤p.2)) := by fun_prop
  have h : Poly (fun p : X×ℕ=>(!decide (p.2<(pref p.1).length) || decide (v=(pref p.1)[p.2]?)) &&
      (!decide ((pref p.1).length+bound p.1≤p.2) || decide (v=none))) := by fun_prop
  apply poly_congr h
  intro p
  rw [Bool.eq_iff_iff]
  simp [Tableau.prefixCell,Bool.or_eq_true,Bool.and_eq_true,imp_iff_not_or]

end FiniteList
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteFilterProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteBoundaryPrograms
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteBoundaryPrograms
namespace MetricKMedian.PCP.Compiler.FiniteList
open Binary Binary.Automatic
open scoped Classical

variable {X I A : Type} [Coding X] [Fintype I] [Coding (Finset I)] [Fintype A] [Coding A] [Hardcoded A] [Inhabited A]
lemma poly_prefixFilter (pref : X→List A) (bound : X→ℕ) (v : I→Option A)
    (hp : Poly pref) (hb : Poly bound) :
    Poly (fun p : X×ℕ=>Finset.univ.filter (fun i=>Tableau.prefixCell (pref p.1) (bound p.1) p.2 (v i))) := by
  exact poly_finite_filter _ (fun i=>poly_prefixCell pref bound (v i) hp hb)
lemma poly_getFilter (pref : X→List A) (v : I→Option A) (hp : Poly pref) :
    Poly (fun p : X×ℕ=>Finset.univ.filter (fun i=>v i=(pref p.1)[p.2]?)) := by
  have hh : Poly (fun a : Option A=>Finset.univ.filter (fun i=>v i=a)) := hardcoded _
  exact hh.comp (poly_getElem?.comp (Poly.pair (hp.comp Poly.fst) Poly.snd))
end MetricKMedian.PCP.Compiler.FiniteList

end Inline_PCPFiniteBoundaryPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedCombinators
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedCombinators
namespace MetricKMedian.PCP.Compiler.SeedCombinators
open Binary Binary.Automatic

variable {T D A : Type} [Coding T] [Coding D] [Coding A]
variable [Fintype A] [Inhabited A] [Hardcoded A]
lemma poly_project (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A)
    (hr : Poly (fun z : (T×ℕ)×D=>r z.1.1 z.1.2 z.2))
    (hf : Poly (fun z : ((T×ℕ)×D)×(A×A)=>fix z.1.1.1 z.1.1.2 z.1.2 z.2)) :
    Poly (fun z : (T×ℕ)×(D×Bool)=>project r fix z.1.1 z.1.2 z.2) := by
  apply poly_coordinates
  intro a
  have hs := poly_source r hr
  have hh := hf.comp (Poly.pair (Poly.pair (Poly.pair (Poly.fst.comp (Poly.fst : Poly (fun z : (T×ℕ)×(D×Bool)=>z.1)))
    (Poly.fst.comp hs)) (Poly.snd.comp hs)) (Automatic.Poly.const a))
  exact Poly.ite (Poly.snd.comp Poly.snd) (Poly.snd.comp hh) (Poly.fst.comp hh)
lemma poly_numbered (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A)
    (index : D→ℕ) (n : ℕ)
    (hr : Poly (fun z : (T×ℕ)×D=>r z.1.1 z.1.2 z.2))
    (hf : Poly (fun z : ((T×ℕ)×D)×(A×A)=>fix z.1.1.1 z.1.1.2 z.1.2 z.2))
    (hi : Poly index) : Poly (fun z : (T×ℕ)×(D×Bool)=>numbered r fix index n z.1.1 z.1.2 z.2) := by
  have hs := poly_source r hr
  exact Poly.pair (Poly.nat_add.comp (Poly.pair (hi.comp (Poly.snd.comp hs))
    (Poly.nat_mul.comp (Poly.pair (Automatic.Poly.const n) (Poly.fst.comp hs))))) (poly_project r fix hr hf)
end MetricKMedian.PCP.Compiler.SeedCombinators

end Inline_PCPSeedCombinators

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseStarActivation
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

theorem mean (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (e : Fin m) (i : Fin n) :
    (law D q).moment (fun S => if i∈S e then 1 else 0)=if i∈D e then q e else 0 := by
  have hh := SparseGraph.run_single (fun e => SparseTargetSubset.law (D e) (q e))
    (fun i e => if i∈D e then q e else 0) (fun i e => SparseTargetSubset.mean (D e) (hq e) i)
    m (le_refl m) i e
  simpa only [law,SparseGraph.edge,SparseGraph.target,e.isLt,ite_eq_left] using hh

theorem pair (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D q).moment (fun S => (if i∈S e then 1 else 0)*(if j∈S f then 1 else 0))=
      (if i∈D e then q e else 0)*(if j∈D f then q f else 0) := by
  have hh := SparseGraph.run_pair (fun e => SparseTargetSubset.law (D e) (q e))
    (fun i e => if i∈D e then q e else 0) (fun i e => SparseTargetSubset.mean (D e) (hq e) i)
    m (le_refl m) i j e f hef
  simpa only [law,SparseGraph.edge,SparseGraph.target,e.isLt,f.isLt,ite_eq_left] using hh

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPreparation
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

theorem kernel_target (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e : Fin m) (i : Fin n) :
    (kernel D q hq).moment (fun z => if i∈z.2.1 e then 1 else 0)=
      if i∈D e then point q e else 0 := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  apply Eq.trans ?_ (SparseStarActivation.mean D (point q) hq e i)
  apply SparseIntegerLaw.moment_congr
  intro a
  dsimp only
  by_cases hi : i∈(SparseStarActivation.law D (point q)).states[a.val] e
  all_goals simp only [hi,ite_true,ite_false]; exact SparseIntegerLaw.moment_const _ _

theorem kernel_target_pair (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (kernel D q hq).moment (fun z => (if i∈z.2.1 e then 1 else 0)*(if j∈z.2.1 f then 1 else 0))=
      (if i∈D e then point q e else 0)*(if j∈D f then point q f else 0) := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  apply Eq.trans ?_ (SparseStarActivation.pair D (point q) hq e f hef i j)
  apply SparseIntegerLaw.moment_congr
  intro a
  dsimp only
  by_cases hi : i∈(SparseStarActivation.law D (point q)).states[a.val] e <;>
    by_cases hj : j∈(SparseStarActivation.law D (point q)).states[a.val] f
  all_goals simp only [hi,hj,ite_true,ite_false]; exact SparseIntegerLaw.moment_const _ _

theorem nominal (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (e : Fin m) :
    (law D c p hp hc).moment (fun z => SparseBernoulli.flag z.2.2 e)=point p e := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_nominal]
  exact SparseSignedRounding.round_mean _ _ _ _

theorem target (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e : Fin m) (i : Fin n) :
    (law D c p hp hc).moment (fun z => if i∈z.2.1 e then 1 else 0)=
      if i∈D e then point p e else 0 := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_target]
  by_cases hi : i∈D e
  · simp only [ite_eq_left hi]
    exact SparseSignedRounding.round_mean _ _ _ _
  · simp only [ite_eq_right hi,mul_zero,sum_const_zero]

theorem target_pair (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c p hp hc).moment (fun z => (if i∈z.2.1 e then 1 else 0)*(if j∈z.2.1 f then 1 else 0)) ≤
      (if i∈D e then point p e else 0)*(if j∈D f then point p f else 0) := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_target_pair _ _ _ _ _ hef]
  by_cases hi : i∈D e <;> by_cases hj : j∈D f
  · simp only [ite_eq_left hi,ite_eq_left hj]
    exact SparseSignedRounding.round_pair _ _ _ _ _ hef
  all_goals simp only [hi,hj,ite_true,ite_false,mul_zero,zero_mul,sum_const_zero,le_refl]

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterLaw
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

theorem activation_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).moment (fun z => activation D q z e i)=if i∈D e then q e else 0 := by
  unfold activation
  rw [SparseIntegerLaw.moment_add,SparseIntegerLaw.moment_const,SparseSignedPreparation.target]
  by_cases hi : i∈D e
  · simp only [ite_eq_left hi,fraction_identity]
  · simp only [ite_eq_right hi,add_zero]

theorem activation_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c q hc hq).moment (fun z => activation D q z e i*activation D q z f j) ≤
      (if i∈D e then q e else 0)*(if j∈D f then q f else 0) := by
  have hh := SparseIntegerLaw.moment_affine_pair_le (law D c q hc hq)
    (fun z => if i∈z.2.1 e then 1 else 0) (fun z => if j∈z.2.1 f then 1 else 0)
    (if i∈D e then (base q e:ℚ) else 0) (if j∈D f then (base q f:ℚ) else 0)
    (if i∈D e then point (fraction q) e else 0) (if j∈D f then point (fraction q) f else 0)
    (SparseSignedPreparation.target _ _ _ _ _ e i) (SparseSignedPreparation.target _ _ _ _ _ f j)
    (SparseSignedPreparation.target_pair _ _ _ _ _ e f hef i j)
  change (law D c q hc hq).moment (fun z => activation D q z e i*activation D q z f j) ≤ _ at hh
  by_cases hi : i∈D e <;> by_cases hj : j∈D f
  all_goals simpa only [hi,hj,ite_true,ite_false,fraction_identity,zero_add] using hh

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterCounts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem activationCount_le (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) :
    activationCount D q (law D c q hc hq).states[a.val] e i ≤
      outsideCount q (law D c q hc hq).states[a.val] e := by
  by_cases hi : i∈D e
  · have hh := (budget D c q hc hq a).2.2.2.2.1 e i
    have he : (activationCount D q (law D c q hc hq).states[a.val] e i:ℚ) ≤
        (outsideCount q (law D c q hc hq).states[a.val] e:ℚ) := by
      rw [activationCount_cast,outsideCount_cast]
      simpa only [activation,ite_eq_left hi] using hh
    exact_mod_cast he
  · rw [activationCount_support D c q hc hq a e i hi]
    exact Nat.zero_le _

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterMoments
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open SparseGridRounding (base)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activation_real_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ))=
      ((if i∈D e then q e else 0:ℚ):ℝ) := by
  exact ((law D c q hc hq).realIndex_expect (fun z => activation D q z e i)).trans
    (congrArg (fun x : ℚ => (x:ℝ)) (activation_mean D c q hc hq e i))

theorem activation_real_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a =>
      (activation D q (law D c q hc hq).states[a.val] e i:ℝ)*
        (activation D q (law D c q hc hq).states[a.val] f j:ℝ)) ≤
      ((if i∈D e then q e else 0:ℚ):ℝ)*((if j∈D f then q f else 0:ℚ):ℝ) := by
  have hh := activation_pair D c q hc hq e f hef i j
  have he := SparseIntegerLaw.realIndex_expect (law D c q hc hq)
    (fun z => activation D q z e i*activation D q z f j)
  simp only [Rat.cast_mul] at he
  rw [he]
  exact_mod_cast hh

theorem deficit_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (i : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a => (deficit D q g (law D c q hc hq).states[a.val] i:ℝ))=
      (g:ℝ)*(targetMean D q i:ℝ) := by
  simp only [deficit,Rat.cast_mul,Rat.cast_sum,FiniteLaw.expect_mul,FiniteLaw.expect_sum,
    activation_real_mean,targetMean]

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterReal
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem nominalMass_cap (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) {g : ℝ} (hg : 0 ≤ g)
    (a : Fin (law D c q hc hq).length) (e : Fin m) :
    nominalMass q g (law D c q hc hq).states[a.val] e ≤
      g * (outsideCount q (law D c q hc hq).states[a.val] e : ℝ) := by
  apply mul_le_mul_of_nonneg_left _ hg
  have h := (budget D c q hc hq a).2.2.2.1 e
  rw [← outsideCount_cast] at h
  exact_mod_cast h

theorem nominalMass_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ) (e : Fin m) :
    (law D c q hc hq).realIndex.expect
      (fun a => nominalMass q g (law D c q hc hq).states[a.val] e) = g * (q e : ℝ) := by
  simp only [nominalMass, FiniteLaw.expect_mul]
  rw [SparseIntegerLaw.realIndex_expect _ (fun z => SparseSignedPreparation.nominalCount (base q) z e), nominal_mean]

theorem nominalMass_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ) (e : Fin m) :
    (law D c q hc hq).realIndex.variance
      (fun a => nominalMass q g (law D c q hc hq).states[a.val] e) ≤ g * (g * (q e : ℝ)) := by
  have hv : (law D c q hc hq).realIndex.variance
      (fun a => (SparseSignedPreparation.nominalCount (base q) (law D c q hc hq).states[a.val] e : ℝ)) ≤
      (q e : ℝ) := by
    apply FiniteLaw.adjacent_variance _ _ (m := (base q e : ℝ)) (Nat.cast_nonneg _) ?_ ?_
    · intro a _
      rcases (budget D c q hc hq a).2.2.1 e with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    · rw [SparseIntegerLaw.realIndex_expect _ (fun z => SparseSignedPreparation.nominalCount (base q) z e), nominal_mean]
  simp only [nominalMass, FiniteLaw.variance_mul]
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hv (sq_nonneg g)

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


