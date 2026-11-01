-- Prove2me | Definitions.Def_OAIQ053K055
-- name    : OAIQ053K055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:10:51.863879+00:00
-- url     : https://prove2.me/theorems/71577c95-40fe-48c2-905e-f689117cc36b
-- title:
--   Definitions bundle OAIQ053K055 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 41 definitions and 44 theorems. The definitions and types are `OAI.MetricKMedian.Coverage.Input.raw`, `OAI.MetricKMedian.Coverage.Raw.clients`, `OAI.MetricKMedian.Coverage.Raw.entry`, `OAI.MetricKMedian.Coverage.Raw.medianBytes`, `OAI.MetricKMedian.Coverage.Raw.parsedProgram`, `OAI.MetricKMedian.Coverage.Raw.sets`, `OAI.MetricKMedian.Coverage.Raw.typedMedianProgram`, `OAI.MetricKMedian.MaskProgram.imageRaw`, `OAI.MetricKMedian.MaskProgram.pullbackMatrix`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.Raw`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.bundleData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.bundlesData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.massData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.missingData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.neighborMask`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.nextData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.cutsData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.flagsData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.outsideData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.pairWeight`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.qData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.targetsData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.weightsData`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Raw`, `OAI.MetricKMedian.RationalSortProgram.foldProgram`, `OAI.MetricKMedian.RationalSortProgram.sort`, `OAI.MetricKMedian.RoundingList.Last.active`, `OAI.MetricKMedian.RoundingList.Last.endpoint`, `OAI.MetricKMedian.RoundingList.Last.probability`, `OAI.MetricKMedian.RoundingProgram.Terminal.boolState`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.lastRaw`, `OAI.MetricKMedian.SparseBernoulli.Program.Row`, `OAI.MetricKMedian.SparseCounts.ListOperation.dimensions`, `OAI.MetricKMedian.SparseCounts.ListOperation.edges`, `OAI.MetricKMedian.SparseCounts.ListOperation.featureList`, `OAI.MetricKMedian.SparseCounts.ListOperation.nextTable`, `OAI.MetricKMedian.SparseGridRounding.Program.counts`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.branchLawProgram`, `OAI.MetricKMedian.SparseStarActivation.Program.Raw`, `OAI.MetricKMedian.SparseTargetSubset.Program.Raw` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Hardness_Encoding`, `KMedian_Hardness_ProjectionEncoding`, `KMedian_Hardness_Verdict`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_CountListOperations`, `KMedian_Programs_BundleGeometryProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_OriginalMaskProgram`, `KMedian_Programs_RationalSortProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseBranchProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K048` and `OAIQ053K049` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K063`, `OAIQ053K064`, `OAIQ053K065`, `OAIQ053K066` and `OAIQ053K067`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K048
import Definitions.Def_OAIQ053K049

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Encoding
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

@[fun_prop] theorem encodeNat_poly : Poly encodeNat := by
  change Poly (fun n : ℕ => encodeNat n)
  have h : Poly (fun n : ℕ => n.bits.map (fun _ => true) ++ [false] ++ n.bits) := by
    fun_prop
  simpa only [List.map_const', encodeNat] using h

def entry (r : Raw) (a b : ℕ) : List Bool :=
  if a = b then encodeRat 0 else
  if a < r.m then
    if b < r.m then encodeRat 2 else
      if (r.table[a * r.n + (b - r.m)]?).getD false then encodeRat 1 else encodeRat 3
  else
    if b < r.m then
      if (r.table[b * r.n + (a - r.m)]?).getD false then encodeRat 1 else encodeRat 3
    else encodeRat 2

@[fun_prop] theorem entry_poly : Poly (fun x : Raw × ℕ × ℕ => x.1.entry x.2.1 x.2.2) := by
  unfold entry; fun_prop

def medianBytes (r : Raw) : List Bool :=
  encodeNat (r.m + r.n) ++ encodeNat r.k ++
  (r.indices.map (fun a => decide (a < r.m))) ++
  (r.indices.map (fun a => decide (r.m ≤ a))) ++
  (r.indices.flatMap (fun a => r.indices.flatMap (fun b => r.entry a b)))

@[fun_prop] theorem medianBytes_poly : Poly medianBytes := by
  have hr : Poly (fun x : Raw × ℕ =>
      x.1.indices.flatMap (fun b => x.1.entry x.2 b)) := by
    apply Poly.list_flatMap
    · exact Poly.comp (g := fun x : (Raw × ℕ) × ℕ => (x.1.1, x.1.2, x.2))
        entry_poly (by fun_prop)
    · exact Poly.comp indices_poly Poly.fst
  have hmatrix : Poly (fun r : Raw => r.indices.flatMap (fun a =>
      r.indices.flatMap (fun b => r.entry a b))) :=
    Poly.list_flatMap hr indices_poly
  have hc : Poly (fun r : Raw => r.indices.map (fun a => decide (a < r.m))) := by
    apply Poly.list_map _ indices_poly
    dsimp only [m]; fun_prop
  have hf : Poly (fun r : Raw => r.indices.map (fun a => decide (r.m ≤ a))) := by
    apply Poly.list_map _ indices_poly
    dsimp only [m]; fun_prop
  have hn : Poly (fun r : Raw => encodeNat (r.m + r.n)) :=
    Poly.comp encodeNat_poly (by dsimp only [m, n]; fun_prop)
  have hk : Poly (fun r : Raw => encodeNat r.k) :=
    Poly.comp (g := fun r : Raw => r.k) encodeNat_poly (by fun_prop)
  let app := Poly.list_append (α := Bool)
  have hh : Poly (fun r : Raw => encodeNat (r.m + r.n) ++ encodeNat r.k) :=
    Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hn hk)
  have hh1 : Poly (fun r : Raw => encodeNat (r.m + r.n) ++ encodeNat r.k ++
      r.indices.map (fun a => decide (a < r.m))) :=
    Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hh hc)
  have hh2 : Poly (fun r : Raw => encodeNat (r.m + r.n) ++ encodeNat r.k ++
      r.indices.map (fun a => decide (a < r.m)) ++
      r.indices.map (fun a => decide (r.m ≤ a))) :=
    Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hh1 hf)
  exact Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hh2 hmatrix)

noncomputable def parsedProgram : PolyProgram id enc parse :=
  BooleanLists.packProgram.comp parse_poly.program

attribute [irreducible] parsedProgram

noncomputable def typedMedianProgram : PolyProgram id enc (fun xs => (parse xs).medianBytes) :=
  PolyProgram.comp (ea := id) (eb := enc) (ec := enc)
    (f := parse) (g := medianBytes) parsedProgram medianBytes_poly.program

attribute [irreducible] typedMedianProgram

end Raw

namespace Input

def raw (C : Input) : Raw :=
  (C.m, C.n, C.k, (List.ofFn (fun j : Fin C.m => List.ofFn (C.incident j))).flatten)

theorem parse_encode (C : Input) : Raw.parse C.encode = C.raw := by
  simp only [Raw.parse, encode, List.append_assoc, InputParser.natRead_append, raw]

theorem table_length (C : Input) : C.raw.table.length = C.m * C.n := by
  simp [raw, Raw.table, List.length_flatten, List.sum_ofFn, Finset.sum_const]

@[simp] theorem raw_m (C : Input) : C.raw.m = C.m := rfl
@[simp] theorem raw_n (C : Input) : C.raw.n = C.n := rfl
@[simp] theorem raw_k (C : Input) : C.raw.k = C.k := rfl

theorem table_flatten (C : Input) : C.raw.table =
    List.ofFn (fun t : Fin (C.m * C.n) =>
      C.incident (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) := by
  symm
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  have hji : j.val * C.n + i.val < C.m * C.n := by
    calc
      _ < j.val * C.n + C.n := Nat.add_lt_add_left i.isLt _
      _ = (j.val + 1) * C.n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ j.isLt
  have he : (⟨j.val * C.n + i.val, hji⟩ : Fin (C.m * C.n)) =
      finProdFinEquiv (j, i) := by
    apply Fin.ext
    change _ = i.val + C.n * j.val
    ac_rfl
  rw [he, finProdFinEquiv.symm_apply_apply]

theorem table_get (C : Input) (j : Fin C.m) (i : Fin C.n) :
    (C.raw.table[j.val * C.n + i.val]?).getD false = C.incident j i := by
  rw [C.table_flatten]
  have hji : j.val * C.n + i.val < C.m * C.n := by
    calc
      _ < j.val * C.n + C.n := Nat.add_lt_add_left i.isLt _
      _ = (j.val + 1) * C.n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ j.isLt
  simp only [List.getElem?_ofFn, dite_eq_left hji, Option.getD_some]
  have he : (⟨j.val * C.n + i.val, hji⟩ : Fin (C.m * C.n)) =
      finProdFinEquiv (j, i) := by
    apply Fin.ext
    change _ = i.val + C.n * j.val
    ac_rfl
  rw [he, finProdFinEquiv.symm_apply_apply]

@[simp] theorem client_val (C : Input) (j : Fin C.m) : (C.client j).val = j.val := rfl
@[simp] theorem facility_val (C : Input) (i : Fin C.n) : (C.facility i).val = C.m + i.val := rfl

theorem entry_point (C : Input) (x y : C.Point) :
    C.raw.entry (finSumFinEquiv x).val (finSumFinEquiv y).val =
      encodeRat (C.pointDistance x y) := by
  cases x with
  | inl j =>
    cases y with
    | inl l =>
      simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Raw.entry, raw_m,
        j.isLt, l.isLt, ↓reduceIte, pointDistance, Fin.val_inj]
      split_ifs <;> rfl
    | inr i =>
      have hij : j.val ≠ C.m + i.val := by omega
      have hm : ¬ C.m + i.val < C.m := by omega
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, Raw.entry, raw_m, raw_n, hij,
        j.isLt, hm, ↓reduceIte, Nat.add_sub_cancel_left, C.table_get, pointDistance]
      split_ifs <;> rfl
  | inr i =>
    cases y with
    | inl j =>
      have hij : C.m + i.val ≠ j.val := by omega
      have hm : ¬ C.m + i.val < C.m := by omega
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, Raw.entry, raw_m, raw_n, hij,
        j.isLt, hm, ↓reduceIte, Nat.add_sub_cancel_left, C.table_get, pointDistance]
      split_ifs <;> rfl
    | inr h =>
      have hi : ¬ C.m + i.val < C.m := by omega
      have hh : ¬ C.m + h.val < C.m := by omega
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, Raw.entry, raw_m,
        hi, hh, ↓reduceIte, Nat.add_left_cancel_iff, Fin.val_inj, pointDistance]
      split_ifs <;> rfl

theorem entry_distance (C : Input) (x y : Fin (C.m + C.n)) :
    C.raw.entry x.val y.val = encodeRat (C.toMedian.distance x y) := by
  simpa only [Equiv.apply_symm_apply, toMedian] using
    C.entry_point (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionEncoding
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace ProjectionRaw

@[fun_prop] theorem lefts_poly : Poly lefts := by
  unfold lefts; apply Poly.comp Poly.list_indices; fun_prop

end ProjectionRaw

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function
variable {α γ : Type}

noncomputable def branchLawProgram :
    PolyProgram (encodePair el (encodeList Ratio.encode)) el branchLawData := by
  let en := encodePair el (encodeList Ratio.encode)
  let law := fst el (encodeList Ratio.encode)
  let probs := snd el (encodeList Ratio.encode)
  let D := probs.comp IntegerList.denominatorProgram
  let nums := law.comp (snd Signed.encode er)
  let zs := probs.comp IntegerList.numeratorsProgram
  let triples := D.fanout ((nums.fanout zs).comp (listZip Signed.encode Signed.encode 0 0))
  let ez := encodePair Signed.encode Signed.encode
  let z := snd Signed.encode ez
  let w := z.comp (fst Signed.encode Signed.encode)
  let a := z.comp (snd Signed.encode Signed.encode)
  let d := fst Signed.encode ez
  let p0 := (w.fanout a).comp intMul
  let p1 := (w.fanout ((d.fanout a).comp intSub)).comp intMul
  let entries := (p0.fanout p1).comp pairList
  let outputnums := triples.comp (entries.listFlatMapWith (0,0) 0)
  let den := ((law.comp (fst Signed.encode er)).fanout D).comp intMul
  exact (den.fanout outputnums).congr _ (fun _ => rfl)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OriginalMaskProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView indices)

def imageRaw (x : (List Unit × List ℕ) × Row) : Row :=
  (indices x.1.1).map (fun h => ((indices x.1.2).map (fun i =>
    get x.2 i && decide (x.1.2[i]?.getD 0=h))).any id)
@[fun_prop] theorem imageRaw_poly : Poly imageRaw := by
  unfold imageRaw
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem pullback_poly : Poly pullback := by unfold pullback; apply list_map <;> fun_prop

def pullbackMatrix (x : List (List ℚ) × List ℕ) : List (List ℚ) :=
  x.2.map (fun i => pullback (x.1[i]?.getD [],x.2))
@[fun_prop] theorem pullbackMatrix_poly : Poly pullbackMatrix := by unfold pullbackMatrix; apply list_map <;> fun_prop
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierListOperations
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)

theorem append_poly {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x++g x) :=
  comp list_append (pair hf hg)

def targetsData (x : SupplierRaw) : BTable :=
  ((indices x.1).map (fun i => (indices x.2.2.2.1).map (fun t => (x.2.2.1[t]?.getD [])[i]?.getD false))) ++
  (((indices x.2.2.2.1).flatMap (fun s => (indices x.2.2.2.1).map (fun _ =>
    (indices x.2.2.2.1).map (fun j => decide (j=s))))) ++
    (indices x.2.2.2.1).map (fun t => (indices x.2.2.2.1).map (fun j => decide (j=t))))
@[fun_prop] theorem targetsData_poly : Poly targetsData := by
  unfold targetsData
  apply append_poly
  · apply list_map <;> (first | (apply list_map <;> fun_prop) | fun_prop)
  · apply append_poly
    · apply list_flatMap
      · apply list_map
        · apply list_map <;> fun_prop
        · fun_prop
      · fun_prop
    · apply list_map
      · apply list_map <;> fun_prop
      · fun_prop

def flagsData (x : SupplierRaw) : QRow := x.1.map (fun _ => 1) ++
  (x.2.2.2.1.flatMap (fun _ => x.2.2.2.1.map (fun _ => 0)) ++ x.2.2.2.1.map (fun _ => 0))
@[fun_prop] theorem flagsData_poly : Poly flagsData := by
  unfold flagsData
  apply append_poly
  · apply list_map <;> fun_prop
  · apply append_poly
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
    · apply list_map <;> fun_prop

def outsideData (x : SupplierRaw) (i : ℕ) : Bool := (x.2.1.map (fun P => !(P[i]?.getD false))).all id
def pairWeight (x : SupplierRaw) (s t : ℕ) : ℚ :=
  ((indices x.1).map (fun i => if ((x.2.2.1[s]?.getD [])[i]?.getD false) &&
    ((x.2.1[t]?.getD [])[i]?.getD false) then x.1[i]?.getD 0 else 0)).sum
def weightsData (x : SupplierRaw) : QRow :=
  ((indices x.1).map (fun i => if outsideData x i then x.1[i]?.getD 0 else 0)) ++
  (((indices x.2.2.2.1).flatMap (fun s => (indices x.2.2.2.1).map (fun t => pairWeight x s t))) ++
    x.2.2.2.2.1.map (fun c => x.2.2.2.2.2*c))
@[fun_prop] theorem outsideData_poly : Poly (fun x : SupplierRaw × ℕ => outsideData x.1 x.2) := by
  unfold outsideData; apply comp bool_all; apply list_map <;> fun_prop
@[fun_prop] theorem pairWeight_poly : Poly (fun x : SupplierRaw × (ℕ × ℕ) => pairWeight x.1 x.2.1 x.2.2) := by
  unfold pairWeight; apply comp rat_sum; apply list_map <;> fun_prop
@[fun_prop] theorem weightsData_poly : Poly weightsData := by
  unfold weightsData; apply append_poly
  · apply list_map <;> fun_prop
  · apply append_poly
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
    · apply list_map <;> fun_prop

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalSortProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RationalSortProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly

@[fun_prop] theorem insertData_poly : Poly insertData := by
  unfold insertData
  apply Preparation.RationalSuppliers.Program.append_poly
  · apply list_filter <;> fun_prop
  · have hf : Poly (fun x : List ℚ × ℚ => x.1.filter (fun a => decide (x.2<a))) := by apply list_filter <;> fun_prop
    exact comp list_cons (pair (by fun_prop) hf)
 theorem insertData_length (xs : List ℚ) (a : ℚ) :
    (enc (insertData (xs,a))).length≤(enc xs).length+1*(2*(enc a).length+1) := by
  have hh := filters_length Ratio.encode (fun q : ℚ => decide (q<a)) (fun q => decide (a<q))
    (fun q h => (lt_asymm (of_decide_eq_true h.1) (of_decide_eq_true h.2))) xs
  simp only [insertData,enc,Coding.encode,EncodedList.append,List.length_append,EncodedList.cons_length,one_mul]
  change (encodeList Ratio.encode _).length+ (2*(Ratio.encode _).length+1+(encodeList Ratio.encode _).length)≤_
  omega

def sort (xs : List ℚ) : List ℚ := xs.foldl (fun s a => insertData (s,a)) []
noncomputable def foldProgram : PolyProgram (enc : List ℚ × List ℚ → List Bool) enc
    (fun x => x.1.foldl (fun s a => insertData (s,a)) x.2) :=
  insertData_poly.program.listFoldLinear 0 1 insertData_length
@[fun_prop] theorem sort_poly : Poly sort := by
  refine ⟨(((identity enc).fanout (constant enc enc ([] : List ℚ))).comp foldProgram).congr _ (fun _ => rfl)⟩

end MetricKMedian.RationalSortProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_SplitListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalSplitting.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
def cutsData (x : Raw × ℕ) : List ℚ :=
  RationalSortProgram.sort ((x.1.1[x.2]?.getD 0 :: x.1.2.map (fun r => r[x.2]?.getD 0)).filter (fun q => decide (0<q)))
end MetricKMedian.Preparation.RationalSplitting.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitRepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
abbrev Raw := (List ℚ × Table) × (List (List ℚ) × (List (List ℚ) × List (List ℚ)))

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundleGeometryProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalBundles.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
abbrev Raw := (List (List ℚ) × List (List ℚ)) × (Table × List ℚ)
def neighborMask (x : List ℚ × ℕ) : Row := (indices x.1).map (fun i => decide (i≠x.2))
@[fun_prop] theorem neighborMask_poly : Poly neighborMask := by unfold neighborMask; simp only [decide_not]; apply list_map <;> fun_prop
def nextData (x : List ℚ × ℕ) : ℕ := if (neighborMask x).any id then MetricKMedian.MaskProgram.nearest (x.1,neighborMask x) else x.2
@[fun_prop] theorem nextData_poly : Poly nextData := by unfold nextData; fun_prop

def bundleData (δ : ℚ) (x : Raw × ℕ) : Row :=
  let t := x.2
  let s := nextData (x.1.1.1[t]?.getD [],t)
  if s=t then x.1.2.1[t]?.getD [] else
    (indices x.1.2.2).map (fun a => MetricKMedian.MaskProgram.get (x.1.2.1[t]?.getD []) a &&
      decide ((x.1.1.2[t]?.getD [])[a]?.getD 0 ≤ δ*(x.1.1.1[t]?.getD [])[s]?.getD 0))
@[fun_prop] theorem bundleData_poly (δ : ℚ) : Poly (bundleData δ) := by
  unfold bundleData
  apply ite_prop
  · fun_prop
  · fun_prop
  · apply list_map <;> fun_prop

def bundlesData (δ : ℚ) (x : Raw) : Table := (indices x.2.1).map (fun t => bundleData δ (x,t))
@[fun_prop] theorem bundlesData_poly (δ : ℚ) : Poly (bundlesData δ) := by unfold bundlesData; apply list_map <;> fun_prop

def missingData (δ : ℚ) (x : Raw) : Table := (indices x.2.1).map (fun t =>
    (indices x.2.2).map (fun a => MetricKMedian.MaskProgram.get (x.2.1[t]?.getD []) a && !MetricKMedian.MaskProgram.get (bundleData δ (x,t)) a))
@[fun_prop] theorem missingData_poly (δ : ℚ) : Poly (missingData δ) := by
  unfold missingData; apply list_map
  · apply list_map <;> fun_prop
  · fun_prop

def massData (x : List ℚ × Table) : List ℚ := x.2.map (fun P =>
  ((indices x.1).map (fun i => if MetricKMedian.MaskProgram.get P i then x.1[i]?.getD 0 else 0)).sum)
@[fun_prop] theorem massData_poly : Poly massData := by
  unfold massData
  apply list_map
  · apply comp rat_sum
    apply list_map <;> fun_prop
  · fun_prop
end MetricKMedian.Preparation.RationalBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram
abbrev Row := ListOperation.Row

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_LastFractionProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList.Last
open Binary Binary.Automatic Binary.Automatic.Poly Finset

def active (p : Row) : Bool := decide (0<(RoundingList.fractional p).length)
@[fun_prop] theorem active_poly : Poly active := by unfold active; fun_prop

def probability (p : Row) : ℚ := if active p then p[first p]?.getD 0 else 0
@[fun_prop] theorem probability_poly : Poly probability := by unfold probability; fun_prop

def endpoint (b : Bool) (p : Row) : Row := if active p then
  (indices p).map (fun k => if k=first p then (if b then 0 else 1) else p[k]?.getD 0)
  else p
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (endpoint b) := by
  unfold endpoint
  have he : Poly (fun p : Row => (indices p).map (fun k => if k=first p then (if b then (0:ℚ) else 1) else p[k]?.getD 0)) := by
    apply list_map <;> fun_prop
  fun_prop
end MetricKMedian.RoundingList.Last

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def lastRaw (x : Row × Data Row) : Row × Data Row :=
  (x.1,(branchLawData (x.2.1,x.2.2.map RoundingList.Last.probability),
    x.2.2.flatMap (fun p => [RoundingList.Last.endpoint false p,RoundingList.Last.endpoint true p])))
@[fun_prop] theorem lastRaw_poly : Poly lastRaw := by
  unfold lastRaw
  have hp : Poly (fun x : Row × Data Row => x.2.2.map RoundingList.Last.probability) := by apply list_map <;> fun_prop
  have he : Poly (fun x : Row × Data Row => x.2.2.flatMap (fun p => [RoundingList.Last.endpoint false p,RoundingList.Last.endpoint true p])) := by
    apply list_flatMap <;> fun_prop
  exact pair (by fun_prop) (pair (comp (⟨branchLawProgram⟩ : Poly branchLawData) (pair (by fun_prop) hp)) he)
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_TargetSubsetProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
abbrev Raw := Row × ℚ
def prepare (x : Raw) : List ℚ × List ℚ := (x.1.map (fun _ => 1),x.1.map (fun b => if b then x.2 else 0))
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)
abbrev Raw := List Unit × (Table × List ℚ)
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedTerminalProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

def boolState (x : (Row × Row) × List Bool) : Row :=
  (List.range x.1.1.length).map (fun i => if x.1.1[i]?.getD 0<0 then x.1.2[i]?.getD 0
    else if x.2[i]?.getD false then 1 else 0)
@[fun_prop] theorem boolState_poly : Poly boolState := by
  unfold boolState
  apply list_map
  · fun_prop
  · exact comp (f:=fun xs : Row => List.range xs.length) (g:=fun x : (Row × Row) × List Bool => x.1.1) list_indices (by fun_prop)

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseCounts.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
@[fun_prop] theorem indices_poly {α : Type} [Coding α] [Inhabited α] : Poly (indices (α:=α)) := list_indices

def edges (x : List Unit × Table) : List ℚ :=
  (indices x.1).flatMap (fun h => x.2.map (fun col => ((col[h]?.getD 0:ℕ):ℚ)))
def featureList (x : List Unit × Table) : List ℚ := RoundingList.features (edges x)
def nextTable (x : (ℕ × Table) × Row) : Table :=
  (indices x.1.2).map (fun i => if i=x.1.1 then x.2 else x.1.2[i]?.getD [])
def dimensions (x : List Unit × List (SparseIntegerLaw.BinarySparse.Data Row)) : List Unit :=
  let bs := x.1.flatMap (fun _ => x.2.map (fun _ => (0:ℚ)))
  RoundingList.dimensions bs

@[fun_prop] theorem edges_poly : Poly edges := by
  unfold edges
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem featureList_poly : Poly featureList := by unfold featureList; fun_prop
@[fun_prop] theorem nextTable_poly : Poly nextTable := by
  unfold nextTable
  apply list_map <;> fun_prop
@[fun_prop] theorem dimensions_poly : Poly dimensions := by
  unfold dimensions
  apply comp RoundingList.dimensions_poly
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop

end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridRoundingProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def counts (x : List ℚ × List Bool) : List ℕ :=
  (SparseGraph.ListOperation.indices x.1).map (fun i => ⌊x.1[i]?.getD 0⌋₊+if x.2[i]?.getD false then 1 else 0)
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
open SparseIntegerLaw.BinarySparse
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)

def qData (x : SupplierRaw) : QRow := (weightsData x).map (fun w => w/qR.g)
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Verdict
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

def clients (r : Raw) : List ℕ := List.range (r.table.take r.m).length
def sets (r : Raw) : List ℕ := List.range (r.table.take r.n).length

end Raw

namespace Input

theorem mem_selectedMask_iff (C : Input) (out : List Bool) (i : Fin C.n) :
    i ∈ C.selectedMask out ↔ (out[C.m+i.val]?).getD false = true := by
  change i ∈ Finset.filter (fun i => (out[(C.facility i).val]?).getD false = true) Finset.univ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, facility_val]

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end


