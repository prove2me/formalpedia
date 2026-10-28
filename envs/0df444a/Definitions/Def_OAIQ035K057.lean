-- Prove2me | Definitions.Def_OAIQ035K057
-- name    : OAIQ035K057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:13:47.662613+00:00
-- url     : https://prove2.me/theorems/3cc925dc-56de-41f9-943d-d8021209dd26
-- title:
--   Definitions bundle OAIQ035K057 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 44 definitions and 25 theorems. The definitions and types are `OAI.MetricKMedian.InputParser.parseProgram`, `OAI.MetricKMedian.LPBinary.Repair.nearestRowsProgram`, `OAI.MetricKMedian.LPBinary.Repair.rawProgram`, `OAI.MetricKMedian.LPBinary.Repair.validProgram`, `OAI.MetricKMedian.LPBinary.Scale.candidateProgram`, `OAI.MetricKMedian.LPBinary.Scale.feasibleProgram`, `OAI.MetricKMedian.LPBinary.Scale.selectedProgram`, `OAI.MetricKMedian.LPBinary.Scale.selectedScaleProgram`, `OAI.MetricKMedian.LPBinary.Scale.valueOfProgram`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.Raw`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.bundleData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.bundlesData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.massData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.missingData`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.neighborMask`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.nextData`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Raw`, `OAI.MetricKMedian.RoundingList.Last.active`, `OAI.MetricKMedian.RoundingList.Last.endpoint`, `OAI.MetricKMedian.RoundingList.Last.probability`, `OAI.MetricKMedian.RoundingProgram.Terminal.boolState`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.lastRaw`, `OAI.MetricKMedian.SparseCounts.ListOperation.dimensions`, `OAI.MetricKMedian.SparseCounts.ListOperation.edges`, `OAI.MetricKMedian.SparseCounts.ListOperation.featureList`, `OAI.MetricKMedian.SparseCounts.ListOperation.nextTable`, `OAI.MetricKMedian.SparseCounts.Program.Context.encode`, `OAI.MetricKMedian.SparseCounts.Program.Context.raw`, `OAI.MetricKMedian.SparseCounts.Program.Input.encode`, `OAI.MetricKMedian.SparseCounts.Program.Input.raw`, `OAI.MetricKMedian.SparseCounts.Program.InputRaw`, `OAI.MetricKMedian.SparseCounts.Program.State.encode`, `OAI.MetricKMedian.SparseCounts.Program.activeProgram`, `OAI.MetricKMedian.SparseCounts.Program.columnRaw`, `OAI.MetricKMedian.SparseCounts.Program.countProgram`, `OAI.MetricKMedian.SparseCounts.Program.ei`, `OAI.MetricKMedian.SparseCounts.Program.startProgram`, `OAI.MetricKMedian.SparseCounts.Program.view`, `OAI.MetricKMedian.SparseGridRounding.Program.counts`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.base` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_NumericParserProgram`, `KMedian_Binary_SequentialParserProgram`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Process_CountListOperations`, `KMedian_Process_CountRunProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BundleGeometryProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBernoulliRun`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseSignedPartial`, `KMedian_Sparse_SparseSignedRounding`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K050`, `OAIQ035K051`, `OAIQ035K052` and `OAIQ035K053` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K061`, `OAIQ035K062`, `OAIQ035K063` and `OAIQ035K064`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K050
import Definitions.Def_OAIQ035K051
import Definitions.Def_OAIQ035K052
import Definitions.Def_OAIQ035K053

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_NumericParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
 theorem prefix_width (n : ℕ) (xs : List Bool) : width (List.replicate n true++false::xs)=n := by
  induction n with
  | zero => simp [width,List.findIdx_cons]
  | succ n ih => simp only [List.replicate_succ,List.cons_append,width,List.findIdx_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte]; exact congrArg Nat.succ ih
 theorem natRead_append (n : ℕ) (xs : List Bool) : natRead (encodeNat n++xs)=(n,xs) := by
  unfold natRead
  have hw : width (encodeNat n++xs)=n.bits.length := by
    simpa only [encodeNat,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using prefix_width n.bits.length (n.bits++xs)
  rw [hw]
  have hd : (encodeNat n++xs).drop (n.bits.length+1)=n.bits++xs := by
    simp [encodeNat,List.drop_append,List.append_assoc]
  rw [hd,show (encodeNat n++xs).drop (n.bits.length+1+n.bits.length)=xs from by
    rw [← List.drop_drop,hd,List.drop_left]]
  simp only [List.take_left,Word.value_bits]
 theorem natRead_rest_length (xs : List Bool) : (natRead xs).2.length≤xs.length := by
  simp only [natRead,List.length_drop]; omega
 theorem ratRead_append (q : ℚ) (xs : List Bool) : ratRead (encodeRat q++xs)=(q,xs) := by
  simp only [ratRead,encodeRat,List.append_assoc,List.cons_append,List.tail_cons,List.head?_cons,Option.getD_some,List.nil_append,natRead_append]
  rw [show Signed.value (decide (q.num<0)) q.num.natAbs=q.num from Signed.value_parts q.num]
  rw [Rat.mkRat_eq_div,q.num_div_den]
 theorem ratRead_rest_length (xs : List Bool) : (ratRead xs).2.length≤xs.length :=
  (natRead_rest_length _).trans ((natRead_rest_length _).trans (by simp only [List.length_tail]; omega))
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_SequentialParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
section Generic
variable {α : Type} [Coding α] [Inhabited α] (read : List Bool → α × List Bool)
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
noncomputable def parseProgram : PolyProgram enc enc (parse read) := by
  have h : Poly (fun x : List Unit × List Bool => (x.1,(x.2,([] : List α)))) := by fun_prop
  have hv : Poly (List.reverse : List α → List α) := ⟨listReverse enc default⟩
  have g : Poly (fun x : State (α:=α) => (x.2.reverse,x.1)) := pair (Poly.comp hv snd) fst
  exact h.program.comp (foldProgram read P hrest) |>.comp g.program
end Generic
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
noncomputable def nearestRowsProgram : PolyProgram (encodePair ers er) ers (fun x : Rows × Row => nearestRows x.1 x.2) :=
  ((exchange ers er).comp (Nearest.fillingProgram.listMapWith [] [])).congr _ (fun _ => rfl)
noncomputable def rawProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode eo (raw r) := by
  let ds := Program.inputRaw.comp (fst ers Nat.bits)
  let H := (Program.inputRaw.comp (Program.rawPenaltyProgram r)).comp ratOfNat
  let ρ := Program.inputRaw.comp (lossProgram r)
  let y := Program.optimizeProgram r hr
  let tr := (ds.fanout H).comp Program.truncateMatrixProgram
  let xs := (tr.fanout y).comp nearestRowsProgram
  exact (((y.fanout ρ).comp openingProgram).fanout ((ds.fanout xs).comp assignmentsProgram)).congr _ (fun _ => rfl)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalListChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

noncomputable def validProgram : PolyProgram (encodePair eo Nat.bits) encodeBool (fun x : Output × ℕ => valid x.1 x.2) := by
  let a := fst eo Nat.bits
  let ys := a.comp (fst er ers)
  let xs := a.comp (snd er ers)
  let k := ((snd eo Nat.bits).comp ratOfNat).fanout (constant (encodePair eo Nat.bits) Ratio.encode 1) |>.comp ratAdd
  let yb := ys.comp (boundedProgram.listAll 0)
  let rowDom := (exchange er er).comp dominatedProgram
  let dom := (ys.fanout xs).comp (rowDom.listAllWith [])
  let one := ((ratSum.fanout (constant er Ratio.encode 1)).comp ratEQ).listAll []
  let sums := xs.comp one
  let cap := ((ys.comp ratSum).fanout k).comp ratLE
  exact (((((yb.fanout dom).comp boolAnd).fanout sums).comp boolAnd).fanout cap |>.comp boolAnd).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalSelectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

noncomputable def candidateProgram (r : ℕ) (hr : 0 < r) :
    PolyProgram (encodePair Input.encode Ratio.encode) Repair.eo (fun x : Input × ℚ => candidate r x.1 x.2) := by
  let test := ((constant (encodePair Input.encode Ratio.encode) Ratio.encode 0).fanout (snd Input.encode Ratio.encode)).comp ratLT
  exact (ite test ((fst Input.encode Ratio.encode).comp Input.zeroOutputProgram)
    (Input.scaleProgram.comp (Repair.rawProgram r hr))).congr _ (fun _ => by
      simp only [Function.comp_apply,candidate,decide_eq_true_eq])

noncomputable def valueOfProgram (r : ℕ) (hr : 0 < r) :
    PolyProgram (encodePair Input.encode Ratio.encode) Ratio.encode (fun x : Input × ℚ => Repair.value (candidate r x.1 x.2) x.1.rows) :=
  (((candidateProgram r hr).fanout ((fst Input.encode Ratio.encode).comp (Program.inputRaw.comp (fst ers Nat.bits)))).comp Repair.valueProgram).congr _ (fun _ => rfl)

noncomputable def feasibleProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode er (feasible r) := by
  let k := (fst Input.encode Ratio.encode).comp (Program.inputRaw.comp (snd ers Nat.bits))
  let test := (((candidateProgram r hr).fanout k).comp Repair.validProgram)
  let guesses := (Program.inputRaw.comp (fst ers Nat.bits)).comp guessesProgram
  let emptyI : Input := ⟨1,1,1,by decide,by decide,by decide,le_rfl,fun _ _ => 0⟩
  exact (((identity Input.encode).fanout guesses).comp (test.listFilterWith 0 emptyI)).congr _ (fun _ => rfl)

noncomputable def selectedScaleProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode Ratio.encode (selectedScale r) := by
  let xs := feasibleProgram r hr
  let values := (((identity Input.encode).fanout xs).comp ((valueOfProgram r hr).listMapWith 0 0))
  let v := values.comp Program.minimumProgram
  let ec := encodePair Input.encode Ratio.encode
  let I := (fst ec Ratio.encode).comp (fst Input.encode Ratio.encode)
  let q := snd ec Ratio.encode
  let C := (I.fanout q).comp (valueOfProgram r hr)
  let V := (fst ec Ratio.encode).comp (snd Input.encode Ratio.encode)
  let test := (C.fanout V).comp ratEQ
  let emptyI : Input := ⟨1,1,1,by decide,by decide,by decide,le_rfl,fun _ _ => 0⟩
  let filtered := ((((identity Input.encode).fanout v).fanout xs).comp (test.listFilterWith 0 (emptyI,0)))
  exact (filtered.comp Program.minimumProgram).congr _ (fun _ => rfl)

noncomputable def selectedProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode Repair.eo (selected r) :=
  ((((identity Input.encode).fanout (selectedScaleProgram r hr)).comp (candidateProgram r hr))).congr _ (fun _ => rfl)

end Scale
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem step_moment {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α)
    (j : Fin d) :
    (step v μ p hp next).moment (fun a => v a j)=
      μ.moment (fun a => p a*v (next a 0) j+(1-p a)*v (next a 1) j) :=
  ((μ.branch p hp next).compressAuto_correct v).2.2 j |>.trans
    (μ.branch_moment p hp next _)

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem run_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) (ht : t ≤ n) (f : Fin d → Fin (n+1)) :
    (run (d := d) p hp t).moment (fun q => monomial q f)=target p t f := by
  induction t generalizing f with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,monomial,flag,target]
  | succ t ih =>
    have htn : t<n := by omega
    have hh := (run (d := d) p hp t).step_moment (features (d := d))
      (fun _ => p ⟨t,htn⟩) (fun _ => hp ⟨t,htn⟩)
      (fun q b => endpoint q ⟨t,htn⟩ b) (finFunctionFinEquiv f)
    simp only [features_code] at hh
    rw [run,dite_eq_left htn]
    refine hh.trans ?_
    rw [target_succ p t htn f]
    by_cases hi : (⟨t,htn⟩ : Fin n) ∈ used f
    · rw [ite_eq_left hi]
      calc
        _ = (run (d := d) p hp t).moment
            (fun q => p ⟨t,htn⟩*monomial q (without f ⟨t,htn⟩)) := by
          apply SparseIntegerLaw.moment_congr
          intro a
          simp [monomial_endpoint,hi]
        _ = _ := by rw [SparseIntegerLaw.moment_mul,ih (by omega)]
    · rw [ite_eq_right hi]
      calc
        _ = (run (d := d) p hp t).moment (fun q => monomial q f) := by
          apply SparseIntegerLaw.moment_congr
          intro a
          simp only [monomial_endpoint,ite_eq_right hi]
          ring
        _ = _ := ih (by omega) f

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem bindCompress_spec {d : ℕ} (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (v : β → Fin d → ℚ) :
    let ν := μ.bindCompress κ v
    ν.length ≤ d+1 ∧
    (∀ i : Fin ν.length, ∃ a : Fin μ.length, ∃ b : Fin (κ a).length,
      ν.states[i.val]=(κ a).states[b.val]) ∧
    ∀ j, ν.moment (fun z => v z j)=
      ∑ a, μ.law.rational.weight a*(κ a).moment (fun z => v z j) := by
  have h := (μ.bindIndexed κ).compressAuto_correct v
  refine ⟨h.1,?_,fun j => (h.2.2 j).trans (bindIndexed_moment μ κ _)⟩
  intro i
  obtain ⟨b,hb⟩ := h.2.1 i
  let z := (finSigmaFinEquiv (n := fun a => (κ a).length)).symm b
  refine ⟨z.1,z.2,?_⟩
  exact hb.trans (by
    simp only [bindIndexed,Vector.getElem_ofFn]
    congr 3)

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

theorem run_terminal (β : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (a : Fin (run β p n).length) :
    ¬Active β (run β p n).states[a.val] := by
  rcases (run_invariants β p hp n a).2.2 with h | h
  · intro ha
    have hi := (pair β (run β p n).states[a.val] ha).property.1
    have hc := card_pos.mpr ⟨_,hi⟩
    omega
  · exact h

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_LastFractionProgram
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
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_StarActivationProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedTerminalProgram
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

end Terminal
end MetricKMedian.RoundingProgram
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

def kernel (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (a : Fin (SparseSignedPartial.run u p n).length) : SparseIntegerLaw (Vector ℚ n) :=
  RationalSignedTerminal.terminal u (SparseSignedPartial.run u p n).states[a.val]
    (SparseSignedPartial.run_invariants u p hp n a).1

def round (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) : SparseIntegerLaw (Vector ℚ n) :=
  (SparseSignedPartial.run u p n).bindCompress (kernel u p hp) features

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)

def Input.μ (x : Input) := SparseSignedRounding.round (SparseSignedPreparation.signed x.D x.c) x.p x.feasible

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedDataOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView indices)

def KernelInput.base (x : KernelInput) : BaseRaw :=
  (List.ofFn (fun e => setView (x.D e)),(List.ofFn x.q,(List.ofFn (fun j => setView (x.P j)),
    (List.ofFn x.y,(List.ofFn x.p,x.Δ)))))
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountListOperations
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
-- module Solutions.OAIQ035_KM.KMedian_Process_CountStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)
abbrev InputRaw := List Unit × List (Data Row)
abbrev ei : InputRaw → List Bool := Binary.Automatic.enc

def columnRaw {n : ℕ} (μ : SparseIntegerLaw ((Fin n → ℕ))) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map ListOperation.setView)
def Input.raw (x : Input) : InputRaw := (List.replicate x.n (),List.ofFn fun i => columnRaw (x.columns i))
abbrev Input.encode (x : Input) := ei x.raw
def Context.raw (c : Context) : InputRaw × ℕ := (c.input.raw,c.t)
abbrev Context.encode (c : Context) := encodePair ei Nat.bits c.raw
abbrev view (c : Context) (G : T c) := ListOperation.view G
abbrev State.encode := Bundle.encode Context.encode et view

noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.m)) := by
  let raw : PolyProgram (encodePair ei Nat.bits) encodeBool
      (fun x : InputRaw × ℕ => decide (x.2<x.1.2.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t < c.input.m)) := raw.recode Context.raw (fun _ => rfl)
    (fun c => by simp only [Context.raw,Input.raw,List.length_ofFn])
  exact (contextProgram Context.encode et view).comp ctx
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)
local notation "erB" => ListOperation.er

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  let raw : PolyProgram ei (encodePair (encodePair ei Nat.bits) (ed et))
      (fun x : InputRaw => ((x,0),(((1:ℤ),[(1:ℤ)]),[x.2.map (fun _ => x.1.map (fun _ => (0:ℕ)))]))) := by
    apply Binary.Automatic.Poly.program
    have hs : Binary.Automatic.Poly (fun x : InputRaw => x.2.map (fun _ => x.1.map (fun _ => (0:ℕ)))) := by
      apply Binary.Automatic.Poly.list_map
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
      · fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.start,SparseIntegerLaw.dirac,
      List.map_const',Input.raw,List.length_ofFn,List.map_replicate,
      Vector.toList_replicate,List.ofFn_const,view,ListOperation.view]
    rfl)

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.m :=
  ((snd (encodeList (fun _ : Unit => [])) (encodeList (ed erB))).comp (listLength (ed erB) ((1,[1]),[]))).recode
    Input.raw (fun _ => rfl) (fun x => by simp only [Function.comp_def,Input.raw,List.length_ofFn])

theorem input_bounds (x : Input) :
    x.n≤x.encode.length ∧ x.m≤x.encode.length ∧
    (∀ i, (x.columns i).length≤x.encode.length) ∧
    (∀ i, (x.columns i).law.denominator≤(2:ℤ)^x.encode.length) := by
  let L := x.encode.length
  have he : L=2*(encodeList (fun _ : Unit => []) x.raw.1).length+1+
      (encodeList (ed erB) x.raw.2).length := encodePair_length _ _ _
  have hn := EncodedList.length_le (fun _ : Unit => []) x.raw.1
  have hm := EncodedList.length_le (ed erB) x.raw.2
  simp only [Input.raw,List.length_ofFn,List.length_replicate] at hn hm he
  have hcol (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length≤L := by
    have h := EncodedList.member_length (ed erB) x.raw.2 (columnRaw (x.columns i))
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simp only [Input.raw] at h
    omega
  have hc (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length=
      2*(2*(Signed.encode (x.columns i).law.denominator).length+1+
        (encodeList Signed.encode (List.ofFn (x.columns i).law.numerator)).length)+1+
      (encodeList erB ((x.columns i).states.toList.map ListOperation.setView)).length := by
    simp only [columnRaw,ed,el,IntegerLaw.ListPivot.el,encodePair_length]
  refine ⟨by change x.n≤L; omega,by change x.m≤L; omega,?_,?_⟩
  · intro i
    have h := EncodedList.length_le Signed.encode (List.ofFn (x.columns i).law.numerator)
    simp only [List.length_ofFn] at h
    have hh := hcol i
    rw [hc i] at hh
    change (x.columns i).length≤L
    omega
  · intro i
    have hh := hcol i
    rw [hc i] at hh
    have hl : (Signed.encode (x.columns i).law.denominator).length≤L := by omega
    exact (le_abs_self _).trans ((Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) hl))

theorem entry_bound (x : Input) : ∀ i, ∀ a : Fin (x.columns i).length, ∀ h,
    (x.columns i).states[a.val] h≤2^x.encode.length := by
  intro i a h
  have he := encodePair_length (encodeList (fun _ : Unit => [])) (encodeList (ed erB)) x.raw
  have hcol := EncodedList.member_length (ed erB) x.raw.2 (columnRaw (x.columns i))
    (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hs := encodePair_length el (encodeList erB) (columnRaw (x.columns i))
  have hrow := EncodedList.member_length erB ((x.columns i).states.toList.map ListOperation.setView)
    (ListOperation.setView (x.columns i).states[a.val]) (by
      apply List.mem_map.mpr
      exact ⟨(x.columns i).states[a.val], by simp, rfl⟩)
  have hv := EncodedList.member_length Nat.bits (ListOperation.setView (x.columns i).states[a.val])
    ((x.columns i).states[a.val] h) (List.mem_ofFn.mpr ⟨h,rfl⟩)
  have hl : ((x.columns i).states[a.val] h).bits.length≤x.encode.length := by
    change x.encode.length=_ at he
    change (ed erB (columnRaw (x.columns i))).length=
      2*(el ((x.columns i).law.denominator,List.ofFn (x.columns i).law.numerator)).length+1+
        (encodeList erB ((x.columns i).states.toList.map ListOperation.setView)).length at hs
    change ((x.columns i).states[a.val] h).bits.length≤(erB (ListOperation.setView (x.columns i).states[a.val])).length at hv
    omega
  exact (NatBinary.le_two_pow_length _).trans (Nat.pow_le_pow_right (by decide) hl)

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BundleGeometryProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitRepresentativeProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_GridRoundingProgram
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


