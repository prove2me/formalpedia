-- Prove2me | Definitions.Def_OAIQ035K049
-- name    : OAIQ035K049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:10:39.07366+00:00
-- url     : https://prove2.me/theorems/48d04011-8b0f-4af5-ad04-6417a4d2c66e
-- title:
--   Definitions bundle OAIQ035K049 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 28 definitions, 1 instance and 1 theorem. The definitions and types are `OAI.MetricKMedian.LPBinary.Input.scaleProgram`, `OAI.MetricKMedian.LPBinary.Input.zeroOutputProgram`, `OAI.MetricKMedian.LPBinary.Program.rawContextProgram`, `OAI.MetricKMedian.LPBinary.Program.rawGradProgram`, `OAI.MetricKMedian.LPBinary.Program.rawInitialProgram`, `OAI.MetricKMedian.LPBinary.Program.rawPenaltyProgram`, `OAI.MetricKMedian.LPBinary.Program.rawRateProgram`, `OAI.MetricKMedian.LPBinary.Program.rawStepsProgram`, `OAI.MetricKMedian.LPBinary.Program.startProgram`, `OAI.MetricKMedian.LPBinary.Program.stepsProgram`, `OAI.MetricKMedian.LPBinary.Program.truncateMatrixProgram`, `OAI.MetricKMedian.LPBinary.Program.truncateRowProgram`, `OAI.MetricKMedian.LPBinary.Program.upperProgram`, `OAI.MetricKMedian.LPBinary.Repair.boundedProgram`, `OAI.MetricKMedian.LPBinary.Repair.lossProgram`, `OAI.MetricKMedian.LPBinary.Repair.openingProgram`, `OAI.MetricKMedian.LPBinary.Repair.weightsProgram`, `OAI.MetricKMedian.LPBinary.statePolynomial`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.Input.unit`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.sup`, `OAI.MetricKMedian.Reduction.Program.Branch.allowed`, `OAI.MetricKMedian.Reduction.Program.Branch.restricted`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.State.last`, `OAI.MetricKMedian.SparseCounts.Program.Input.start`, `OAI.MetricKMedian.SparseCounts.Program.State`, `OAI.MetricKMedian.SparseCounts.Program.State.increment`, `OAI.MetricKMedian.SparseCounts.Program.State.product`, `OAI.MetricKMedian.SparseEnumeratedBernoulli.law`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_TruncatedListCompiler`, `KMedian_Process_CountRunProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_ScaleListProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Sparse_SparseEnumeratedCount`, `KMedian_Sparse_SparsePreparedBudget`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K038`, `OAIQ035K039`, `OAIQ035K040`, `OAIQ035K042` and `OAIQ035K043` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K053`; the statements `OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq`, `OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail`; the proofs of `OAI.MetricKMedian.SparseCopyState.physical_count_tail`, `OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq`, `OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K038
import Definitions.Def_OAIQ035K039
import Definitions.Def_OAIQ035K040
import Definitions.Def_OAIQ035K042
import Definitions.Def_OAIQ035K043

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

namespace Program
open Binary Binary.PolyProgram
noncomputable def upperProgram : PolyProgram (encodePair Ratio.encode er) er (fun x : ℚ × Row => upper x.2 x.1) :=
  (listFilterWith ratLE 0 0).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function

noncomputable def truncateRowProgram : PolyProgram (encodePair Ratio.encode er) er (fun x : ℚ × Row => Truncated.row x.2 x.1) := by
  let t := snd Ratio.encode Ratio.encode
  let test := (t.fanout (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1)).comp ratLE
  let coord := ite test (fst Ratio.encode Ratio.encode) t
  exact (coord.listMapWith 0 0).congr _ (fun x => by simp only [Function.comp_apply,decide_eq_true_eq,Truncated.row])

noncomputable def truncateMatrixProgram : PolyProgram (encodePair ers Ratio.encode) ers (fun x : Rows × ℚ => Truncated.matrix x.1 x.2) :=
  ((exchange ers Ratio.encode).comp (truncateRowProgram.listMapWith [] [])).congr _ (fun _ => rfl)

end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function

namespace Program
noncomputable def rawPenaltyProgram (r : ℕ) : PolyProgram ei Nat.bits (rawPenalty r) := by
  let k := snd ers Nat.bits
  let p := (k.fanout (constant ei Nat.bits 1)).comp natAdd
  exact ((constant ei Nat.bits (4*r)).fanout p |>.comp natMul).congr _ (fun _ => rfl)
noncomputable def rawGradProgram (r : ℕ) : PolyProgram ei Nat.bits (rawGrad r) := by
  let ds := fst ers Nat.bits
  let n := (ds.comp (listHead er [])).comp (listLength Ratio.encode 0)
  let m := ds.comp (listLength er [])
  let mh := (m.fanout (rawPenaltyProgram r)).comp natMul
  exact ((n.fanout ((mh.fanout mh).comp natMul)).comp natMul).congr _ (fun x => by dsimp only [Function.comp_apply,rawGrad]; rw [pow_two])
noncomputable def rawRateProgram (r : ℕ) : PolyProgram ei Ratio.encode (rawRate r) := by
  let grad := (rawGradProgram r).comp ratOfNat
  let den := ((constant ei Ratio.encode (2*(r:ℚ))).fanout grad).comp ratMul
  exact (den.comp ratInv).congr _ (fun x => by simp only [Function.comp_apply,rawRate,one_div])
noncomputable def rawStepsProgram (r : ℕ) : PolyProgram ei Nat.bits (rawSteps r) := by
  let k := snd ers Nat.bits
  let kk := (k.fanout k).comp natMul
  let g := ((constant ei Nat.bits (8*r^2)).fanout (rawGradProgram r)).comp natMul
  exact ((g.fanout kk).comp natMul).congr _ (fun _ => by dsimp only [Function.comp_apply,rawSteps]; simp only [pow_two])
noncomputable def rawContextProgram (r : ℕ) : PolyProgram ei ec (rawContext r) :=
  ((fst ers Nat.bits).fanout (((rawPenaltyProgram r).comp ratOfNat).fanout (((snd ers Nat.bits).comp ratOfNat).fanout (rawRateProgram r)))).congr _ (fun _ => rfl)
noncomputable def rawInitialProgram : PolyProgram ei er rawInitial := by
  let ids := ((fst ers Nat.bits).comp (listHead er [])).comp (listIndices Ratio.encode 0)
  let k := (snd ers Nat.bits).comp ratOfNat
  let test := (snd Ratio.encode Nat.bits).comp natZero
  let coord := ite test (constant (encodePair Ratio.encode Nat.bits) Ratio.encode 0) (fst Ratio.encode Nat.bits)
  exact ((k.fanout ids).comp (coord.listMapWith 0 0)).congr _ (fun x => by simp only [Function.comp_apply,rawInitial,decide_eq_true_eq])
noncomputable def startProgram (r : ℕ) : PolyProgram Input.encode es (start r) :=
  (inputRaw.comp ((rawContextProgram r).fanout rawInitialProgram)).congr _ (fun _ => rfl)
noncomputable def stepsProgram (r : ℕ) : PolyProgram Input.encode Nat.bits (fun I => rawSteps r I.raw) :=
  (inputRaw.comp (rawStepsProgram r)).congr _ (fun _ => rfl)
end Program

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

noncomputable def statePolynomial (r : ℕ) : Polynomial ℕ :=
  2*(Program.startProgram r).sizeBound+1+X*(2*(3*heightPolynomial r+10)+1)

end MetricKMedian.LPBinary
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

noncomputable def openingProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => opening x.1 x.2) := by
  let y := snd Ratio.encode Ratio.encode
  let den := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1).fanout (fst Ratio.encode Ratio.encode)).comp ratSub
  let val := (y.fanout den).comp ratDiv
  let coord := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1).fanout val).comp Program.ratMin
  exact ((exchange er Ratio.encode).comp (coord.listMapWith 0 0)).congr _ (fun _ => rfl)
noncomputable def weightsProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => weights x.1 x.2) := by
  let test := ((fst Ratio.encode Ratio.encode).fanout (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1)).comp ratLE
  let coord := ite test (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 0) (snd Ratio.encode Ratio.encode)
  exact ((listZip Ratio.encode Ratio.encode 0 0).comp (coord.listMap (0,0))).congr _ (fun _ => by simp only [Function.comp_apply,weights,decide_eq_true_eq])
noncomputable def lossProgram (r : ℕ) : PolyProgram ei Ratio.encode (fun x : Rows × ℕ => TruncatedLP.loss r x.2) :=
  (((constant ei Ratio.encode (1+1/(r:ℚ))).fanout ((Program.rawPenaltyProgram r).comp ratOfNat)).comp ratDiv).congr _ (fun _ => rfl)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBernoulli
open Finset
variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

def law (enum : Fin n ≃ E) (q : E → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    SparseIntegerLaw (E → Bool) :=
  (SparseBernoulli.run (d := 4) (fun a => q (enum a)) (fun a => hq (enum a)) n).map
    (fun ω e => ω (enum.symm e))

end MetricKMedian.SparseEnumeratedBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw SparseGridRounding
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem raw_identity (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) :
    opening D c q Δ z=(n:ℚ)*(Δ:ℚ)+SparseSignedPreparation.raw D c (base q) z+
      ∑ j,discarded D q Δ z j := by
  have ht : ∀ j,(total D q Δ z j:ℚ)=(Δ:ℚ)-
      (min (∑ e,activationCount D q z e j) (Δ/2):ℕ) := by
    intro j
    exact Nat.cast_sub ((min_le_right _ _).trans (Nat.div_le_self _ _))
  simp only [opening,ht,raw_counts,discarded,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_sum]
  ring

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def Input.unit (z : Input) : RationalUnitInput.Program.Input :=
  ⟨count z.a z.k z.ha z.hj z.dc,z.j,unitInput z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds⟩
end MetricKMedian.Preparation.FractionalRefinement.Program
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

noncomputable def boundedProgram : PolyProgram Ratio.encode encodeBool bounded := by
  let lo := ((constant Ratio.encode Ratio.encode 0).fanout (identity Ratio.encode)).comp ratLE
  let hi := ((identity Ratio.encode).fanout (constant Ratio.encode Ratio.encode 1)).comp ratLE
  exact ((lo.fanout hi).comp boolAnd).congr _ (fun q => by simp only [Function.comp_apply,id_eq,bounded,Bool.decide_and])
end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_ScaleListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Input

noncomputable def scaleProgram : PolyProgram (encodePair Input.encode Ratio.encode) Input.encode (fun x : Input × ℚ => x.1.scale x.2) := by
  let coord := (exchange Ratio.encode Ratio.encode).comp ratDiv
  let matrix := (coord.listMapWith 0 0).listMapWith [] []
  let I := fst Input.encode Ratio.encode
  let B := snd Input.encode Ratio.encode
  let ds := I.comp (Program.inputRaw.comp (fst ers Nat.bits))
  let k := I.comp (Program.inputRaw.comp (snd ers Nat.bits))
  let raw := ((B.fanout ds).comp matrix).fanout k
  exact raw.recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_apply,id_eq]
    change ei ((x.1.rows.map (fun ds => ds.map (fun d => d/x.2))),x.1.k)=ei ((x.1.scale x.2).raw)
    rw [Input.raw,scale_rows]
    rfl)
end Input
end MetricKMedian.LPBinary
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
namespace Input
noncomputable def zeroOutputProgram : PolyProgram Input.encode Repair.eo Input.zeroOutput := by
  let rows := Program.inputRaw.comp (fst ers Nat.bits)
  let rowZero := (constant Ratio.encode Ratio.encode 0).listMap 0
  let mat := rows.comp (rowZero.listMap [])
  let row := (rows.comp (listHead er [])).comp rowZero
  exact (row.fanout mat).congr _ (fun I => by
    change (((I.rows.head?.getD []).map (fun _ => (0:ℚ))),I.rows.map (fun ds => ds.map (fun _ => (0:ℚ))))=I.zeroOutput
    have hi : I.rows.head?.getD []=List.ofFn (I.distance ⟨0,I.mpos⟩) := by
      dsimp only [Input.rows]
      rw [List.head?_eq_getElem?]
      simp only [List.getElem?_ofFn, I.mpos, dite_eq_left, Option.getD_some]
    rw [hi]
    simp only [Input.rows,List.map_ofFn,Function.comp_def,Input.zeroOutput,List.ofFn_const])
end Input
end MetricKMedian.LPBinary
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
abbrev State := Bundle T

def State.product (x : State) : State := ⟨x.ctx,x.law.prod (column x.ctx) (update x.ctx)⟩

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
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
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ _ => 0)⟩

end MetricKMedian.SparseCounts.Program
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

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def State.last (x : RoundingProgram.State false) : RoundingProgram.State false :=
  ⟨x.n,x.β,x.positive,x.μ.branch RationalLastFraction.probability RationalLastFraction.probability_unit RationalLastFraction.endpoint⟩
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open Program
variable {η τ : ℝ} (p : RationalAllParameters η τ)
def Input.sup (x : Input) : RationalSuppliers.Program.ScanInput :=
  letI := x.metric
  ⟨x.f,(x.U.representatives p.M).card,x.j,x.U.suppliers x.R p,x.U.df,x.U.dc,x.B⟩
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
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
open Enumeration
namespace Branch
def allowed (B : Branch) : Prop := B.original.k ≤ B.facilities.card
instance instDecidablePredAllowed : DecidablePred allowed := fun B => inferInstanceAs (Decidable (B.original.k≤B.facilities.card))
def restricted (B : Branch) (h : B.allowed) : Instance := B.original.restrictFacilities B.facilities h
end Branch
end MetricKMedian.Reduction.Program
end

end OAI
end


