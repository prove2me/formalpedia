-- Prove2me | Definitions.Def_OAIQ035K076
-- name    : OAIQ035K076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:28:38.666379+00:00
-- url     : https://prove2.me/theorems/7a48ea16-1b88-4cc3-9a0d-6c7d2123f2f9
-- title:
--   Definitions bundle OAIQ035K076 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 15 definitions and 9 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.coupled`, `OAI.MetricKMedian.Reduction.Program.Branch.allowedProgram`, `OAI.MetricKMedian.Reduction.Program.Branch.encode`, `OAI.MetricKMedian.Reduction.Program.Branch.restrictedData`, `OAI.MetricKMedian.Reduction.Program.Branch.restrictedProgram`, `OAI.MetricKMedian.Reduction.Program.Branch.view`, `OAI.MetricKMedian.Reduction.Program.allListProgram`, `OAI.MetricKMedian.Reduction.Program.branchListProgram`, `OAI.MetricKMedian.Reduction.Program.branchProgram`, `OAI.MetricKMedian.Reduction.Program.completionsData`, `OAI.MetricKMedian.Reduction.Program.endpointsData`, `OAI.MetricKMedian.Reduction.Program.goodProgram`, `OAI.MetricKMedian.Reduction.Program.ordinaryProgram`, `OAI.MetricKMedian.Reduction.Program.outcomesData`, `OAI.MetricKMedian.Reduction.Program.selectedProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Preparation_RationalSupplierScan`, `KMedian_Programs_BranchProgram`, `KMedian_Reduction_DeletionProgram`, `KMedian_Reduction_OrdinaryListProgram`, `KMedian_Reduction_ReductionOutcomesProgram`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundle `OAIQ035K075` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec` and `OAI.MetricKMedian.main_finite_work`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K075

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

noncomputable def coupled (heven : Even qR.Δ) := RationalSuppliers.coupled D.y D.P D.A D.p D.c D.γ qR.g qR.Δ
  D.hy D.hp D.hP D.hm D.hc D.hc0 D.hc1 D.hunit D.hγ D.hγ1 (FixedParameters.positive qR) heven (FixedParameters.grid qR)

end Data
end MetricKMedian.Preparation.RationalSuppliers
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
open Preparation.RationalNearest.MaskProgram (erase erase_view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration

 theorem valuesData_view (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    valuesData c (view I,setView T)=values I T c := by
  simp only [valuesData,choicesRaw_choices,List.flatMap_map,Preparation.RationalUnitInput.Program.ranks_view,List.map_ofFn,
    Function.comp_def,diff_view,erase_view,costData_view,values]

def endpointsData (c : ℕ) (x : Raw × Row) : Table :=
  (0::valuesData c x).map (fun B => historyData c ((x.1,B),x.2))
@[fun_prop] theorem endpointsData_poly (c : ℕ) : Poly (endpointsData c) := by
  unfold endpointsData
  apply list_map
  · fun_prop
  · have h := comp (list_cons (α := ℚ)) (pair (const 0 : Poly (fun _ : Raw × Row => (0:ℚ))) (valuesData_poly c))
    exact h
 theorem endpointsData_view (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    endpointsData c (view I,setView T)=(endpoints I T c).map setView := by
  simp only [endpointsData,valuesData_view,endpoints,List.map_map,Function.comp_def,historyData_view]
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
def completionsData (δ : ℚ) (b : ℕ) (x : Raw × (Row × Row)) : Table :=
  (choicesRaw b x.2.2).flatMap (fun H => (choicesRaw b x.2.1).map (fun B =>
    completionData (((x.1,(x.2.1,B)),(radiiData (x.1,x.2.2),δ)),diff (x.2.2,H))))
@[fun_prop] theorem completionsData_poly (δ : ℚ) (b : ℕ) : Poly (completionsData δ b) := by
  unfold completionsData; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
 theorem completionsData_view (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    completionsData δ b (view I,(setView F,setView U))=(completions I F U δ b).map setView := by
  simp only [completionsData,choicesRaw_choices,List.flatMap_map,List.map_map,Function.comp_def,diff_view,radiiData_view,
    completionData_view,completions,List.map_flatMap]

def outcomesData (δ : ℚ) (c b : ℕ) (x : Raw × (Row × Row)) : Table :=
  x.2.2::(endpointsData c (x.1,x.2.2)).flatMap (fun U => U::completionsData δ b (x.1,(x.2.1,U)))
@[fun_prop] theorem outcomesData_poly (δ : ℚ) (c b : ℕ) : Poly (outcomesData δ c b) := by
  unfold outcomesData
  have h : Poly (fun x : (Raw × (Row × Row)) × Row => x.2::completionsData δ b (x.1.1,(x.1.2.1,x.2))) := by
    have hh := comp (list_cons (α := Row)) (pair (snd : Poly (fun x : (Raw × (Row × Row)) × Row =>x.2))
      (show Poly (fun x : (Raw × (Row × Row)) × Row => completionsData δ b (x.1.1,(x.1.2.1,x.2))) from by fun_prop))
    exact hh
  have hh : Poly (fun x : Raw × (Row × Row) => (endpointsData c (x.1,x.2.2)).flatMap (fun U => U::completionsData δ b (x.1,(x.2.1,U)))) := by
    apply list_flatMap <;> fun_prop
  have hhh := comp (list_cons (α := Row)) (pair (show Poly (fun x : Raw × (Row × Row) => x.2.2) from by fun_prop) hh)
  exact hhh
 theorem outcomesData_view (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    outcomesData δ c b (view I,(setView F,setView T))=(outcomes I F T δ c b).map setView := by
  simp only [outcomesData,endpointsData_view,List.flatMap_map,completionsData_view,outcomes,List.map_cons,List.map_flatMap]
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
namespace Branch
def view (B : Branch) : Raw × Row := (InstanceProgram.view B.original,setView B.facilities)
def encode (B : Branch) : List Bool := enc B.view
noncomputable def allowedProgram : PolyProgram encode encodeBool (fun B => decide B.allowed) :=
  (by fun_prop : Poly (fun x : Raw × Row => decide (x.1.2.1 ≤ card x.2))).program.recode view (fun _ => rfl) (fun B => by
    apply congrArg encodeBool
    simp only [view,InstanceProgram.view,card_view,allowed]
    rfl)
def restrictedData (x : Raw × Row) : Raw := ((x.1.1.1,x.2),x.1.2)
@[fun_prop] theorem restrictedData_poly : Poly restrictedData := by unfold restrictedData; fun_prop
 theorem restrictedData_view (B : Branch) (h : B.allowed) : restrictedData B.view=InstanceProgram.view (B.restricted h) := rfl
noncomputable def restrictedProgram : PolyProgram (fun B : {B : Branch // B.allowed} => encode B.val) InstanceProgram.encode
    (fun B => B.val.restricted B.property) :=
  restrictedData_poly.program.recode
    (fun B : {B : Branch // B.allowed} => B.val.view) (fun _ => rfl)
    (fun B => congrArg enc (restrictedData_view B.val B.property))
end Branch
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
noncomputable def goodProgram : PolyProgram (fun B : {B : Branch // B.allowed} => Branch.encode B.val)
    (enc : Table → List Bool) (fun B => (outcomes B.val.original B.val.facilities
      ((B.val.restricted B.property).computedPseudo r hr p c) δ c b).map setView) :=
  (((identity enc).recode (fun B : {B : Branch // B.allowed} => B.val.view) (fun _ => rfl) (fun _ => rfl)).fanout
    (Branch.restrictedProgram.comp (InstanceProgram.pseudoProgram r hr p c)) |>.comp
      (by fun_prop : Poly (fun x : (Raw × Row) × Row => outcomesData δ c b (x.1.1,(x.1.2,x.2)))).program).congr
      _ (fun B => outcomesData_view B.val.original B.val.facilities _ δ c b)
noncomputable def branchProgram : PolyProgram Branch.encode (enc : Table → List Bool)
    (fun B => (branchOut r hr p c b δ B).map setView) :=
  (dependentIfTotal Branch.allowed Branch.allowedProgram (fun _ _ => ([] : Table))
    (fun B h => (outcomes B.original B.facilities ((B.restricted h).computedPseudo r hr p c) δ c b).map setView)
    (constant _ enc []) (goodProgram r hr p c b δ)).congr _ (by
      intro B
      unfold branchOut
      split_ifs <;> rfl)
noncomputable def branchListProgram : PolyProgram InstanceProgram.encode (encodeList Branch.encode) (branchList a) :=
  (by
    have h : Poly (fun x : Raw => (branchesData a (x,x.1.2)).map (fun F => (x,F))) := by
      apply list_map <;> fun_prop
    exact h.program.recode InstanceProgram.view (fun _ => rfl) (fun I => by
      unfold branchList
      change encodeList enc ((branchesData a (view I,setView I.facilities)).map (fun F => (view I,F)))=_
      rw [branchesData_view]
      simp only [encodeList_map,List.map_map,Function.comp_def,Branch.encode,Branch.view]))
noncomputable def allListProgram : PolyProgram InstanceProgram.encode (enc : Table → List Bool)
    (fun I => (allList r hr p c a b δ I).map setView) :=
  ((branchListProgram a).comp ((branchProgram r hr p c b δ).listMapTotal) |>.comp
    (listFlatten enc ([] : Row))).congr _ (by
      intro I
      simp only [Function.comp_def,branchList,List.map_map,List.flatMap,allList,List.map_flatten])
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_OrdinaryListProgram
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
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
noncomputable def selectedProgram : PolyProgram InstanceProgram.encode (enc : Row → List Bool)
    (fun I => setView (selectList I (allList r hr p c a b δ I))) :=
  ((((identity enc).recode view (fun _ => rfl) (fun _ => rfl)).fanout (allListProgram r hr p c a b δ)).comp
    selectData_poly.program).congr _ (fun I => selectData_view I _)
noncomputable def ordinaryProgram : PolyProgram InstanceProgram.encode (enc : Row → List Bool)
    (fun I => setView (ordinarySet r hr p c a b δ I)) :=
  (PolyProgram.ite InstanceProgram.zeroTestProgram (selectedProgram r hr p c a b δ)
    InstanceProgram.zeroOutputProgram).congr _ (by
      intro I
      unfold ordinarySet
      by_cases h : I.zeroTest <;> simp [h])
end MetricKMedian.Reduction.Program
end

end OAI
end


