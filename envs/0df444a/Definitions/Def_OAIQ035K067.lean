-- Prove2me | Definitions.Def_OAIQ035K067
-- name    : OAIQ035K067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:18:32.621483+00:00
-- url     : https://prove2.me/theorems/f3d1d89a-36e3-428b-a107-96d79fa3935f
-- title:
--   Definitions bundle OAIQ035K067 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 23 definitions and 27 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.geometryProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.repInputProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.repProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.supplierRawProgram`, `OAI.MetricKMedian.Reduction.Enumeration.maskWord`, `OAI.MetricKMedian.RoundingProgram.Terminal.result`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.lastProgram`, `OAI.MetricKMedian.SparseGridRounding.Program.cardinalInputProgram`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input.raw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.ker`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.kernels`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.result`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.encode`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.result`, `OAI.MetricKMedian.SparseSignedPreparation.Program.bernoulliInputProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.signedInputProgram`, `OAI.MetricKMedian.SparseSignedPreparation.Program.starInputProgram`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.encode`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.raw`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.result`, `OAI.MetricKMedian.SparseStarActivation.Program.columnsProgram`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input.encode`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input.result`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Process_CountListOperations`, `KMedian_Process_CountRunHeight`, `KMedian_Process_CountRunProgram`, `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitGeometryProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseStarActivation`, `KMedian_Sparse_SparseTargetSubset`, `KMedian_Sparse_SparseWeightedPartial`, `KMedian_Sparse_SparseWeightedRounding`.
--
--   **Imports.** It imports the bundles `OAIQ035K061`, `OAIQ035K062` and `OAIQ035K063` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K069`, `OAIQ035K070` and `OAIQ035K071`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K061
import Definitions.Def_OAIQ035K062
import Definitions.Def_OAIQ035K063

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseWeightedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

 theorem run_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (i : Fin n) :
    (run β hβ p t).moment (fun q => point q i)=point p i := by
  induction t with
  | zero => exact SparseIntegerLaw.dirac_moment _ _
  | succ t ih => rw [run,step_mean,ih]

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseWeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedRounding
open Finset RationalWeightedStep SparseWeightedPartial
variable {n : ℕ}

theorem round_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (i : Fin n) :
    (round β hβ p).moment (fun q => point q i)=point p i := by
  have hh := (run β hβ p n).step_moment features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint
    (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (((run β hβ p n).moment_congr _ _
    (fun a => RationalLastFraction.endpoint_mean _ i)).trans (run_mean β hβ p n i))

end MetricKMedian.SparseWeightedRounding
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

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

 theorem lastRaw_state (x : RoundingProgram.State false) : lastRaw x.raw=(State.last x).raw := by
  change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData _)
  apply congrArg (fun d => (List.ofFn x.β,d))
  exact vectorData_branch x.μ _ RationalLastFraction.probability_unit _ RoundingList.Last.probability
    (RoundingList.Last.endpoint false) (RoundingList.Last.endpoint true)
    RoundingList.Last.probability_list (fun p => RoundingList.Last.endpoint_list p 0)
    (fun p => RoundingList.Last.endpoint_list p 1)
noncomputable def lastProgram : PolyProgram RoundingProgram.State.encode RoundingProgram.State.encode State.last :=
  lastRaw_poly.program.recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun x => by
    rw [lastRaw_state]
    exact RoundingProgram.State.encode_raw _)

end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTargetSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

theorem mean (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) (i : Fin n) :
    (law D q).moment (fun S => if i∈S then 1 else 0)=if i∈D then q else 0 := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (vectors D q).moment (fun p => point p i) :=
      SparseIntegerLaw.moment_congr _ _ _ (fun a =>
        SparseCardinalRounding.selected_indicator _ (integral D hq a) i)
    _ = point (initial D q) i := SparseWeightedRounding.round_mean _ _ _ _
    _ = _ := point_initial D q i

theorem subset (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) : (law D q).states[a.val] ⊆ D := by
  intro i hi
  by_contra hn
  exact (law D q).zero_indicator (fun S => i∈S)
    (by rw [mean D hq i,ite_eq_right hn]) a (positive D q a) hi

theorem fixed (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) :
    (q=0 → (law D q).states[a.val]=∅) ∧ (q=1 → (law D q).states[a.val]=D) := by
  constructor
  · intro hq0
    apply eq_empty_iff_forall_notMem.mpr
    intro i
    exact (law D q).zero_indicator (fun S => i∈S)
      (by rw [mean D hq i,hq0]; split_ifs <;> rfl) a (positive D q a)
  · intro hq1
    apply Subset.antisymm (subset D hq a)
    intro i hi
    exact (law D q).one_indicator (fun S => i∈S)
      (by rw [mean D hq i,ite_eq_left hi,hq1]) a (positive D q a)

theorem count_error (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) :
    |(((law D q).states[a.val]).card:ℚ)-(D.card:ℚ)*q| ≤ 1 := by
  have hh := (SparseWeightedRounding.round_invariants (fun _ => 1) (fun _ => by norm_num)
    (initial D q) (initial_unit D hq) (show (0:ℚ) ≤ 1 by norm_num) (fun _ => le_rfl) a).2
  simp only [one_mul] at hh
  have hsum : (∑ i, point (initial D q) i)=(D.card:ℚ)*q := by
    simp only [point_initial,sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul]
  have hcard : (((law D q).states[a.val]).card:ℚ)=
      ∑ i, point (vectors D q).states[a.val] i := by
    have he := SparseIntegerLaw.map_states (vectors D q) SparseCardinalRounding.selected a
    change (law D q).states[a.val]=_ at he
    rw [he]
    calc
      _ = ∑ i, if i∈SparseCardinalRounding.selected (vectors D q).states[a.val] then (1:ℚ) else 0 := by simp
      _ = _ := sum_congr rfl (fun i _ =>
        SparseCardinalRounding.selected_indicator _ (integral D hq a) i)
  rw [hcard]
  rwa [hsum] at hh

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
abbrev Input.encode (x : Input) := enc x.raw

 theorem prepare_input (x : Input) : prepare x.raw=x.weighted.raw := by
  simp only [prepare,Input.raw,setView,List.map_ofFn,Function.comp_def,Input.weighted,RoundingProgram.Input.raw,
    initial,Vector.toList_ofFn,decide_eq_true_eq]

def Input.result (x : Input) := SparseGraph.Program.columnRaw (law x.D x.q)
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseStarActivation
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

theorem columns (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (a : Fin (law D q).length) (e : Fin m) :
    let S := (law D q).states[a.val] e
    S ⊆ D e ∧ |(S.card:ℚ)-((D e).card:ℚ)*q e| ≤ 1 ∧
      (q e=0 → S=∅) ∧ (q e=1 → S=D e) := by
  apply SparseGraph.run_columns (fun e => SparseTargetSubset.law (D e) (q e))
    (fun e S => S ⊆ D e ∧ |(S.card:ℚ)-((D e).card:ℚ)*q e| ≤ 1 ∧
      (q e=0 → S=∅) ∧ (q e=1 → S=D e))
    (fun e b => ⟨SparseTargetSubset.subset (D e) (hq e) b,
      SparseTargetSubset.count_error (D e) (hq e) b,
      SparseTargetSubset.fixed (D e) (hq e) b⟩) m (le_refl m) a e e.isLt

theorem upper_domination (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (a : Fin (law D q).length) (e : Fin m) (i : Fin n) :
    (if i∈(law D q).states[a.val] e then (1:ℚ) else 0) ≤ upper (q e) := by
  by_cases he : 0 < q e
  · simp only [upper,ite_eq_left he]
    split_ifs <;> norm_num
  · have hz : q e=0 := le_antisymm (le_of_not_gt he) (hq e).1
    rw [(columns D q hq a e).2.2.1 hz]
    simp only [notMem_empty,ite_false,upper,ite_eq_right he,le_refl]

end MetricKMedian.SparseStarActivation
end
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
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),List.ofFn x.q))
abbrev Input.encode (x : Input) := enc x.raw

 theorem prepare_input (x : Input) : prepare x.raw=x.columns.map SparseTargetSubset.Program.Input.raw := by
  simp only [prepare,Input.raw,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,Input.columns]
  rfl
noncomputable def columnsProgram : PolyProgram Input.encode (encodeList SparseTargetSubset.Program.Input.encode) Input.columns :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    change encodeList enc (prepare x.raw)=_
    rw [prepare_input,RoundingProgram.encodeList_map])

def Input.result (x : Input) : Data Table :=
  (((law x.D x.q).law.denominator,List.ofFn (law x.D x.q).law.numerator),
    (law x.D x.q).states.toList.map SparseGraph.ListOperation.view)
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

 theorem boolState_list {n : ℕ} (u : Fin n → ℚ) (p : Vector ℚ n) (q : Fin n → Bool) :
    boolState ((List.ofFn u,p.toList),List.ofFn q)=(RationalSignedTerminal.state u p q).toList := by
  rw [point_toList]
  apply List.ext_getElem
  · simp only [boolState,List.length_map,List.length_range,List.length_ofFn,Vector.length_toList]
  · intro i hi hi'
    have hi'' : i<n := by simpa only [boolState,List.length_map,List.length_range,List.length_ofFn] using hi
    simp only [boolState,List.getElem_map,List.getElem_range,List.getElem?_ofFn,dite_eq_left hi'',Option.getD_some,
      RationalSignedTerminal.state,Vector.toList_ofFn,List.getElem_ofFn,SparseBernoulli.flag]

def result (x : Input true) : Data Row :=
  let μ := RationalSignedTerminal.terminal x.β x.p x.feasible
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)

end Terminal
end MetricKMedian.RoundingProgram
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
abbrev KernelInput.encode (x : KernelInput) := enc x.raw

noncomputable def starInputProgram : PolyProgram KernelInput.encode SparseStarActivation.Program.Input.encode KernelInput.star :=
  (identity enc).recode KernelInput.raw (fun _ => rfl) (fun x => by
    simp only [SparseStarActivation.Program.Input.encode,SparseStarActivation.Program.Input.raw,
      KernelInput.star,point_list]; rfl)
noncomputable def bernoulliInputProgram : PolyProgram KernelInput.encode SparseBernoulli.Program.Input.encode KernelInput.bernoulli :=
  ((snd enc enc).comp (snd enc enc)).recode KernelInput.raw (fun _ => rfl) (fun x => by
    simp only [SparseBernoulli.Program.Input.encode,KernelInput.bernoulli,point_list]; rfl)

def KernelInput.result (x : KernelInput) : Data StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (kernel x.D x.p x.feasible)).1,(kernel x.D x.p x.feasible).states.toList.map view)
 theorem kernel_raw (x : KernelInput) :
    attach (x.p.toList,prodData (x.star.result,
       (((SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.denominator,
         List.ofFn (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.numerator),
       (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).states.toList.map List.ofFn)))=x.result := by
  simp only [KernelInput.star,SparseStarActivation.Program.Input.result,attach,prodData,
    KernelInput.result,kernel,SparseIntegerLaw.BinarySparse.raw,SparseIntegerLaw.prod,
    states_list,List.flatMap_def,List.map_ofFn,Function.comp_def,
    RoundingList.ofFn_product,Vector.toList_ofFn,view]
  rfl

 theorem beta_input (x : Input) : beta x.raw=List.ofFn (SparseSignedPreparation.signed x.D x.c) := by
  simp only [beta,Input.raw,SparseGraph.ListOperation.indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  congr 1
  funext e
  rw [Completion.Rational.BestProgram.card_view]
  rfl
noncomputable def signedInputProgram : PolyProgram Input.encode RoundingProgram.Input.encode Input.signed := by
  let p : PolyProgram enc enc (fun x : Raw => (beta x,x.2.2.2)) := Poly.program (by fun_prop)
  exact p.recode Input.raw (fun _ => rfl) (fun x => by
    change enc (beta x.raw,x.p.toList)=_
    rw [beta_input]; rfl)

def Input.ker (x : Input) (i : Fin x.μ.length) : KernelInput :=
  ⟨x.n,x.m,x.D,x.μ.states[i.val],
    (SparseSignedRounding.round_invariants (SparseSignedPreparation.signed x.D x.c) x.p x.feasible (fun e _ =>
      (sub_le_self _ (Nat.cast_nonneg _)).trans (x.c_unit e).2) i).1⟩
def Input.kernels (x : Input) := List.ofFn x.ker

def Input.result (x : Input) : Data StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.p x.feasible x.c_unit)).1,
    (law x.D x.c x.p x.feasible x.c_unit).states.toList.map view)
theorem result_bind (x : Input) : x.result=
    ((SparseIntegerLaw.BinarySparse.raw (x.μ.bindIndexed (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible))).1,
      (x.μ.bindIndexed (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible)).states.toList.map view) := rfl
 theorem bind_result (x : Input) :
    bindData ((SparseIntegerLaw.BinarySparse.raw x.μ).1,x.kernels.map KernelInput.result)=x.result := by
  rw [result_bind]
  unfold Input.kernels
  simp only [List.map_ofFn,Function.comp_def,KernelInput.result,Input.ker]
  exact bindData_raw x.μ (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible) view

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

theorem activationData_view (x : KernelInput) (e : Fin x.m) (j : Fin x.n) :
    activationData x.raw e.val j.val=SparseOuterLaw.activationCount x.D x.q x.z e j := by
  simp only [activationData,KernelInput.raw,KernelInput.base,SparseSignedPreparation.Program.view,
    SparseGraph.ListOperation.view,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    decide_eq_true_eq,Fin.eta,SparseOuterLaw.activationCount,SparseGridRounding.base]

theorem totalData_view (x : KernelInput) (j : Fin x.n) :
    totalData x.raw j.val=total x.D x.q x.Δ x.z j := by
  unfold totalData
  simp only [KernelInput.raw,KernelInput.base,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change x.Δ-min ((List.ofFn (fun e => activationData x.raw e.val j.val)).sum) (x.Δ/2)=_
  simp only [activationData_view,List.sum_ofFn,total]

theorem pieces_view (x : KernelInput) : pieces x.raw=
    List.ofFn (fun j => List.ofFn (fun i => SparseRescaledInner.piece x.P x.y x.p (total x.D x.q x.Δ x.z) i j)) := by
  simp only [pieces,KernelInput.raw,KernelInput.base,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,setView,decide_eq_true_eq,Fin.eta]
  change (List.ofFn (fun j : Fin x.n => List.ofFn (fun i : Fin x.f => if i∈x.P j then
    (totalData x.raw j.val:ℚ)*x.y i/x.p j else 0)))=_
  simp only [totalData_view,SparseRescaledInner.piece]
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)

 theorem targetsData_view {f n : ℕ} (S : Data f n) :
    targetsData (supplierView S)=List.ofFn (fun e => setView (D S.A e)) := by
  rw [show (fun e => setView (D S.A e))=(fun e => setView (SupplierStars.targets S.A (index e))) by rfl,ofFn_star (fun e => setView (SupplierStars.targets S.A e))]
  simp only [targetsData,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    List.flatMap_def,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,SupplierStars.targets,
    setView,mem_filter,mem_univ,true_and,mem_singleton]
  simp only [Fin.val_inj]

 theorem flagsData_view {f n : ℕ} (S : Data f n) : flagsData (supplierView S)=List.ofFn (a (f:=f) (n:=n)) := by
  change _=List.ofFn (fun e => flagQ (index e))
  rw [ofFn_star]
  simp only [flagsData,supplierView,List.flatMap_def,List.map_ofFn,Function.comp_def,flagQ]

end MetricKMedian.Preparation.RationalSuppliers.Program
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

 theorem featureList_view {n m : ℕ} (G : SparseCounts.Table n m) :
    featureList (List.replicate n (),view G)=List.ofFn (features G) := by
  simp only [featureList,edges_view,RoundingList.features,List.flatMap_def,List.map_ofFn,
    Function.comp_def,RoundingList.ofFn_product]
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i
    have hi : (Fin.castAdd ((n*m)*(n*m)) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inl i) := rfl
    change edgeCode G i = features G (Fin.castAdd ((n*m)*(n*m)) i)
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inl]
  · congr 1; funext i
    have hi : (Fin.natAdd (n*m) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inr i) := by apply Fin.ext; simp [finSumFinEquiv]
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inr]

end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseCounts
open Binary
variable {n m : ℕ}

theorem denominator_height (ν : Fin m → SparseIntegerLaw (Fin n → ℕ)) (N L H : ℕ)
    (hN : ∀ i, (ν i).length≤N) (hL : ∀ i, (ν i).law.denominator≤(2:ℤ)^L)
    (hν : ∀ i, ∀ a : Fin (ν i).length, ∀ h, (ν i).states[a.val] h≤2^H) (t : ℕ) :
    (run ν t).law.denominator≤(2:ℤ)^(stepHeight n m N L H*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      let μ := run ν t
      let ρ := μ.prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)
      have hr : ∀ a : Fin ρ.length, ∀ i h,ρ.states[a.val] i h≤2^H := by
        apply SparseIntegerLaw.prod_property μ (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩) (fun G => ∀ i h,G i h≤2^H)
        intro a b
        exact next_bound _ _ _ _ (run_bound ν _ hν t a) (hν _ b)
      have hc := ρ.compressAuto_denominator features (H+H)
        (fun i a => (features_height ρ.states[i.val] H (hr i) a).1)
        (fun i a => (features_height ρ.states[i.val] H (hr i) a).2)
      have hrD : ρ.law.denominator=μ.law.denominator*(ν ⟨t,ht⟩).law.denominator := rfl
      have hrN : ρ.length ≤ (n*m+(n*m)*(n*m)+1)*N :=
        Nat.mul_le_mul (run_length ν t) (hN _)
      change (ρ.compressAuto features).law.denominator≤_
      apply hc.trans
      rw [hrD]
      calc
        _ ≤ ((2:ℤ)^(stepHeight n m N L H*t)*(2:ℤ)^L)*
            (2:ℤ)^((2*(n*m+(n*m)*(n*m)+1)*(n*m+(n*m)*(n*m)+1+
              (H+H)*((n*m+(n*m)*(n*m)+1)*N+1)))*
              ((n*m+(n*m)*(n*m)+1)*N+1)*((n*m+(n*m)*(n*m)+1)*N)) := by
          gcongr
          · exact (ν ⟨t,ht⟩).law.denominator_pos.le
          · exact hL _
          · norm_num
        _ = _ := by rw [← pow_add,← pow_add]; congr 1; simp only [stepHeight]; ring
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))
end MetricKMedian.SparseCounts
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

theorem state_size (x : Input) (t : ℕ) (ht : t≤x.m) :
    (State.encode (x.state t)).length≤ sizePolynomial.eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hm,hN,hD⟩ := input_bounds x
  have htL : t≤L := ht.trans hm
  have hc : (Context.encode ⟨x,t⟩).length≤3*L+2 := by
    have hbits : t.bits.length≤t+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
    change (encodePair Input.encode Nat.bits (x,t)).length≤_
    rw [encodePair_length]
    change 2*L+1+t.bits.length≤_
    omega
  have hsupport : (x.state t).law.length≤ supportBound L := by
    apply (run_length x.columns t).trans
    unfold supportBound
    gcongr
  have hheight : SparseCounts.stepHeight x.n x.m L L L*t≤heightBound L := by
    unfold heightBound SparseCounts.stepHeight
    dsimp only
    gcongr
  have hden : (x.state t).law.law.denominator≤(2:ℤ)^(heightBound L) :=
    (denominator_height x.columns L L L hN hD (entry_bound x) t).trans (pow_le_pow_right₀ (by norm_num) hheight)
  have hr (S : Fin x.n → ℕ) (hS : ∀ i,S i≤2^L) : (erB (ListOperation.setView S)).length≤L*(2*(L+1)+1) := by
    have h := EncodedList.length_bound Nat.bits (ListOperation.setView S) (L+1) (by
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact NatBinary.length_le_height (hS i))
    simp only [ListOperation.setView,List.length_ofFn] at h
    exact h.trans (Nat.mul_le_mul_right _ hn)
  have hs (a : Fin (run x.columns t).length) :
      (et (ListOperation.view (run x.columns t).states[a.val])).length≤graphSize L := by
    have hg := run_bound x.columns (2^L) (entry_bound x) t a
    have h := EncodedList.length_bound erB (ListOperation.view (run x.columns t).states[a.val]) (L*(2*(L+1)+1)) (by
      intro row hrow
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
      exact hr _ (hg i))
    simp only [ListOperation.view,List.length_ofFn] at h
    apply h.trans
    unfold graphSize
    gcongr
  have hb := SparseIntegerLaw.encode_length_bound (fun G : SparseCounts.Table x.n x.m => et (ListOperation.view G))
    (run x.columns t) (supportBound L) (heightBound L) (graphSize L) hsupport hden (fun i => hs _)
  have he : State.encode (x.state t)=encodePair Context.encode
      (SparseIntegerLaw.BinarySparse.encode (fun G : SparseCounts.Table x.n x.m => et (ListOperation.view G)))
        (⟨x,t⟩,run x.columns t) := by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.state,view,
      SparseIntegerLaw.BinarySparse.encode,SparseIntegerLaw.BinarySparse.raw,ed,encodePair,RoundingProgram.encodeList_map]
  rw [sizePolynomial_eval,he,encodePair_length]
  unfold sizeBound
  dsimp only at ⊢
  simp only [L] at hc hb ⊢
  omega

end MetricKMedian.SparseCounts.Program
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
 theorem values_view {f j : ℕ} (U : RationalUnitInput f j) : values (view U)=List.ofFn U.V := by
  simp only [values,view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,decide_eq_true_eq,List.sum_ofFn,← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rfl

 theorem repData_view (M : ℚ) (x : Input) : repData M x.raw=(x.rep M).raw := by
  unfold repData
  rw [show values x.raw=List.ofFn x.U.V from values_view x.U]
  simp only [Input.rep,RationalRepresentatives.Program.Input.raw,Input.raw,view,setView,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (decide_eq_true (Finset.mem_univ i)).symm

noncomputable def repInputProgram (M : ℚ) : PolyProgram Input.encode RationalRepresentatives.Program.Input.encode (Input.rep M) :=
  (repData_poly M).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (repData_view M x))
noncomputable def repProgram (M : ℚ) : PolyProgram Input.encode (enc : Row → List Bool)
    (fun x => setView (x.U.representatives M)) :=
  (repInputProgram M |>.comp RationalRepresentatives.Program.program).congr _ (fun _ => rfl)

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

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
def maskWord (x : Row × List ℕ) : Row := (indices x.1).map (fun i => (x.2.map (fun a => decide (a=i))).any id)
end MetricKMedian.Reduction.Enumeration
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
 theorem fractionRow_list {n : ℕ} (q : Fin n → ℚ) : fractionRow (List.ofFn q)=(fraction q).toList := by
  simp only [fractionRow,List.map_ofFn,fraction,base,Function.comp_def,Vector.toList_ofFn]
noncomputable def cardinalInputProgram : PolyProgram Input.encode SparseCardinalRounding.Program.encodeInput Input.cardinal :=
  fractionRow_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    rw [fractionRow_list]
    change enc ((fraction x.q).toList)=enc (List.ofFn (RationalWeightedStep.point (fraction x.q)))
    rw [ofFn_point])

end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),(List.ofFn x.c,List.ofFn x.q)))
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitGeometryProgram
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

noncomputable def geometryProgram (M : ℚ) : PolyProgram Input.encode enc
    (fun x => geometryData (x.raw,setView (x.U.representatives M))) :=
  ((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl) |>.fanout (repProgram M)).comp geometryData_poly.program

noncomputable def supplierRawProgram {η τ : ℝ} (p : RationalAllParameters η τ) : PolyProgram Input.encode enc
    (fun x => suppliersData p.δ p.γ (geometryData (x.raw,setView (x.U.representatives p.M)))) :=
  geometryProgram p.M |>.comp (suppliersData_poly p.δ p.γ).program
end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end


