-- Prove2me | Definitions.Def_OAIQ035K034
-- name    : OAIQ035K034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:00:04.52855+00:00
-- url     : https://prove2.me/theorems/7e3d7ae5-470e-4a10-9efd-93578c64b631
-- title:
--   Definitions bundle OAIQ035K034 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 37 definitions, 2 inductive types or structures and 25 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Context`, `OAI.MetricKMedian.LPBinary.Input.iterate`, `OAI.MetricKMedian.LPBinary.Input.vector`, `OAI.MetricKMedian.LPBinary.Input.zeroOutput`, `OAI.MetricKMedian.LPBinary.Repair.valid`, `OAI.MetricKMedian.LPBinary.Repair.value`, `OAI.MetricKMedian.LPBinary.Scale.guesses`, `OAI.MetricKMedian.LPBinary.State`, `OAI.MetricKMedian.LPBinary.Truncated.component`, `OAI.MetricKMedian.LPBinary.Truncated.gradient`, `OAI.MetricKMedian.LPBinary.Truncated.matrix`, `OAI.MetricKMedian.LPBinary.Truncated.next`, `OAI.MetricKMedian.LPBinary.Truncated.objective`, `OAI.MetricKMedian.LPBinary.choose`, `OAI.MetricKMedian.LPBinary.rawContext`, `OAI.MetricKMedian.LPBinary.rawGrad`, `OAI.MetricKMedian.LPBinary.rawInitial`, `OAI.MetricKMedian.LPBinary.rawPenalty`, `OAI.MetricKMedian.LPBinary.rawRate`, `OAI.MetricKMedian.LPBinary.rawSteps`, `OAI.MetricKMedian.LPBinary.update`, `OAI.MetricKMedian.LPBinary.value`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.supplierView`, `OAI.MetricKMedian.Preparation.RationalSuppliers.counts`, `OAI.MetricKMedian.RoundingProgram.SignedRound.emptyInput`, `OAI.MetricKMedian.SparseBundles.Program.QInput.encode`, `OAI.MetricKMedian.SparseBundles.Program.eqi`, `OAI.MetricKMedian.SparseBundles.Program.qr`, `OAI.MetricKMedian.SparseBundles.Program.qt`, `OAI.MetricKMedian.SparseCounts.ListOperation.er`, `OAI.MetricKMedian.SparseCounts.ListOperation.et`, `OAI.MetricKMedian.SparseGridRounding.Program.Input.cardinal`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input.signed`, `OAI.MetricKMedian.SparseOuterLaw.outsideCount`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.bernoulli`, `OAI.MetricKMedian.SparseSignedPreparation.Program.KernelInput.star`, `OAI.MetricKMedian.SparseSignedPreparation.Program.dummy`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_NearestFillingFormula`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Instance`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_DualListOperations`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_GradientDenominator`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_TruncatedListOperations`, `KMedian_Preparation_RationalRepresentatives`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Process_CountListOperations`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_ScaleListProgram`, `KMedian_Reduction_BudgetReduction`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedRoundProgram`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseSupplierSupport`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K014`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K023` and `OAIQ035K024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K042` and `OAIQ035K043`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K020
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K022
import Definitions.Def_OAIQ035K023
import Definitions.Def_OAIQ035K024

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_NearestFillingFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

theorem fill_formula (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ)
    (hy : ∀ i∈U, 0 ≤ y i) (ht : 0 ≤ t) (hm : t ≤ ∑ i∈U, y i) (i : Fin n) :
    (fill U y d t hy ht hm).amount i=
      if i∈U then min (y i) (max 0 (t-priorMass U y d i)) else 0 := by
  revert t hy
  refine U.strongInductionOn ?_
  intro U ih t hy ht hm
  by_cases hi : i∈U
  · have hU : U.Nonempty := ⟨i,hi⟩
    let a := firstNearest U d hU
    have ha : a∈U := (firstNearest_spec U d hU).1
    have hpref : priorMass U y d a=0 := priorMass_first U y d hU
    rw [ite_eq_left hi]
    by_cases hs : t ≤ y a
    · rw [fill]
      have hs' : t ≤ y (firstNearest U d hU) := hs
      simp only [dite_eq_left hU,dite_eq_left hs']
      change (if i=a then t else 0)=min (y i) (max 0 (t-priorMass U y d i))
      by_cases he : i=a
      · subst i
        rw [ite_eq_left rfl,hpref,sub_zero,max_eq_right ht,min_eq_right hs]
      · rw [ite_eq_right he]
        have hp := priorMass_nonneg (U.erase a) y d i (fun j hj => hy j (mem_of_mem_erase hj))
        rw [priorMass_erase U y d a i ha (first_before U d hU i hi he)]
        rw [max_eq_left (by linarith),min_eq_right (hy i hi)]
    · rw [fill]
      have hs' : ¬t ≤ y (firstNearest U d hU) := hs
      simp only [dite_eq_left hU,dite_eq_right hs']
      by_cases he : i=a
      · subst i
        change @Function.update (Fin n) (fun _ => ℚ) _ _ a (y a) a = _
        simp only [Function.update_self,hpref,sub_zero,max_eq_right ht,min_eq_left (le_of_not_ge hs)]
      · rw [Function.update_of_ne he]
        rw [ih (U.erase a) (erase_ssubset ha)]
        rw [ite_eq_left (mem_erase.mpr ⟨he,hi⟩)]
        rw [priorMass_erase U y d a i ha (first_before U d hU i hi he)]
        congr 2
        ring
  · rw [ite_eq_right hi]
    exact (fill U y d t hy ht hm).outside i hi

 theorem computedNearest_formula (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) (i : Fin n) :
    (computedNearest y d hy hm)[i.val]=min (y i) (max 0 (1-priorMass univ y d i)) := by
  simp only [computedNearest,Vector.getElem_ofFn,fill_formula,mem_univ,ite_true]
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation.RationalRepresentatives
open Finset
variable {n : ℕ}

theorem select_spec (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ)
    (hd0 : ∀ j, d j j=0) (hds : ∀ i j, d i j=d j i) (hM : 0 ≤ M)
    (k : ℕ) (U : Finset (Fin n)) (hk : U.card ≤ k) (hV : ∀ j ∈ U, 0 ≤ V j) :
    select d V M k U ⊆ U ∧
      (↑(select d V M k U) : Set (Fin n)).Pairwise
        (fun s t => M*max (V s) (V t) < d s t) ∧
      ∀ j ∈ U, ∃ s ∈ select d V M k U, V s ≤ V j ∧ d j s ≤ M*V j := by
  induction k generalizing U with
  | zero =>
      have he : U=∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      simp [select, he]
  | succ k ih =>
      by_cases hU : U.Nonempty
      · let s := firstNearest U V hU
        have hs : s ∈ U := (firstNearest_spec U V hU).1
        have hmin : ∀ j ∈ U, V s ≤ V j := (firstNearest_spec U V hU).2
        let W := U.filter (fun j => M*V j < d j s)
        have hWU : W ⊆ U := filter_subset _ _
        have hsW : s ∉ W := by
          intro hh
          have h := (mem_filter.mp hh).2
          rw [hd0] at h
          exact not_lt_of_ge (mul_nonneg hM (hV s hs)) h
        have hwk : W.card ≤ k := by
          have hproper : W ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hWU, fun he => hsW (he ▸ hs)⟩
          have hc := card_lt_card hproper
          omega
        obtain ⟨hsub,hpair,hcover⟩ := ih W hwk (fun j hj => hV j (hWU hj))
        simp only [select, dite_eq_left hU]
        change insert s (select d V M k W) ⊆ U ∧ _
        refine ⟨insert_subset hs (hsub.trans hWU), ?_, ?_⟩
        · intro a ha b hb hab
          rcases mem_insert.mp ha with rfl | ha
          · have hb' := (mem_insert.mp hb).resolve_left (Ne.symm hab)
            have hbW := hsub hb'
            rw [max_eq_right (hmin b (hWU hbW)),hds]
            exact (mem_filter.mp hbW).2
          · rcases mem_insert.mp hb with rfl | hb
            · have haW := hsub ha
              rw [max_eq_left (hmin a (hWU haW))]
              exact (mem_filter.mp haW).2
            · exact hpair ha hb hab
        · intro j hj
          by_cases hjW : j ∈ W
          · obtain ⟨a,ha,hv,hd⟩ := hcover j hjW
            exact ⟨a,mem_insert_of_mem ha,hv,hd⟩
          · exact ⟨s,mem_insert_self _ _,hmin j hj,
              le_of_not_gt (fun h => hjW (mem_filter.mpr ⟨hj,h⟩))⟩
      · have he := not_nonempty_iff_eq_empty.mp hU
        simp [select, he]

theorem representatives_spec (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ)
    (hd0 : ∀ j, d j j=0) (hds : ∀ i j, d i j=d j i) (hM : 0 ≤ M)
    (hV : ∀ j, 0 ≤ V j) :
    (↑(representatives d V M) : Set (Fin n)).Pairwise
        (fun s t => M*max (V s) (V t) < d s t) ∧
      ∀ j, ∃ s ∈ representatives d V M, V s ≤ V j ∧ d j s ≤ M*V j := by
  have hh := select_spec d V M hd0 hds hM n univ (by simp) (fun j _ => hV j)
  exact ⟨hh.2.1, fun j => hh.2.2 j (mem_univ _)⟩

end MetricKMedian.Preparation.RationalRepresentatives
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalUnitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

theorem representative_separation (M : ℚ) (hM : 0≤M) :
    ∀ t u, t≠u → M*max (U.V (U.ridx M t)) (U.V (U.ridx M u)) <
      U.dd (U.ridx M t) (U.ridx M u) := by
  intro t u htu
  have hh := (RationalRepresentatives.representatives_spec U.dd U.V M U.hdd U.hsymm hM U.V_nonneg).1
  exact hh ((U.representatives M).orderEmbOfFin_mem rfl t)
    ((U.representatives M).orderEmbOfFin_mem rfl u)
    (fun h => htu ((U.representatives M).orderEmbOfFin rfl |>.injective h))

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Instance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem optimum_le (I : Instance) {S : Finset (Fin I.n)}
    (hS : S ⊆ I.facilities) (hne : S.Nonempty) (hk : S.card ≤ I.k) : optimum I ≤ cost I S := by
  rw [optimum,dite_eq_left I.feasible_nonempty]
  exact min'_le _ _ (mem_image_of_mem _ ((I.mem_feasible S).mpr ⟨hS,hne,hk⟩))

theorem cost_eq_zero_iff (I : Instance) (S : Finset (Fin I.n)) (hne : S.Nonempty) :
    cost I S=0 ↔ I.clients ⊆ S := by
  constructor
  · intro hc j hj
    have hj0 : nearest I j S=0 := (sum_eq_zero_iff_of_nonneg
      (fun j _ => I.nearest_nonneg j S)).mp hc j hj
    obtain ⟨i,hi,he⟩ := I.nearest_attained j S hne
    have hd : I.distance j i=0 := by exact_mod_cast (he.symm.trans hj0)
    exact (I.distance_eq_zero j i).mp hd ▸ hi
  · intro hsub
    apply sum_eq_zero
    intro j hj
    apply le_antisymm _ (I.nearest_nonneg j S)
    have hh := I.nearest_le j (hsub hj)
    simpa only [(I.distance_eq_zero j j).mpr rfl,Rat.cast_zero] using hh

theorem optimum_eq_zero_iff (I : Instance) :
    optimum I=0 ↔ I.clients ⊆ I.facilities ∧ I.clients.card ≤ I.k := by
  constructor
  · intro hz
    obtain ⟨S,hSF,hne,hSk,hcost⟩ := I.optimum_attained
    have hJS := (I.cost_eq_zero_iff S hne).mp (hcost.trans hz)
    exact ⟨hJS.trans hSF,(card_le_card hJS).trans hSk⟩
  · rintro ⟨hJF,hJk⟩
    by_cases hJ : I.clients.Nonempty
    · apply le_antisymm _ I.optimum_nonneg
      exact (I.optimum_le hJF hJ hJk).trans_eq ((I.cost_eq_zero_iff I.clients hJ).mpr Subset.rfl)
    · have he := not_nonempty_iff_eq_empty.mp hJ
      obtain ⟨S,hSF,hne,hSk,_⟩ := I.optimum_attained
      apply le_antisymm _ I.optimum_nonneg
      exact (I.optimum_le hSF hne hSk).trans_eq (by simp [cost,he])

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_GradientDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.TruncatedLP
open Finset RationalGrid
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem threshold_grid (d y : ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ i, At D (d i)) : At D (FractionalDual.bestThreshold d y H) := by
  have hh := (FractionalDual.bestThreshold_spec d y H).1
  obtain he | hh := mem_insert.mp hh
  · rw [he]; exact RationalGrid.zero D
  · obtain he | hh := mem_insert.mp hh
    · rw [he]; exact RationalGrid.integer D H hD
    · obtain ⟨i,_,he⟩ := mem_image.mp hh
      rw [← he]
      exact hd i

theorem gradient_grid (d : κ → ι → ℚ) (y : ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ j i, At D (d j i)) (i : ι) : At D (gradient d y H i) := by
  apply RationalGrid.sum
  intro j _
  unfold FractionalDual.gradient
  exact RationalGrid.neg (RationalGrid.max (RationalGrid.zero D)
    (RationalGrid.sub (threshold_grid _ _ D H hD (truncated_grid d D H hD hd j))
      (truncated_grid d D H hD hd j i)))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input

def vector (I : Input) (r : ℕ) (t : ℕ) : Vector ℚ I.n :=
  ProjectedSubgradient.trajectory (I.k:ℚ) (TruncatedLP.rate (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k))
    (fun y => TruncatedLP.gradient I.distance y (TruncatedLP.penalty r I.k))
    (ProjectedSubgradient.initial (I.k:ℚ)) t

def iterate (I : Input) (r : ℕ) (t : ℕ) : Row := List.ofFn (ProjectedSubgradient.point (I.vector r t))
end Input

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_DualListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

namespace Dual

 theorem value_ofFn {n : ℕ} (d y : Fin n → ℚ) (H : ℚ) :
    value (List.ofFn d) (List.ofFn y) H=FractionalDual.value d y H := by
  unfold value FractionalDual.value
  apply maximum_eq_finset
  intro q
  simp only [List.mem_map,mem_image,mem_candidates,affine_ofFn]

 theorem best_ofFn {n : ℕ} (d y : Fin n → ℚ) (H : ℚ) :
    best (List.ofFn d) (List.ofFn y) H=FractionalDual.bestThreshold d y H := by
  have hU : ((FractionalDual.thresholds d H).filter (fun t => FractionalDual.affine d y t=FractionalDual.value d y H)).Nonempty := by
    obtain ⟨ht,he⟩ := FractionalDual.bestThreshold_spec d y H
    exact ⟨_,mem_filter.mpr ⟨ht,he⟩⟩
  unfold best FractionalDual.bestThreshold
  rw [dite_eq_left hU]
  apply maximum_eq_finset
  intro q
  simp only [List.mem_filter,mem_filter,decide_eq_true_eq,mem_candidates,affine_ofFn,value_ofFn]

end Dual
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Finset

namespace Truncated

def matrix (ds : Rows) (H : ℚ) : Rows := ds.map (fun d => row d H)
def objective (ds : Rows) (ys : Row) (H : ℚ) : ℚ := ((matrix ds H).map (fun d => Dual.value d ys H)).sum

def component (ds : Rows) (ys : Row) (H : ℚ) (i : ℕ) : ℚ :=
  ((matrix ds H).map (fun d => -max 0 (Dual.best d ys H-d[i]?.getD 0))).sum

def gradient (ds : Rows) (ys : Row) (H : ℚ) : Row :=
  (List.range ys.length).map (component ds ys H)

def next (ds : Rows) (ys : Row) (H k rate : ℚ) : Row :=
  project ((ys.zip (gradient ds ys H)).map (fun p => p.1-rate*p.2)) k

 theorem row_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (H : ℚ) (j : Fin m) :
    row (List.ofFn (d j)) H=List.ofFn (TruncatedLP.truncated d H j) := by
  simp only [row,List.map_ofFn]
  rfl
 theorem matrix_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (H : ℚ) :
    matrix (List.ofFn (fun j => List.ofFn (d j))) H=List.ofFn (fun j => List.ofFn (TruncatedLP.truncated d H j)) := by
  simp only [matrix,List.map_ofFn]
  congr 1
  funext j
  exact row_ofFn d H j
 theorem objective_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) :
    objective (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H=TruncatedLP.objective d y H := by
  simp only [objective,matrix_ofFn,List.map_ofFn,List.sum_ofFn,TruncatedLP.objective]
  apply sum_congr rfl
  intro j _
  exact Dual.value_ofFn _ _ _
 theorem component_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) (i : Fin n) :
    component (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H i.val=TruncatedLP.gradient d y H i := by
  simp only [component,matrix_ofFn,List.map_ofFn,List.sum_ofFn,TruncatedLP.gradient]
  apply sum_congr rfl
  intro j _
  simp only [Function.comp_apply,Dual.best_ofFn,Gaussian.ListOperation.get_ofFn,FractionalDual.gradient]
 theorem gradient_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) :
    gradient (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H=List.ofFn (TruncatedLP.gradient d y H) := by
  simp only [gradient,List.length_ofFn]
  rw [range_ofFn,List.map_ofFn]
  congr 1
  funext i
  exact component_ofFn d y H i
 theorem next_ofFn {n m : ℕ} [NeZero n] (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H k rate : ℚ) :
    next (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H k rate=
      List.ofFn (ProjectedSubgradient.point (ProjectedSubgradient.next k rate (fun y => TruncatedLP.gradient d y H) (Vector.ofFn y))) := by
  simp only [next,gradient_ofFn,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,project_ofFn]
  congr 1
  funext i
  simp only [ProjectedSubgradient.next_apply,ProjectedSubgradient.point_ofFn]
  simp only [ProjectedSubgradient.point_ofFn_apply,Function.comp_def]
end Truncated
end MetricKMedian.LPBinary
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
abbrev Context := Rows × (ℚ × (ℚ × ℚ))
abbrev State := Context × Row

def rawPenalty (r : ℕ) (x : Rows × ℕ) : ℕ := 4*r*(x.2+1)
def rawGrad (r : ℕ) (x : Rows × ℕ) : ℕ := (x.1.head?.getD []).length*(x.1.length*rawPenalty r x)^2
def rawRate (r : ℕ) (x : Rows × ℕ) : ℚ := 1/(2*(r:ℚ)*(rawGrad r x:ℚ))
def rawSteps (r : ℕ) (x : Rows × ℕ) : ℕ := 8*r^2*rawGrad r x*x.2^2
def rawContext (r : ℕ) (x : Rows × ℕ) : Context := (x.1,(rawPenalty r x,(x.2,rawRate r x)))
def rawInitial (x : Rows × ℕ) : Row := (List.range (x.1.head?.getD []).length).map (fun i => if i=0 then (x.2:ℚ) else 0)
def update (s : State) : State := (s.1,Truncated.next s.1.1 s.2 s.1.2.1 s.1.2.2.1 s.1.2.2.2)

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

def value (s : State) : ℚ := Truncated.objective s.1.1 s.2 s.1.2.1
def choose (ss : List State) : State := selectMinimum value ss (([],(0,(0,0))),[])
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest

theorem entries_ofFn {n : ℕ} (y d : Fin n → ℚ) :
    entries (List.ofFn y) (List.ofFn d)=List.ofFn (fun i => (i.val,(y i,d i))) := by
  simp only [entries,Gaussian.ListOperation.zip_ofFn,List.length_ofFn,range_ofFn]

end Nearest
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

theorem opening_ofFn {n : ℕ} (y : Fin n → ℚ) (ρ : ℚ) :
    opening (List.ofFn y) ρ=List.ofFn (TruncatedLP.repairedOpening y ρ) := by
  simp only [opening,List.map_ofFn,Function.comp_def]
  rfl
theorem weights_ofFn {n : ℕ} (d x : Fin n → ℚ) :
    weights (List.ofFn d) (List.ofFn x)=List.ofFn (fun i => if d i ≤ 1 then x i else 0) := by
  simp only [weights,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def]
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

def valid (a : Output) (k : ℕ) : Bool :=
  a.1.all bounded && a.2.all (fun xs => dominated xs a.1) &&
    a.2.all (fun xs => decide (xs.sum=1)) && decide (a.1.sum ≤ (k:ℚ)+1)
def value (a : Output) (ds : Rows) : ℚ := ((a.2.zip ds).map (fun p => dot p.1 p.2)).sum

end MetricKMedian.LPBinary.Repair
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

def outsideCount (q : Fin m → ℚ) (z : State n m) (e : Fin m) : ℕ :=
  base q e+if 0 < point z.1 e then 1 else 0

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSupplierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

def counts (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ g : ℚ) (zG : SparseSignedPreparation.State n (size f n) × SparseCounts.Table f n)
    (a : Fin (f+n*f)) : ℕ :=
  Sum.elim (fun i => SparseOuterLaw.outsideCount (q y P A c γ g) zG.1 (index.symm (.inl i)))
    (fun ti => zG.2 ti.1 ti.2) (physicalIndex a)

end MetricKMedian.Preparation.RationalSuppliers
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
def supplierView {f n : ℕ} (S : Data f n) : SupplierRaw :=
  (List.ofFn S.y,(List.ofFn (fun t => setView (S.P t)),(List.ofFn (fun t => setView (S.A t)),
    (List.ofFn S.p,(List.ofFn S.c,S.γ)))))

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
abbrev er := encodeList Nat.bits
abbrev et := encodeList er

end MetricKMedian.SparseCounts.ListOperation
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
def Input.cardinal (x : Input) : SparseCardinalRounding.Program.Input :=
  ⟨x.n,RationalWeightedStep.point (fraction x.q),fraction_unit x.q x.nonnegative⟩
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseCounts.Program
abbrev qr := encodeList Ratio.encode
abbrev qt := encodeList qr
abbrev eqi := encodePair (encodeList (fun _ : Unit => [])) qt

abbrev QInput.encode (x : QInput) := eqi x.raw

end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

def emptyInput : Input true := ⟨0,Fin.elim0,#v[],by simp,fun i => Fin.elim0 i⟩

end SignedRound
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
structure KernelInput where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  p : Vector ℚ m
  feasible : ∀ e, 0≤RationalWeightedStep.point p e ∧ RationalWeightedStep.point p e≤1

def KernelInput.star (x : KernelInput) : SparseStarActivation.Program.Input :=
  ⟨x.n,x.m,x.D,RationalWeightedStep.point x.p,x.feasible⟩
def KernelInput.bernoulli (x : KernelInput) : SparseBernoulli.Program.Input :=
  ⟨x.m,RationalWeightedStep.point x.p,x.feasible⟩
 theorem point_list {m : ℕ} (p : Vector ℚ m) : List.ofFn (RationalWeightedStep.point p)=p.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp [RationalWeightedStep.point]

structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  p : Vector ℚ m
  feasible : ∀ e, 0≤RationalWeightedStep.point p e ∧ RationalWeightedStep.point p e≤1
  c_unit : ∀ e, 0 ≤ c e ∧ c e≤1

def dummy : KernelInput := ⟨0,0,Fin.elim0,#v[],fun i => Fin.elim0 i⟩

end MetricKMedian.SparseSignedPreparation.Program
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
def Input.signed (x : Input) : SparseSignedPreparation.Program.Input :=
  ⟨x.n,x.m,x.D,x.c,SparseGridRounding.fraction x.q,SparseGridRounding.fraction_unit x.q x.q_nonnegative,x.c_unit⟩
end MetricKMedian.SparseOuterLaw.Program
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
namespace Scale

def guesses (ds : Rows) : Row :=
  ds.flatten.flatMap (fun q => if 0 < q then (Dyadic.powers ds.length).map (fun t => q*t) else [])

theorem guesses_mem {n m : ℕ} (d : Fin m → Fin n → ℚ) (q : ℚ) :
    q ∈ guesses (List.ofFn (fun j => List.ofFn (d j))) ↔ q ∈ Normalization.matrixGuesses d := by
  unfold guesses Normalization.matrixGuesses
  simp only [List.mem_flatMap,List.mem_flatten,mem_biUnion,mem_univ,true_and]
  constructor
  · rintro ⟨v,⟨xs,hxs,hv⟩,hq⟩
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    by_cases h : 0 < d j i
    · simp only [ite_eq_left h,List.length_ofFn,Dyadic.powers_eq,List.mem_map,List.mem_range] at hq
      obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hq
      exact ⟨(j,i),by simp only [ite_eq_left h,mem_image,mem_range]; exact ⟨t,ht,he⟩⟩
    · simp only [ite_eq_right h,List.not_mem_nil] at hq
  · rintro ⟨⟨j,i⟩,hq⟩
    by_cases h : 0 < d j i
    · simp only [ite_eq_left h,mem_image,mem_range] at hq
      obtain ⟨t,ht,rfl⟩ := hq
      refine ⟨d j i,⟨List.ofFn (d j),List.mem_ofFn.mpr ⟨j,rfl⟩,List.mem_ofFn.mpr ⟨i,rfl⟩⟩,?_⟩
      simp only [ite_eq_left h,List.length_ofFn,Dyadic.powers_eq,List.mem_map,List.mem_range]
      exact ⟨(2:ℚ)^t,⟨t,ht,rfl⟩,rfl⟩
    · simp only [ite_eq_right h,notMem_empty] at hq

end Scale
namespace Input

def zeroOutput (I : Input) : Repair.Output :=
  (List.replicate I.n 0,List.replicate I.m (List.replicate I.n 0))

theorem scale_rows (I : Input) (B : ℚ) :
    (I.scale B).rows=I.rows.map (fun ds => ds.map (fun d => d/B)) := by
  simp only [rows,scale,List.map_ofFn,Function.comp_def]

end Input
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_BudgetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

@[simp] theorem restrict_cost (I : Instance) (F : Finset (Fin I.n)) (hF : I.k ≤ F.card)
    (S : Finset (Fin I.n)) : cost (I.restrictFacilities F hF) S=cost I S := rfl

end Instance

end MetricKMedian
end
end

end OAI
end


