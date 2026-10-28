-- Prove2me | Definitions.Def_OAIQ035K044
-- name    : OAIQ035K044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:04:44.695101+00:00
-- url     : https://prove2.me/theorems/5f98a5b9-7d23-4d01-b59c-1319a6f05544
-- title:
--   Definitions bundle OAIQ035K044 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 19 definitions and 5 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.CoupledLaw.reindexStars`, `OAI.MetricKMedian.RationalPhysicalKernel.labels`, `OAI.MetricKMedian.RationalPhysicalKernel.replay`, `OAI.MetricKMedian.RationalPhysicalKernel.replayList`, `OAI.MetricKMedian.Reduction.Program.feasible`, `OAI.MetricKMedian.Reduction.Program.selectList`, `OAI.MetricKMedian.Reduction.deleteStep`, `OAI.MetricKMedian.Reduction.deletionEndpoints`, `OAI.MetricKMedian.Reduction.deletionHistory`, `OAI.MetricKMedian.Reduction.deletionValues`, `OAI.MetricKMedian.Reduction.eligible`, `OAI.MetricKMedian.Reduction.rationalDeleteStep`, `OAI.MetricKMedian.Reduction.rationalEligible`, `OAI.MetricKMedian.Reduction.rationalHistory`, `OAI.MetricKMedian.Reduction.reductionOutputs`, `OAI.MetricKMedian.Reduction.sparseOutcomes`, `OAI.MetricKMedian.ScalarTransfer.Q0`, `OAI.MetricKMedian.ScalarTransfer.Q1`, `OAI.MetricKMedian.ScalarTransfer.Y`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_ScalarTransfer`, `KMedian_Preparation_CoupledReindex`, `KMedian_Programs_FinalSelectionProgram`, `KMedian_Reduction_BudgetReduction`, `KMedian_Reduction_DeletionHistory`, `KMedian_Reduction_RationalDeletion`, `KMedian_Rounding_RationalPhysicalReplay`, `KMedian_Sparse_SparseAffineMoments`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparsePreparedBudget`, `KMedian_Sparse_SparsePreparedProbability`, `KMedian_Sparse_SparseReduction`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K028`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004`, `OAIQ035K005`, `OAIQ035K006`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K032`, `OAIQ035K033`, `OAIQ035K008`, `OAIQ035K010`, `OAIQ035K011`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K035` and `OAIQ035K036` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K064`; the statements `OAI.MetricKMedian.Certificates.Q0_actual_pos`, `OAI.MetricKMedian.Certificates.Q1_actual_pos`, `OAI.MetricKMedian.Certificates.Y_actual_bounds`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival` and `OAI.MetricKMedian.Reduction.sparse_outcome_exists`; the proofs of `OAI.MetricKMedian.Certificates.Q0_actual_pos`, `OAI.MetricKMedian.Certificates.Q1_actual_pos`, `OAI.MetricKMedian.Certificates.Y_actual_bounds`, `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds`, `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival` and `OAI.MetricKMedian.Reduction.sparse_outcome_exists`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K028
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K032
import Definitions.Def_OAIQ035K033
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K010
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K023
import Definitions.Def_OAIQ035K024
import Definitions.Def_OAIQ035K035
import Definitions.Def_OAIQ035K036

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def Q0 (p a k W : ℝ) (s : Bool) : ℝ :=
  N p k s - d s*a + p*W*(hh s*W-2*d s)
noncomputable def Q1 (p a k x : ℝ) (s : Bool) : ℝ :=
  N p k s-(2-bit s)*p*x-d s*(c p s*p-ell p a x s)-hh s*p*(uOne s)^2
noncomputable def Y (p k x : ℝ) (s : Bool) : ℝ :=
  N p k s-p*((2-bit s)*x+(2-bit s)^2/(32/5))

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseAffineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
variable {α : Type}

theorem moment_affine_pair (μ : SparseIntegerLaw α) (f g : α → ℚ) (a b : ℚ) :
    μ.moment (fun x => (a+f x)*(b+g x))=
      a*b+a*μ.moment g+b*μ.moment f+μ.moment (fun x => f x*g x) := by
  calc
    _ = μ.moment (fun x => a*b+a*g x+b*f x+f x*g x) :=
      μ.moment_congr _ _ (fun _ => by ring)
    _ = _ := by rw [moment_add,moment_add,moment_add,moment_const,moment_mul,moment_mul]

theorem moment_affine_pair_le (μ : SparseIntegerLaw α) (f g : α → ℚ) (a b x y : ℚ)
    (hf : μ.moment f=x) (hg : μ.moment g=y)
    (hpair : μ.moment (fun t => f t*g t) ≤ x*y) :
    μ.moment (fun t => (a+f t)*(b+g t)) ≤ (a+x)*(b+y) := by
  rw [moment_affine_pair,hf,hg]
  nlinarith only [hpair]

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

theorem integral_of_small_fractional (q : Vector ℚ n)
    (hq : ∀ i, 0 ≤ point q i ∧ point q i ≤ 1) (K : ℕ)
    (hs : (∑ i, point q i)=(K:ℚ)) (hf : (fractional q).card ≤ 1) :
    ∀ i, point q i=0 ∨ point q i=1 := by
  have has : MarginalRounding.fractional (realPoint q)=∅ := by
    by_contra h
    obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr h
    have h0 : ∀ i, 0 ≤ realPoint q i := fun i => by
      dsimp only [realPoint]; exact_mod_cast (hq i).1
    have h1 : ∀ i, realPoint q i ≤ 1 := fun i => by
      dsimp only [realPoint]; exact_mod_cast (hq i).2
    have hsum : (∑ i, realPoint q i)=(K:ℝ) := by
      dsimp only [realPoint]; exact_mod_cast hs
    obtain ⟨j,hj,hji⟩ := MarginalRounding.second_fractional h0 h1 hsum hi
    rw [real_fractional] at hi hj
    exact hji (card_le_one.mp hf j hj i hi)
  intro i
  apply RationalLastFraction.nonfractional q hq i
  rw [← real_fractional,has]
  exact notMem_empty i

end MetricKMedian.SparseCardinalRounding
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

theorem discarded_mass (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℚ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℚ)=1) :
    (g:ℝ)*(discarded D q Δ z j:ℝ)=
      (deficit D q g z j:ℝ)-min (deficit D q g z j:ℝ) (1/2) := by
  have he : (deficit D q g z j:ℝ)=(g:ℝ)*((∑ e,activationCount D q z e j):ℕ) := by
    simp only [deficit,Rat.cast_mul,Rat.cast_sum,Nat.cast_sum,← activationCount_cast,
      Rat.cast_natCast]
  rw [he,(Preparation.grid_clip (by exact_mod_cast hg) heven (by exact_mod_cast hunit)
    (∑ e,activationCount D q z e j)).1]
  simp only [discarded,Rat.cast_sub,Rat.cast_natCast,mul_sub]

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem total_deficit_identity (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℚ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℚ)=1) :
    (g:ℝ)*(total D q Δ z j:ℝ)=1-min (deficit D q g z j:ℝ) (1/2) := by
  have he : (deficit D q g z j:ℝ)=(g:ℝ)*((∑ e,activationCount D q z e j):ℕ) := by
    simp only [deficit,Rat.cast_mul,Rat.cast_sum,Nat.cast_sum,← activationCount_cast,
      Rat.cast_natCast]
  rw [he]
  exact (Preparation.grid_clip (by exact_mod_cast hg) heven (by exact_mod_cast hunit)
    (∑ e,activationCount D q z e j)).2.1.symm

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_CoupledReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Preparation
open Finset
attribute [instance] CoupledLaw.finite
variable {E E' T I : Type} [Fintype E] [DecidableEq E]
  [Fintype E'] [DecidableEq E'] [Fintype T] [DecidableEq T]
  [Fintype I] [DecidableEq I]

noncomputable def CoupledLaw.reindexStars (e : E ≃ E')
    {D : E' → Finset T} {a w : E' → ℝ} {P : T → Finset I}
    {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (D ∘ e) (a ∘ e) (w ∘ e) P y p c g γ B Δ) :
    CoupledLaw D a w P y p c g γ B Δ where
  Ω := L.Ω
  ν := L.ν
  κ := L.κ
  O := fun z i => L.O z (e.symm i)
  N := fun z i => L.N z (e.symm i)
  R := fun z t i => L.R z t (e.symm i)
  K := L.K
  C := L.C
  open_cap := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z hz i => L.open_cap z hz (e.symm i)
  open_zero := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z hz i => L.open_zero z hz (e.symm i)
  nominal_nonneg := fun z hz i => L.nominal_nonneg z hz (e.symm i)
  nominal_cap := fun z hz i => L.nominal_cap z hz (e.symm i)
  nominal_mean := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun i => L.nominal_mean (e.symm i)
  nominal_variance := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun i => L.nominal_variance (e.symm i)
  nominal_pair := by
    intro i j hij
    simpa only [Function.comp_apply, e.apply_symm_apply] using
      L.nominal_pair (e.symm i) (e.symm j) (e.symm.injective.ne hij)
  request_cap := fun z hz t i => L.request_cap z hz t (e.symm i)
  request_target := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun z t i => L.request_target z t (e.symm i)
  request_mean := by simpa only [Function.comp_apply, e.apply_symm_apply] using
    fun t i => L.request_mean t (e.symm i)
  exact_total := by
    intro z t
    rw [e.symm.sum_comp]
    exact L.exact_total z t
  half := L.half
  total_cap := L.total_cap
  total_deviation := L.total_deviation
  pieces := L.pieces
  piece_mean := L.piece_mean
  piece_pair := L.piece_pair
  piece_variance := L.piece_variance
  budget := by
    have he : ∀ z, (∑ i, a i * (g * (L.O z (e.symm i) : ℝ))) =
        ∑ j, a (e j) * (g * (L.O z j : ℝ)) := by
      intro z
      rw [← e.sum_comp]
      simp only [e.symm_apply_apply]
    simpa only [he, Function.comp_apply] using L.budget

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F J : Type} [LinearOrder F] {Δ : ℕ}

noncomputable def labels (g β : ℚ) (x : ℝ) (d : J → F → ℝ)
    (s : State F Δ g β) (S : J → Finset (CopyState.Copy (F := F) Δ)) :
    J → Finset (CopyState.Copy (F := F) Δ) :=
  match s.2 with
  | none => S
  | some ⟨A,⟨G,Z⟩⟩ => fun j => CopyState.roundAlive A (S j) G
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z x (g:ℝ) (d j)

noncomputable def replayList (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ)) :
    List (State F Δ g β) → J → Finset (CopyState.Copy (F := F) Δ)
  | [] => S₀
  | s::L => labels g β (x (L.length-1)) d s (replayList g β x d S₀ L)

noncomputable def replay (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) :
    J → Finset (CopyState.Copy (F := F) Δ) := replayList g β x d S₀ (h.1::h.2)

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_FinalSelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
def feasible (I : Instance) (S : Finset (Fin I.n)) : Bool := decide (S⊆I.facilities ∧ S.Nonempty ∧ S.card≤I.k)
def selectList (I : Instance) (L : List (Finset (Fin I.n))) : Finset (Fin I.n) :=
  (SparseSelect.best (feasible I) (rationalCost I) L).getD {I.facilities.min' I.facilities_nonempty}
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def deletionValues (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : Finset ℚ :=
  (deletionChoices T c).biUnion (fun D => T.image (fun i =>
    rationalCost I ((T \ D).erase i)-rationalCost I (T \ D)))

noncomputable def eligible (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) : Finset (Fin I.n) := by
  classical
  exact U.filter (fun i => ((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B)

noncomputable def deleteStep (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  if I.k < U.card then
    if h : (eligible I B U).Nonempty then U.erase ((eligible I B U).min' h) else U
  else U

noncomputable def deletionHistory (I : Instance) (B : ℝ) (T : Finset (Fin I.n)) :
    ℕ → Finset (Fin I.n)
  | 0 => T
  | t+1 => deleteStep I B (deletionHistory I B T t)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalEligible (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  U.filter (fun i => rationalCost I (U.erase i)-rationalCost I U ≤ B)

def rationalDeleteStep (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  if I.k < U.card then
    if h : (rationalEligible I B U).Nonempty then U.erase ((rationalEligible I B U).min' h) else U
  else U

def rationalHistory (I : Instance) (B : ℚ) (T : Finset (Fin I.n)) : ℕ → Finset (Fin I.n)
  | 0 => T
  | t+1 => rationalDeleteStep I B (rationalHistory I B T t)

def deletionEndpoints (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : Finset (Finset (Fin I.n)) :=
  (insert 0 (deletionValues I T c)).image (fun r => rationalHistory I r T c)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def sparseOutcomes (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    Finset (Finset (Fin I.n)) :=
  insert T ((deletionEndpoints I T c).biUnion (fun U => insert U (completionBranches I F U δ b)))

end MetricKMedian.Reduction
end
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

namespace Reduction

def reductionOutputs (pseudo : (I : Instance) → Finset (Fin I.n)) (I : Instance)
    (δ : ℚ) (c a b : ℕ) : Finset (Finset (Fin I.n)) :=
  (sparseBranches I I.facilities a).biUnion (fun F =>
    if hF : I.k ≤ F.card then sparseOutcomes I F (pseudo (I.restrictFacilities F hF)) δ c b
    else ∅)

end Reduction
end MetricKMedian
end
end

end OAI
end


