-- Prove2me | Definitions.Def_OAIQ053K043
-- name    : OAIQ053K043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:04:14.98122+00:00
-- url     : https://prove2.me/theorems/da5a78d9-97d1-4763-8be3-d5241603c183
-- title:
--   Definitions bundle OAIQ053K043 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 11 definitions and 18 theorems. The definitions and types are `OAI.MetricKMedian.PCP.PortCSP.diagHit`, `OAI.MetricKMedian.PCP.PortCSP.projection`, `OAI.MetricKMedian.PCP.PortCSP.stoppedWitness`, `OAI.MetricKMedian.PCP.PortCSP.witness`, `OAI.MetricKMedian.PCP.Tableau.decodeCfg`, `OAI.MetricKMedian.PCP.Tableau.decodeRow`, `OAI.MetricKMedian.Preparation.physicalOpen`, `OAI.MetricKMedian.RationalPhysicalKernel.labels`, `OAI.MetricKMedian.RationalPhysicalKernel.replay`, `OAI.MetricKMedian.RationalPhysicalKernel.replayList`, `OAI.MetricKMedian.SparsePrepared.opening`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_PoweringMean`, `KMedian_CookLevin_TableauQueryProgram`, `KMedian_CookLevin_TableauRelationProgram`, `KMedian_CookLevin_TableauSystem`, `KMedian_Preparation_CoupledGeometry`, `KMedian_Projection_CSPProjection`, `KMedian_Projection_CodingLaws`, `KMedian_Rounding_RationalPhysicalReplay`, `KMedian_Sparse_SparseAffineMoments`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseCoupledPreparation`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparsePreparedBudget`, `KMedian_Sparse_SparsePreparedProbability`.
--
--   **Imports.** It imports the bundles `OAIQ053K031`, `OAIQ053K032`, `OAIQ053K035` and `OAIQ053K036` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K060` and `OAIQ053K061`; the statements `OAI.MetricKMedian.PCP.PortCSP.projection_expands_s53`, `OAI.MetricKMedian.PCP.PortCSP.witness_energy_le_s53`, `OAI.MetricKMedian.Preparation.distant_assignments_s53`, `OAI.MetricKMedian.Preparation.nearby_assignments_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53` and `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s53`; the proofs of `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53`, `OAI.MetricKMedian.PCP.PortCSP.powered_sound_s53`, `OAI.MetricKMedian.PCP.PortCSP.projection_expands_s53`, `OAI.MetricKMedian.PCP.PortCSP.witness_energy_le_s53`, `OAI.MetricKMedian.Preparation.distant_assignments_s53`, `OAI.MetricKMedian.Preparation.nearby_assignments_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_mass_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53` and `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K031
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K035
import Definitions.Def_OAIQ053K036

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBind
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem bindIndexed_property (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (P : β → Prop) (hP : ∀ a, ∀ b : Fin (κ a).length, P (κ a).states[b.val]) :
    ∀ i : Fin (μ.bindIndexed κ).length, P (μ.bindIndexed κ).states[i.val] := by
  intro i
  change P ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
    (κ z.1).states[z.2.val]))[i.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringMean
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringMean

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

noncomputable def diagHit (a : V → Advice D A cap) (x : V → A) (i j n : ℕ)
    (p : G.Walk n) : ℝ :=
  if h : n=i+(j+1) then C.cutHit a x i j (p.cast h) else 0

noncomputable def witness (a : V → Advice D A cap) (x : V → A) (L n : ℕ)
    (p : G.Walk n) : ℝ :=
  ∑ i ∈ range (L+1), ∑ j ∈ range (L+1), C.diagHit a x i j n p

noncomputable def stoppedWitness (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (z : (Fin cap → Fin (t+1)) × G.Walk cap) : ℝ :=
  C.witness a x L (Stopped.length t cap z.1)
    (z.2.segment 0 (Stopped.length t cap z.1) (by have := Stopped.length_le t cap z.1; omega))

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringMean

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauSystem

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
lemma satisfies_iff (T L : ℕ) (a : Var (K := K) T L → Value M) :
    (system M T L).Satisfies a ↔ ∀ t, relation M T L t (a ∘ query M T L t) := by
  simp only [FiniteCSP.Satisfies,system,mem_filter,mem_univ,true_and]

lemma row_valid (T L : ℕ) (a : Var (K := K) T L → Value M) (ha : (system M T L).Satisfies a)
    (t : Fin (T+1)) (k : K) : ValidRow L (getRow M T L a t k) := by
  have h := (satisfies_iff M T L a).mp ha
  exact ⟨h (.end t k),fun i => h (.shape t k i)⟩

noncomputable def decodeRow (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) (k : K) : List (Γ k) :=
  (valid_row_list L (getRow M T L a t k) (row_valid M T L a ha t k)).choose
noncomputable def decodeCfg (T L : ℕ) (a : Var (K := K) T L → Value M)
    (ha : (system M T L).Satisfies a) (t : Fin (T+1)) : Cfg Γ Λ σ :=
  ⟨(getControl M T L a t).1,(getControl M T L a t).2,decodeRow M T L a ha t⟩

end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalReplay
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledGeometry
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

noncomputable def physicalOpen {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) (a : Physical I T) : ℝ := g*(physicalCount L z a:ℝ)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseAffineMoments
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterCounts
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

theorem outsideCount_cast (q : Fin m → ℚ) (z : State n m) (e : Fin m) :
    (outsideCount q z e:ℚ)=SparseSignedPreparation.outside (base q) z e := by
  simp only [outsideCount,SparseSignedPreparation.outside,SparseStarActivation.upper]
  split_ifs <;> simp

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedBudget
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem raw_counts (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (z : State n m) :
    SparseSignedPreparation.raw D c (base q) z=
      (∑ e,c e*(outsideCount q z e:ℚ))-(∑ j,∑ e,(activationCount D q z e j:ℚ)) := by
  rw [sum_comm]
  simp only [SparseSignedPreparation.raw,sum_sub_distrib,← Nat.cast_sum,activation_sum,
    Nat.cast_add,Nat.cast_mul,outsideCount_cast]

def opening (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : ℚ :=
  (∑ e,c e*(outsideCount q z e:ℚ))+(∑ j,(total D q Δ z j:ℚ))

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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedProbability
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCoupledPreparation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem opening_cast (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (g : ℝ) :
    g * (opening D a q Δ z : ℝ) =
      (∑ e, (a e : ℝ) * (g * (outsideCount q z e : ℝ))) +
      (∑ j, g * (total D q Δ z j : ℝ)) := by
  simp only [opening, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    mul_add, mul_sum]
  congr 1
  exact sum_congr rfl (fun _ _ => by ring)

end MetricKMedian.SparsePrepared
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauQueryProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
lemma rawQuery_correct (T L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ))
    (c : Clause (K := K) T L ⊕ BoundaryClause (K := K) L) (q : Query M) :
    rawQuery M k0 T L (testCode k0 c) q=varCode k0 ((boundedSystem M B T L).query c q) := by
  cases c with
  | inl c => exact rawQuery_clause M k0 T L c q
  | inr b => exact rawQuery_boundary M k0 T L b q
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauQueryProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRelationProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRelationProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
lemma rawAccept_clause (T L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (c : Clause (K := K) T L) :
    rawAccept M B (clauseCode k0 c)=(Tableau.system M T L).accept c := by
  cases c <;> ext z <;> simp +instances [rawAccept,clauseCode,Tableau.system,relation]
  all_goals exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
lemma rawAccept_correct (T L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ))
    (c : Clause (K := K) T L ⊕ BoundaryClause (K := K) L) :
    rawAccept M B (testCode k0 c)=(boundedSystem M B T L).accept c := by
  cases c with
  | inl c => exact rawAccept_clause M k0 T L B c
  | inr b => exact rawAccept_boundary M k0 L B b
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauRelationProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_CSPProjection
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPProjection

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D} [DecidableEq A]
variable (C : PortCSP G A)
variable (chosen : V × D → A × A) (hchosen : ∀ p, C.Legal p (chosen p))
omit [DecidableEq A]
include hchosen in
lemma repair_legal (p : V × D) (a : A × A) : C.Legal p (C.repair chosen p a) := by
  unfold repair
  split_ifs with h
  · exact h
  · exact hchosen p
noncomputable def projection : BiProjection (V × D) V Bool (D × Bool) (A × A) A :=
  G.incidence (fun q a => if q.2 then (C.repair chosen q.1 a).2 else (C.repair chosen q.1 a).1)

include hchosen in
lemma projection_consistent : (C.projection chosen).Consistent := by
  intro p b c h a
  have hl := (C.repair_legal chosen hchosen p a).2
  cases b <;> cases c
  · rfl
  · have he : p.1=(G.rotate p).1 := h
    exact hl he.symm
  · have he : (G.rotate p).1=p.1 := h
    exact (hl he).symm
  · rfl

end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPProjection

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_CodingLaws
attribute [-instance] _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionCodingLaws
namespace MetricKMedian.PCP.Compiler.SeedCombinators
open scoped Classical

variable {T V D A : Type} [DecidableEq A]
variable (G : PortGraph V D) (C : PortCSP G A) (chosen : V×D→A×A)
variable (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A) (t : T) (code : V→ℕ)
variable (hr : ∀v d,r t (code v) d=(code (G.rotate (v,d)).1,(G.rotate (v,d)).2))
include hr in
omit [DecidableEq A] in
lemma source_correct (v : V) (s : D×Bool) :
    source r t (code v) s=(code ((C.projection chosen).edge.symm (v,s)).1.1,
      ((C.projection chosen).edge.symm (v,s)).1.2) := by
  cases s with | mk d b =>
    cases b
    · rfl
    · exact hr v d
variable (hf : ∀ v d a,fix t (code v) d a=C.repair chosen (v,d) a)
include hr hf in
omit [DecidableEq A] in
lemma project_correct (v : V) (s : D×Bool) :
    project r fix t (code v) s=(C.projection chosen).project ((C.projection chosen).edge.symm (v,s)) := by
  funext a
  unfold project
  rw [source_correct G C chosen r t code hr v s]
  dsimp only
  rw [hf]
  cases s with | mk d b => cases b <;> rfl
variable {m k : ℕ} (ue : V≃Fin m) (de : D≃Fin k)
omit [DecidableEq A] in
lemma numbered_correct (hr' : ∀v d,r t (ue v).val d=((ue (G.rotate (v,d)).1).val,(G.rotate (v,d)).2))
    (hf' : ∀v d a,fix t (ue v).val d a=C.repair chosen (v,d) a) (v : V) (s : D×Bool) :
    numbered r fix (fun d=>(de d).val) k t (ue v).val s=
      ((((ue.prodCongr de).trans finProdFinEquiv) ((C.projection chosen).edge.symm (v,s)).1).val,
        (C.projection chosen).project ((C.projection chosen).edge.symm (v,s))) := by
  apply Prod.ext
  · simp only [numbered,source_correct G C chosen r t (fun v=>(ue v).val) hr',
      Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map,finProdFinEquiv]
    rfl
  · exact project_correct G C chosen r fix t (fun v=>(ue v).val) hr' hf' v s
end MetricKMedian.PCP.Compiler.SeedCombinators

end Inline_PCPProjectionCodingLaws

end OAI
end


