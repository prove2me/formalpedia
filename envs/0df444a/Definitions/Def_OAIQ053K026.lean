-- Prove2me | Definitions.Def_OAIQ053K026
-- name    : OAIQ053K026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:58:29.927038+00:00
-- url     : https://prove2.me/theorems/7a8bb98e-7989-4b25-9d8b-5f443fb79f93
-- title:
--   Definitions bundle OAIQ053K026 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 30 definitions, 2 instances and 24 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.build`, `OAI.MetricKMedian.PCP.FourCSP.Satisfies`, `OAI.MetricKMedian.PCP.FourCSP.rejection`, `OAI.MetricKMedian.PCP.IncidenceReduction.decoded`, `OAI.MetricKMedian.PCP.LocalRelation.packed`, `OAI.MetricKMedian.PCP.PortGraph.Contracts`, `OAI.MetricKMedian.PCP.PortGraph.cloud`, `OAI.MetricKMedian.PCP.PortGraph.countSquareMean`, `OAI.MetricKMedian.PCP.PortGraph.edgeMass`, `OAI.MetricKMedian.PCP.PortGraph.equalityFailure`, `OAI.MetricKMedian.PCP.PortGraph.permute`, `OAI.MetricKMedian.PCP.QuadraticSystem.Satisfies`, `OAI.MetricKMedian.PCP.QuadraticSystem.equationRate`, `OAI.MetricKMedian.PCP.QuadraticSystem.rejectionWeight`, `OAI.MetricKMedian.PCP.Tableau.emptyControl`, `OAI.MetricKMedian.PCP.Tableau.emptyResponse`, `OAI.MetricKMedian.PCP.Tableau.getControl`, `OAI.MetricKMedian.PCP.Tableau.getResponse`, `OAI.MetricKMedian.PCP.Tableau.getRow`, `OAI.MetricKMedian.PCP.Tableau.stackPrefix`, `OAI.MetricKMedian.PCP.boundaryRate`, `OAI.MetricKMedian.PCP.coordinates`, `OAI.MetricKMedian.PCP.l2`, `OAI.MetricKMedian.PCP.linearityRate`, `OAI.MetricKMedian.PCP.multiplicationDiscrepancy`, `OAI.MetricKMedian.PCP.multiplicationRate`, `OAI.MetricKMedian.PhysicalBatchLaw.balanced`, `OAI.MetricKMedian.Preparation.SupplierStars.flag`, `OAI.MetricKMedian.SparseOuterLaw.activation`, `OAI.MetricKMedian.SparsePrepared.requests`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_CookLevin_TM2Response`, `KMedian_CookLevin_TableauCorrect`, `KMedian_CookLevin_TableauRows`, `KMedian_CookLevin_TableauSystem`, `KMedian_Expanders_EqualityExpansion`, `KMedian_Expanders_GraphProducts`, `KMedian_Expanders_L2`, `KMedian_Expanders_SpectralWalk`, `KMedian_Expanders_WalkMoments`, `KMedian_PCP_AlphabetReduction`, `KMedian_PCP_BinaryReduction`, `KMedian_PCP_Boundary`, `KMedian_PCP_FiniteTest`, `KMedian_PCP_Hadamard`, `KMedian_PCP_Quadratic`, `KMedian_PCP_Queries`, `KMedian_PCP_Tester`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Process_PhysicalBatchLaw`, `KMedian_Projection_ProductTable`, `KMedian_Projection_Repeat`, `KMedian_Projection_RowsBuild`, `KMedian_Projection_Tables`, `KMedian_Rounding_ExceptionalStar`, `KMedian_Rounding_RationalLastFraction`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalWeightedStep`, `KMedian_Rounding_WeightedRounding`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparsePreparedLaw`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K005`, `OAIQ053K006`, `OAIQ053K008`, `OAIQ053K009`, `OAIQ053K010` and `OAIQ053K011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K036`, `OAIQ053K037` and `OAIQ053K047`; the statements `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53`, `OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53` and `OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53`; the proofs of `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53`, `OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53`, `OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53`, `OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53` and `OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K005
import Definitions.Def_OAIQ053K006
import Definitions.Def_OAIQ053K008
import Definitions.Def_OAIQ053K009
import Definitions.Def_OAIQ053K010
import Definitions.Def_OAIQ053K011

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section LinearityRates
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H]
  [DecidableEq H]

noncomputable def linearityRate (f : G → H) : ℝ :=
  testRate (fun p : G × G => f (p.1 + p.2) ≠ f p.1 + f p.2)

end LinearityRates
end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSpectralWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

def Contracts (ρ : ℝ) : Prop :=
  ∀ f : V → ℝ, (𝔼 v, f v) = 0 → energy (G.adjacency f) ≤ ρ^2 * energy f

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_WalkMoments
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPWalkMoments

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {D : Type} [Fintype D]

namespace PortGraph
variable {V : Type} [Fintype V] [Nonempty V] [Nonempty D]
variable (G : PortGraph V D) (bad : V × D → Prop)

noncomputable def edgeMass (v : V) : ℝ := 𝔼 d, G.edgeHit bad v d

noncomputable def countSquareMean (n : ℕ) : ℝ := 𝔼 v, 𝔼 c, (G.badCount bad n v c)^2

end PortGraph
end MetricKMedian.PCP

end Inline_PCPWalkMoments

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TM2Response
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTM2Response

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)

noncomputable def stackPrefix (S : ∀ k, List (Γ k)) : Prefix M :=
  fun k => ⟨(S k).take (radius M), by simp only [List.length_take]; exact min_le_left _ _⟩
end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Response

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Hadamard
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_add _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_single _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_zero _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination _root_.OAI.MetricKMedian.PCP.QuadraticSystem.equationDiscrepancy_single _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_left _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_right _root_.OAI.MetricKMedian.PCP.dot_liftQuery _root_.OAI.MetricKMedian.PCP.dot_single _root_.OAI.MetricKMedian.PCP.dot_smul _root_.OAI.MetricKMedian.PCP.dot_sum _root_.OAI.MetricKMedian.PCP.dot_unitForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPHadamard

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Vectors
variable {V W : Type} [Fintype V] [Fintype W]

noncomputable def coordinates (f : BitVector V →+ Bit) : BitVector V := by
  classical
  exact fun i => f (Pi.single i 1)

def multiplicationDiscrepancy (f : BitVector V →+ Bit) (g : BitVector W →+ Bit)
    (h : BitVector (V × W) →+ Bit) : BitVector V →+ (BitVector W →+ Bit) where
  toFun x :=
    { toFun := fun y => h (tensor x y) - f x * g y
      map_zero' := by simp
      map_add' := by intros; simp [mul_add]; ring }
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp [add_mul]; ring

end Vectors
end MetricKMedian.PCP

end Inline_PCPHadamard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Quadratic
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQuadratic

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Quadratic
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

def Satisfies (a : BitVector V) : Prop := ∀ e, dot (tensor a a) (Q.form e) = Q.rhs e

noncomputable def equationRate (h : BitVector (V × V) → Bit) : ℝ :=
  testRate (fun p : BitVector E × BitVector (V × V) =>
    derivative h (Q.combination p.1) p.2 ≠ dot Q.rhs p.1)

end QuadraticSystem

noncomputable def multiplicationRate (f : BitVector V → Bit)
    (h : BitVector (V × V) → Bit) : ℝ :=
  testRate (fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.1 * f p.1.2 ≠ derivative h (tensor p.1.1 p.1.2) p.2)

end Quadratic
end MetricKMedian.PCP

end Inline_PCPQuadratic

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Boundary
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBoundary

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Boundary
variable {I V : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

noncomputable def boundaryRate (embed : I → V) (f : BitVector V → Bit)
    (u : BitVector I → Bit) : ℝ :=
  testRate (fun p : BitVector I × BitVector V =>
    derivative f (liftQuery embed p.1) p.2 ≠ u p.1)

end Boundary
end MetricKMedian.PCP

end Inline_PCPBoundary

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Tester
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTester

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def QuadraticSystem.rejectionWeight (Q : QuadraticSystem V E)
    (f : BitVector V → Bit) (h : BitVector (V × V) → Bit) : ℝ :=
  linearityRate f + linearityRate h + multiplicationRate f h + Q.equationRate h

end MetricKMedian.PCP

end Inline_PCPTester

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Queries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQueries

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]
variable (R : Relation K) [DecidablePred (· ∈ R)]

def packed (s : Fin 6 × Pad R) : FourQuery (LocalPosition R) := query R s.1 (s.2 s.1)

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPQueries

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_AlphabetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]

namespace FourCSP
variable {P T : Type} [Fintype T] (C : FourCSP P T)
def Satisfies (a : P → Bit) : Prop := ∀ t, ¬ (C.query t).Rejects a
noncomputable def rejection (a : P → Bit) : ℝ := testRate (fun t => (C.query t).Rejects a)
end FourCSP

end MetricKMedian.PCP

end Inline_PCPAlphabetReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRows

namespace MetricKMedian.PCP.Tableau
open scoped Classical

variable {A : Type}
lemma valid_row_list (L : ℕ) (row : Row A L) (h : ValidRow L row) :
    ∃ l : List A, l.length≤L ∧ ∀ i, l[i]?=rowCell L row i := by
  obtain ⟨l,hl,he⟩ := row_list (rowCell L row) L
    (by simpa only [rowCell,dite_eq_left (Nat.le_refl L)] using h.1)
    (by
      intro i hi hn
      simp only [rowCell,dite_eq_left (by omega : i≤L)] at hn
      simpa only [rowCell,dite_eq_left (by omega : i+1≤L)] using h.2 ⟨i,hi⟩ hn)
  refine ⟨l,hl,?_⟩
  intro i
  by_cases hi : i≤L
  · exact he i hi
  · rw [List.getElem?_eq_none (by omega),rowCell,dite_eq_right hi]
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauRows

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

def getControl (T L : ℕ) (a : Var (K := K) T L → Value M) (t : Fin (T+1)) : Control (Λ := Λ) (σ := σ) :=
  (a (ctrl T L t)).1
def getResponse (T L : ℕ) (a : Var (K := K) T L → Value M) (t : Fin T) : Response M :=
  (a (resp T L t)).2.1
def getRow (T L : ℕ) (a : Var (K := K) T L → Value M) (t : Fin (T+1)) (k : K) : Row (Γ k) L :=
  fun i => (a (cell T L t k i)).2.2 k
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauCorrect

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)

variable [Inhabited σ]
def emptyControl : Control (Λ := Λ) (σ := σ) := (none,default)
def emptyResponse : Response M := ⟨emptyControl,fun _ => ⟨[],by simp⟩⟩
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauCorrect

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_EqualityExpansion
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPEqualityExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

variable [Fintype A] [Nonempty A] (a : V → A)
noncomputable def equalityFailure : ℝ := testRate (fun z : V × D => a z.1 ≠ a (G.step z.1 z.2))

end PortGraph
end MetricKMedian.PCP

end Inline_PCPEqualityExpansion

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphProducts

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type}

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

variable [Fintype S] [Nonempty S]

noncomputable def cloud (H : PortGraph D S) (f : V × D → ℝ) : V × D → ℝ :=
  fun p => H.adjacency (fun d => f (p.1,d)) p.2
noncomputable def permute (G : PortGraph V D) (f : V × D → ℝ) : V × D → ℝ :=
  fun p => f (G.rotate p)

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphProducts

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_L2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPL2

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section
variable {S : Type} [Fintype S]

noncomputable def l2 (f : S → ℝ) : ℝ := Real.sqrt (energy f)

end

end MetricKMedian.PCP

end Inline_PCPL2

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_BinaryReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace IncidenceReduction
variable {P T : Type} [Fintype T] (C : FourCSP P T)

def decoded (a : P ⊕ T → Label) : P → Bit := fun p => a (.inl p) 0

end IncidenceReduction

end MetricKMedian.PCP

end Inline_PCPBinaryReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationStars
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def flag : Star I T → ℝ
  | .inl _ => 1
  | .inr _ => 0

omit [DecidableEq T] in

theorem mass_partition (y : I → ℝ) (P : T → Finset I)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t))) (F : Finset I) :
    (∑ i ∈ F ∩ outside P, y i)+(∑ t, ∑ i ∈ F ∩ P t, y i)=∑ i ∈ F, y i := by
  simp_rw [← sum_ite_mem]
  rw [sum_comm,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : ∃ t, i ∈ P t
  · obtain ⟨t,ht⟩ := hi
    have hu : i ∉ outside P := by simp only [outside,mem_filter,mem_univ,true_and]; exact fun h => h t ht
    rw [ite_eq_right hu,sum_eq_single t,ite_eq_left ht,zero_add]
    · intro s _ hst
      exact ite_eq_right (fun hs => (disjoint_left.mp (hP hst)) hs ht)
    · simp
  · have hu : i ∈ outside P := by simp only [outside,mem_filter,mem_univ,true_and]; exact fun t ht => hi ⟨t,ht⟩
    have hn : ∀ t, i ∉ P t := fun t ht => hi ⟨t,ht⟩
    simp only [ite_eq_left hu,hn,ite_false,sum_const_zero,add_zero]

theorem targeted_weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hc : ∀ t, ∑ i ∈ A t, y i=c t) (t : T) :
    (∑ e, if t ∈ targets A e then weight y P A c γ e else 0)=(1+γ)*c t := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [targets,weight,mem_filter,mem_univ,true_and,mem_singleton]
  have ho : (∑ i, if i ∈ A t then (if i ∈ outside P then y i else 0) else 0)=
      ∑ i ∈ A t ∩ outside P, y i := by
    rw [sum_ite_mem,univ_inter,sum_ite_mem]
  have hb : (∑ s, ∑ r, if t=s then ∑ i ∈ A s ∩ P r, y i else 0)=
      ∑ r, ∑ i ∈ A t ∩ P r, y i := by
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true]
  rw [ho,hb,sum_ite_eq,ite_eq_left (mem_univ t)]
  have hp := mass_partition y P hP (A t)
  rw [hc t] at hp
  linarith only [hp]

omit [DecidableEq T] in
 theorem flagged_weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ) :
    (∑ e, flag e*weight y P A c γ e)=∑ i ∈ outside P, y i := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [flag,weight,one_mul,zero_mul,sum_const_zero,add_zero,sum_ite_mem,univ_inter]

theorem raw_identity (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hunit : ∀ t, (∑ i ∈ P t, y i)+c t=1) :
    (Fintype.card T:ℝ)+(∑ e, (flag e-((targets A e).card:ℝ))*weight y P A c γ e)=
      (∑ i, y i)-γ*∑ t, c t := by
  simp_rw [sub_mul]
  rw [sum_sub_distrib,flagged_weight,target_card_sum]
  simp_rw [targeted_weight y P A c γ hP hc]
  rw [← mul_sum]
  have hp := mass_partition y P hP univ
  simp only [univ_inter] at hp
  have hu := congrArg (fun f : T → ℝ => ∑ t, f t) (funext hunit)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,card_univ] at hu
  linarith only [hu,hp]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedRounding
attribute [-simp] _root_.OAI.MetricKMedian.RationalWeightedStep.real_move
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

omit [Fintype I] in
theorem sign_distinct {i j k l : I} {r : ℝ} (hr : 0 ≤ r) (hkl : k ≠ l) :
    sign i j r k*sign i j r l ≤ 0 := by
  unfold sign
  split_ifs <;> simp_all

omit [Fintype I] in

theorem endpoint_mean (p : I → ℝ) (i j k : I) (r : ℝ) {u d : ℝ}
    (hu : 0 < u) (hd : 0 < d) :
    d/(u+d)*move p i j r u k+(1-d/(u+d))*move p i j r (-d) k=p k := by
  unfold move
  field_simp
  ring

omit [Fintype I] in
theorem endpoint_pair (p : I → ℝ) (i j : I) {k l : I} (hkl : k ≠ l) {r u d : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hd : 0 < d) :
    d/(u+d)*(move p i j r u k*move p i j r u l)+
      (1-d/(u+d))*(move p i j r (-d) k*move p i j r (-d) l) ≤ p k*p l := by
  have hpos : 0 < u+d := add_pos hu hd
  have hid : d/(u+d)*(move p i j r u k*move p i j r u l)+
      (1-d/(u+d))*(move p i j r (-d) k*move p i j r (-d) l) =
      p k*p l+u*d*(sign i j r k*sign i j r l) := by
    unfold move
    field_simp
    ring
  rw [hid]
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu.le hd.le)
    (sign_distinct hr hkl))

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_ExceptionalStar
attribute [-simp] _root_.OAI.MetricKMedian.RationalWeightedStep.real_fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset MarginalRounding
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

omit [DecidableEq E] [Fintype T] [DecidableEq T] in

theorem exceptional_raw_error (D : E → Finset T) (q a : E → ℝ) (S : E → Finset T)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (_ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1)
    (hsmall : (fractional q).card ≤ 1)
    (hS : ∀ e, |((S e).card:ℝ)-((D e).card:ℝ)*q e| ≤ 1 ∧
      (q e=0 → S e=∅) ∧ (q e=1 → S e=D e)) :
    (∑ e, (a e*(upperBit (q e)-q e)+((D e).card:ℝ)*q e-((S e).card:ℝ))) ≤ 2 := by
  let v : E → ℝ := fun e => a e*(upperBit (q e)-q e)+((D e).card:ℝ)*q e-((S e).card:ℝ)
  have hv0 : ∀ e, e ∉ fractional q → v e=0 := by
    intro e he
    rcases nonfractional_integral hq0 hq1 he with h | h
    · simp only [v, h, upperBit, lt_self_iff_false, ite_false, sub_self, mul_zero, zero_add,
        (hS e).2.1 h, card_empty, Nat.cast_zero]
    · simp only [v, h, upperBit, zero_lt_one, ite_true, sub_self, mul_zero, mul_one,
        zero_add, (hS e).2.2 h, sub_self]
  have hv : ∀ e, v e ≤ 2 := by
    intro e
    have hu := upperBit_bounds (hq0 e) (hq1 e)
    have hprod := mul_le_mul (ha1 e)
      (show upperBit (q e)-q e ≤ 1 by linarith only [hu.2, hq0 e])
      (sub_nonneg.mpr hu.1) (by norm_num : (0:ℝ) ≤ 1)
    have herr := (abs_le.mp (hS e).1).1
    dsimp only [v]
    nlinarith only [hprod, herr]
  have heq : (∑ e, v e)=∑ e ∈ fractional q, v e := by
    apply (sum_subset (subset_univ _) (fun e _ he => hv0 e he)).symm
  change (∑ e, v e) ≤ 2
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ fractional q, (2:ℝ) := sum_le_sum (fun e _ => hv e)
    _ = ((fractional q).card:ℝ)*2 := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ 2 := by exact_mod_cast (by omega : (fractional q).card*2 ≤ 2)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalWeightedStep
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) (k : Fin n) :
    probability β p*point (endpoint β p 0) k+
      (1-probability β p)*point (endpoint β p 1) k=point p k := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_mean (realPoint p) a.val.1 a.val.2 k (r:ℝ) hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalLastFraction
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial _root_.OAI.MetricKMedian.SparseWeightedPartial.features_pair _root_.OAI.MetricKMedian.SparseWeightedPartial.features_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalLastFraction
open Finset RationalWeightedStep
variable {n : ℕ}

theorem endpoint_mean (p : Vector ℚ n) (k : Fin n) :
    probability p*point (endpoint p 0) k+
      (1-probability p)*point (endpoint p 1) k=point p k := by
  by_cases h : (fractional p).Nonempty
  · simp only [probability,endpoint,dite_eq_left h,point,Vector.getElem_ofFn,Fin.eta]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    by_cases hi : k=pick p h
    · subst k; simp only [ite_true]; ring
    · simp only [ite_eq_right hi]; ring
  · simp only [probability,endpoint,dite_eq_right h]; ring

theorem nonfractional (p : Vector ℚ n)
    (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (k : Fin n)
    (hk : k ∉ fractional p) : point p k=0 ∨ point p k=1 := by
  have h := hp k
  simp only [fractional,mem_filter,mem_univ,true_and,not_and_or,not_lt] at hk
  rcases hk with hk | hk
  · exact Or.inl (le_antisymm hk h.1)
  · exact Or.inr (le_antisymm h.2 hk)

theorem endpoint_integral (p : Vector ℚ n)
    (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1)
    (hsmall : (fractional p).card ≤ 1) (b : Fin 2) (k : Fin n) :
    point (endpoint p b) k=0 ∨ point (endpoint p b) k=1 := by
  by_cases h : (fractional p).Nonempty
  · simp only [endpoint,dite_eq_left h,point,Vector.getElem_ofFn,Fin.eta]
    by_cases hk : k=pick p h
    · simp only [ite_eq_left hk]; split_ifs <;> simp
    · simp only [ite_eq_right hk]
      apply nonfractional p hp k
      intro hm
      exact hk (card_le_one.mp hsmall k hm (pick p h) (pick_mem p h))
  · simp only [endpoint,dite_eq_right h]
    apply nonfractional p hp
    exact fun hm => h ⟨k,hm⟩

theorem endpoint_noise (p : Vector ℚ n) (β : Fin n → ℚ) {M : ℚ}
    (hβ0 : ∀ k, 0 ≤ β k) (hβM : ∀ k, β k ≤ M) (hM : 0 ≤ M) (b : Fin 2) :
    |(∑ k, β k*point (endpoint p b) k)-(∑ k, β k*point p k)| ≤ M := by
  by_cases h : (fractional p).Nonempty
  · simp only [endpoint,dite_eq_left h]
    let i := pick p h
    have hi := (mem_filter.mp (pick_mem p h)).2
    rw [← sum_sub_distrib]
    have hid : (∑ k, (β k*point (Vector.ofFn
        (fun k => if k=pick p h then (if b=0 then 1 else 0) else point p k)) k-β k*point p k))=
        β i*((if b=0 then 1 else 0)-point p i) := by
      rw [sum_eq_single i]
      · simp only [point,Vector.getElem_ofFn,Fin.eta,i,ite_true]
        ring
      · intro k _ hki
        simp only [point,Vector.getElem_ofFn,Fin.eta,show k ≠ pick p h from hki,ite_false,sub_self]
      · intro hh; exact False.elim (hh (mem_univ i))
    rw [hid,abs_mul,abs_of_nonneg (hβ0 i)]
    have herr : |(if b=0 then (1:ℚ) else 0)-point p i| ≤ 1 := by
      apply abs_le.mpr
      split_ifs <;> constructor <;> dsimp only [i] <;> linarith only [hi.1,hi.2]
    exact (mul_le_mul_of_nonneg_left herr (hβ0 i)).trans (by simpa only [mul_one] using hβM i)
  · simpa only [endpoint,dite_eq_right h,sub_self,abs_zero] using hM

end MetricKMedian.RationalLastFraction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalRounding
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
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

theorem selected_indicator (q : Vector ℚ n)
    (hq : ∀ i, point q i=0 ∨ point q i=1) (i : Fin n) :
    (if i ∈ selected q then (1:ℚ) else 0)=point q i := by
  rcases hq i with h | h <;> simp [selected,h]

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedStep
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedStep
open Finset RationalWeightedStep
variable {n : ℕ}

theorem endpoint_mean (β : Fin n → ℚ) (p : Vector ℚ n) (k : Fin n) :
    probability β p*point (endpoint β p 0) k+
      (1-probability β p)*point (endpoint β p 1) k=point p k := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_mean (realPoint p) a.val.1 a.val.2 k (r:ℝ) hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add]

theorem endpoint_pair (β : Fin n → ℚ) 
    (p : Vector ℚ n) (k l : Fin n) (hkl : k ≠ l) :
    probability β p*(point (endpoint β p 0) k*point (endpoint β p 0) l)+
      (1-probability β p)*(point (endpoint β p 1) k*point (endpoint β p 1) l) ≤
        point p k*point p l := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hrr : (0:ℝ) ≤ r := by exact_mod_cast hr.le
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_pair (realPoint p) a.val.1 a.val.2 hkl hrr hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add,le_refl]

end MetricKMedian.RationalSignedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterLaw
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

def activation (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) : ℚ :=
  (if i∈D e then (base q e:ℚ) else 0)+(if i∈z.2.1 e then 1 else 0)

end MetricKMedian.SparseOuterLaw
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

theorem activationCount_cast (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) :
    (activationCount D q z e i:ℚ)=activation D q z e i := by
  simp only [activationCount,activation,Nat.cast_add,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedLaw
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
variable {n m f : ℕ}

def requests (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : Fin n → Fin m → ℕ :=
  fun j => RationalRetain.keep (fun e => activationCount D q z e j) (Δ/2)

theorem exact_total (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) :
    total D q Δ z j+(∑ e,requests D q Δ z j e)=Δ := by
  unfold total requests
  rw [RationalRetain.total]
  exact Nat.sub_add_cancel ((min_le_right _ _).trans (Nat.div_le_self _ _))

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

theorem flag_cast (e : Star (Fin f) (Fin n)) : (flagQ e : ℝ)=flag e := by
  cases e <;> simp [flagQ, flag]

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def balanced (Z : Finset E) (C : E → Finset E) (ω : E → Bool) : Finset E :=
  FiniteLaw.selected C ω ∩ Z

end MetricKMedian.PhysicalBatchLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Repeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRepeat

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Nested
instance fintype (A : Type) [Fintype A] : (n : ℕ) → Fintype (Nested A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := fintype A n; inferInstanceAs (Fintype (A × Nested A n))
instance nonempty (A : Type) [Nonempty A] : (n : ℕ) → Nonempty (Nested A n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => letI := nonempty A n; inferInstanceAs (Nonempty (A × Nested A n))
end Nested

end MetricKMedian.PCP

end Inline_PCPProjectionRepeat

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Tables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace Ordered
variable {V : Type} [DecidableEq V]
lemma entries_ofFn (o : Ordered V) : List.ofFn (fun i => o.equiv.symm i)=o.entries := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    have hh := o.get_equiv (o.equiv.symm ⟨i,hj⟩)
    simpa only [Equiv.apply_symm_apply] using hh.symm
lemma map_entries {C : Type} (o : Ordered V) (f : V→C) : o.entries.map f=List.ofFn (fun i => f (o.equiv.symm i)) := by
  calc
    _ = (List.ofFn (fun i=>o.equiv.symm i)).map f := congrArg (List.map f) (entries_ofFn o).symm
    _ = _ := List.map_ofFn
end Ordered
namespace ProjectionTable
variable {U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {nu : ℕ} (ue : U≃Fin nu) (vo : Ordered V) (so : Ordered S)
noncomputable def build : ProjectionTable A B :=
  (List.replicate nu (),vo.entries.map (fun v => so.entries.map (fun s =>
    ((ue (G.edge.symm (v,s)).1).val,G.project (G.edge.symm (v,s))))))
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_ProductTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionProductTable
namespace MetricKMedian.PCP.Compiler.ProjectionTable
open Binary Binary.Automatic
open scoped Classical

variable {A B A' B' : Type} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Inhabited B] [Inhabited B']
variable {U V D S U' V' D' S' : Type}
  [Fintype U] [Fintype V] [Fintype D] [Fintype S]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S']
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
  [DecidableEq V'] [DecidableEq S'] [DecidableEq A'] [DecidableEq B']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')
  {n n' : ℕ} (ue : U≃Fin n) (ue' : U'≃Fin n')
  (vo : Ordered V) (vo' : Ordered V') (so : Ordered S) (so' : Ordered S')
omit [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Inhabited B] [Inhabited B']
  [Fintype U] [Fintype V] [Fintype D] [Fintype S]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S']
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
  [DecidableEq V'] [DecidableEq S'] [DecidableEq A'] [DecidableEq B'] in
lemma product_build : product (build G ue vo so) (build H ue' vo' so')=
    build (G.prod H) ((ue.prodCongr ue').trans finProdFinEquiv) (vo.prod vo') (so.prod so') := by
  apply Prod.ext
  · apply unitList_eq_length
    simp only [product,build,List.length_replicate]
    rw [length_flatMap_uniform _ _ n' (by intros; simp only [List.length_replicate])]
    simp only [List.length_replicate]
  · simp only [product,build,Ordered.prod,List.product,List.flatMap_map,List.map_flatMap,List.map_map,
      Function.comp_def,combine,List.length_replicate,BiProjection.prod,Equiv.trans_apply,
      Equiv.prodCongr_apply,Prod.map,finProdFinEquiv]
    rfl
end MetricKMedian.PCP.Compiler.ProjectionTable

end Inline_PCPProjectionProductTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RowsBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRowsBuild
namespace MetricKMedian.PCP.Compiler.ProjectionTable
open scoped Classical

variable {Z U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
omit [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B] in
lemma rows_build (G : BiProjection U V D S A B) {m k : ℕ} (ue : U≃Fin (m*k)) (ve : V≃Fin m)
    (so : Ordered S) (xs : List Z) (hx : xs.length=m) (row : ℕ→S→ProjectionRow A B)
    (hr : ∀v s,row (ve v).val s=((ue (G.edge.symm (v,s)).1).val,G.project (G.edge.symm (v,s)))) :
    (xs.flatMap (fun _=>List.replicate k ()),(List.range xs.length).map (fun v=>so.entries.map (row v)))=
      build G ue ((Ordered.fin m).map ve.symm) so := by
  apply Prod.ext
  · apply unitList_eq_length
    simp only [build,List.length_replicate]
    rw [length_flatMap_uniform _ _ k (by intros; simp only [List.length_replicate]),hx]
  · change (List.range xs.length).map _ = _
    rw [hx]
    simp only [build,Ordered.map,Ordered.fin,List.map_map,Function.comp_def]
    have he (i : Fin m) : (ve (ve.symm i)).val=i.val := congrArg Fin.val (ve.apply_symm_apply i)
    simp_rw [← hr,he]
    rw [RoundingList.range_finRange,List.map_map]
    rfl
end MetricKMedian.PCP.Compiler.ProjectionTable

end Inline_PCPProjectionRowsBuild

end OAI
end


