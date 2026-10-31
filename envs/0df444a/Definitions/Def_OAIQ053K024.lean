-- Prove2me | Definitions.Def_OAIQ053K024
-- name    : OAIQ053K024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:58:01.157266+00:00
-- url     : https://prove2.me/theorems/5fc2fc8b-8353-462a-b9a8-960f20747f1d
-- title:
--   Definitions bundle OAIQ053K024 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 40 definitions, 1 inductive type or structure, 3 instances and 16 theorems. The definitions and types are `OAI.MetricKMedian.PCP.BiProjection.Expands`, `OAI.MetricKMedian.PCP.BiProjection.Perfect`, `OAI.MetricKMedian.PCP.BiProjection.Sound`, `OAI.MetricKMedian.PCP.BiProjection.collisionNorm`, `OAI.MetricKMedian.PCP.BiProjection.impossible`, `OAI.MetricKMedian.PCP.BiProjection.input`, `OAI.MetricKMedian.PCP.BiProjection.neutral`, `OAI.MetricKMedian.PCP.BiProjection.partialPush`, `OAI.MetricKMedian.PCP.BiProjection.power`, `OAI.MetricKMedian.PCP.BiProjection.reindex`, `OAI.MetricKMedian.PCP.BiProjection.scalarPush`, `OAI.MetricKMedian.PCP.BiProjection.score`, `OAI.MetricKMedian.PCP.BiProjection.system`, `OAI.MetricKMedian.PCP.BiProjection.trivial`, `OAI.MetricKMedian.PCP.BinaryCSP.Satisfies`, `OAI.MetricKMedian.PCP.BinaryCSP.mapLabels`, `OAI.MetricKMedian.PCP.BinaryCSP.pullLabels`, `OAI.MetricKMedian.PCP.BinaryCSP.reindex`, `OAI.MetricKMedian.PCP.BinaryCSP.rejection`, `OAI.MetricKMedian.PCP.CloudCopies.dartFlip`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.B`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.I`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.Tag`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.bitIndex`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.info`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.intIndex`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.positionInfo`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.Represents`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.Represents.relabel`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.build`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.build_represents`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.csp`, `OAI.MetricKMedian.PCP.Compiler.Expander.Raw`, `OAI.MetricKMedian.PCP.Compiler.Expander.nodeIndex`, `OAI.MetricKMedian.PCP.Compiler.Ordered.filter`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.table`, `OAI.MetricKMedian.PCP.ExpanderFamily.vertexEquiv`, `OAI.MetricKMedian.PCP.MixedNorm.norm`, `OAI.MetricKMedian.PCP.PortGraph.labelMass`, `OAI.MetricKMedian.PCP.PortGraph.majorityLabel` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_LabelTransport`, `KMedian_Amplification_RegularizationObjects`, `KMedian_CookLevin_FiniteConstraints`, `KMedian_CookLevin_TableauSystem`, `KMedian_Expanders_EqualityExpansion`, `KMedian_Expanders_ExpanderFamily`, `KMedian_Expanders_ExpanderGuard`, `KMedian_Expanders_ExpanderIndex`, `KMedian_Expanders_ExpanderStep`, `KMedian_Machines_AlphabetIndex`, `KMedian_Machines_BinaryReindex`, `KMedian_Machines_BlendSpec`, `KMedian_Machines_FixedImpossible`, `KMedian_Machines_Ordered`, `KMedian_Machines_OrderedLists`, `KMedian_Machines_RawCSP`, `KMedian_Machines_RawRotation`, `KMedian_Machines_RelabelTables`, `KMedian_Machines_RotationBounds`, `KMedian_Machines_TableBuilders`, `KMedian_PCP_AlphabetReduction`, `KMedian_PCP_Queries`, `KMedian_Projection_Contraction`, `KMedian_Projection_Expansion`, `KMedian_Projection_Input`, `KMedian_Projection_Norm`, `KMedian_Projection_Product`, `KMedian_Projection_Promises`, `KMedian_Projection_Reindex`, `KMedian_Projection_Repeat`, `KMedian_Projection_Rounding`, `KMedian_Projection_Seed`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K006`, `OAIQ053K008`, `OAIQ053K009` and `OAIQ053K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K035` and `OAIQ053K036`; the statements `OAI.MetricKMedian.PCP.AlphabetReduction.padded_complete_s53`, `OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53`, `OAI.MetricKMedian.PCP.BiProjection.collision_sound_s53` and `OAI.MetricKMedian.PCP.BiProjection.variance_bound_s53`; the proofs of `OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53`, `OAI.MetricKMedian.PCP.BiProjection.collision_sound_s53`, `OAI.MetricKMedian.PCP.BiProjection.variance_bound_s53` and `OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K006
import Definitions.Def_OAIQ053K008
import Definitions.Def_OAIQ053K009
import Definitions.Def_OAIQ053K010

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Queries
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff
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

instance sampleNonempty (i : Fin 6) : Nonempty (Sample R i) := by
  fin_cases i <;> dsimp [Sample] <;> infer_instance

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

namespace BinaryCSP
variable {A : Type} [DecidableEq A] (C : BinaryCSP V E A)
def Satisfies (a : V → A) : Prop := ∀ e, (a (C.left e), a (C.right e)) ∈ C.allowed e
noncomputable def rejection (a : V → A) : ℝ :=
  testRate (fun e => (a (C.left e), a (C.right e)) ∉ C.allowed e)
end BinaryCSP

end MetricKMedian.PCP

end Inline_PCPAlphabetReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_LabelTransport
attribute [-simp] _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLabelTransport

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E A B : Type} [Fintype E] [DecidableEq A] [DecidableEq B]
variable (C : BinaryCSP V E A) (e : A ≃ B)
def mapLabels : BinaryCSP V E B where
  left := C.left
  right := C.right
  allowed t := (C.allowed t).map (e.prodCongr e).toEmbedding

omit [Fintype E] [DecidableEq A] [DecidableEq B] in
@[simp] lemma mapLabels_allowed (t : E) (a b : B) :
    (a,b) ∈ (C.mapLabels e).allowed t ↔ (e.symm a,e.symm b) ∈ C.allowed t := by
  simp [mapLabels,Finset.mem_map_equiv]

end BinaryCSP

end MetricKMedian.PCP

end Inline_PCPLabelTransport

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_EqualityExpansion
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
noncomputable def labelMass (b : A) : ℝ := testRate (fun v => a v=b)

noncomputable def majorityLabel : A := Classical.choose (show ∃ b : A, ∀ c : A,
    labelMass a c ≤ labelMass a b from by
  obtain ⟨b,_,hb⟩ := exists_max_image univ (labelMass a) univ_nonempty
  exact ⟨b,fun c => hb c (mem_univ c)⟩)

end PortGraph
end MetricKMedian.PCP

end Inline_PCPEqualityExpansion

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderFamily
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderFamily

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace ExpanderFamily

instance vertexNonempty : (n : ℕ) → Nonempty (Vertex n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => letI := vertexNonempty n; inferInstanceAs (Nonempty (Vertex n × Branch))

lemma padding_upper (n : ℕ) : Fintype.card (Vertex (level n)) ≤ growth*(n+1) := by
  rw [card_vertex,level,pow_succ]
  have h := Nat.pow_log_le_self growth (Nat.succ_ne_zero n)
  exact (Nat.mul_le_mul_right growth h).trans_eq (Nat.mul_comm _ _)

end ExpanderFamily
end MetricKMedian.PCP

end Inline_PCPExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularizationObjects
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularizationObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
variable (C : BinaryCSP V E A)

def dartFlip : Dart (E := E) ≃ Dart (E := E) where
  toFun d := (d.1,!d.2)
  invFun d := (d.1,!d.2)
  left_inv d := by simp
  right_inv d := by simp

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPRegularizationObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_FiniteConstraints
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteConstraints

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E A B : Type} [DecidableEq A] [Fintype B]
variable (C : BinaryCSP V E A) (decode : B → A)
noncomputable def pullLabels : BinaryCSP V E B where
  left := C.left
  right := C.right
  allowed e := univ.filter (fun p => (decode p.1,decode p.2)∈C.allowed e)
end BinaryCSP
end MetricKMedian.PCP

end Inline_PCPFiniteConstraints

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
def qtop (k : K) (i : Fin (radius M)) : Query M := .inr (.inr (.inl (k,i)))
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderIndex
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderIndex
namespace MetricKMedian.PCP.ExpanderFamily
open scoped Classical

noncomputable def vertexEquiv : (n : ℕ) → Vertex n ≃ Fin ((Fintype.card Branch)^n)
  | 0 => (Equiv.ofUnique Unit (Fin 1)).trans (finCongr (pow_zero (Fintype.card Branch)).symm)
  | n+1 => ((vertexEquiv n).prodCongr (Fintype.equivFin Branch)).trans
      (finProdFinEquiv.trans (finCongr (pow_succ _ _).symm))
lemma vertexEquiv_succ (n : ℕ) (v : Vertex n) (b : Branch) :
    (vertexEquiv (n+1) (v,b)).val=(vertexEquiv n v).val*Fintype.card Branch+(Fintype.equivFin Branch b).val := by
  change (Fintype.equivFin Branch b).val+Fintype.card Branch*(vertexEquiv n v).val=_
  simp only [Nat.mul_comm, Nat.add_comm]
end MetricKMedian.PCP.ExpanderFamily

end Inline_PCPExpanderIndex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawRotation
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawRotation

namespace MetricKMedian.PCP.Compiler
open Binary
open scoped Classical

namespace RotationTable
variable {D : Type} [Fintype D] [Inhabited D]
noncomputable def table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) : RotationTable D :=
  List.ofFn (fun i : Fin N => ports.map (fun d => ((e (G.step (e.symm i) d)).val,G.back (e.symm i) d)))
omit [Inhabited D] in
@[simp] lemma table_length {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) :
    (table G e).length=N := List.length_ofFn
lemma lookup_table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) (v : V) (d : D) :
    lookup (table G e) (e v).val d=((e (G.step v d)).val,G.back v d) := by
  simp only [lookup,table,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some,
    Fin.eta,Equiv.symm_apply_apply,ports,List.map_ofFn]
  simp only [Function.comp_def,Equiv.symm_apply_apply]
end RotationTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawRotation

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderStep
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderStep

namespace MetricKMedian.PCP.Compiler.Expander
open Binary ExpanderFamily RotationTable
open scoped Classical

abbrev Raw := RotationTable Degree
noncomputable def nodeIndex (v : ℕ) (b : Branch) : ℕ := v*growth+(Fintype.equivFin Branch b).val
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderStep

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RotationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRotationBounds
namespace MetricKMedian.PCP.Compiler.RotationTable
open Binary Finset
open scoped BigOperators Classical

variable {D : Type} [Fintype D] [Inhabited D]
omit [Inhabited D]
lemma table_wellFormed {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) :
    WellFormed (table G e) := by
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  constructor
  · simp only [List.length_map,ports_length]
  · intro q hq
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hq
    simpa only [table_length] using (e (G.step (e.symm i) d)).isLt
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRotationBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderGuard
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable Binary
open scoped Classical

lemma level_le (n : ℕ) : level n ≤ n+1 := by
  have h := Nat.log_lt_self growth (Nat.succ_ne_zero n)
  unfold level
  have h' : Nat.log growth (n+1) < n+1 := by simpa only [Nat.succ_eq_add_one] using h
  omega
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderGuard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_BinaryReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReindex

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E V' E' A : Type} [DecidableEq A]
variable (C : BinaryCSP V E A) (ev : V ≃ V') (ee : E ≃ E')
def reindex : BinaryCSP V' E' A where
  left e := ev (C.left (ee.symm e))
  right e := ev (C.right (ee.symm e))
  allowed e := C.allowed (ee.symm e)
end BinaryCSP
end MetricKMedian.PCP

end Inline_PCPBinaryReindex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawCSP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawCSP
namespace MetricKMedian.PCP.Compiler
open Binary
open scoped Classical

namespace CSPTable
variable {A : Type} [Fintype A] [DecidableEq A]
noncomputable def csp (t : CSPTable A) (h : WellFormed t) :
    BinaryCSP (Fin t.1.length) (Fin t.2.length) A where
  left e := ⟨t.2[e.val].1,(h.2 _ (List.getElem_mem e.isLt)).1⟩
  right e := ⟨t.2[e.val].2.1,(h.2 _ (List.getElem_mem e.isLt)).2⟩
  allowed e := t.2[e.val].2.2
variable {V E : Type} [Fintype V] [Fintype E]
structure Represents (t : CSPTable A) (C : BinaryCSP V E A) where
  vertex : V ≃ Fin t.1.length
  edge : E ≃ Fin t.2.length
  row : ∀ e, t.2[(edge e).val]=((vertex (C.left e)).val,(vertex (C.right e)).val,C.allowed e)
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawCSP

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AlphabetIndex
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetIndex
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
noncomputable instance sampleInhabited : Inhabited (EdgeSample K) := Classical.inhabited_of_nonempty inferInstance
abbrev Tag := EdgeSample K × Fin 4
noncomputable def B : ℕ := Fintype.card (BitVector K)
noncomputable def I : ℕ := Fintype.card (UniversalInterior K)
noncomputable def bitIndex (b : BitVector K) : ℕ := (Fintype.equivFin _ b).val
noncomputable def intIndex (b : UniversalInterior K) : ℕ := (Fintype.equivFin _ b).val
noncomputable def positionInfo (R : Relations K) : LocalRelation.LocalPosition (R : LocalRelation.Relation K) → Fin 3 × ℕ
  | .inl x => (2,intIndex K ⟨R,.inl x⟩)
  | .inr (.inl x) => (2,intIndex K ⟨R,.inr x⟩)
  | .inr (.inr (b,x)) => (if b=0 then 0 else 1,bitIndex K x)
noncomputable def info (R : Relations K) (z : Tag K) : Fin 3 × ℕ :=
  positionInfo K R ((LocalRelation.query (R : LocalRelation.Relation K) z.1.1 (z.1.2 R z.1.1)).address z.2)
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetIndex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_BlendSpec
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBlendSpec
namespace MetricKMedian.PCP.PortGraph
variable {V W D S : Type} (G : PortGraph V D) (H : PortGraph V S) (code : V → W)
lemma blend_coded (v : V) (d : BlendPort (D := D) (S := S)) :
    (code ((G.blend H).step v d),(G.blend H).back v d)=
      if d.1=0 then (code (G.step v d.2.1),(d.1,(G.back v d.2.1,d.2.2)))
      else (code (H.step v d.2.2),(d.1,(d.2.1,H.back v d.2.2))) := by
  change (code (blendRotate G H (v,d)).1,(blendRotate G H (v,d)).2)=_
  by_cases hd : d.1=0 <;> simp only [blendRotate,hd,ite_true,ite_false]
end MetricKMedian.PCP.PortGraph

end Inline_PCPBlendSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionNorm

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {V T : Type} [Fintype V] [Fintype T]

noncomputable def norm (f : V → T → ℝ) : ℝ := Real.sqrt (sq f)

end MixedNorm
end MetricKMedian.PCP

end Inline_PCPProjectionNorm

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable (G : BiProjection U V D S A B)

def Expands (γ : ℝ) : Prop := ∀ h : U → ℝ,
  energy (G.average h) ≤ (1-γ)*energy h+γ*(𝔼 u, h u)^2

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionExpansion

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Rounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRounding

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

noncomputable def score (a : U → A) (b : V → B) : ℝ :=
  𝔼 u, 𝔼 d, if G.project (u,d) (a u)=b (G.edge (u,d)).1 then 1 else 0

def Sound (s : ℝ) : Prop := ∀ a b, G.score a b ≤ s

noncomputable def scalarPush (f : U → A → ℝ) (v : V) (b : B) : ℝ :=
  G.push (fun u a (_ : Unit) => f u a) v b ()

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRounding

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Contraction
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionContraction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

noncomputable def collisionNorm (f : U → A → T → ℝ) : ℝ :=
  MixedNorm.norm (fun v (p : B × T) => G.push f v p.1 p.2)

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionContraction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionProduct

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' T I : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Fintype T] [Fintype I]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')

noncomputable def partialPush (f : (U × U') → (A × A') → T → ℝ) :
    U → A → (V' × (B' × T)) → ℝ := fun u a z =>
  H.push (fun u' a' t => f (u,u') (a,a') t) z.1 z.2.1 z.2.2

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionProduct

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

namespace BiProjection
variable {U V D S A B : Type}
def trivial : BiProjection Unit Unit Unit Unit Unit Unit where
  edge := Equiv.refl _
  project _ _ := ()
def power (G : BiProjection U V D S A B) : (n : ℕ) →
    BiProjection (Nested U n) (Nested V n) (Nested D n) (Nested S n) (Nested A n) (Nested B n)
  | 0 => trivial
  | n+1 => G.prod (power G n)

variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

def Perfect (G : BiProjection U V D S A B) : Prop :=
  ∃ a : U → A, ∃ b : V → B, ∀ u d, G.project (u,d) (a u)=b (G.edge (u,d)).1

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRepeat

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FixedImpossible
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFixedImpossible

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection

def impossible : BiProjection Bool Bool Bool Bool Bool Bool where
  edge := Equiv.prodComm Bool Bool
  project p a := if p.1 && p.2 then !a else a

lemma impossible_consistent : impossible.Consistent := by
  intro u d e h a
  change d=e at h
  subst e
  rfl

end BiProjection
end MetricKMedian.PCP

end Inline_PCPFixedImpossible

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_Ordered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPOrdered

namespace MetricKMedian.PCP.Compiler
open scoped Classical

namespace Ordered
variable {A B : Type} [DecidableEq A] [DecidableEq B]

def filter (o : Ordered A) (p : A → Prop) [DecidablePred p] : Ordered {a // p a} where
  entries := o.entries.attach.filterMap (fun a => if h : p a.val then some ⟨a.val,h⟩ else none)
  nodup := by
    apply List.Nodup.filterMap _ o.nodup.attach
    intro a b c ha hb
    split_ifs at ha hb <;> simp_all
    exact Subtype.ext (congrArg (fun x : {a // p a} => x.val) (ha.trans hb.symm))
  all a := by
    apply List.mem_filterMap.mpr
    refine ⟨⟨a.val,o.all a.val⟩,List.mem_attach _ _,?_⟩
    simp only [dite_eq_left a.property]
end Ordered
end MetricKMedian.PCP.Compiler

end Inline_PCPOrdered

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_OrderedLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPOrderedLists
namespace MetricKMedian.PCP.Compiler.Ordered
open scoped Classical

variable {A B : Type} [DecidableEq A] [DecidableEq B]
omit [DecidableEq A] in
lemma filter_val (o : Ordered A) (p : A → Prop) [DecidablePred p] :
    ((o.filter p).entries.map Subtype.val)=o.entries.filter (fun a => decide (p a)) := by
  unfold filter
  rw [List.map_filterMap]
  have hf : (fun a : {a // a∈o.entries} =>
    Option.map Subtype.val (if h : p a.val then some (⟨a.val,h⟩ : {a // p a}) else none))=
      (fun a : {a // a∈o.entries} => Option.guard (fun x => decide (p x)) a.val) := by
    funext a
    by_cases h : p a.val <;> simp [h,Option.guard]
  rw [hf]
  change List.filterMap ((Option.guard (fun x => decide (p x))) ∘ Subtype.val) o.entries.attach = _
  rw [← List.filterMap_map,List.attach_map_subtype_val,List.filterMap_eq_filter]
end MetricKMedian.PCP.Compiler.Ordered

end Inline_PCPOrderedLists

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RelabelTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRelabelTables
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary
open scoped Classical

variable {A B V E : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Fintype V] [Fintype E]
noncomputable def Represents.relabel {s : CSPTable A} {C : BinaryCSP V E A}
    (r : s.Represents C) (e : A ≃ B) : (s.relabel e).Represents (C.mapLabels e) where
  vertex := r.vertex
  edge := r.edge.trans (finCongr (List.length_map _).symm)
  row j := by
    change (s.2.map _)[(r.edge j).val]=_
    rw [List.getElem_map,r.row]
    rfl
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRelabelTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_TableBuilders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableBuilders
namespace MetricKMedian.PCP.Compiler
open scoped Classical

namespace CSPTable
variable {V E A : Type} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]
noncomputable def build (C : BinaryCSP V E A) (vo : Ordered V) (eo : Ordered E) : CSPTable A :=
  (vo.entries.map (fun _ => ()),eo.entries.map (fun e => ((vo.equiv (C.left e)).val,(vo.equiv (C.right e)).val,C.allowed e)))
noncomputable def build_represents (C : BinaryCSP V E A) (vo : Ordered V) (eo : Ordered E) :
    (build C vo eo).Represents C where
  vertex := vo.equiv.trans (finCongr (by simp only [build,List.length_map]))
  edge := eo.equiv.trans (finCongr (by simp only [build,List.length_map]))
  row e := by
    change (eo.entries.map (fun j => ((vo.equiv (C.left j)).val,(vo.equiv (C.right j)).val,C.allowed j)))[(eo.equiv e).val]=
      ((vo.equiv (C.left e)).val,(vo.equiv (C.right e)).val,C.allowed e)
    rw [List.getElem_map,Ordered.get_equiv]
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPTableBuilders

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Input
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionInput

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {u v d s a b : ℕ}
variable (G : BiProjection (Fin u) (Fin v) (Fin d) (Fin s) (Fin a) (Fin b))
def system : Coverage.ProjectionSystem (Fin u) (Fin v) (Fin s) (Fin a) (Fin b) where
  neighbor v s := (G.edge.symm (v,s)).1
  project v s := G.project (G.edge.symm (v,s))

lemma system_regular : G.system.LeftRegular d := by
  intro x
  change (univ.filter (fun p : Fin v × Fin s => (G.edge.symm p).1=x)).card=d
  rw [card_filter]
  calc
    _ = ∑ p : Fin u × Fin d, if p.1=x then 1 else 0 :=
      Equiv.sum_comp G.edge.symm (fun p : Fin u × Fin d => if p.1=x then (1:ℕ) else 0)
    _ = d := by
      simp only [Fintype.sum_prod_type]
      rw [sum_comm]
      simp
lemma system_consistent (h : G.Consistent) : G.system.DuplicateConsistent := by
  intro y i j he c
  let p := G.edge.symm (y,i)
  let q := G.edge.symm (y,j)
  have hp : G.edge p=(y,i) := G.edge.apply_symm_apply _
  have hq : G.edge q=(y,j) := G.edge.apply_symm_apply _
  have hx : p.1=q.1 := he
  have ht : (G.edge (p.1,p.2)).1=(G.edge (p.1,q.2)).1 := by
    have hq' : (p.1,q.2)=q := by rw [hx]
    simp only [Prod.eta,hq',hp,hq]
  change G.project p c=G.project q c
  have hh := h p.1 p.2 q.2 ht c
  have hq' : (p.1,q.2)=q := by rw [hx]
  simpa only [Prod.eta,hq'] using hh

noncomputable def input (hu : 0<u) (hv : 0<v) (hs : 0 < s) (ha : 0<a) (hb : 0<b)
    (hc : G.Consistent) : Coverage.ProjectionInput s a b where
  u := u
  v := v
  u_pos := hu
  v_pos := hv
  r_pos := hs
  a_pos := ha
  b_pos := hb
  system := G.system
  degree := d
  regular := G.system_regular
  consistent := G.system_consistent hc

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionInput

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Promises
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionPromises

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' : Type}
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')
lemma consistent_prod (hG : G.Consistent) (hH : H.Consistent) : (G.prod H).Consistent := by
  rintro ⟨u,u'⟩ ⟨d,d'⟩ ⟨e,e'⟩ he ⟨a,a'⟩
  have h0 : (G.edge (u,d)).1=(G.edge (u,e)).1 := congrArg (fun p : V × V' => p.1) he
  have h1 : (H.edge (u',d')).1=(H.edge (u',e')).1 := congrArg (fun p : V × V' => p.2) he
  exact Prod.ext (hG u d e h0 a) (hH u' d' e' h1 a')
lemma consistent_power (hG : G.Consistent) (n : ℕ) : (G.power n).Consistent := by
  induction n with
  | zero => exact fun _ _ _ _ _ => rfl
  | succ n ih => exact G.consistent_prod (G.power n) hG ih
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionPromises

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionReindex

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' : Type}
variable (G : BiProjection U V D S A B)
variable (eu : U ≃ U') (ev : V ≃ V') (ed : D ≃ D') (es : S ≃ S')
variable (ea : A ≃ A') (eb : B ≃ B')
def reindex : BiProjection U' V' D' S' A' B' where
  edge := ((eu.prodCongr ed).symm.trans G.edge).trans (ev.prodCongr es)
  project p a := eb (G.project ((eu.prodCongr ed).symm p) (ea.symm a))

lemma reindex_consistent (h : G.Consistent) : (G.reindex eu ev ed es ea eb).Consistent := by
  intro u d e he a
  have hh : (G.edge (eu.symm u,ed.symm d)).1=(G.edge (eu.symm u,ed.symm e)).1 := ev.injective he
  exact congrArg eb (h (eu.symm u) (ed.symm d) (ed.symm e) hh (ea.symm a))

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionReindex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Seed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionSeed

namespace MetricKMedian.PCP
open Finset
open scoped Classical BigOperators

namespace BiProjection
variable (D S A B : Type) [Inhabited A] [Inhabited B]
def neutral : BiProjection S D D S A B where
  edge := Equiv.prodComm _ _
  project _ _ := default
omit [Inhabited A] in
lemma neutral_consistent : (neutral D S A B).Consistent := fun _ _ _ _ _ => rfl
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end


