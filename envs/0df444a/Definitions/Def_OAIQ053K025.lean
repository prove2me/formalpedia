-- Prove2me | Definitions.Def_OAIQ053K025
-- name    : OAIQ053K025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:58:13.891429+00:00
-- url     : https://prove2.me/theorems/86a21a8c-3d5b-4c5c-a485-c116c2d40644
-- title:
--   Definitions bundle OAIQ053K025 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 31 definitions, 4 instances and 17 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.LocalCompiler.row`, `OAI.MetricKMedian.PCP.Compiler.LocalCompiler.table`, `OAI.MetricKMedian.PCP.Compiler.Ordered.nested`, `OAI.MetricKMedian.PCP.Compiler.Ordered.sum`, `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.nestedEquiv`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.boolOrder`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.boundaries`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.boundaryCode`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.boundaryOrder`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.clauseCode`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.clauseOrder`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.clauses`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.firstControlSet`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.lastCellSet`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.lastControlSet`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.rawQuery`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.testCode`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.testOrder`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.tests`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.varOrder`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.vars`, `OAI.MetricKMedian.PCP.FiniteCSP.binary`, `OAI.MetricKMedian.PCP.PortGraph.incidence`, `OAI.MetricKMedian.PCP.PortGraph.incidenceEdge`, `OAI.MetricKMedian.PCP.Tableau.PrefixRelation`, `OAI.MetricKMedian.PCP.Tableau.boundaryQuery`, `OAI.MetricKMedian.PCP.Tableau.boundaryRelation`, `OAI.MetricKMedian.PCP.Tableau.cellTable`, `OAI.MetricKMedian.PCP.Tableau.query`, `OAI.MetricKMedian.PCP.Tableau.qwin`, `OAI.MetricKMedian.PCP.Tableau.respond`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_CookLevin_FiniteConstraints`, `KMedian_CookLevin_TM2Locality`, `KMedian_CookLevin_TM2Response`, `KMedian_CookLevin_TableauBoundary`, `KMedian_CookLevin_TableauDirectories`, `KMedian_CookLevin_TableauLocal`, `KMedian_CookLevin_TableauQueryProgram`, `KMedian_CookLevin_TableauRelationProgram`, `KMedian_CookLevin_TableauSystem`, `KMedian_Expanders_PortWalk`, `KMedian_Machines_AdviceInstances`, `KMedian_Machines_LocalCompiler`, `KMedian_Machines_TableBuilders`, `KMedian_Machines_UnaryPolynomial`, `KMedian_Projection_IncidenceOperator`, `KMedian_Projection_PowerTable`, `KMedian_Projection_Tables`.
--
--   **Imports.** It imports the bundles `OAIQ053K002`, `OAIQ053K008`, `OAIQ053K009`, `OAIQ053K010` and `OAIQ053K011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K035` and `OAIQ053K036`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K008
import Definitions.Def_OAIQ053K009
import Definitions.Def_OAIQ053K010
import Definitions.Def_OAIQ053K011

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

namespace FiniteCSP
variable {V T Q A : Type} [Fintype Q] [Fintype A] [DecidableEq A]
variable [Nonempty Q] [Inhabited A]
variable (C : FiniteCSP V T Q A)
noncomputable def binary : BinaryCSP (V ⊕ T) (T × Q) (Label (Q := Q) (A := A)) where
  left t := .inl (C.query t.1 t.2)
  right t := .inr t.1
  allowed t := univ.filter (fun p => ∃ a b, p=(Sum.inl a,Sum.inr b) ∧
    b∈C.accept t.1 ∧ a=b t.2)
end FiniteCSP
end MetricKMedian.PCP

end Inline_PCPFiniteConstraints

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_PortWalk
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPortWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D : Type} (G : PortGraph V D)

namespace Walk
variable {G} {n : ℕ}

instance instFintype [Fintype V] [Fintype D] : Fintype (G.Walk n) := Fintype.ofEquiv _ wordEquiv.symm

end Walk
end PortGraph
end MetricKMedian.PCP

end Inline_PCPPortWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TM2Locality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTM2Locality

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

lemma stepAux_length (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (j : K) :
    ((stepAux q v S).stk j).length ≤ (S j).length+depth q := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [stepAux,depth]
    have h := ih v (update S k (f v::S k))
    by_cases he : j=k
    · subst j; simp only [update_self,List.length_cons] at h; omega
    · simp only [update_of_ne he] at h
      omega
  | peek k f q ih =>
    simp only [stepAux,depth]
    exact (ih _ _).trans (by omega)
  | pop k f q ih =>
    simp only [stepAux,depth]
    have h := ih (f v (S k).head?) (update S k (S k).tail)
    by_cases he : j=k
    · subst j; simp only [update_self,List.length_tail] at h; omega
    · simp only [update_of_ne he] at h
      omega
  | load f q ih =>
    simp only [stepAux,depth]
    exact (ih _ _).trans (by omega)
  | branch f q r ihq ihr =>
    simp only [stepAux,depth]
    cases hf : f v
    · simp only [Bool.cond_false]
      exact (ihr _ _).trans (by omega)
    · simp only [Bool.cond_true]
      exact (ihq _ _).trans (by omega)
  | goto f => simp [stepAux,depth]
  | halt => simp [stepAux,depth]
end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Locality

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
omit [DecidableEq K] in
lemma depth_le (l : Λ) : depth (M l) ≤ radius M := by
  exact Finset.le_sup (f := fun l => depth (M l)) (Finset.mem_univ l)

noncomputable def respond (c : Control (Λ := Λ) (σ := σ)) (p : Prefix M) : Response M :=
  let next := advance M ⟨c.1,c.2,fun k => (p k).val⟩
  ⟨(next.l,next.var),fun k => ⟨next.stk k,by
    dsimp [next,advance]
    cases h : c.1 with
    | none => simpa [h] using (p k).property.trans (Nat.le_mul_of_pos_left _ (by omega))
    | some l =>
      exact (stepAux_length (M l) c.2 (fun j => (p j).val) k).trans
        (by have := (p k).property; have := depth_le M l; omega)⟩⟩

end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Response

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauLocal

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)

def PrefixRelation (c : Control (Λ := Λ) (σ := σ)) (tops : Tops M) (r : Response M) : Prop :=
  ∃ p : Prefix M, (∀ k, BoundedList.cells (p k)=tops k) ∧ r=respond M c p
def cellTable (k : K) (cat : Fin (2*radius M+1))
    (p : BoundedList (Γ k) (2*radius M)) (window : Fin (2*radius M+1) → Option (Γ k)) : Option (Γ k) :=
  if cat.val<p.val.length then p.val[cat.val]? else window ⟨p.val.length,by have := p.property; omega⟩
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauLocal

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
def qwin (h : Fin (2*radius M+1)) : Query M := .inr (.inr (.inr h))
instance queryNonempty : Nonempty (Query M) := ⟨q0 M⟩

noncomputable def query (T L : ℕ) (test : Clause (K := K) T L) : Query M → Var (K := K) T L :=
  fun q => match test,q with
  | .shape t k i,.inl _ => cell T L t k ⟨i.val,by omega⟩
  | .shape t k i,_ => cell T L t k ⟨i.val+1,by omega⟩
  | .end t k,_ => cell T L t k ⟨L,by omega⟩
  | .prefix t,.inl _ => ctrl T L (now T t)
  | .prefix t,.inr (.inl _) => resp T L t
  | .prefix t,.inr (.inr (.inl (k,i))) => cell T L (now T t) k (clamp L i.val)
  | .prefix t,_ => ctrl T L (now T t)
  | .control t,.inl _ => ctrl T L (later T t)
  | .control t,_ => resp T L t
  | .update t k i,.inl _ => resp T L t
  | .update t k i,.inr (.inl _) => cell T L (later T t) k i
  | .update t k i,.inr (.inr (.inr h)) => cell T L (now T t) k (clamp L (i.val+radius M-h.val))
  | .update t k i,_ => resp T L t

end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauBoundary

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
def boundaryQuery (T L : ℕ) (b : BoundaryClause (K := K) L) (_ : Query M) : Var (K := K) T L :=
  b.2.elim (fun _ => ctrl T L (boundaryTime T b.1))
    (fun ki => cell T L (boundaryTime T b.1) ki.1 ki.2)
def boundaryRelation (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (L : ℕ)
    (b : BoundaryClause (K := K) L) (z : Query M → Value M) : Prop :=
  match b.2 with
  | .inl _ => (z (q0 M)).1=if b.1 then (B.last.l,B.last.var) else B.firstControl
  | .inr (k,i) => if b.1 then (z (q0 M)).2.2 k=(B.last.stk k)[i.val]?
      else prefixCell (B.firstPrefix k) (B.certificateBound k) i.val ((z (q0 M)).2.2 k)
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauBoundary

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

namespace Ordered
variable {A B : Type} [DecidableEq A] [DecidableEq B]
def sum (o : Ordered A) (s : Ordered B) : Ordered (A ⊕ B) where
  entries := o.entries.map Sum.inl ++ s.entries.map Sum.inr
  nodup := by
    apply List.Nodup.append (o.nodup.map Sum.inl_injective) (s.nodup.map Sum.inr_injective)
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,h⟩ := List.mem_map.mp hy
    cases h
  all x := by cases x with
    | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a,o.all a,rfl⟩)
    | inr b => exact List.mem_append_right _ (List.mem_map.mpr ⟨b,s.all b,rfl⟩)
end Ordered
end MetricKMedian.PCP.Compiler

end Inline_PCPTableBuilders

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauDirectories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauDirectories
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau
open scoped Classical

variable {K : Type} (k0 : K)
def clauseCode {T L : ℕ} : Clause (K := K) T L → TC (K := K)
  | .shape t k i => (0,t.val,k,i.val)
  | .end t k => (1,t.val,k,0)
  | .prefix t => (2,t.val,k0,0)
  | .control t => (3,t.val,k0,0)
  | .update t k i => (4,t.val,k,i.val)
def boundaryCode {L : ℕ} (b : BoundaryClause (K := K) L) : TC (K := K) :=
  match b.2 with
  | .inl _ => (if b.1 then 6 else 5,0,k0,0)
  | .inr (k,i) => (if b.1 then 8 else 7,0,k,i.val)
def testCode {T L : ℕ} : Clause (K := K) T L ⊕ BoundaryClause (K := K) L → TC (K := K) :=
  Sum.elim (clauseCode k0) (boundaryCode k0)
lemma clauseCode_injective (T L : ℕ) : Function.Injective (clauseCode k0 (T := T) (L := L)) := by
  intro a b hab
  cases a <;> cases b <;>
    simp only [clauseCode,Prod.mk.injEq] at hab <;>
    try { have h := congrArg Fin.val hab.1; contradiction }
  all_goals congr <;> first | exact Fin.ext hab.2.1 | exact hab.2.2.1 | exact Fin.ext hab.2.2.2
lemma boundaryCode_injective (L : ℕ) : Function.Injective (boundaryCode k0 (L := L)) := by
  rintro ⟨side,a⟩ ⟨side',b⟩ hab
  cases side <;> cases side' <;> rcases a with a|⟨k,i⟩ <;> rcases b with b|⟨l,j⟩ <;>
    simp only [boundaryCode,Bool.false_eq_true,↓reduceIte,Prod.mk.injEq] at hab
  all_goals try { have h := congrArg Fin.val hab.1; contradiction }
  all_goals try { cases a; cases b; rfl }
  all_goals
    have hk := hab.2.2.1
    have hi := Fin.ext hab.2.2.2
    cases hk
    cases hi
    rfl
lemma testCode_injective (T L : ℕ) : Function.Injective (testCode k0 (T := T) (L := L)) := by
  rintro (a|a) (b|b) hab
  · exact congrArg Sum.inl (clauseCode_injective k0 T L hab)
  · cases a <;> rcases b with ⟨side,b⟩ <;> cases side <;> rcases b with b|⟨k,i⟩ <;>
      cases congrArg (fun z => z.1.val) hab
  · cases b <;> rcases a with ⟨side,a⟩ <;> cases side <;> rcases a with a|⟨k,i⟩ <;>
      cases congrArg (fun z => z.1.val) hab
  · exact congrArg Sum.inr (boundaryCode_injective k0 L hab)
variable [Fintype K]
noncomputable def varOrder (T L : ℕ) : Ordered (Var (K := K) T L) :=
  (Ordered.fin (T+1)).sum ((Ordered.fin T).sum ((Ordered.fin (T+1)).prod ((Ordered.fixed K).prod (Ordered.fin (L+1)))))
noncomputable def clauseOrder (T L : ℕ) : Ordered (Clause (K := K) T L) :=
  (((Ordered.fin (T+1)).prod ((Ordered.fixed K).prod (Ordered.fin L))).sum
    (((Ordered.fin (T+1)).prod (Ordered.fixed K)).sum
      ((Ordered.fin T).sum ((Ordered.fin T).sum
        ((Ordered.fin T).prod ((Ordered.fixed K).prod (Ordered.fin (L+1)))))))).map (Tableau.clauseEquiv T L).symm
noncomputable def boolOrder : Ordered Bool where
  entries := [false,true]
  nodup := by simp
  all b := by cases b <;> simp
noncomputable def boundaryOrder (L : ℕ) : Ordered (BoundaryClause (K := K) L) :=
  boolOrder.prod ((Ordered.fixed Unit).sum ((Ordered.fixed K).prod (Ordered.fin (L+1))))
noncomputable def testOrder (T L : ℕ) := (clauseOrder (K := K) T L).sum (boundaryOrder (K := K) L)
noncomputable def vars (T L : ℕ) : List (VC (K := K)) :=
  (List.range (T+1)).map (fun t => (0,t,k0,0)) ++
  (List.range T).map (fun t => (1,t,k0,0)) ++
  (List.range (T+1)).flatMap (fun t => (Ordered.fixed K).entries.flatMap
    (fun k => (List.range (L+1)).map (fun i => (2,t,k,i))))
noncomputable def clauses (T L : ℕ) : List (TC (K := K)) :=
  (List.range (T+1)).flatMap (fun t => (Ordered.fixed K).entries.flatMap
    (fun k => (List.range L).map (fun i => (0,t,k,i)))) ++
  (List.range (T+1)).flatMap (fun t => (Ordered.fixed K).entries.map (fun k => (1,t,k,0))) ++
  (List.range T).map (fun t => (2,t,k0,0)) ++
  (List.range T).map (fun t => (3,t,k0,0)) ++
  (List.range T).flatMap (fun t => (Ordered.fixed K).entries.flatMap
    (fun k => (List.range (L+1)).map (fun i => (4,t,k,i))))
noncomputable def boundaries (L : ℕ) : List (TC (K := K)) :=
  [false,true].flatMap (fun b => [(if b then 6 else 5,0,k0,0)] ++
    (Ordered.fixed K).entries.flatMap (fun k => (List.range (L+1)).map (fun i => (if b then 8 else 7,0,k,i))))
noncomputable def tests (T L : ℕ) : List (TC (K := K)) := clauses k0 T L++boundaries k0 L
lemma vars_correct (T L : ℕ) : vars k0 T L=(varOrder (K := K) T L).entries.map (varCode k0) := by
  simp only [varOrder,Ordered.sum,Ordered.prod,Ordered.fin,List.map_append,List.map_map,
    List.product,List.map_flatMap,Function.comp_def,varCode]
  simp only [vars,RoundingList.range_finRange,List.flatMap_map,List.map_map,Function.comp_def,List.append_assoc]
lemma clauses_correct (T L : ℕ) : clauses k0 T L=(clauseOrder (K := K) T L).entries.map (clauseCode k0) := by
  simp only [clauseOrder,Ordered.map,Ordered.sum,Ordered.prod,Ordered.fin,List.map_append,List.map_map,
    List.product,List.map_flatMap,Function.comp_def,Tableau.clauseEquiv,Equiv.symm_mk,Equiv.coe_fn_mk,clauseCode]
  simp only [clauses,RoundingList.range_finRange,List.flatMap_map,List.map_map,Function.comp_def,List.append_assoc]
lemma boundaries_correct (L : ℕ) : boundaries k0 L=(boundaryOrder (K := K) L).entries.map (boundaryCode k0) := by
  have hu : (Ordered.fixed Unit).entries=[()] := by
    apply List.ext_getElem
    · rw [Ordered.length_card]; simp
    · intros; exact Subsingleton.elim _ _
  simp only [boundaryOrder,Ordered.prod,Ordered.sum,Ordered.fin,List.product,List.map_flatMap,
    List.map_append,List.map_map,Function.comp_def,boundaryCode,hu,List.map_singleton,boolOrder]
  simp only [boundaries,RoundingList.range_finRange,List.map_map,Function.comp_def]
lemma tests_correct (T L : ℕ) : tests k0 T L=(testOrder (K := K) T L).entries.map (testCode k0) := by
  rw [tests,clauses_correct,boundaries_correct]
  simp only [testOrder,Ordered.sum,List.map_append,List.map_map,Function.comp_def,testCode,Sum.elim_inl,Sum.elim_inr]
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauDirectories

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
noncomputable def rawQuery (T L : ℕ) (test : TC (K := K)) (q : Query M) : VC (K := K) :=
  let t := test.2.1
  let k := test.2.2.1
  let i := test.2.2.2
  if test.1=0 then (2,t,k,if q=q0 M then i else i+1)
  else if test.1=1 then (2,t,k,L)
  else if test.1=2 then
    match q with
    | .inl _ => (0,t,k0,0)
    | .inr (.inl _) => (1,t,k0,0)
    | .inr (.inr (.inl (k,j))) => (2,t,k,min j.val L)
    | _ => (0,t,k0,0)
  else if test.1=3 then if q=q0 M then (0,t+1,k0,0) else (1,t,k0,0)
  else if test.1=4 then
    match q with
    | .inl _ => (1,t,k0,0)
    | .inr (.inl _) => (2,t+1,k,i)
    | .inr (.inr (.inr h)) => (2,t,k,min (i+radius M-h.val) L)
    | _ => (1,t,k0,0)
  else if test.1=5 then (0,0,k0,0)
  else if test.1=6 then (0,T,k0,0)
  else if test.1=7 then (2,0,k,i)
  else (2,T,k,i)
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma rawQuery_clause (T L : ℕ) (c : Clause (K := K) T L) (q : Query M) :
    rawQuery M k0 T L (clauseCode k0 c) q=varCode k0 (Tableau.query M T L c q) := by
  cases c <;> rcases q with ⟨⟩ | ⟨⟩ | ⟨k,j⟩ | h <;>
    simp [rawQuery,clauseCode,Tableau.query,varCode,q0,cell,ctrl,resp,now,later,clamp]
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma rawQuery_boundary (T L : ℕ) (b : BoundaryClause (K := K) L) (q : Query M) :
    rawQuery M k0 T L (boundaryCode k0 b) q=varCode k0 (boundaryQuery M T L b q) := by
  rcases b with ⟨side,b⟩
  cases side <;> rcases b with b|⟨k,i⟩ <;>
    simp [rawQuery,boundaryCode,boundaryQuery,varCode,ctrl,cell,boundaryTime,time0,timeLast]
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauQueryProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalCompiler
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace Ordered
variable {V T : Type} [DecidableEq V] [DecidableEq T]
lemma sum_left_index (vo : Ordered V) (eo : Ordered T) (v : V) :
    ((vo.sum eo).equiv (.inl v)).val=(vo.equiv v).val := by
  classical
  let : BEq (V ⊕ T) := instBEqOfDecidableEq
  rw [Ordered.equiv_val,Ordered.equiv_val]
  simp only [Ordered.sum]
  rw [List.idxOf_append_of_mem (List.mem_map.mpr ⟨v,vo.all v,rfl⟩)]
  simp only [List.idxOf,List.findIdx_map]
  congr 1
  funext x
  simp only [Function.comp_def,Bool.beq_eq_decide_eq,Sum.inl.injEq]
lemma sum_right_index (vo : Ordered V) (eo : Ordered T) (t : T) :
    ((vo.sum eo).equiv (.inr t)).val=vo.entries.length+(eo.equiv t).val := by
  classical
  let : BEq (V ⊕ T) := instBEqOfDecidableEq
  rw [Ordered.equiv_val,Ordered.equiv_val]
  simp only [Ordered.sum]
  rw [List.idxOf_append_of_notMem (by simp),List.length_map]
  congr 1
  simp only [List.idxOf,List.findIdx_map]
  congr 1
  funext x
  simp only [Function.comp_def,Bool.beq_eq_decide_eq,Sum.inr.injEq]
end Ordered
namespace LocalCompiler
variable {X VC TC Q A : Type}
  [Fintype Q]
  [Fintype A]
  [DecidableEq A]
  [DecidableEq VC]
  [DecidableEq TC]
  [Inhabited X]
  [Inhabited VC]
  [Inhabited TC]
  [Inhabited Q]
  [Inhabited A]
variable (vars : X→List VC) (tests : X→List TC) (query : X→TC→Q→VC) (accept : X→TC→Finset (Q→A))
noncomputable def row (x:X) (t:TC) (q:Q) : CSPRow (Label (Q := Q) (A := A)) :=
  ((vars x).findIdx (fun v => decide (v=query x t q)),
    (vars x).length+(tests x).findIdx (fun u => decide (u=t)),relation (accept x t) q)
noncomputable def table (x:X) : CSPTable (Label (Q := Q) (A := A)) :=
  ((vars x).map (fun _=>())++(tests x).map (fun _=>()),
    (tests x).flatMap (fun t => (Ordered.fixed Q).entries.map (fun q => row vars tests query accept x t q)))
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRelationProgram
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
noncomputable def firstControlSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) : RelationSet M :=
  Finset.univ.filter (fun z => (z (q0 M)).1=B.firstControl)
noncomputable def lastControlSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) : RelationSet M :=
  Finset.univ.filter (fun z => (z (q0 M)).1=(B.last.l,B.last.var))
noncomputable def lastCellSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (k : K) (i : ℕ) : RelationSet M :=
  Finset.univ.filter (fun z => (z (q0 M)).2.2 k=(B.last.stk k)[i]?)
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauRelationProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AdviceInstances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAdviceInstances
namespace MetricKMedian.PCP.Compiler
open scoped Classical

noncomputable instance adviceFintype {D A : Type} [Fintype D] [Fintype A] (cap:ℕ) : Fintype (Advice D A cap) := by
  unfold Advice
  infer_instance
end MetricKMedian.PCP.Compiler

end Inline_PCPAdviceInstances

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_UnaryPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUnaryPolynomial
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic Polynomial
open scoped Classical

lemma unaryPower_length (n : ℕ) (xs : List Unit) : (unaryPower n xs).length=xs.length^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unaryPower,length_flatMap_uniform xs _ (xs.length^n) (by intros; exact ih),pow_succ']
end MetricKMedian.PCP.Compiler

end Inline_PCPUnaryPolynomial

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_IncidenceOperator
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BiProjection.prod_source _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPIncidenceOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V D A B : Type} (G : PortGraph V D)
def incidenceEdge : (V × D) × Bool ≃ V × (D × Bool) where
  toFun p := let q := if p.2 then G.rotate p.1 else p.1; (q.1,(q.2,p.2))
  invFun p := (if p.2.2 then G.rotate (p.1,p.2.1) else (p.1,p.2.1),p.2.2)
  left_inv p := by
    rcases p with ⟨⟨v,d⟩,b⟩
    cases b
    · rfl
    · change (G.rotate (G.rotate (v,d)),true)=((v,d),true)
      rw [G.involutive (v,d)]
  right_inv p := by
    rcases p with ⟨v,d,b⟩
    cases b
    · rfl
    · change ((G.rotate (G.rotate (v,d))).1,((G.rotate (G.rotate (v,d))).2,true))=(v,d,true)
      rw [G.involutive (v,d)]

def incidence (π : (V × D) × Bool → A → B) : BiProjection (V × D) V Bool (D × Bool) A B where
  edge := G.incidenceEdge
  project := π

@[simp] lemma incidence_source_false (π : (V × D) × Bool → A → B) (v : V) (d : D) :
    (G.incidence π).source v (d,false)=((v,d),false) := rfl
@[simp] lemma incidence_source_true (π : (V × D) × Bool → A → B) (v : V) (d : D) :
    (G.incidence π).source v (d,true)=(G.rotate (v,d),true) := rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPIncidenceOperator

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

namespace ProjectionTable
variable {U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {nu : ℕ} (ue : U≃Fin nu) (vo : Ordered V) (so : Ordered S)
variable (ao : Ordered A) (bo : Ordered B)
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
lemma order_pos {I : Type} [DecidableEq I] [Nonempty I] (o : Ordered I) : 0<o.entries.length := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact List.length_pos_of_mem (o.all i)
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_PowerTable
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionPowerTable
namespace MetricKMedian.PCP
open scoped Classical

namespace Nested
noncomputable instance inhabited (A : Type) [Inhabited A] : (n : ℕ)→Inhabited (Nested A n)
  | 0 => inferInstanceAs (Inhabited Unit)
  | n+1 => letI := inhabited A n; inferInstanceAs (Inhabited (A×Nested A n))
end Nested
namespace Compiler
open Binary Binary.Automatic

namespace Ordered
noncomputable def nested {A : Type} (o : Ordered A) : (n : ℕ)→Ordered (Nested A n)
  | 0 => fixed Unit
  | n+1 => o.prod (nested o n)
end Ordered
namespace ProjectionTable
noncomputable def nestedEquiv {U : Type} {m : ℕ} (ue : U≃Fin m) : (n : ℕ)→Nested U n≃Fin (m^n)
  | 0 => (Equiv.ofUnique Unit (Fin 1)).trans (finCongr (pow_zero m).symm)
  | n+1 => ((ue.prodCongr (nestedEquiv ue n)).trans finProdFinEquiv).trans (finCongr (by rw [pow_succ']))
end ProjectionTable
end Compiler
end MetricKMedian.PCP

end Inline_PCPProjectionPowerTable

end OAI
end


