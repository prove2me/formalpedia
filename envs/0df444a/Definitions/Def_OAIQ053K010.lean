-- Prove2me | Definitions.Def_OAIQ053K010
-- name    : OAIQ053K010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:54:13.313627+00:00
-- url     : https://prove2.me/theorems/c8ec1a25-0309-4231-b1d4-62f018520e74
-- title:
--   Definitions bundle OAIQ053K010 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 52 definitions, 2 inductive types or structures, 1 instance and 22 theorems. The definitions and types are `OAI.MetricKMedian.PCP.BiProjection.pointLabel`, `OAI.MetricKMedian.PCP.BinaryCSP.extendAssignment`, `OAI.MetricKMedian.PCP.Compiler.CSPRow`, `OAI.MetricKMedian.PCP.Compiler.CSPTable`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.WellFormed`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.check`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.grid`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.rect`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.relabel`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.row`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.boolOrder`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.Dart`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.active`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.dartIndex`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.darts`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.endpoint`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.incident`, `OAI.MetricKMedian.PCP.Compiler.Ordered`, `OAI.MetricKMedian.PCP.Compiler.Ordered.equiv`, `OAI.MetricKMedian.PCP.Compiler.Ordered.fin`, `OAI.MetricKMedian.PCP.Compiler.Ordered.fixed`, `OAI.MetricKMedian.PCP.Compiler.Ordered.indexed`, `OAI.MetricKMedian.PCP.Compiler.Ordered.map`, `OAI.MetricKMedian.PCP.Compiler.Ordered.prod`, `OAI.MetricKMedian.PCP.Compiler.Ordered.sigma`, `OAI.MetricKMedian.PCP.Compiler.RotationTable`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.WellFormed`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.blockRows`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.fourthLookup`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.lookup`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.ports`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.squareLookup`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.RelationSet`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.TC`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.firstCellSet`, `OAI.MetricKMedian.PCP.Compiler.blendProgram`, `OAI.MetricKMedian.PCP.Nested`, `OAI.MetricKMedian.PCP.Tableau.Boundary`, `OAI.MetricKMedian.PCP.Tableau.BoundedList`, `OAI.MetricKMedian.PCP.Tableau.BoundedList.cells` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_AmplifierTableSize`, `KMedian_CookLevin_TM2Locality`, `KMedian_CookLevin_TM2Response`, `KMedian_CookLevin_TableauBoundary`, `KMedian_CookLevin_TableauDirectories`, `KMedian_CookLevin_TableauLocal`, `KMedian_CookLevin_TableauRelationProgram`, `KMedian_CookLevin_TableauSystem`, `KMedian_Expanders_CloudOrder`, `KMedian_Expanders_CloudPrograms`, `KMedian_Expanders_CloudSpec`, `KMedian_Expanders_ExpanderTables`, `KMedian_Expanders_SpectralWalk`, `KMedian_Machines_BlendCompiler`, `KMedian_Machines_BlockRotation`, `KMedian_Machines_CSPTableBounds`, `KMedian_Machines_GridTables`, `KMedian_Machines_ListCompiler`, `KMedian_Machines_Ordered`, `KMedian_Machines_OrderedLists`, `KMedian_Machines_RawCSP`, `KMedian_Machines_RawRotation`, `KMedian_Machines_RawSquare`, `KMedian_Machines_RectTables`, `KMedian_Machines_RelabelTables`, `KMedian_Machines_RotationBounds`, `KMedian_Machines_RotationExt`, `KMedian_Machines_VertexMap`, `KMedian_Projection_Bound`, `KMedian_Projection_Repeat`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K024`, `OAIQ053K025` and `OAIQ053K026`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

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

section FiniteEnergy
variable {S T : Type} [Fintype S] [Fintype T]

noncomputable def energy (f : S → ℝ) : ℝ := 𝔼 s, f s ^ 2

end FiniteEnergy

end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_VertexMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPVertexMap
namespace MetricKMedian.PCP.BinaryCSP
open scoped Classical

variable {V W E A : Type} [Fintype E] [DecidableEq A]
variable (e : V ↪ W)
omit [DecidableEq A]
noncomputable def extendAssignment [Inhabited A] (a : V → A) (w : W) : A :=
  if h : w∈Set.range e then a (Classical.choose h) else default
@[simp] lemma extendAssignment_image [Inhabited A] (a : V → A) (v : V) :
    extendAssignment e a (e v)=a v := by
  simp only [extendAssignment,Set.mem_range_self,↓reduceDIte]
  exact congrArg a (e.injective (Classical.choose_spec (Set.mem_range_self v)))
end MetricKMedian.PCP.BinaryCSP

end Inline_PCPVertexMap

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
open scoped Classical

abbrev CSPRow (A : Type) := ℕ × ℕ × Finset (A × A)
abbrev CSPTable (A : Type) := List Unit × List (CSPRow A)
namespace CSPTable
variable {A : Type} [Fintype A] [DecidableEq A]
def WellFormed (t : CSPTable A) : Prop :=
  0<t.2.length ∧ ∀ e∈t.2, e.1<t.1.length ∧ e.2.1<t.1.length
variable {V E : Type} [Fintype V] [Fintype E]
noncomputable def row (t : CSPTable A) (e : ℕ) : CSPRow A := t.2[e]?.getD (0,0,∅)
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawCSP

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

structure Ordered (A : Type) where
  entries : List A
  nodup : entries.Nodup
  all : ∀ a, a ∈ entries
namespace Ordered
variable {A B : Type} [DecidableEq A] [DecidableEq B]
def equiv (o : Ordered A) : A ≃ Fin o.entries.length :=
  (List.Nodup.getEquivOfForallMemList o.entries o.nodup o.all).symm
@[simp] lemma equiv_val (o : Ordered A) (a : A) : (o.equiv a).val=o.entries.idxOf a := rfl
lemma length_card [Fintype A] (o : Ordered A) : o.entries.length=Fintype.card A := by
  simpa only [Fintype.card_fin] using Fintype.card_congr o.equiv.symm
@[simp] lemma get_equiv (o : Ordered A) (a : A) : o.entries[(o.equiv a).val]=a :=
  o.equiv.symm_apply_apply a
def map (o : Ordered A) (e : A ≃ B) : Ordered B where
  entries := o.entries.map e
  nodup := o.nodup.map e.injective
  all b := List.mem_map.mpr ⟨e.symm b,o.all _,e.apply_symm_apply b⟩
def fin (n : ℕ) : Ordered (Fin n) where
  entries := List.finRange n
  nodup := List.nodup_finRange n
  all := List.mem_finRange
noncomputable def fixed (A : Type) [Fintype A] : Ordered A := (fin _).map (Fintype.equivFin A).symm

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
def sigma (o : Ordered A) {B : A → Type} (s : ∀ a, Ordered (B a)) : Ordered (Sigma B) where
  entries := o.entries.sigma (fun a => (s a).entries)
  nodup := o.nodup.sigma (fun a => (s a).nodup)
  all a := List.mem_sigma.mpr ⟨o.all a.1,(s a.1).all a.2⟩
def prod (o : Ordered A) (s : Ordered B) : Ordered (A × B) where
  entries := o.entries.product s.entries
  nodup := o.nodup.product s.nodup
  all a := List.mem_product.mpr ⟨o.all a.1,s.all a.2⟩
lemma index_coded (o : Ordered A) (f : A → B) (hf : Function.Injective f) (a : A) :
    (o.equiv a).val=(o.entries.map f).findIdx (fun b => decide (b=f a)) := by
  rw [equiv_val,List.idxOf,List.findIdx_map]
  congr 1
  funext x
  simp only [Function.comp_def,hf.eq_iff,Bool.beq_eq_decide_eq]
omit [DecidableEq B] in
lemma get_coded (o : Ordered A) (f : A → B) (a : A) :
    (o.entries.map f)[(o.equiv a).val]?=some (f a) := by
  rw [List.getElem?_map,List.getElem?_eq_getElem (o.equiv a).isLt,get_equiv]
  rfl
end MetricKMedian.PCP.Compiler.Ordered

end Inline_PCPOrderedLists

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudOrder
namespace MetricKMedian.PCP.Compiler.CloudOrder
open scoped Classical

variable {V E A : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
variable (vo : Ordered V)
  (eo : Ordered E)
def boolOrder : Ordered Bool := ⟨[false,true],by simp,by decide⟩
lemma sigmaCode_injective {U : Type} {W : U → Type} (f : U → ℕ) (g : ∀ u, W u → ℕ)
    (hf : Function.Injective f) (hg : ∀ u, Function.Injective (g u)) :
    Function.Injective (fun p : Sigma W => (f p.1,g p.1 p.2)) := by
  rintro ⟨u,x⟩ ⟨v,y⟩ h
  have hu : u=v := hf (congrArg Prod.fst h)
  subst v
  have hx : x=y := hg u (congrArg Prod.snd h)
  subst y
  rfl
end MetricKMedian.PCP.Compiler.CloudOrder

end Inline_PCPCloudOrder

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_ListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPListCompiler
namespace MetricKMedian.PCP.Compiler
open scoped Classical

lemma length_flatMap_uniform {A B : Type} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ x∈xs, (f x).length=n) : (xs.flatMap f).length=xs.length*n := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    simp only [Nat.add_mul,Nat.one_mul]; omega
lemma getElem?_flatMap_uniform {A B : Type} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ x∈xs, (f x).length=n) (i : ℕ) (hi : i<xs.length) (j : ℕ) (hj : j<n) :
    (xs.flatMap f)[i*n+j]?=(f xs[i])[j]? := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      have hn := h a (by simp)
      simp only [List.flatMap_cons,Nat.zero_mul,Nat.zero_add,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      have hn := h a (by simp)
      have hi' : i<xs.length := by simpa using hi
      have hnle : (f a).length ≤ (i+1)*n+j := by rw [hn,Nat.add_mul,Nat.one_mul]; omega
      rw [List.flatMap_cons,List.getElem?_append_right hnle,hn]
      have he : (i+1)*n+j-n=i*n+j := by simp only [Nat.add_mul,Nat.one_mul]; omega
      rw [he]
      exact ih xs (fun x hx => h x (by simp [hx])) hi'
end MetricKMedian.PCP.Compiler

end Inline_PCPListCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawRotation

namespace MetricKMedian.PCP.Compiler
open scoped Classical

abbrev RotationTable (D : Type) := List (List (ℕ × D))
namespace RotationTable
variable {D : Type} [Fintype D] [Inhabited D]
noncomputable def ports : List D := List.ofFn (Fintype.equivFin D).symm
omit [Inhabited D] in
@[simp] lemma ports_length : (ports (D := D)).length=Fintype.card D := List.length_ofFn
noncomputable def lookup (R : RotationTable D) (v : ℕ) (d : D) : ℕ × D :=
  (R[v]?.getD [])[((Fintype.equivFin D) d).val]?.getD (0,default)
end RotationTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawRotation

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_BlockRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBlockRotation
namespace MetricKMedian.PCP.Compiler.RotationTable
open scoped Classical

variable {D B : Type} [Fintype D] [Inhabited D] [Fintype B] [Inhabited B]
noncomputable def blockRows (N : ℕ) (f : ℕ → B → D → ℕ × D) : RotationTable D :=
  (List.range N).flatMap (fun v => (ports (D := B)).map (fun b => (ports (D := D)).map (f v b)))
omit [Inhabited B] in
lemma lookup_blockRows (N : ℕ) (f : ℕ → B → D → ℕ × D)
    (v : ℕ) (hv : v<N) (b : B) (d : D) :
    lookup (blockRows N f) (v*Fintype.card B+(Fintype.equivFin B b).val) d=f v b d := by
  unfold lookup blockRows
  rw [getElem?_flatMap_uniform _ _ (Fintype.card B)
    (by intro u hu; simp only [List.length_map,ports_length]) v
    (by simpa only [List.length_range] using hv) _ (Fintype.equivFin B b).isLt]
  simp only [List.getElem_range,List.getElem?_map,ports,List.getElem?_ofFn,
    Fin.isLt,↓reduceDIte,Option.map_some,Option.getD_some,Fin.eta,Equiv.symm_apply_apply]
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPBlockRotation

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
open Finset
open scoped BigOperators Classical

variable {D : Type} [Fintype D] [Inhabited D]
def WellFormed (R : RotationTable D) : Prop :=
  ∀ row ∈ R, row.length=Fintype.card D ∧ ∀ q∈row, q.1<R.length
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRotationBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RotationExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRotationExt
namespace MetricKMedian.PCP.Compiler.RotationTable
open scoped Classical

variable {D B : Type} [Fintype D] [Inhabited D] [Fintype B] [Inhabited B]
lemma lookup_getElem {R : RotationTable D} (v : ℕ) (hv : v<R.length)
    (hrow : R[v].length=Fintype.card D) (j : ℕ) (hj : j<Fintype.card D) :
    lookup R v ((Fintype.equivFin D).symm ⟨j,hj⟩)=R[v][j]'(hrow.symm ▸ hj) := by
  simp only [lookup,Equiv.apply_symm_apply,List.getElem?_eq_getElem hv,
    Option.getD_some,List.getElem?_eq_getElem (hrow.symm ▸ hj)]
lemma ext_lookup {R S : RotationTable D} (hlen : R.length=S.length)
    (hR : ∀ row∈R, row.length=Fintype.card D) (hS : ∀ row∈S, row.length=Fintype.card D)
    (h : ∀ v, v<R.length → ∀ d, lookup R v d=lookup S v d) : R=S := by
  apply List.ext_getElem hlen
  intro i hi hj
  have hr := hR _ (List.getElem_mem hi)
  have hs := hS _ (List.getElem_mem hj)
  apply List.ext_getElem (hr.trans hs.symm)
  intro j hj hk
  have hd : j<Fintype.card D := hj.trans_eq hr
  exact (lookup_getElem i hi hr j hd).symm.trans
    ((h i hi ((Fintype.equivFin D).symm ⟨j,hd⟩)).trans (lookup_getElem i _ hs j hd))
omit [Inhabited D] [Inhabited B]
lemma blockRows_row_length (N : ℕ) (f : ℕ → B → D → ℕ × D) :
    ∀ row∈blockRows N f, row.length=Fintype.card D := by
  intro row hr
  obtain ⟨v,hv,hb⟩ := List.mem_flatMap.mp hr
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hb
  simp only [List.length_map,ports_length]
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRotationExt

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderTables
namespace MetricKMedian.PCP.Compiler.Expander
open RotationTable
open scoped Classical

lemma iterate_sequence {A : Type} (f : A → A) (a : ℕ → A)
    (h : ∀ n, f (a n)=a (n+1)) (n : ℕ) : f^[n] (a 0)=a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,h]
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudPrograms
namespace MetricKMedian.PCP.Compiler
open scoped Classical

namespace CloudProgram
variable {A : Type} [Fintype A]
abbrev Dart := ℕ × Bool
noncomputable def darts (t : CSPTable A) : List Dart :=
  (List.range t.2.length).flatMap (fun e => [(e,false),(e,true)])
noncomputable def endpoint (t : CSPTable A) (d : Dart) : ℕ :=
  if d.2 then (CSPTable.row t d.1).2.1 else (CSPTable.row t d.1).1
noncomputable def incident (t : CSPTable A) (v : ℕ) : List Dart :=
  (darts t).filter (fun d => decide (endpoint t d=v))
noncomputable def active (t : CSPTable A) : List ℕ :=
  (List.range t.1.length).filter (fun v => !(incident t v).isEmpty)
noncomputable def dartIndex (t : CSPTable A) (v : ℕ) (d : Dart) : ℕ :=
  (incident t v).findIdx (fun q => decide (q.1=d.1 ∧ q.2=d.2))
end CloudProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPCloudPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
lemma finRange_val (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_BlendCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBlendCompiler
namespace MetricKMedian.PCP.Compiler

variable {X D S : Type}
noncomputable def blendProgram (f : X → D → ℕ × D) (g : X → S → ℕ × S)
    (x : X) (d : Fin 3 × D × S) : ℕ × (Fin 3 × D × S) :=
  if d.1=0 then
    let q := f x d.2.1
    (q.1,(d.1,(q.2,d.2.2)))
  else
    let q := g x d.2.2
    (q.1,(d.1,(d.2.1,q.2)))
end MetricKMedian.PCP.Compiler

end Inline_PCPBlendCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawSquare
namespace MetricKMedian.PCP.Compiler.RotationTable

variable {D : Type} [Fintype D] [Inhabited D]
noncomputable def squareLookup (R : RotationTable D) (v : ℕ) (d : D × D) : ℕ × (D × D) :=
  let q := lookup R v d.1
  let r := lookup R q.1 d.2
  (r.1,(r.2,q.2))
noncomputable def fourthLookup (R : RotationTable D) (v : ℕ) (d : (D × D) × (D × D)) : ℕ × ((D × D) × (D × D)) :=
  let q := squareLookup R v d.1
  let r := squareLookup R q.1 d.2
  (r.1,(r.2,q.2))
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRawSquare

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_GridTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGridTables
namespace MetricKMedian.PCP.Compiler
open scoped Classical

namespace Ordered
variable {V W : Type} [DecidableEq V] [DecidableEq W]
def indexed {n : ℕ} (e : V ≃ Fin n) : Ordered V := (fin n).map e.symm
lemma indexed_index {n : ℕ} (e : V ≃ Fin n) (v : V) :
    ((indexed e).equiv v).val=(e v).val := by
  change ((List.finRange n).map e.symm).idxOf v=(e v).val
  rw [show v=e.symm (e v) from (e.symm_apply_apply v).symm]
  simp only [List.idxOf,List.findIdx_map]
  have hh : (fun x : Fin n => e.symm x == e.symm (e v))=(fun x : Fin n => x == e v) := by
    funext x
    simp only [Bool.beq_eq_decide_eq,e.symm.injective.eq_iff]
  change (List.finRange n).findIdx (fun x => e.symm x == e.symm (e v))=_
  rw [hh]
  simpa only [Equiv.apply_symm_apply,List.idxOf] using List.idxOf_finRange (e v)
omit [DecidableEq V] in
lemma indexed_codes {n : ℕ} (e : V ≃ Fin n) :
    (indexed e).entries.map (fun v => (e v).val)=List.range n := by
  simp only [indexed,map,fin,List.map_map,Function.comp_def,Equiv.apply_symm_apply]
  apply List.ext_getElem
  · simp
  · intros; simp
omit [DecidableEq V] in
lemma indexed_length {n : ℕ} (e : V ≃ Fin n) : (indexed e).entries.length=n := by
  simp only [indexed,map,fin,List.length_map,List.length_finRange]
end Ordered
namespace CSPTable
variable {A T B : Type}
  [Fintype A]
noncomputable def grid (seeds : List Unit) (tags : List B) (row : ℕ → B → CSPRow A) : CSPTable A :=
  (seeds,(List.range seeds.length).flatMap (fun v => tags.map (row v)))
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPGridTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RectTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRectTables
namespace MetricKMedian.PCP.Compiler.CSPTable
open scoped Classical

variable {A T B : Type}
  [Fintype A]
noncomputable def rect (seeds roots : List Unit) (tags : List B) (row : ℕ → B → CSPRow A) : CSPTable A :=
  (seeds,(List.range roots.length).flatMap (fun v => tags.map (row v)))
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRectTables

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
open scoped Classical

variable {A B V E : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Fintype V] [Fintype E]
noncomputable def relabel (e : A ≃ B) (s : CSPTable A) : CSPTable B :=
  (s.1,s.2.map (fun r => (r.1,r.2.1,r.2.2.map (e.prodCongr e).toEmbedding)))
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRelabelTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierTableSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierTableSize
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open CloudSpec
open scoped Classical

lemma arithmetic (v e a b nv ne f g c t n z : ℕ)
    (ha : a=v) (hb : b=v*z) (hnv : nv=a*f+b*g+b*c)
    (hne : ne=b*t) (hv : v≤n*e) :
    nv+ne ≤ (1+n*(f+z*(g+c+t)))*e := by
  subst a; subst b; subst nv; subst ne
  calc
    _ = v*(f+z*(g+c+t)) := by ring
    _ ≤ (n*e)*(f+z*(g+c+t)) := Nat.mul_le_mul_right _ hv
    _ ≤ (1+n*(f+z*(g+c+t)))*e := by nlinarith
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierTableSize

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

def depth : Stmt Γ Λ σ → ℕ
  | .push _ _ q => depth q+1
  | .peek _ _ q => depth q+1
  | .pop _ _ q => depth q+1
  | .load _ q => depth q+1
  | .branch _ q r => max (depth q) (depth r)+1
  | .goto _ => 0
  | .halt => 0

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

abbrev BoundedList (A : Type) (r : ℕ) := {l : List A // l.length ≤ r}
namespace BoundedList
variable {A : Type} {r : ℕ}
def cells (l : BoundedList A r) : Fin r → Option A := fun i => l.val[i.val]?
lemma cells_injective : Function.Injective (cells (A := A) (r := r)) := by
  intro l m h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < r
  · exact congrFun h ⟨i,hi⟩
  · rw [List.getElem?_eq_none (l.property.trans (by omega)),
      List.getElem?_eq_none (m.property.trans (by omega))]
noncomputable instance instFintype [Fintype A] : Fintype (BoundedList A r) :=
  Fintype.ofInjective cells cells_injective
end BoundedList

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)
noncomputable def radius : ℕ := Finset.univ.sup (fun l => depth (M l))

def advance (c : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  match c.l with
  | none => c
  | some l => stepAux (M l) c.var c.stk

abbrev Control := Option Λ × σ
abbrev Prefix := ∀ k, BoundedList (Γ k) (radius M)
abbrev Response := Control (Λ := Λ) (σ := σ) × (∀ k, BoundedList (Γ k) (2*radius M))
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

abbrev Tops := ∀ k, Fin (radius M) → Option (Γ k)

noncomputable def category (i : ℕ) : Fin (2*radius M+1) := ⟨min i (2*radius M),by omega⟩
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
abbrev Value := Control (Λ := Λ) (σ := σ) × Response M × (∀ k, Option (Γ k))
abbrev Query := Unit ⊕ Unit ⊕ (K × Fin (radius M)) ⊕ Fin (2*radius M+1)
def q0 : Query M := .inl ()
def q1 : Query M := .inr (.inl ())
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

def prefixCell {A : Type} (p : List A) (b i : ℕ) (v : Option A) : Prop :=
  (i<p.length → v=p[i]?) ∧ (p.length+b ≤ i → v=none)

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
structure Boundary where
  firstControl : Control (Λ := Λ) (σ := σ)
  firstPrefix : ∀ k, List (Γ k)
  certificateBound : K → ℕ
  last : Cfg Γ Λ σ
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauBoundary

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
open Tableau
open scoped Classical

variable {K : Type} (k0 : K)
abbrev TC := Fin 9 × (ℕ × (K × ℕ))
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauDirectories

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
open Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
abbrev RelationSet := Finset (Query M→Value M)
noncomputable def firstCellSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (k : K) (i : ℕ) : RelationSet M :=
  Finset.univ.filter (fun z => prefixCell (B.firstPrefix k) (B.certificateBound k) i ((z (q0 M)).2.2 k))
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauRelationProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_CSPTableBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPTableBounds
namespace MetricKMedian.PCP.Compiler.CSPTable
open Finset
open scoped BigOperators Classical

variable {A : Type} [Fintype A] [DecidableEq A]
noncomputable def check (s : CSPTable A) : Bool :=
  decide (0 < s.2.length) && ((s.2.filter fun r => !(decide (r.1 < s.1.length) && decide (r.2.1 < s.1.length))).isEmpty)
omit [Fintype A] [DecidableEq A] in
lemma check_iff (s : CSPTable A) : check s=true ↔ s.WellFormed := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff,List.filter_eq_nil_iff,
    Bool.not_eq_true,CSPTable.WellFormed]
  aesop
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPCSPTableBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]

noncomputable def pointLabel (a : U → A) : U → A → Unit → ℝ := fun u c _ => if c=a u then 1 else 0

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionBound

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

def Nested (A : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => A × Nested A n
end MetricKMedian.PCP

end Inline_PCPProjectionRepeat

end OAI
end


