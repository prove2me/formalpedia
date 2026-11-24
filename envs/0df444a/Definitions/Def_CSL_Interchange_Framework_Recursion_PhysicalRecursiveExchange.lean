-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_PhysicalRecursiveExchange
-- name    : CSL_Interchange_Framework_Recursion_PhysicalRecursiveExchange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:39:13.495006+00:00
-- url     : https://prove2.me/theorems/70a1d19e-db71-4258-b94b-cc99edeadb9c
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / PhysicalRecursiveExchange
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.PhysicalRecursiveExchange` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   File-level execution of the concrete recursive program. Every primitive
--   accepts an already existing external file and returns the file subsequently
--   consumed by its successor. Canonical blocking describes physical positions;
--   it is not an additional payload permutation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.PhysicalRecursiveExchange

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_StatefulRecursiveExchange
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchangeCost
import Definitions.Def_CSL_Shared_Programs_NodeStreamMachine
import Definitions.Def_CSL_Interchange_Framework_Fields_ScalarLayoutBridge

/-! File-level execution of the concrete recursive program. Every primitive
accepts an already existing external file and returns the file subsequently
consumed by its successor. Canonical blocking describes physical positions;
it is not an additional payload permutation. -/

set_option maxRecDepth 4096

namespace CSL.PhysicalRecursiveExchange
open Circuit CircuitProgram ProgramNetwork Address CodedSimulation
open RecursiveExchange ScanProgram
open scoped BigOperators
noncomputable section

abbrev File := List (List Bit)

def canonical {V : ℕ} (B : ℕ) (hB : 0 < B) (F : Fin V → Bit) : File :=
  BucketMachine.pack B hB (List.ofFn F)

/-- Two views of the same external cells. The final block is restricted to
the logical file length; padding outside that length is not payload. -/
def fileCells (B : ℕ) (source : File) : BlockReflection.Disk Bit :=
  fun i => (source.getD (i / B) []).getD (i % B) 0

def cellBlocks (V B : ℕ) (hB : 0 < B) (source : BlockReflection.Disk Bit) : File :=
  canonical B hB (fun i : Fin V => source i.val)

theorem pack_getD {α : Type} (B : ℕ) (hB : 0 < B) (xs : List α) (n : ℕ) :
    (BucketMachine.pack B hB xs).getD n [] = (xs.drop (B*n)).take B := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [BucketMachine.pack]
    | cons a xs => simp [BucketMachine.pack]
  | succ n ih =>
    cases xs with
    | nil => simp [BucketMachine.pack]
    | cons a xs =>
      rw [BucketMachine.pack,List.getD_cons_succ,ih]
      simp only [List.drop_drop,Nat.mul_succ]
      congr 2
      omega

theorem canonical_cells {V : ℕ} (B : ℕ) (hB : 0 < B) (F : Fin V → Bit) (y : Fin V) :
    fileCells B (canonical B hB F) y.val = F y := by
  unfold fileCells canonical
  rw [pack_getD]
  rw [List.getD_eq_getElem?_getD,List.getElem?_take_of_lt (Nat.mod_lt _ hB),
    List.getElem?_drop]
  rw [Nat.div_add_mod]
  simp only [List.getElem?_ofFn,dif_pos y.isLt,Option.getD_some]

/-- This is the actual primitive runner on external files. Reflections use
BlockReflection's physical block trace and expose its resulting block cells
in the same file format used by the streaming Reader/Writer machine. -/
def executePass {V : ℕ} (p : Pass V) (B : ℕ) (hB : 0 < B) (source : File) :
    Option (File × ℕ) :=
  match p with
  | .streams _ e key _ =>
      (DiskStreamPass.run e key B source).map (fun result => (result.output.finish,result.transfers))
  | .reverse _ L _ _ =>
      let result := BlockReflection.run (fileCells B source) B L hB ((V+B-1)/B)
        ⟨fun _ => 0,[]⟩
      some (cellBlocks V B hB result.disk,result.trace.length)

theorem executePass_of_evidence {V : ℕ} (p : Pass V) (F : Fin V → Bit)
    (B : ℕ) (hB : 0 < B) (cost : ℕ) (he : StepEvidence p F B hB cost) :
    executePass p B hB (canonical B hB F) =
      some (canonical B hB (moved p F),cost) := by
  cases p with
  | streams K e key hi =>
    obtain ⟨result,hr,ho,hc,_,_⟩ := he
    have hinput : BucketMachine.pack B hB (TagErasure.inputValues F) = canonical B hB F := by
      rw [canonical,List.ofFn_eq_map]; rfl
    have houtput : BucketMachine.pack B hB (TagErasure.outputValues e F) =
        canonical B hB (moved (.streams K e key hi) F) := by
      rw [canonical,List.ofFn_eq_map]; rfl
    rw [hinput] at hr
    simp [executePass,hr,ho,houtput,← hc]
  | reverse T L hL hV =>
    obtain ⟨hc,hout⟩ := he (fileCells B (canonical B hB F)) (fun _ => 0) (canonical_cells B hB F)
    have hfile : cellBlocks V B hB
        (BlockReflection.run (fileCells B (canonical B hB F)) B L hB ((V+B-1)/B)
          ⟨fun _ => 0,[]⟩).disk = canonical B hB (moved (.reverse T L hL hV) F) := by
      apply congrArg (canonical B hB)
      funext y
      exact hout y
    simp only [executePass,hfile,hc]

/-- Actual output files, rather than freshly supplied semantic arrays, flow
through this runner. No regrouping or repacking action is inserted. -/
def executeProgram {V : ℕ} (B : ℕ) (hB : 0 < B) :
    List (Pass V) → File → Option (File × ℕ)
  | [],source => some (source,0)
  | p::ps,source => do
      let head ← executePass p B hB source
      let tail ← executeProgram B hB ps head.1
      return (tail.1,head.2+tail.2)

theorem executeProgram_of_execution {V : ℕ} (B : ℕ) (hB : 0 < B)
    (ps : List (Pass V)) (F : Fin V → Bit) (cost : ℕ)
    (he : Execution B hB ps F cost) :
    executeProgram B hB ps (canonical B hB F) =
      some (canonical B hB (eval ps F),cost) := by
  induction he with
  | nil F => rfl
  | cons p ps F c d hh ht ih =>
    simp [executeProgram,executePass_of_evidence p F B hB c hh,ih,eval]

/-- A concrete file execution exists, with the cost of its actual primitive
runs. This is later applied to each successive intermediate file. -/
theorem executeProgram_exists {V : ℕ} (B : ℕ) (hB : 0 < B)
    (ps : List (Pass V)) (F : Fin V → Bit) :
    ∃ cost, executeProgram B hB ps (canonical B hB F) =
      some (canonical B hB (eval ps F),cost) ∧
      Execution B hB ps F cost ∧ cost ≤ totalConstant ps * (V/B+1) := by
  obtain ⟨cost,he,hc⟩ := program_correct ps F B hB
  exact ⟨cost,executeProgram_of_execution B hB ps F cost he,he,hc⟩

section Layout
variable {Addr : Type} {V : ℕ}

def encoded (layout : Addr ≃ Fin V) (F : Addr → Bit) : Fin V → Bit := F ∘ layout.symm

def represented (layout : Addr ≃ Fin V) (B : ℕ) (hB : 0 < B) (F : Addr → Bit) : File :=
  canonical B hB (encoded layout F)

/-- A scan program's concrete destination agrees with one address map in
one fixed physical layout. The same layout is used before and after. -/
def Realizes (layout : Addr ≃ Fin V) (ps : List (Pass V)) (perm : Equiv.Perm Addr) : Prop :=
  ∀ a, destination ps (layout a) = layout (perm a)

theorem realizes_eval (layout : Addr ≃ Fin V) (ps : List (Pass V)) (perm : Equiv.Perm Addr)
    (hr : Realizes layout ps perm) (F : Addr → Bit) :
    eval ps (encoded layout F) = encoded layout (transport perm F) := by
  funext y
  rw [eval_eq_pullback]
  change F (layout.symm ((destination ps).symm y)) = F (perm.symm (layout.symm y))
  apply congrArg F
  apply perm.injective
  apply layout.injective
  rw [← hr,Equiv.apply_symm_apply,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  exact (layout.apply_symm_apply y).symm

/-- Both boundary files are explicit. Composition below shares the target
file of one primitive with the source file of the next primitive. -/
structure ScanRun (layout : Addr ≃ Fin V) (B : ℕ) (hB : 0 < B)
    (ps : List (Pass V)) (F G : Addr → Bit) (source target : File) (cost : ℕ) : Prop where
  source_eq : source = represented layout B hB F
  execution : Execution B hB ps (encoded layout F) cost
  meaning : eval ps (encoded layout F) = encoded layout G
  actual : executeProgram B hB ps source = some (target,cost)
  target_eq : target = represented layout B hB G

theorem scanRun_exists (layout : Addr ≃ Fin V) (B : ℕ) (hB : 0 < B)
    (ps : List (Pass V)) (perm : Equiv.Perm Addr) (hr : Realizes layout ps perm)
    (F : Addr → Bit) (source : File) (hs : source = represented layout B hB F) :
    ∃ target cost, ScanRun layout B hB ps F (transport perm F) source target cost ∧
      cost ≤ totalConstant ps * (V/B+1) := by
  obtain ⟨cost,hactual,he,hcost⟩ := executeProgram_exists B hB ps (encoded layout F)
  have hm := realizes_eval layout ps perm hr F
  refine ⟨represented layout B hB (transport perm F),cost,?_,hcost⟩
  refine ⟨hs,he,hm,?_,rfl⟩
  rw [hs]
  simpa only [represented,hm] using hactual

/-- Coordinate regrouping is permitted without I/O only when its two
explicit physical encodings give the identical finite address. -/
theorem represented_regroup {Other : Type} (layout : Addr ≃ Fin V)
    (otherLayout : Other ≃ Fin V) (regroup : Addr ≃ Other)
    (hphysical : ∀ a, otherLayout (regroup a) = layout a) (B : ℕ) (hB : 0 < B) (F : Addr → Bit) :
    represented otherLayout B hB (F ∘ regroup.symm) = represented layout B hB F := by
  apply congrArg (canonical B hB)
  funext y
  apply congrArg F
  apply layout.injective
  rw [← hphysical,Equiv.apply_symm_apply]
  simp only [Equiv.apply_symm_apply]

end Layout

section ConcreteEdges
open RecursiveExchangeCost

abbrev EdgeAddress (f P G S : ℕ) :=
  LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f

abbrev EdgeStream (f P G S : ℕ) := EdgeAddress f P G S → Bit

/-- The fixed four-factor programs used by the concrete edge interpreter. -/
def beforeProgram (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S) (e : Edge) :=
  coordinateProgram f e .leftInverse P G S hG hS ++
    coordinateProgram f e .right P G S hG hS

def afterProgram (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S) (e : Edge) :=
  coordinateProgram f e .left P G S hG hS ++
    coordinateProgram f e .rightInverse P G S hG hS

/-- These are finite codec identities, not hypotheses about the existence
or cost of a scan. Each program below is the already implemented disk scan. -/
structure LayoutLaws (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S) where
  layout : EdgeAddress f P G S ≃ Fin (longVolume f P G S)
  before : ∀ e, Realizes layout (beforeProgram f P G S hG hS e) (coordinatePermutation f e)
  after : ∀ e, Realizes layout (afterProgram f P G S hG hS e) (coordinatePermutation f e).symm
  shortBefore : ∀ c, Realizes layout (scalarBefore f P G S c)
    (RecursiveExchange.shortBefore f (childRow c) (childCol c))
  shortAfter : ∀ c, Realizes layout (scalarAfter f P G S c hS)
    (RecursiveExchange.shortAfter f (childRow c) (childCol c))

/-- All codec obligations are instantiated for the actual jointly
specialized network factors and actual selected scalar coordinates. -/
def actualLayouts (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S) : LayoutLaws f P G S hG hS where
  layout := CoordinateLayoutBridge.commonLayout f P G S
  before e := CoordinateLayoutBridge.before_destination f e P G S hG hS
  after e := CoordinateLayoutBridge.after_destination f e P G S hG hS
  shortBefore c := by
    intro a
    have hdec : (@LinearOrder.toDecidableEq Index indexOrder) =
        (inferInstance : DecidableEq Index) := Subsingleton.elim _ _
    first
    | exact ScalarLayoutBridge.scalar_before_destination f P G S c a
    | (have h_sx := ScalarLayoutBridge.scalar_before_destination f P G S c a; simp only [RecursiveExchange.shortBefore,selectedPermutation,Equiv.coe_fn_mk,
      Equiv.symm_apply_apply,lowerSubtractEquiv,SingleCoordinate.beforeScan,hdec] at h_sx ⊢; exact h_sx)
    | (have h_sx := ScalarLayoutBridge.scalar_before_destination f P G S c a; simp only [RecursiveExchange.shortBefore,selectedPermutation,Equiv.coe_fn_mk,
      Equiv.symm_apply_apply,lowerSubtractEquiv,SingleCoordinate.beforeScan,hdec] at h_sx; exact h_sx)
    | (simp only [RecursiveExchange.shortBefore,selectedPermutation,Equiv.coe_fn_mk,
      Equiv.symm_apply_apply,lowerSubtractEquiv,SingleCoordinate.beforeScan,hdec]; exact ScalarLayoutBridge.scalar_before_destination f P G S c a)
  shortAfter c := by
    intro a
    have hdec : (@LinearOrder.toDecidableEq Index indexOrder) =
        (inferInstance : DecidableEq Index) := Subsingleton.elim _ _
    simpa only [RecursiveExchange.shortAfter,selectedPermutation,Equiv.coe_fn_mk,
      lowerReflectEquiv,SingleCoordinate.afterScan,hdec]
      using ScalarLayoutBridge.scalar_after_destination f P G S c hS a

structure ChildOutput (σ : Type) where
  output : File
  returned : Child
  state : σ
  cost : ℕ

structure Output (σ : Type) where
  output : File
  state : σ
  localCost : ℕ
  recursiveCost : ℕ

abbrev FileChild (σ : Type) := Child → File → σ → Option (ChildOutput σ)

variable {σ : Type} {f P G S : ℕ} {hG : 0 < G} {hS : 0 < S}

/-- A child invocation has the same boundary file as its immediately
preceding scan, and returns the actual continuation identity. -/
structure ChildRun (layout : EdgeAddress f P G S ≃ Fin (longVolume f P G S))
    (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (c : Child) (F : EdgeStream f P G S) (state : σ) (source : File)
    (result : ChildOutput σ) : Prop where
  source_eq : source = represented layout B hB F
  actual : runChild c source state = some result
  output_eq : result.output = represented layout B hB (child c F state).1.1
  returned_eq : result.returned = (child c F state).1.2
  state_eq : result.state = (child c F state).2

/-- Only the recursive call remains abstract at one recursion level. -/
def ChildAvailable (layout : EdgeAddress f P G S ≃ Fin (longVolume f P G S))
    (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) : Prop :=
  ∀ c F state source, source = represented layout B hB F →
    ∃ result, ChildRun layout B hB child runChild c F state source result

def executeShort (B : ℕ) (hB : 0 < B) (runChild : FileChild σ)
    (c : Child) (source : File) (state : σ) : Option (Output σ) := do
  let before ← executeProgram B hB (scalarBefore f P G S c) source
  let result ← runChild c before.1 state
  let after ← executeProgram B hB (scalarAfter f P G S result.returned hS) result.output
  return ⟨after.1,result.state,before.2+after.2,result.cost⟩

/-- Every intermediate file is shared between successive actual calls.
The post-scan is chosen from the child's returned continuation. -/
def ShortRun (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (c : Child) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) : Prop :=
  ∃ (preFile : File) (beforeCost : ℕ) (result : ChildOutput σ) (afterCost : ℕ),
    ScanRun L.layout B hB (scalarBefore f P G S c) F
      (transport (RecursiveExchange.shortBefore f (childRow c) (childCol c)) F)
      source preFile beforeCost ∧
    ChildRun L.layout B hB child runChild c
      (transport (RecursiveExchange.shortBefore f (childRow c) (childCol c)) F)
      state preFile result ∧
    ScanRun L.layout B hB (scalarAfter f P G S result.returned hS)
      (child c (transport (RecursiveExchange.shortBefore f (childRow c) (childCol c)) F) state).1.1
      (transport (RecursiveExchange.shortAfter f (childRow result.returned) (childCol result.returned))
        (child c (transport (RecursiveExchange.shortBefore f (childRow c) (childCol c)) F) state).1.1)
      result.output out.output afterCost ∧
    out.state = result.state ∧ out.localCost = beforeCost+afterCost ∧
      out.recursiveCost = result.cost

theorem ShortRun.actual (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (c : Child) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : ShortRun L B hB child runChild c F state source out) :
    executeShort (f := f) (P := P) (G := G) (S := S) (hS := hS) B hB runChild c source state = some out := by
  obtain ⟨preFile,cb,result,ca,hb,hc,ha,hs,hl,hr⟩ := h
  have he : (⟨out.output,result.state,cb+ca,result.cost⟩ : Output σ) = out := by
    cases out
    simp_all
  simpa [executeShort,hb.actual,hc.actual,ha.actual] using congrArg some he

theorem ShortRun.projection (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (c : Child) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : ShortRun L B hB child runChild c F state source out) :
    out.output = represented L.layout B hB (StatefulRecursiveExchange.shortStep f child F c state).1 ∧
    out.state = (StatefulRecursiveExchange.shortStep f child F c state).2 := by
  obtain ⟨preFile,cb,result,ca,hb,hc,ha,hs,hl,hr⟩ := h
  constructor
  · simpa only [StatefulRecursiveExchange.shortStep,hc.returned_eq] using ha.target_eq
  · exact hs.trans hc.state_eq

theorem shortRun_exists (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable L.layout B hB child runChild)
    (c : Child) (F : EdgeStream f P G S) (state : σ) (source : File)
    (hs : source = represented L.layout B hB F) :
    ∃ out, ShortRun L B hB child runChild c F state source out := by
  obtain ⟨preFile,cb,hb,_⟩ := scanRun_exists L.layout B hB (scalarBefore f P G S c)
    _ (L.shortBefore c) F source hs
  obtain ⟨result,hchild⟩ := hc c _ state preFile hb.target_eq
  obtain ⟨target,ca,ha,_⟩ := scanRun_exists L.layout B hB (scalarAfter f P G S result.returned hS)
    _ (L.shortAfter result.returned) _ result.output hchild.output_eq
  exact ⟨⟨target,result.state,cb+ca,result.cost⟩,preFile,cb,result,ca,hb,hchild,ha,rfl,rfl,rfl⟩

def executeSparse (B : ℕ) (hB : 0 < B) (runChild : FileChild σ) (e : Edge) :
    List (EdgeChild e) → File → σ → Option (Output σ)
  | [],source,state => some ⟨source,state,0,0⟩
  | p::ps,source,state => do
      let head ← executeShort (f := f) (P := P) (G := G) (S := S) (hS := hS)
        B hB runChild ⟨e,p⟩ source state
      let tail ← executeSparse B hB runChild e ps head.output head.state
      return ⟨tail.output,tail.state,head.localCost+tail.localCost,
        head.recursiveCost+tail.recursiveCost⟩

inductive SparseRun (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (e : Edge) :
    List (EdgeChild e) → EdgeStream f P G S → σ → File → Output σ → Prop
  | nil (F state source) (hs : source = represented L.layout B hB F) :
      SparseRun L B hB child runChild e [] F state source ⟨source,state,0,0⟩
  | cons (p ps F state source head tail)
      (hh : ShortRun L B hB child runChild ⟨e,p⟩ F state source head)
      (ht : SparseRun L B hB child runChild e ps
        (StatefulRecursiveExchange.shortStep f child F ⟨e,p⟩ state).1
        head.state head.output tail) :
      SparseRun L B hB child runChild e (p::ps) F state source
        ⟨tail.output,tail.state,head.localCost+tail.localCost,head.recursiveCost+tail.recursiveCost⟩

theorem SparseRun.actual (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (e : Edge)
    (ps : List (EdgeChild e)) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : SparseRun L B hB child runChild e ps F state source out) :
    executeSparse (f := f) (P := P) (G := G) (S := S) (hS := hS)
      B hB runChild e ps source state = some out := by
  induction h with
  | nil => rfl
  | cons p ps F state source head tail hh ht ih =>
    simp [executeSparse,ShortRun.actual L B hB child runChild _ _ _ _ _ hh,ih]

theorem SparseRun.projection (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (e : Edge)
    (ps : List (EdgeChild e)) (F : EdgeStream f P G S) (state : σ) (source : File)
    (out : Output σ) (h : SparseRun L B hB child runChild e ps F state source out) :
    out.output = represented L.layout B hB
      (StatefulRecursiveExchange.sparseProgram f e child ps F state).1 ∧
    out.state = (StatefulRecursiveExchange.sparseProgram f e child ps F state).2 := by
  induction h with
  | nil F state source hs => exact ⟨hs,rfl⟩
  | cons p ps F state source head tail hh ht ih =>
    have hp := hh.projection
    simpa only [StatefulRecursiveExchange.sparseProgram,StatefulRecursiveExchange.sequence,
      hp.2] using ih

theorem sparseRun_exists (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable L.layout B hB child runChild)
    (e : Edge) (ps : List (EdgeChild e)) (F : EdgeStream f P G S) (state : σ) (source : File)
    (hs : source = represented L.layout B hB F) :
    ∃ out, SparseRun L B hB child runChild e ps F state source out := by
  induction ps generalizing F state source with
  | nil => exact ⟨_,.nil F state source hs⟩
  | cons p ps ih =>
    obtain ⟨head,hh⟩ := shortRun_exists L B hB child runChild hc ⟨e,p⟩ F state source hs
    obtain ⟨tail,ht⟩ := ih _ head.state head.output (ShortRun.projection L B hB child runChild _ _ _ _ _ hh).1
    exact ⟨_,.cons p ps F state source head tail hh ht⟩

def executeEdge (B : ℕ) (hB : 0 < B) (runChild : FileChild σ)
    (e : Edge) (source : File) (state : σ) : Option (Output σ) := do
  let before ← executeProgram B hB (beforeProgram f P G S hG hS e) source
  let middle ← executeSparse (f := f) (P := P) (G := G) (S := S) (hS := hS)
    B hB runChild e (edgePivots e) before.1 state
  let after ← executeProgram B hB (afterProgram f P G S hG hS e) middle.output
  return ⟨after.1,middle.state,before.2+middle.localCost+after.2,middle.recursiveCost⟩

def EdgeRun (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (e : Edge) (F : EdgeStream f P G S) (state : σ) (source : File) (out : Output σ) : Prop :=
  ∃ (preFile : File) (cb : ℕ) (middle : Output σ) (ca : ℕ),
    ScanRun L.layout B hB (beforeProgram f P G S hG hS e) F
      (transport (coordinatePermutation f e) F) source preFile cb ∧
    SparseRun L B hB child runChild e (edgePivots e)
      (transport (coordinatePermutation f e) F) state preFile middle ∧
    ScanRun L.layout B hB (afterProgram f P G S hG hS e)
      (StatefulRecursiveExchange.sparseProgram f e child (edgePivots e)
        (transport (coordinatePermutation f e) F) state).1
      (transport (coordinatePermutation f e).symm
        (StatefulRecursiveExchange.sparseProgram f e child (edgePivots e)
          (transport (coordinatePermutation f e) F) state).1)
      middle.output out.output ca ∧
    out.state = middle.state ∧ out.localCost = cb+middle.localCost+ca ∧
      out.recursiveCost = middle.recursiveCost

theorem EdgeRun.actual (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (e : Edge) (F : EdgeStream f P G S) (state : σ) (source : File) (out : Output σ)
    (h : EdgeRun L B hB child runChild e F state source out) :
    executeEdge (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB runChild e source state = some out := by
  obtain ⟨preFile,cb,middle,ca,hb,hm,ha,hs,hl,hr⟩ := h
  have he : (⟨out.output,middle.state,cb+middle.localCost+ca,middle.recursiveCost⟩ : Output σ) = out := by
    cases out
    simp_all
  simpa [executeEdge,hb.actual,SparseRun.actual L B hB child runChild _ _ _ _ _ _ hm,ha.actual]
    using congrArg some he

theorem EdgeRun.projection (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (e : Edge) (F : EdgeStream f P G S) (state : σ) (source : File) (out : Output σ)
    (h : EdgeRun L B hB child runChild e F state source out) :
    out.output = represented L.layout B hB (StatefulRecursiveExchange.edgeProgram f e child F state).1 ∧
    out.state = (StatefulRecursiveExchange.edgeProgram f e child F state).2 := by
  obtain ⟨preFile,cb,middle,ca,hb,hm,ha,hs,hl,hr⟩ := h
  exact ⟨ha.target_eq,hs.trans (SparseRun.projection L B hB child runChild _ _ _ _ _ _ hm).2⟩

theorem edgeRun_exists (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable L.layout B hB child runChild)
    (e : Edge) (F : EdgeStream f P G S) (state : σ) (source : File)
    (hs : source = represented L.layout B hB F) :
    ∃ out, EdgeRun L B hB child runChild e F state source out := by
  obtain ⟨preFile,cb,hb,_⟩ := scanRun_exists L.layout B hB (beforeProgram f P G S hG hS e)
    _ (L.before e) F source hs
  obtain ⟨middle,hm⟩ := sparseRun_exists L B hB child runChild hc e (edgePivots e)
    _ state preFile hb.target_eq
  obtain ⟨target,ca,ha,_⟩ := scanRun_exists L.layout B hB (afterProgram f P G S hG hS e)
    _ (L.after e) _ middle.output (SparseRun.projection L B hB child runChild _ _ _ _ _ _ hm).1
  exact ⟨⟨target,middle.state,cb+middle.localCost+ca,middle.recursiveCost⟩,
    preFile,cb,middle,ca,hb,hm,ha,rfl,rfl,rfl⟩

/-- The node machine receives only the incoming ports of this actual wire. -/
def portFiles (input : Reg → File) (stored : Edge → File) (e : Edge) :
    InputPort (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e) → File :=
  fun port => match port with
    | .inl i => input i.val
    | .inr incoming => stored incoming.val

def executeGate (B V : ℕ) (input : Reg → File) (stored : Edge → File) (e : Edge) :=
  NodeStreamMachine.nodeOutput B V (globalProgram Parameters.d)
    (wireTail (globalProgram Parameters.d) e) (portFiles input stored e) ⟨e,rfl⟩

structure GateRun (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File) (e : Edge)
    (result : GateStreamMachine.Result) : Prop where
  input_eq : ∀ r, inputFiles r = represented L.layout B hB (input r)
  stored_eq : ∀ incoming, wireHead (globalProgram Parameters.d) incoming =
    wireTail (globalProgram Parameters.d) e →
    storedFiles incoming = represented L.layout B hB (stored incoming)
  actual : executeGate B (longVolume f P G S) inputFiles storedFiles e = some result
  output_eq : result.disk = represented L.layout B hB
    (StatefulRecursiveExchange.gateInput f input stored e)
  cost_eq : result.cost = NodeStreamMachine.nodeScans (globalProgram Parameters.d)
    (wireTail (globalProgram Parameters.d) e) ⟨e,rfl⟩ * (3*((longVolume f P G S+B-1)/B))

theorem gateRun_exists (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File) (e : Edge)
    (hi : ∀ r, inputFiles r = represented L.layout B hB (input r))
    (hs : ∀ incoming, wireHead (globalProgram Parameters.d) incoming =
      wireTail (globalProgram Parameters.d) e →
      storedFiles incoming = represented L.layout B hB (stored incoming)) :
    ∃ result, GateRun L B hB input stored inputFiles storedFiles e result := by
  let values : InputPort (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e) → Fin (longVolume f P G S) → Bit :=
    fun port => match port with
      | .inl i => encoded L.layout (input i.val)
      | .inr incoming => encoded L.layout (stored incoming.val)
  have hp : portFiles inputFiles storedFiles e =
      fun port => BucketMachine.pack B hB (List.ofFn (values port)) := by
    funext port
    cases port with
    | inl i => exact hi i.val
    | inr incoming => exact hs incoming.val incoming.property
  refine ⟨⟨represented L.layout B hB (StatefulRecursiveExchange.gateInput f input stored e),
    NodeStreamMachine.nodeScans (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e) ⟨e,rfl⟩*(3*((longVolume f P G S+B-1)/B))⟩,
    hi,hs,?_,rfl,rfl⟩
  rw [executeGate,hp]
  convert NodeStreamMachine.nodeOutput_correct B (longVolume f P G S) hB
    (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e) values ⟨e,rfl⟩ using 1
  apply congrArg some
  apply congrArg (fun disk => GateStreamMachine.Result.mk disk _)
  apply congrArg (BucketMachine.pack B hB)
  apply congrArg List.ofFn
  funext i
  change localMap (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e)
    (fun port => match port with
      | .inl r => input r.val (L.layout.symm i)
      | .inr incoming => stored incoming.val (L.layout.symm i)) ⟨e,rfl⟩ = _
  apply congrArg (fun vals => localMap (globalProgram Parameters.d)
    (wireTail (globalProgram Parameters.d) e) vals ⟨e,rfl⟩)
  funext port
  cases port <;> rfl

structure RowsOutput (σ : Type) where
  files : Reg → File
  state : σ
  localCost : ℕ
  recursiveCost : ℕ

def executeRows (B : ℕ) (hB : 0 < B) (runChild : FileChild σ)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) :
    List Reg → (Reg → File) → σ → Option (RowsOutput σ)
  | [],table,state => some ⟨table,state,0,0⟩
  | r::rs,table,state => do
      let gate ← executeGate B (longVolume f P G S) inputFiles storedFiles (t,r)
      let head ← executeEdge (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
        B hB runChild (t,r) gate.disk state
      let tail ← executeRows B hB runChild inputFiles storedFiles t rs
        (Function.update table r head.output) head.state
      return ⟨tail.files,tail.state,gate.cost+head.localCost+tail.localCost,
        head.recursiveCost+tail.recursiveCost⟩

/-- Frozen incoming files and fresh outgoing files implement the same
simultaneous gate semantics as the eager stateful circuit evaluator. -/
inductive RowsRun (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) :
    List Reg → (Reg → EdgeStream f P G S) → (Reg → File) → σ → RowsOutput σ → Prop
  | nil (table files state) (ht : ∀ r, files r = represented L.layout B hB (table r)) :
      RowsRun L B hB child runChild input stored inputFiles storedFiles t [] table files state
        ⟨files,state,0,0⟩
  | cons (r rs table files state gate head tail)
      (hg : GateRun L B hB input stored inputFiles storedFiles (t,r) gate)
      (he : EdgeRun L B hB child runChild (t,r)
        (StatefulRecursiveExchange.gateInput f input stored (t,r)) state gate.disk head)
      (ht : RowsRun L B hB child runChild input stored inputFiles storedFiles t rs
        (Function.update table r (StatefulRecursiveExchange.edgeProgram f (t,r) child
          (StatefulRecursiveExchange.gateInput f input stored (t,r)) state).1)
        (Function.update files r head.output) head.state tail) :
      RowsRun L B hB child runChild input stored inputFiles storedFiles t (r::rs) table files state
        ⟨tail.files,tail.state,gate.cost+head.localCost+tail.localCost,
          head.recursiveCost+tail.recursiveCost⟩

theorem RowsRun.actual (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (rs : List Reg)
    (table : Reg → EdgeStream f P G S) (files : Reg → File) (state : σ) (out : RowsOutput σ)
    (h : RowsRun L B hB child runChild input stored inputFiles storedFiles t rs table files state out) :
    executeRows (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB runChild inputFiles storedFiles t rs files state = some out := by
  induction h with
  | nil => rfl
  | cons r rs table files state gate head tail hg he ht ih =>
    simp [executeRows,hg.actual,EdgeRun.actual L B hB child runChild _ _ _ _ _ he,ih]

theorem RowsRun.projection (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (rs : List Reg)
    (table : Reg → EdgeStream f P G S) (files : Reg → File) (state : σ) (out : RowsOutput σ)
    (h : RowsRun L B hB child runChild input stored inputFiles storedFiles t rs table files state out) :
    let expected := StatefulRecursiveExchange.tabulate rs
      (fun r => StatefulRecursiveExchange.edgeProgram f (t,r) child
        (StatefulRecursiveExchange.gateInput f input stored (t,r))) table state
    (∀ r,out.files r = represented L.layout B hB (expected.1 r)) ∧ out.state = expected.2 := by
  induction h with
  | nil table files state ht => exact ⟨ht,rfl⟩
  | cons r rs table files state gate head tail hg he ht ih =>
    have hp := EdgeRun.projection L B hB child runChild _ _ _ _ _ he
    simpa only [StatefulRecursiveExchange.tabulate,StatefulRecursiveExchange.sequence,hp.2] using ih

theorem rowsRun_exists (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable L.layout B hB child runChild)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (hi : ∀ r, inputFiles r = represented L.layout B hB (input r))
    (hs : ∀ e, storedFiles e = represented L.layout B hB (stored e))
    (t : Fin ((globalProgram Parameters.d).length+1)) (rs : List Reg)
    (table : Reg → EdgeStream f P G S) (files : Reg → File) (state : σ)
    (hf : ∀ r, files r = represented L.layout B hB (table r)) :
    ∃ out, RowsRun L B hB child runChild input stored inputFiles storedFiles t rs table files state out := by
  induction rs generalizing table files state with
  | nil => exact ⟨_,.nil table files state hf⟩
  | cons r rs ih =>
    obtain ⟨gate,hg⟩ := gateRun_exists L B hB input stored inputFiles storedFiles (t,r) hi (fun incoming _ => hs incoming)
    obtain ⟨head,he⟩ := edgeRun_exists L B hB child runChild hc (t,r) _ state gate.disk hg.output_eq
    have hp := EdgeRun.projection L B hB child runChild _ _ _ _ _ he
    have hu : ∀ i, (Function.update files r head.output) i = represented L.layout B hB
        ((Function.update table r (StatefulRecursiveExchange.edgeProgram f (t,r) child
          (StatefulRecursiveExchange.gateInput f input stored (t,r)) state).1) i) := by
      intro i
      by_cases h : i = r
      · subst i; simpa only [Function.update_self] using hp.1
      · simpa only [Function.update_of_ne h] using hf i
    obtain ⟨tail,ht⟩ := ih _ _ head.state hu
    exact ⟨_,.cons r rs table files state gate head tail hg he ht⟩

/-- Sequential tabulation never inspects its old table while computing a
new value. Initial file references therefore need no initialized payload. -/
theorem tabulate_initial {Key Value State : Type} [DecidableEq Key]
    (keys : List Key) (run : Key → State → Value × State)
    (initial other : Key → Value) (state : State) :
    (StatefulRecursiveExchange.tabulate keys run initial state).2 =
      (StatefulRecursiveExchange.tabulate keys run other state).2 ∧
    ∀ k, (k ∈ keys ∨ initial k = other k) →
      (StatefulRecursiveExchange.tabulate keys run initial state).1 k =
        (StatefulRecursiveExchange.tabulate keys run other state).1 k := by
  induction keys generalizing initial other state with
  | nil => exact ⟨rfl,fun k hk => hk.resolve_left (by simp)⟩
  | cons k keys ih =>
    have h := ih (Function.update initial k (run k state).1)
      (Function.update other k (run k state).1) (run k state).2
    refine ⟨h.1,fun j hj => h.2 j ?_⟩
    rcases hj with hj | hj
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inr (by simp)
      · exact Or.inl hj
    · right
      by_cases he : j = k
      · subst j; simp
      · simpa only [Function.update_of_ne he] using hj

structure LayerOutput (σ : Type) where
  files : Edge → File
  state : σ
  localCost : ℕ
  recursiveCost : ℕ

def executeLayer (B : ℕ) (hB : 0 < B) (runChild : FileChild σ)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) : Option (LayerOutput σ) := do
  let out ← executeRows (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
    B hB runChild inputFiles storedFiles t (Finset.univ : Finset Reg).toList inputFiles state
  return ⟨fun e => if e.1=t then out.files e.2 else storedFiles e,
    out.state,out.localCost,out.recursiveCost⟩

/-- The initial row table consists of existing source-file references.
Every row is overwritten once before the layer returns. -/
def LayerRun (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) (out : LayerOutput σ) : Prop :=
  ∃ rows, RowsRun L B hB child runChild input stored inputFiles storedFiles t
      (Finset.univ : Finset Reg).toList input inputFiles state rows ∧
    out.files = (fun e => if e.1=t then rows.files e.2 else storedFiles e) ∧
    out.state = rows.state ∧ out.localCost = rows.localCost ∧ out.recursiveCost = rows.recursiveCost

theorem LayerRun.actual (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) (out : LayerOutput σ)
    (h : LayerRun L B hB child runChild input stored inputFiles storedFiles t state out) :
    executeLayer (f := f) (P := P) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB runChild inputFiles storedFiles t state = some out := by
  obtain ⟨rows,hr,hf,hs,hl,hc⟩ := h
  have he : (⟨fun e => if e.1=t then rows.files e.2 else storedFiles e,
      rows.state,rows.localCost,rows.recursiveCost⟩ : LayerOutput σ) = out := by
    cases out
    simp_all
  simpa [executeLayer,RowsRun.actual L B hB child runChild _ _ _ _ _ _ _ _ _ _ hr]
    using congrArg some he

theorem LayerRun.projection (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ) (out : LayerOutput σ)
    (h : LayerRun L B hB child runChild input stored inputFiles storedFiles t state out) :
    let expected := StatefulRecursiveExchange.layer f input stored
      (fun e => StatefulRecursiveExchange.edgeProgram f e child) t state
    (∀ e, e.1=t → out.files e = represented L.layout B hB (expected.1 e)) ∧
      out.state = expected.2 ∧ (∀ e,e.1≠t → out.files e=storedFiles e) := by
  obtain ⟨rows,hr,hf,hs,hl,hc⟩ := h
  have hp := RowsRun.projection L B hB child runChild _ _ _ _ _ _ _ _ _ _ hr
  have hz := tabulate_initial (Finset.univ : Finset Reg).toList
    (fun r => StatefulRecursiveExchange.edgeProgram f (t,r) child
      (StatefulRecursiveExchange.gateInput f input stored (t,r))) input (fun _ _ => 0) state
  refine ⟨?_,hs.trans (hp.2.trans hz.1),?_⟩
  · intro e he
    simp only [hf,if_pos he]
    try dsimp only [StatefulRecursiveExchange.layer]
    have hmem : e.2 ∈ (Finset.univ : Finset Reg).toList := by
      simp only [Finset.mem_toList,Finset.mem_univ]
    rw [if_pos he,hp.1,hz.2 e.2 (Or.inl hmem)]
  · intro e he
    simp only [hf,if_neg he]

/-- Only actual incoming ports need files; future wire slots can remain
empty because the node machine never reads them. -/
theorem rowsRun_exists_of_gates (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable L.layout B hB child runChild)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1))
    (hgates : ∀ r,∃ result,GateRun L B hB input stored inputFiles storedFiles (t,r) result)
    (rs : List Reg) (table : Reg → EdgeStream f P G S) (files : Reg → File) (state : σ)
    (hf : ∀ r, files r = represented L.layout B hB (table r)) :
    ∃ out, RowsRun L B hB child runChild input stored inputFiles storedFiles t rs table files state out := by
  induction rs generalizing table files state with
  | nil => exact ⟨_,.nil table files state hf⟩
  | cons r rs ih =>
    obtain ⟨gate,hg⟩ := hgates r
    obtain ⟨head,he⟩ := edgeRun_exists L B hB child runChild hc (t,r) _ state gate.disk hg.output_eq
    have hp := EdgeRun.projection L B hB child runChild _ _ _ _ _ he
    have hu : ∀ i, (Function.update files r head.output) i = represented L.layout B hB
        ((Function.update table r (StatefulRecursiveExchange.edgeProgram f (t,r) child
          (StatefulRecursiveExchange.gateInput f input stored (t,r)) state).1) i) := by
      intro i
      by_cases h : i = r
      · subst i; simpa only [Function.update_self] using hp.1
      · simpa only [Function.update_of_ne h] using hf i
    obtain ⟨tail,ht⟩ := ih _ _ head.state hu
    exact ⟨_,.cons r rs table files state gate head tail hg he ht⟩

theorem layerRun_exists (L : LayoutLaws f P G S hG hS) (B : ℕ) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin P) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ)
    (hc : ChildAvailable L.layout B hB child runChild)
    (input : Reg → EdgeStream f P G S) (stored : Edge → EdgeStream f P G S)
    (inputFiles : Reg → File) (storedFiles : Edge → File)
    (t : Fin ((globalProgram Parameters.d).length+1)) (state : σ)
    (hi : ∀ r, inputFiles r = represented L.layout B hB (input r))
    (hs : ∀ e,e.1.val<t.val → storedFiles e = represented L.layout B hB (stored e)) :
    ∃ out, LayerRun L B hB child runChild input stored inputFiles storedFiles t state out := by
  have hgates : ∀ r,∃ result,GateRun L B hB input stored inputFiles storedFiles (t,r) result := by
    intro r
    exact gateRun_exists L B hB input stored inputFiles storedFiles (t,r) hi
      (fun incoming he => hs incoming (incoming_index_lt (t,r) incoming he))
  obtain ⟨rows,hr⟩ := rowsRun_exists_of_gates L B hB child runChild hc input stored inputFiles
    storedFiles t hgates _ input inputFiles state hi
  exact ⟨⟨fun e => if e.1=t then rows.files e.2 else storedFiles e,
    rows.state,rows.localCost,rows.recursiveCost⟩,rows,hr,rfl,rfl,rfl,rfl⟩

end ConcreteEdges

end
end CSL.PhysicalRecursiveExchange


