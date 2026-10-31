-- Prove2me | Definitions.Def_BulteauTranspositions_NPHard_Blocks
-- name    : BulteauTranspositions_NPHard_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:52:53.764992+00:00
-- url     : https://prove2.me/theorems/7968e304-0b21-4b63-8385-a17ad78b27e1
-- title:
--   Block decompositions, variables, local behavior and assembling
-- statement:
--   A block decomposition has increasing cuts starting at zero and lying below the span; the final endpoint is the span. Blocks retain their one-based indices, while their local words omit dots. A variable pairs oriented triples (a,b,c) and (x,y,z), with b,x,y in a source block and a,c,z in a distinct target. Located variables satisfy precisely these two placement conditions. Validity additionally requires x≺y to imply x◁b◁y and requires a≺z≺c. A valid context partitions exactly the external triples into valid variables. Context steps transport every cut by the inverse transposition, and finite runs need not assume validity of intermediate contexts.
--
--   The four basic gates have exactly the words and internal triples of §3.2. Ports use distinct even labels, internal symbols distinct odd labels. Their operational local graph allows deletion/transposition of a cyclically ordered internal triple, incoming activation replacing z by b and making (a,b,c) internal, or outgoing activation deleting the factor xby. Complete activation orders are labels of finite paths that exhaust the input and output ports. No desired activation order is built into this definition.
--
--   An assembling concatenates the gate words, takes their internal and port triples, and places cuts at the word boundaries. Every port occurs once as an input and once as an output of a different gate. Relabeling allows an arbitrary finite source alphabet and any order of the triple list. The definition does not assume collapsibility, a valid variable context, or existence of an equivalent permutation.
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, definitions and constructions, printed/PDF pp. 11–25; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace BulteauTranspositions.NPHard

structure Variable where
  abc : Triple
  xyz : Triple
  deriving DecidableEq, Inhabited

structure Context where
  inst : Instance
  cuts : List ℕ

def Context.WF (C : Context) : Prop :=
  C.inst.WF ∧ C.cuts ≠ [] ∧ C.cuts.headD 0 = 0 ∧
  C.cuts.Pairwise (· < ·) ∧ ∀ s ∈ C.cuts, s < C.inst.span

/-- One-based block numbers: a cut belongs to the preceding block. -/
def Context.block (C : Context) (a : ℕ) : ℕ :=
  (C.cuts.filter (· < C.inst.pos a)).length

def Internal (C : Context) (t : Triple) : Prop :=
  C.block t.1 = C.block t.2.1 ∧ C.block t.2.1 = C.block t.2.2

def Variable.Located (A : Variable) (C : Context) : Prop :=
  A.abc ∈ C.inst.triples ∧ A.xyz ∈ C.inst.triples ∧ A.abc ≠ A.xyz ∧
  C.block A.abc.2.1 = C.block A.xyz.1 ∧
  C.block A.xyz.1 = C.block A.xyz.2.1 ∧
  C.block A.abc.1 = C.block A.abc.2.2 ∧
  C.block A.abc.2.2 = C.block A.xyz.2.2 ∧
  C.block A.abc.2.1 ≠ C.block A.abc.1

def Variable.Valid (A : Variable) (C : Context) : Prop :=
  A.Located C ∧
  (C.inst.Before A.xyz.1 A.xyz.2.1 →
    C.inst.Consecutive A.xyz.1 A.abc.2.1 ∧ C.inst.Consecutive A.abc.2.1 A.xyz.2.1) ∧
  C.inst.Before A.abc.1 A.xyz.2.2 ∧ C.inst.Before A.xyz.2.2 A.abc.2.2

/-- Partition of exactly the external triples, with each used once. -/
def VariablePartition (C : Context) (As : List Variable) : Prop :=
  (As.flatMap fun A => [A.abc, A.xyz]).Nodup ∧
  ∀ t, (t ∈ C.inst.triples ∧ ¬ Internal C t) ↔
    t ∈ As.flatMap (fun A => [A.abc, A.xyz])

def ValidContext (C : Context) : Prop :=
  C.WF ∧ ∃ As, VariablePartition C As ∧ ∀ A ∈ As, A.Valid C

def ContextStep (C : Context) (t : Triple) (D : Context) : Prop :=
  C.WF ∧ D.WF ∧ Step C.inst t D.inst ∧
  D.cuts = C.cuts.map (tripleCut C.inst t).inv.tau

def ContextRun (C D : Context) : Prop :=
  Relation.ReflTransGen (fun U V => ∃ t, ContextStep U t V) C D

inductive GateKind where
  | copy | and | or | var
  deriving DecidableEq, Inhabited

/-- For copy/var, w0 is the input; for and/or, w0 is the output. -/
structure Gate where
  kind : GateKind
  w0 : ℕ
  w1 : ℕ
  w2 : ℕ
  deriving DecidableEq, Inhabited

def Gate.inputs (g : Gate) : List ℕ :=
  match g.kind with
  | .copy | .var => [g.w0]
  | .and | .or => [g.w1, g.w2]

def Gate.outputs (g : Gate) : List ℕ :=
  match g.kind with
  | .copy | .var => [g.w1, g.w2]
  | .and | .or => [g.w0]

/-- Even labels are port symbols; odd labels are fresh internal symbols. -/
def wire (w : ℕ) : Variable :=
  ⟨(12*w, 12*w+2, 12*w+4), (12*w+6, 12*w+8, 12*w+10)⟩

def fresh (h r : ℕ) : ℕ := 2*(9*h+r)+1

def Gate.word (g : Gate) (h : ℕ) : List ℕ :=
  let A := wire g.w0
  let A1 := wire g.w1
  let A2 := wire g.w2
  let d := fresh h 0; let e := fresh h 1; let f := fresh h 2
  let a' := fresh h 6; let b' := fresh h 7; let c' := fresh h 8
  match g.kind with
  | .copy => [A.abc.1,A1.xyz.2.1,e,A.xyz.2.2,d,A2.xyz.2.1,A1.xyz.1,
      A1.abc.2.1,A.abc.2.2,A2.xyz.1,A2.abc.2.1,f]
  | .and => [A1.abc.1,e,A1.xyz.2.2,A2.abc.1,A1.abc.2.2,A2.xyz.2.2,d,
      A.xyz.2.1,A2.abc.2.2,A.xyz.1,A.abc.2.1,f]
  | .or => [A1.abc.1,b',A1.xyz.2.2,A2.abc.1,d,A.xyz.2.1,a',A.xyz.1,
      A.abc.2.1,f,A2.xyz.2.2,A1.abc.2.2,e,c',A2.abc.2.2]
  | .var => [d,A1.xyz.2.1,A.abc.1,fresh h 3,A2.xyz.2.1,e,a',fresh h 4,
      A1.xyz.1,A1.abc.2.1,f,c',A.xyz.2.2,b',A.abc.2.2,A2.xyz.1,
      A2.abc.2.1,fresh h 5]

def Gate.internals (g : Gate) (h : ℕ) : List Triple :=
  let t := (fresh h 0, fresh h 1, fresh h 2)
  let u := (fresh h 6, fresh h 7, fresh h 8)
  match g.kind with
  | .copy | .and => [t]
  | .or => [u,t]
  | .var => [t,(fresh h 3,fresh h 4,fresh h 5),u]

/-- The local behavior graph forgets dots but retains unactivated ports and internal triples. -/
structure LocalState where
  word : List ℕ
  internalTriples : List Triple
  inputs : List Variable
  outputs : List Variable

def Gate.localState (g : Gate) (h : ℕ) : LocalState :=
  ⟨g.word h, g.internals h, g.inputs.map wire, g.outputs.map wire⟩

def Cyclic (t u : Triple) : Prop :=
  u = t ∨ u = (t.2.1,t.2.2,t.1) ∨ u = (t.2.2,t.1,t.2.1)

/-- Operational arcs of pp.14–16, not a table of allowed activation orders. -/
inductive LocalArc : LocalState → Option Variable → LocalState → Prop where
  | internal (S : LocalState) (t u : Triple) (R X Y Z : List ℕ)
      (ht : t ∈ S.internalTriples) (hc : Cyclic t u)
      (hw : S.word = R ++ [u.1] ++ X ++ [u.2.1] ++ Y ++ [u.2.2] ++ Z) :
      LocalArc S none { S with
        word := R ++ Y ++ X ++ Z,
        internalTriples := S.internalTriples.erase t }
  | input (S : LocalState) (A : Variable) (R U V W : List ℕ)
      (ha : A ∈ S.inputs)
      (hw : S.word = R ++ [A.abc.1] ++ U ++ [A.xyz.2.2] ++ V ++ [A.abc.2.2] ++ W) :
      LocalArc S (some A) { S with
        word := R ++ [A.abc.1] ++ U ++ [A.abc.2.1] ++ V ++ [A.abc.2.2] ++ W,
        inputs := S.inputs.erase A, internalTriples := A.abc :: S.internalTriples }
  | output (S : LocalState) (A : Variable) (R T : List ℕ)
      (ha : A ∈ S.outputs)
      (hw : S.word = R ++ [A.xyz.1,A.abc.2.1,A.xyz.2.1] ++ T) :
      LocalArc S (some A) { S with word := R ++ T, outputs := S.outputs.erase A }

inductive LocalRun : LocalState → List Variable → LocalState → Prop where
  | refl (S) : LocalRun S [] S
  | step {S T U e es} : LocalArc S e T → LocalRun T es U →
      LocalRun S (e.toList ++ es) U

def ActivationOrder (g : Gate) (h : ℕ) (order : List Variable) : Prop :=
  ∃ S, LocalRun (g.localState h) order S ∧ S.inputs = [] ∧ S.outputs = []

def assemblyWord (gs : List Gate) : List ℕ :=
  gs.zipIdx |>.flatMap fun gh => gh.1.word gh.2

def assemblyTriples (gs : List Gate) : List Triple :=
  (gs.zipIdx.flatMap fun gh => gh.1.internals gh.2) ++
  ((gs.flatMap Gate.inputs).eraseDups.flatMap fun w => [(wire w).abc,(wire w).xyz])

def assembly (gs : List Gate) : Context :=
  let w := assemblyWord gs
  ⟨⟨w.length, assemblyTriples gs, fun a => w.idxOf a + 1⟩,
    (List.range gs.length).map fun h => (assemblyWord (gs.take h)).length⟩

def WellWired (gs : List Gate) : Prop :=
  gs ≠ [] ∧ (∀ g ∈ gs, [g.w0,g.w1,g.w2].Nodup) ∧
  (gs.flatMap Gate.inputs).Nodup ∧ (gs.flatMap Gate.outputs).Nodup ∧
  (gs.flatMap Gate.inputs).Perm (gs.flatMap Gate.outputs) ∧
  ∀ g ∈ gs, ∀ w ∈ g.inputs, w ∉ g.outputs

/-- Relabeling allows every finite alphabet of Definition 14, not only canonical names. -/
def Relabels (C D : Context) (f : ℕ → ℕ) : Prop :=
  C.cuts = D.cuts ∧ C.inst.span = D.inst.span ∧
  Set.InjOn f {a | a ∈ C.inst.symbols} ∧
  (C.inst.triples.map fun t => (f t.1,f t.2.1,f t.2.2)).Perm D.inst.triples ∧
  ∀ a ∈ C.inst.symbols, D.inst.pos (f a) = C.inst.pos a

def IsAssembly (C : Context) : Prop :=
  C.WF ∧ ∃ gs f, WellWired gs ∧ Relabels (assembly gs) C f

end BulteauTranspositions.NPHard


