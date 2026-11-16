-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_PathOutput
-- name    : DecrAlmostLinearSSSP_Decremental_Supplement_PathOutput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:15:19.395424+00:00
-- url     : https://prove2.me/theorems/3520bdf7-c031-48cc-bcc5-884278f21aef
-- title:
--   Explicit distance queries and charged simple-path output
-- statement:
--   For a completed state, the explicit distance array occupies the first $n$ cells of its natural and real memory banks. A natural flag equal to one denotes infinity. Query mode zero returns the stored distance and mode one returns the unreachability flag. A path consists of original directed edge identifiers with matching endpoints, all active at the current prefix, and with no repeated vertex. Its vertex count includes the source:
--
--   $$
--   |P|=1+\#\{\text{edges in its list}\},\qquad w(P)=\sum_{e\in P}w(e).
--   $$
--
--   A path query must execute the scalar program, terminate without a fault, and emit the complete ordered vertex/edge transcript through charged scalar stores to two reserved output ports. It must produce a simple source-to-target path of weight at most the current label. The source path therefore emits its single vertex and has cost bounded by the same output constant.
--
--   All loads, traversal, stack or reversal work and output stores are charged by the instruction counter. Scalar queries have a uniform constant bound; path queries have a uniform constant times $|P|$ bound. Queries preserve persistent memory, and both output ports are reset at public entry points. These conditions allow repeated queries followed by further updates; no mathematical shortest-path evaluator is installed as a primitive.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), pp.1, 3, 31–34, Lemma 5.1 and path-query operation

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Execution

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

inductive OutputEvent
  | vertex (v : ℕ)
  | edge (e : ℕ)
  deriving DecidableEq

/-- A storeN to port n emits a vertex, and to port n+1 emits an original edge identifier.
These are ordinary charged scalar store instructions, with no path evaluation primitive. -/
def emitted (p : Program) (n : ℕ) (c : Machine) : Option OutputEvent :=
  if c.halted then none else
  match p.code[c.pc]? with
  | some (.storeN a d) => if c.natReg a = n then some (.vertex (c.natReg d))
    else if c.natReg a = n + 1 then some (.edge (c.natReg d)) else none
  | _ => none

noncomputable def outputTrace (p : Program) (n : ℕ) (c : Machine) (t : ℕ) : List OutputEvent :=
  (List.range t).filterMap (fun j => emitted p n (execute p c j))

def pathTranscript (i : Instance) (es : List (Fin i.k)) : List OutputEvent :=
  .vertex i.source.val :: es.flatMap (fun e => [.edge e.val, .vertex (i.graph.head e).val])

def SimplePath (i : Instance) (updates : List (Fin i.k)) (v : Fin i.n)
    (es : List (Fin i.k)) : Prop :=
  Walk i.graph (i.active updates) i.source v es ∧
  (i.source :: es.map i.graph.head).Nodup

noncomputable def pathWeight (i : Instance) (es : List (Fin i.k)) : ℝ≥0∞ :=
  (es.map (fun e => ENNReal.ofReal (i.weight e))).sum

/-- Query mode 0: distance, 1: unreachable flag, 2: path; target and mode in natural 4,5. -/
def queryCall (p : Program) (i : Instance) (c : Machine) (v mode : ℕ) : Machine :=
  {resume c p.query with
    natReg := fun r => if r = 0 then i.n else if r = 1 then i.size
      else if r = 3 then i.source.val else if r = 4 then v else if r = 5 then mode else 0
    realReg := fun r => if r = 0 then i.accuracy else if r = 1 then i.W else 0}

/-- Queries preserve persistent memory. Only the two output-port cells may change, and these
are reset by the call wrapper, making arbitrary sequences of queries composable. -/
def Preserves (i : Instance) (c d : Machine) : Prop :=
  d.realMem = c.realMem ∧ ∀ a, a ≠ i.n → a ≠ i.n + 1 → d.natMem a = c.natMem a

def ScalarQueries (p : Program) (i : Instance) (c : Machine) (Q : ℕ) : Prop :=
  ∀ v : Fin i.n, ∀ mode ∈ [0, 1], ∃ d,
    Ends p (queryCall p i (clearPorts i c) v.val mode) d ∧
    d.work + 32 ≤ c.work + Q ∧ Preserves i c d ∧
    d.natReg 8 = c.natMem v.val ∧ d.realReg 3 = c.realMem v.val

/-- Successful reporting emits the whole vertex/edge list, including the singleton source path.
The final memory condition permits further maintenance and arbitrary subsequent queries. -/
def PathQuery (p : Program) (i : Instance) (updates : List (Fin i.k))
    (c : Machine) (v : Fin i.n) (C : ℕ) : Prop :=
  ∃ (es : List (Fin i.k)) (t : ℕ) (d : Machine),
    SimplePath i updates v es ∧ pathWeight i es ≤ stored c v.val ∧
    execute p (queryCall p i (clearPorts i c) v.val 2) t = d ∧
    d.halted = true ∧ d.fault = false ∧ Preserves i c d ∧
    outputTrace p i.n (queryCall p i (clearPorts i c) v.val 2) t = pathTranscript i es ∧
    d.work + 32 ≤ c.work + C * (es.length + 1)

end DecrAlmostLinearSSSP.Decremental.Supplement


