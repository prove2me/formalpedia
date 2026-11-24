-- Prove2me | Definitions.Def_GomoryGroup_Rel_Supplement_Tabulation
-- name    : GomoryGroup_Rel_Supplement_Tabulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:19:50.748408+00:00
-- url     : https://prove2.me/theorems/5006e82e-27f6-4225-a942-98026fa54eef
-- title:
--   (8), p. 264 — initialized tabulation and recorded optimal-vector recovery
-- statement:
--   The **tabulation procedure** takes only an enumeration of the standard-form group, the nonbasic column images and their relative costs. A cell is either unreachable or a real value with a nonnegative integer witness. The empty prefix has value $0$ and zero witness at the identity, and is unreachable elsewhere. For column $a_s$ with cost $c_s^*$, the update compares the old cell with the candidate obtained from its predecessor:
--   $$\varphi_s(p)=\max\{\varphi_s(p-a_s)+c_s^*,\ \varphi_{s-1}(p)\}.$$
--
--   The procedure constructs each cyclic orbit by charged group additions, then sweeps each orbit twice. Predecessor cells are read from the orbit order. Every candidate real addition, real comparison and successful witness increment is recorded. Ties retain the old witness. Persistent witness vectors are recorded during forward calculation; recovery materializes their coordinates, charging one output copy per coordinate. No precomputed orbit, value or witness table is an input.
--
--   **Formalization Note** Unreachable cells represent $-\infty$ without performing extended-real arithmetic. This repairs the insufficient finite-sentinel initialization printed on p. 264. The optional smallest-total-witness refinement in the proof is not asserted by THEOREM 3, which requires an optimal vector. Correctness and all operation bounds are separate theorem obligations, not fields assumed by these definitions.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 264, (8), initialization and backtracking paragraphs; p. 262, THEOREM 3

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Supplement_Arithmetic

set_option autoImplicit false

namespace GomoryGroup.Rel.Supplement

/-- None is unreachable (−∞); a reachable cell stores its real value and a witness.
The input never contains a value or witness table. -/
abbrev Cell (n : ℕ) := Option (ℝ × (Fin n → ℕ))
abbrev ValueTable (G : Type) (n : ℕ) := G → Cell n

/-- Construct one cyclic orbit. The fuel is the cardinality of the group.
Each successor is a charged group addition; equality tests and list bookkeeping
are administrative, as are visited-table tests in `tabulateStage`. -/
def walkOrbit {G : Type} [AddCommGroup G] [DecidableEq G]
    (a origin : G) : ℕ → G → ArithmeticRun (List G)
  | 0, _ => pure []
  | fuel + 1, p => do
      let q ← ArithmeticRun.addGroup p a
      if q = origin then
        pure [p]
      else
        let tail ← walkOrbit a origin fuel q
        pure (p :: tail)

/-- One update of (8), using the previous cell along the cyclic orbit.
Unavailable states are never treated as finite numbers. Ties keep the old cell. -/
noncomputable def relax {n : ℕ} (j : Fin n) (c : ℝ) (previous old : Cell n) :
    ArithmeticRun (Cell n) := do
  match previous with
  | none => pure old
  | some (v, y) =>
      let candidate ← ArithmeticRun.addReal v c
      match old with
      | none =>
          let k ← ArithmeticRun.succWitness (y j)
          pure (some (candidate, Function.update y j k))
      | some (w, _) =>
          let improve ← ArithmeticRun.lessReal w candidate
          if improve then
            let k ← ArithmeticRun.succWitness (y j)
            pure (some (candidate, Function.update y j k))
          else pure old

/-- One in-place sweep around an orbit. Its last cell supplies the predecessor
of its first cell, so no extra group subtraction is needed. -/
noncomputable def sweep {G : Type} [Zero G] [DecidableEq G] {n : ℕ}
    (j : Fin n) (c : ℝ) (orbit : List G) (table : ValueTable G n) :
    ArithmeticRun (ValueTable G n) :=
  let start : ArithmeticRun (ValueTable G n × Cell n) :=
    pure (table, table (orbit.getLast?.getD 0))
  let finish := orbit.foldl (fun state p => do
    let (t, previous) ← state
    let cell ← relax j c previous (t p)
    pure (Function.update t p cell, cell)) start
  do
    let (t, _) ← finish
    pure t

/-- Stage s: find each coset of the new column's cyclic subgroup by walking
unvisited elements, then sweep it twice. The standard-form enumeration is input
metadata; no optimal-answer or orbit table is an input. -/
noncomputable def tabulateStage {G : Type} [AddCommGroup G] [DecidableEq G] {n : ℕ}
    (enumeration : List G) (j : Fin n) (a : G) (c : ℝ) (table : ValueTable G n) :
    ArithmeticRun (ValueTable G n) :=
  let start : ArithmeticRun (ValueTable G n × List G) := pure (table, [])
  let finish := enumeration.foldl (fun state p => do
    let (t, seen) ← state
    if p ∈ seen then pure (t, seen)
    else
      let orbit ← walkOrbit a p enumeration.length p
      let t₁ ← sweep j c orbit t
      let t₂ ← sweep j c orbit t₁
      pure (t₂, seen ++ orbit)) start
  do
    let (t, _) ← finish
    pure t

/-- Exact empty-prefix initialization: value 0 with zero witness at the origin;
unreachable everywhere else. This repairs the finite-sentinel sentence on p.264. -/
def initialTable {G : Type} [Zero G] [DecidableEq G] (n : ℕ) : ValueTable G n :=
  fun p => if p = 0 then some (0, fun _ => 0) else none

/-- A fixed algorithm, uniform in the supplied column images and reduced costs.
The input consists only of the group enumeration, column images and costs. -/
noncomputable def tabulate {G : Type} [AddCommGroup G] [DecidableEq G] {n : ℕ}
    (enumeration : List G) (columns : Fin n → G) (costs : Fin n → ℝ) :
    ArithmeticRun (ValueTable G n) :=
  (List.finRange n).foldl (fun state j => do
    let table ← state
    tabulateStage enumeration j (columns j) (costs j) table)
    (pure (initialTable n))

/-- Materialize one vector with one charged copy per output coordinate. -/
def copyVector {n : ℕ} (y : Fin n → ℕ) : ArithmeticRun (Fin n → ℕ) :=
  (List.finRange n).foldl (fun state j => do
    let v ← state
    let k ← ArithmeticRun.copyOutput (y j)
    pure (Function.update v j k)) (pure (fun _ => 0))

/-- Recover one witness from the records produced during the forward run. -/
def recoverOne {G : Type} {n : ℕ} (table : ValueTable G n) (p : G) :
    ArithmeticRun (Option (Fin n → ℕ)) := do
  match table p with
  | none => pure none
  | some (_, y) =>
      let v ← copyVector y
      pure (some v)

/-- Recover every witness, counting every coordinate copy; no new optimization
or real/group arithmetic is performed. -/
def recoverAll {G : Type} [DecidableEq G] {n : ℕ}
    (enumeration : List G) (table : ValueTable G n) :
    ArithmeticRun (G → Option (Fin n → ℕ)) :=
  enumeration.foldl (fun state p => do
    let t ← state
    let y ← recoverOne table p
    pure (Function.update t p y)) (pure (fun _ => none))

end GomoryGroup.Rel.Supplement


