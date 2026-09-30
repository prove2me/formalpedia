-- Prove2me | Definitions.Def_FriedbergMuchnik_Priority
-- name    : FriedbergMuchnik_Priority
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-09T20:03:53.979257+00:00
-- url     : https://prove2.me/theorems/f2694398-e1bb-42a9-bf73-d3a5cf78714e
-- title:
--   Oracle programs and the explicit Friedberg–Muchnik priority construction
-- statement:
--   The bundle defines a countably numbered oracle-program language and a fixed two-set priority construction. Program instructions are oracle query, successor, the two pairing projections, pairing, composition, primitive recursion, and minimization from zero. Its partial-function interpretation is parameterized by the oracle. The syntax is numbered through an explicit bijection with Mathlib's program-tree type; its oracle semantics is defined separately.
--
--   Finite simulation uses a natural-number fuel bound. Every oracle query is below that bound. Bounded minimization tests inputs in sequence and stops if an earlier test is undefined. A finite stage is represented by two enumeration lists and a list of active followers with Boolean acted flags.
--
--   At stage $s+1$, the procedure considers active requirements $q<s$, with program number $\lfloor q/2\rfloor$ and oracle side $q\bmod2$. It selects the least waiting requirement whose bounded simulation returns zero, enumerates its follower into the opposite set, marks it as having acted, and gives fresh followers to lower priority requirements. A new follower for requirement $s$ is then appended. The initial lists are empty.
--
--   For each side $i\in\{0,1\}$, the limit set is
--
--   $$A_i=\{n:\exists s,\ n\in L_{i,s}\}.$$
--
--   The bundle supplies definitions and the structural encoding equivalence. Computability of the stages and success of the diagonal requirements are separate theorem obligations.
-- source:
--   Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=51, pp. 52–53, Construction. Representation-specific syntax and bounded simulation follow the recursive-function presentation of https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/RecursiveIn.lean and reuse the syntax encoding in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/PartrecCode.lean.

import Definitions.Def_friedberg_muchnik_sets
import Mathlib.Computability.PartrecCode

namespace FriedbergMuchnik

/-- Oracle program trees. The constant-zero function is expressible as `mu right`. -/
inductive Program where
  | query | succ | left | right
  | pair (f g : Program)
  | comp (f g : Program)
  | prec (f g : Program)
  | mu (f : Program)

/-- Transport the syntax to Mathlib's effectively numbered finite trees. This is
an encoding of syntax, not an identification with Mathlib's ordinary evaluator. -/
def Program.toCode : Program → Nat.Partrec.Code
  | .query => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair f g => .pair f.toCode g.toCode
  | .comp f g => .comp f.toCode g.toCode
  | .prec f g => .prec f.toCode g.toCode
  | .mu f => .rfind' f.toCode

/-- Decode Mathlib's finite program-tree syntax into the oracle language. -/
def Program.ofCode : Nat.Partrec.Code → Program
  | .zero => .query
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair f g => .pair (ofCode f) (ofCode g)
  | .comp f g => .comp (ofCode f) (ofCode g)
  | .prec f g => .prec (ofCode f) (ofCode g)
  | .rfind' f => .mu (ofCode f)

/-- The syntax encoding and decoding are inverse. -/
def Program.codeEquiv : Program ≃ Nat.Partrec.Code where
  toFun := Program.toCode
  invFun := Program.ofCode
  left_inv c := by induction c <;> simp_all [Program.toCode, Program.ofCode]
  right_inv c := by induction c <;> simp_all [Program.toCode, Program.ofCode]

instance : Denumerable Program := Denumerable.ofEquiv Nat.Partrec.Code Program.codeEquiv

/-- Partial-function semantics of the oracle program language. -/
def oracleEval (O : ℕ →. ℕ) : Program → ℕ →. ℕ
  | .query => O
  | .succ => Nat.succ
  | .left => fun n => Part.some n.unpair.1
  | .right => fun n => Part.some n.unpair.2
  | .pair f g => fun n => Nat.pair <$> oracleEval O f n <*> oracleEval O g n
  | .comp f g => fun n => oracleEval O g n >>= oracleEval O f
  | .prec f g => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (oracleEval O f a) fun y ih => do
        let z ← ih
        oracleEval O g (Nat.pair a (Nat.pair y z))
  | .mu f => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> oracleEval O f (Nat.pair a n)

/-- Bounded sequential minimization. An undefined earlier value stops the search. -/
def boundedMu (f : ℕ → Option ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | k + 1, n => do
      let v ← f n
      if v = 0 then some n else boundedMu f k (n + 1)

/-- Finite simulation with a total oracle. Every evaluated input, and therefore
every oracle query, is strictly below the fuel supplied to that call. -/
def oracleEvaln (O : ℕ → ℕ) : ℕ → Program → ℕ → Option ℕ
  | 0, _, _ => none
  | k + 1, c, n =>
      if n < k + 1 then
        match c with
        | .query => some (O n)
        | .succ => some (n + 1)
        | .left => some n.unpair.1
        | .right => some n.unpair.2
        | .pair f g => do
            let a ← oracleEvaln O k f n
            let b ← oracleEvaln O k g n
            pure (Nat.pair a b)
        | .comp f g => do
            let a ← oracleEvaln O k g n
            oracleEvaln O k f a
        | .prec f g =>
            let (a, m) := Nat.unpair n
            m.rec (oracleEvaln O k f a) fun y ih => do
              let z ← ih
              oracleEvaln O k g (Nat.pair a (Nat.pair y z))
        | .mu f => boundedMu (fun m => oracleEvaln O k f (Nat.pair n m)) (k + 1) 0
      else none

/-- Two finite enumeration lists, followed by the active followers and acted flags. -/
abbrev PriorityState := (List ℕ × List ℕ) × List (ℕ × Bool)

/-- `false` selects the first set and `true` selects the second. -/
def stateList (t : PriorityState) (i : Bool) : List ℕ :=
  if i then t.1.2 else t.1.1

/-- The total membership oracle for a finite stage approximation. -/
def stateOracle (t : PriorityState) (i : Bool) (n : ℕ) : ℕ :=
  if n ∈ stateList t i then 1 else 0

/-- Requirement `q = 2e + i` uses the oracle on side `i`. -/
def side (q : ℕ) : Bool := q % 2 == 1

/-- A waiting active requirement whose finite simulation has returned zero. -/
def wantsAttention (s : ℕ) (t : PriorityState) (q : ℕ) : Bool :=
  let entry := t.2[q]?.getD (0, false)
  !entry.2 && oracleEvaln (stateOracle t (side q)) s
    (Denumerable.ofNat Program (q / 2)) entry.1 == some 0

/-- Miller's stage step: act for the least eligible requirement, reset all lower
priority followers, and finally appoint the newly active requirement's follower. -/
def priorityStep (s : ℕ) (t : PriorityState) : PriorityState :=
  let fresh := (Nat.pair s (s + 1), false)
  match (List.range s).find? (wantsAttention s t) with
  | none => (t.1, t.2 ++ [fresh])
  | some q =>
      let x := (t.2[q]?.getD (0, false)).1
      let sets := if side q then (x :: t.1.1, t.1.2) else (t.1.1, x :: t.1.2)
      let entries := t.2.mapIdx fun k entry =>
        if q < k then (Nat.pair k (s + 1), false)
        else if k = q then (entry.1, true)
        else entry
      (sets, entries ++ [fresh])

/-- The explicitly defined finite stages, beginning with two empty sets. -/
def priorityStage : ℕ → PriorityState
  | 0 => (([], []), [])
  | s + 1 => priorityStep s (priorityStage s)

/-- The elements enumerated on side `i` by stage `s`. -/
def stageList (i : Bool) (s : ℕ) : List ℕ := stateList (priorityStage s) i

/-- The union over all finite stages on side `i`. -/
def limitSet (i : Bool) : Set ℕ := {n | ∃ s, n ∈ stageList i s}

end FriedbergMuchnik


