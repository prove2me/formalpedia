-- Prove2me | Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Machine
-- name    : WeightedSetCoverWorstCase_Dynamic_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:28:48.388877+00:00
-- url     : https://prove2.me/theorems/e7036f1b-c994-465b-8286-d16ecb934089
-- title:
--   Deterministic online programs on the exact real RAM; set-cover and disjoint-set call protocols
-- statement:
--   The paper names no machine; §13 uses exact arithmetic and comparisons on the given real costs, pointers and lists, charging every operation. The model is the published real RAM `ClusterDecomp` (exact real registers and memory, integer pointers and memory, one unit of work per executed instruction, no floor, logarithm or sort primitive), with programs that never execute `coin` (`NoCoin`). `AdmissibleWith ps P`: every real literal is rational or in `ps`.
--
--   **Set-cover protocol.** Preprocessing starts at instruction 0 on memory holding $u,m$, every set (size and sorted elements), $U_0$ (integer cells) and the costs exactly (real cells), and runs to `halt`. Each update is then written into integer cells $-1,-2$ ($1,x$ for an insertion, $2,x$ for a deletion), and the program resumes at instruction 1 with all memory kept, until `halt`; the work of the call is its number of executed instructions (`HaltsWithin`). Only the current update is written, so the program cannot see future updates. The maintained solution is $\{j: \text{integer cell } -(10+j)\ne0\}$ (`outFamily`); `familyRecourse` $=|F\setminus G|+|G\setminus F|$.
--
--   **Disjoint-set protocol.** Operations `make x`, `del x`, `union h₁ h₂` (set handles), `find x`, written into cells $-1..-3$; the answer is cell $-10$. `DSAbs` tracks the live handles and their sets from the machine's answers; `Legal` and `Correct` specify a fresh handle for `make`/`union`, and for `find x` the handle of the set containing $x$; `size` is the number of stored elements.
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Theorem 1.1, p. 1 (PDF 4); §6.1, p. 21 (PDF 24); §13, pp. 60–69 (PDF 63–72)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_ClusterDecomp_Machine
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem

namespace WeightedSetCoverWorstCase.Dynamic

/-!
# Deterministic online programs on the exact-arithmetic real RAM

Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Theorem 1.1 (p. 1, PDF 4), §6.1 (p. 21,
PDF 24) and §13 (pp. 60–69, PDF 63–72). The paper names no machine; §13 implements the algorithm
with exact arithmetic and comparisons on the given real costs, pointers, doubly linked lists and a
disjoint-set structure, charging every operation. This module reads that as the published real RAM
`ClusterDecomp` (exact real registers and memory, integer pointers and integer memory, unit cost per
executed instruction, no floor, logarithm or sorting primitive), used **without** its coin
instruction (the algorithm is deterministic), plus an online call wrapper:

* **Preprocessing.** The program starts at instruction `0` on memory holding the instance and the
  initial live set (`scInit`) and runs until `halt`.
* **Update calls.** For each adversarial update, in order, the wrapper writes the update into the
  integer cells `-1, -2` (`1, x` for an insertion of `x`, `2, x` for a deletion), resumes the
  program at instruction `1` with all registers, pointers and memory kept, resets the work counter
  and runs until `halt`. The work of the call is the number of executed instructions. Only the
  current update is ever written: the program cannot read future updates.
* **Output.** After a call, input set `j` belongs to the maintained solution iff integer cell
  `-(10 + j)` is nonzero (the deduplicated set family; §6.1, §13.1.5).
-/

open ClusterDecomp

/-- The program never executes a coin instruction (it is deterministic). -/
def NoCoin (P : Program) : Prop := ∀ op ∈ P, ∀ d, op ≠ .coin d

/-- Every real literal of `P` is rational or one of the parameters `ps`, and `P` does not use the
core `accept`/`reject` (it stops only through `halt`). `AdmissibleWith []` is `ClusterDecomp`'s
`Admissible`. -/
def AdmissibleWith (ps : List ℝ) (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => (∃ q : ℚ, value = (q : ℝ)) ∨ value ∈ ps
    | .core .accept | .core .reject => False
    | _ => True

/-- The coin tape is never read by a program without coins; any fixed tape will do. -/
def noCoins : ℕ → Bool := fun _ => false

/-- Started in state `s`, program `P` halts within `T` steps. -/
def HaltsWithin (P : Program) (s : State) (T : ℕ) : Prop := (run P s noCoins T).halted = true

open Classical in
/-- The halted state reached from `s` (if `P` halts from `s`; otherwise `s` itself, a junk value
never used: every statement asserts halting). -/
noncomputable def result (P : Program) (s : State) : State :=
  if h : ∃ T, HaltsWithin P s T then run P s noCoins (Nat.find h) else s

/-- Write the list `ins` into the integer cells `-1, -2, …`. -/
def writeInputs (mem : ℤ → ℤ) (ins : List ℤ) : ℤ → ℤ := fun z =>
  if z < 0 ∧ (-z - 1).toNat < ins.length then ins.getD (-z - 1).toNat 0 else mem z

/-- Begin a call: inputs written, program counter at the update entry point `1`, not halted, work
counter `0`; registers, pointers and memory are kept. -/
def callState (s : State) (ins : List ℤ) : State :=
  { s with core := { s.core with pc := 1 }, integerMemory := writeInputs s.integerMemory ins,
           halted := false, work := 0 }

/-- The sorted list of the elements of `A`, as integers. -/
def encFinset {u : ℕ} (A : Finset (Fin u)) : List ℤ :=
  (A.sort (· ≤ ·)).map fun x => (x.val : ℤ)

/-- The integer part of the input: `u, m`, then for each set `j` its size and its sorted elements,
then the size of `U₀` and its sorted elements. -/
def encInts (inst : Instance) (U₀ : Finset (Fin inst.u)) : List ℤ :=
  [(inst.u : ℤ), (inst.m : ℤ)] ++
    (List.finRange inst.m).flatMap (fun j => ((inst.S j).card : ℤ) :: encFinset (inst.S j)) ++
    ((U₀.card : ℤ) :: encFinset U₀)

/-- The real part of the input: the costs `c(0), …, c(m-1)`, exactly. -/
def encReals (inst : Instance) : List ℝ := (List.finRange inst.m).map inst.c0

/-- The state at the start of preprocessing. -/
noncomputable def scInit (inst : Instance) (U₀ : Finset (Fin inst.u)) : State :=
  initState (encInts inst U₀) (encReals inst)

/-- The input cells of an update call. -/
def encUpd {u : ℕ} : Update u → List ℤ
  | .ins x => [1, (x.val : ℤ)]
  | .del x => [2, (x.val : ℤ)]

/-- The machine state after preprocessing and the update calls for `ups`, in order. -/
noncomputable def scAfter (P : Program) (inst : Instance) (U₀ : Finset (Fin inst.u))
    (ups : List (Update inst.u)) : State :=
  ups.foldl (fun s x => result P (callState s (encUpd x))) (result P (scInit inst U₀))

/-- The maintained solution in a state: the input sets `j` with integer cell `-(10+j)` nonzero. -/
def outFamily (inst : Instance) (s : State) : Finset (Fin inst.m) :=
  Finset.univ.filter fun j => s.integerMemory (-(10 + (j.val : ℤ))) ≠ 0

/-- Recourse between two set families: `|F ⊕ G| = |F ∖ G| + |G ∖ F|` (§6.1). -/
def familyRecourse {m : ℕ} (F G : Finset (Fin m)) : ℕ := (F \ G).card + (G \ F).card

/-! ## A disjoint-set data structure on the same machine (Theorem 13.2) -/

/-- Operations: create the singleton `{x}`, delete `x`, merge the sets with handles `h₁, h₂`, find
(the handle of) the set containing `x`. -/
inductive DSOp
  | make (x : ℤ)
  | del (x : ℤ)
  | union (h₁ h₂ : ℤ)
  | find (x : ℤ)

/-- The input cells of an operation call. -/
def DSOp.enc : DSOp → List ℤ
  | .make x => [1, x]
  | .del x => [2, x]
  | .union a b => [3, a, b]
  | .find x => [4, x]

/-- The answer of an operation call (a set handle) is integer cell `-10`. -/
def dsOutput (s : State) : ℤ := s.integerMemory (-10)

/-- The abstract content of the structure: the live set handles and the set of each handle. -/
structure DSAbs where
  H : Finset ℤ
  S : ℤ → Finset ℤ

namespace DSAbs

/-- No sets. -/
def empty : DSAbs := ⟨∅, fun _ => ∅⟩

/-- `n`: the number of elements currently stored. -/
def size (A : DSAbs) : ℕ := ∑ h ∈ A.H, (A.S h).card

/-- `x` is currently stored. -/
def Present (A : DSAbs) (x : ℤ) : Prop := ∃ h ∈ A.H, x ∈ A.S h

/-- The operation is a legal use of the structure: `make x` for an `x` not stored, `del`/`find`
of a stored element, `union` of two different live handles. -/
def Legal (A : DSAbs) : DSOp → Prop
  | .make x => ¬ A.Present x
  | .del x => A.Present x
  | .union a b => a ∈ A.H ∧ b ∈ A.H ∧ a ≠ b
  | .find x => A.Present x

/-- The answer `o` is correct: a fresh handle for `make` and `union` (the merged set may reuse
`h₁` or `h₂`), the handle of the set containing `x` for `find`. -/
def Correct (A : DSAbs) : DSOp → ℤ → Prop
  | .make _, o => o ∉ A.H
  | .del _, _ => True
  | .union a b, o => o ∉ (A.H.erase a).erase b
  | .find x, o => o ∈ A.H ∧ x ∈ A.S o

/-- The abstract content after the operation with answer `o`. -/
def next (A : DSAbs) : DSOp → ℤ → DSAbs
  | .make x, o => ⟨insert o A.H, Function.update A.S o {x}⟩
  | .del x, _ => ⟨A.H, fun h => (A.S h).erase x⟩
  | .union a b, o => ⟨insert o ((A.H.erase a).erase b), Function.update A.S o (A.S a ∪ A.S b)⟩
  | .find _, _ => A

end DSAbs

/-- The machine state and the abstract content after initialisation (from empty memory) and the
calls for `ops`, in order; the abstract content follows the machine's answers. -/
noncomputable def dsAfter (P : Program) (ops : List DSOp) : State × DSAbs :=
  ops.foldl (fun sa op =>
      let s' := result P (callState sa.1 op.enc)
      (s', sa.2.next op (dsOutput s')))
    (result P (initState [] []), DSAbs.empty)

/-- Every operation of `ops` was legal when it was issued. -/
def DSHistLegal (P : Program) (ops : List DSOp) : Prop :=
  ∀ i (h : i < ops.length), (dsAfter P (ops.take i)).2.Legal (ops.get ⟨i, h⟩)

end WeightedSetCoverWorstCase.Dynamic


