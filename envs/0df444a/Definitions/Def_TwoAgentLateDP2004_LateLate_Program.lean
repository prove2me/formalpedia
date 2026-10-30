-- Prove2me | Definitions.Def_TwoAgentLateDP2004_LateLate_Program
-- name    : TwoAgentLateDP2004_LateLate_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:47:52.766632+00:00
-- url     : https://prove2.me/theorems/7bb630e0-06a4-470e-8658-814e846e17a4
-- title:
--   The fixed bottom-up tabulator, least-finite scan and actual execution
-- statement:
--   For an integer budget $Q$, the fixed program first rejects $Q<0$. Otherwise it counts A jobs, derives the B count, and sets $q=\min(Q,n_B)$. It initializes $(n+1)(n_A+1)(q+1)$ cells to infinity, sets every entry of row zero to zero, and writes each state of rows $1,\ldots,n$ once using previous-row random-access reads and the displayed guarded recurrence. Finally it scans $h=0,\ldots,n_A$ in increasing order and returns the first finite final-column entry, or infeasible if all entries are infinite.
--   $$\operatorname{run}(I,Q)=(\text{computed registers},\text{final memory},\text{charged steps}).$$
--   The registers include the derived owner counts, clipped budget and optional answer. All initialization writes, arithmetic, reads, comparisons, branches, loop tests and scan steps are interpreted by the preceding RAM semantics. No recursive table evaluator is called. This definition fixes the algorithm whose output and runtime Theorem 7.3 must justify.
--   **Formalization Note** EDD-numbered input is assumed by the goal, as in the source. Saturation and infeasibility handling extend the source's presupposed feasible case; their correctness is a conclusion of the goal. Unallocated RAM cells are infinity and every accessed table cell is initialized.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici (2004), Scheduling Problems with Two Competing Agents, Operations Research 52(2):229–242, https://doi.org/10.1287/opre.1030.0092, §7, Recursion Relation and Theorem 7.3 complexity paragraph, p.236 (PDF p.8)

import Mathlib
import Definitions.Def_TwoAgentLateDP2004_LateLate_RAM
import Definitions.Def_TwoAgentLateDP2004_LateLate_Recurrence

namespace TwoAgentLateDP2004.LateLate

/-- One state update, with actual previous-layer reads. No recursive C call.
`i` is the zero-based input job; this writes row i+1. -/
def fillCell (H K i h k : ℕ) : Code Unit := do
  let a ← addressCode H K i h k
  let prev ← Code.instr (Op.read a)
  let p ← Code.instr (Op.processing i)
  let d ← Code.instr (Op.due i)
  let v ← Code.instr (Op.add prev p)
  let fits ← Code.instr (Op.le v d)
  let _ ← Code.instr Op.control
  let early := if fits then v else ⊤
  let own ← Code.instr (Op.owner i)
  let _ ← Code.instr Op.control
  let omitted ← if own then do
      let z ← Code.instr (Op.zero h)
      let _ ← Code.instr Op.control
      if z then pure ⊤ else do
        let h' ← Code.instr (Op.nsub h 1)
        let b ← addressCode H K i h' k
        Code.instr (Op.read b)
    else do
      let z ← Code.instr (Op.zero k)
      let _ ← Code.instr Op.control
      if z then pure ⊤ else do
        let k' ← Code.instr (Op.nsub k 1)
        let b ← addressCode H K i h k'
        Code.instr (Op.read b)
  let value ← Code.instr (Op.minimum early omitted)
  let row ← Code.instr (Op.nadd i 1)
  let dst ← addressCode H K row h k
  Code.instr (Op.write dst value)

/-- Increasing scan, stopping at the first finite final-column entry.
The remaining-length recursion bounds the actual execution. -/
def scan (H K n q start : ℕ) : ℕ → Code (Option ℕ)
  | 0 => do
    let _ ← Code.instr Op.control
    pure none
  | len + 1 => do
    let _ ← Code.instr Op.control
    let a ← addressCode H K n start q
    let v ← Code.instr (Op.read a)
    let finite ← Code.instr (Op.finite v)
    let _ ← Code.instr Op.control
    if finite then pure (some start) else do
      let next ← Code.instr (Op.nadd start 1)
      scan H K n q next len

/-- Algorithm result registers, all computed from the inputs. Negative Q returns
none before counting or allocating; its unused dimension registers are zero. -/
structure Registers where
  a : ℕ
  b : ℕ
  q : ℕ
  answer : Option ℕ

/-- The fixed bottom-up program: count owners; saturate Q; initialize every
allocated cell to +∞; set row zero; fill rows 1..n once; scan h increasingly.
The memory has (n+1)(nA+1)(q+1) initialized cells, and access is random access. -/
def program (n : ℕ) (Q : ℤ) : Code Registers := do
  let neg ← Code.instr (Op.negative Q)
  let _ ← Code.instr Op.control
  if neg then pure ⟨0, 0, 0, none⟩ else do
    let a ← countA 0 n 0
    let b ← Code.instr (Op.nsub n a)
    let budget ← Code.instr (Op.toNat Q)
    let q ← Code.instr (Op.nmin budget b)
    let H ← Code.instr (Op.nadd a 1)
    let K ← Code.instr (Op.nadd q 1)
    let rows ← Code.instr (Op.nadd n 1)
    let layer ← Code.instr (Op.nmul H K)
    let cells ← Code.instr (Op.nmul rows layer)
    loop 0 cells (fun addr => Code.instr (Op.write addr ⊤))
    loop 0 layer (fun addr => Code.instr (Op.write addr 0))
    loop 0 n (fun i => loop 0 H (fun h => loop 0 K (fun k => fillCell H K i h k)))
    let answer ← scan H K n q 0 H
    pure ⟨a, b, q, answer⟩

/-- A fully interpreted finite execution. No supplied clock/correctness field.
Unallocated addresses are +∞; every accessed table address is initialized. -/
noncomputable def run {n : ℕ} (I : Input n) (Q : ℤ) : Registers × Memory × ℕ :=
  execute I (program n Q) (fun _ => ⊤)

end TwoAgentLateDP2004.LateLate


