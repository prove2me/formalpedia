-- Prove2me | Definitions.Def_DetANN_DataStructure
-- name    : DetANN_DataStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:50.481237+00:00
-- url     : https://prove2.me/theorems/6dcd8cfd-5cfe-4412-8e47-284353412362
-- title:
--   Deterministic programs and the semantics of a deterministic ANN data structure on the real RAM
-- statement:
--   Theorem 1.1 and Lemma 3.3 assert that there is a *(fully) deterministic data structure*; the paper names no machine. This definition fixes the reading on the published real RAM `PNormReg.Machine`: exact $+,-,\times,\div$ and $\sqrt{\cdot}$ on reals, rational literals, integer pointers and integer memory, a pointer-to-real cast, comparison jumps and halt, at unit cost per executed instruction, with no floor and no real-to-integer cast.
--
--   1. A **deterministic program** is an admissible program (rational literals, no core accept/reject) that contains neither the fair-coin instruction nor the real power. Its runs never read the coin tape and are taken on the all-false tape.
--   2. **Input layout.** For points $Y_0,\dots,Y_{N-1}\in\mathbb R^m$ and a real parameter $\theta$, preprocessing starts with integer cells $0,1$ holding $N,m$, real cell $0$ holding $\theta$, and real cell $1+im+j$ holding the $j$th coordinate of $Y_i$.
--   3. **Data structure and queries.** The data structure is the memory of the halted preprocessing state. A query $q\in\mathbb R^m$ runs the query program from that memory with $q_j$ written into real cell $-1-j$; program counter, registers, pointers and work are reset.
--   4. **Answer.** The answer is pointer register $0$ of the halted query state, read as an index $k<N$.
--   5. **Space** is the number of distinct memory cells (real or integer) that preprocessing stores to.
--
--   `IsDetANNStructure Pre Qry Y θ c T_pre S T_q` holds when preprocessing halts within work $T_{pre}$ after storing to at most $S$ cells, and **every** query $q\in\mathbb R^m$ halts within work $T_q$ with an answer $k<N$ satisfying $\|q-Y_k\|_2\le c\,\|q-Y_j\|_2$ for all $j$.
--
--   This is the cost model in which the paper's resource bounds are stated.
--
--   **Formalization Note** Forbidding the coin makes every run deterministic; forbidding `rpow` only shrinks the instruction set, so existence statements become stronger. Floor is absent from the machine, as in every machine of this series.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Theorem 1.1, p.2; Lemma 3.3, p.7; resource discussion pp.16, 19 (reading: the paper names no machine)

import Mathlib
import Definitions.Def_PNormReg_Machine

namespace DetANN

/-!
# Deterministic programs and the semantics of a nearest-neighbor data structure

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), Theorem 1.1, p.2, and Lemma 3.3, p.7. Both say "there is a
(fully) deterministic data structure" and name no machine; this module fixes the reading.

**Formalization Note.**
* The machine is the published `PNormReg.Machine` (exact `+ − × ÷` and `√` on reals, rational
  literals, integer pointers and integer memory, a pointer-to-real cast, comparison jumps, `halt`; no
  floor, no real-to-integer cast, no pointer multiplication). `DetProgram` further forbids the fair
  coin (the structure is fully deterministic) and the real power `rpow`. With no coin, the coin tape
  is never read, and every run uses the all-false tape `detTape`.
* Input layout of preprocessing for points `Y : Fin N → ℝ^m` and a real parameter `θ` (the paper's
  `ε` or `δ`): integer cells `0, 1` hold `N, m`; real cell `0` holds `θ`; real cell `1 + i·m + j`
  holds the `j`th coordinate of `Y i`; every other cell is `0`.
* The data structure is the real and integer memory of the halted preprocessing state. A query
  `q ∈ ℝ^m` runs the query program from that memory with `q j` written into real cell `−1 − j`
  (`j < m`); program counter, registers, pointers, coin cursor, halted flag and work are reset.
* The answer is pointer register `0` of the halted query state, read as an index `k < N`.
* Space is the number of distinct memory cells (real or integer) that preprocessing stores to.
* Time is `work`: one unit per executed instruction, counted from the start of each run.
-/

/-- A fully deterministic program: admissible (rational literals, no core accept/reject), and
containing neither the fair-coin instruction nor the real power. -/
def DetProgram (P : PNormReg.Program) : Prop :=
  PNormReg.Admissible P ∧ ∀ op ∈ P, (∀ r, op ≠ PNormReg.Instr.coin r) ∧
    (∀ r a e, op ≠ PNormReg.Instr.rpow r a e)

/-- The all-false coin tape. A `DetProgram` never reads the tape. -/
def detTape : ℕ → Bool := fun _ => false

/-- The memory cell that the next step of `P` from `s` stores to, if any: `(true, z)` for real cell
`z`, `(false, z)` for integer cell `z`. Halted states store nothing. -/
def writtenCell (P : PNormReg.Program) (s : PNormReg.State) : Option (Bool × ℤ) :=
  if s.halted then none else
    match P[s.core.pc]? with
    | some (.core (.store q _)) => some (true, s.core.ptrs q)
    | some (.integerStore a _) => some (false, s.core.ptrs a)
    | _ => none

/-- The set of distinct memory cells stored to during the first `t` steps of `P` from `s₀`. -/
noncomputable def cellsWritten (P : PNormReg.Program) (s₀ : PNormReg.State) (t : ℕ) :
    Finset (Bool × ℤ) :=
  (Finset.range t).biUnion fun i => (writtenCell P (PNormReg.run P s₀ detTape i)).toFinset

/-- The input layout of preprocessing: integer memory `[N, m]`, real memory `θ` followed by the
points in row-major order. -/
noncomputable def inputState {N m : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ : ℝ) :
    PNormReg.State :=
  PNormReg.initState [(N : ℤ), (m : ℤ)]
    (θ :: (List.ofFn fun i : Fin N => List.ofFn fun j : Fin m => Y i j).flatten)

/-- The start state of a query `q ∈ ℝ^m` on the data structure stored in the state `s`: real cell
`−1 − j` holds `q j` for `j < m`, every other real cell and the whole integer memory are those of
`s`; program counter, registers, pointers, cursor, halted flag and work are reset. -/
noncomputable def queryState (m : ℕ) (s : PNormReg.State) (q : EuclideanSpace ℝ (Fin m)) :
    PNormReg.State :=
  ⟨⟨0, fun _ => 0, fun _ => 0,
      fun z => if h : z < 0 ∧ (-1 - z).toNat < m then q ⟨(-1 - z).toNat, h.2⟩ else s.core.mem z⟩,
    s.integerMemory, 0, false, 0⟩

/-- `Pre` and `Qry` form a deterministic data structure for `c`-approximate nearest-neighbor search
on the points `Y` (with input parameter `θ`), with preprocessing time `Tpre`, space `Space` and query
time `Tq`:
1. preprocessing from the input layout halts after some `t` steps, with work at most `Tpre`, having
   stored to at most `Space` distinct cells;
2. for **every** query `q ∈ ℝ^m`, the query program, started from the query layout on the halted
   preprocessing memory, halts with work at most `Tq`, and its pointer register `0` equals an index
   `k < N` with `‖q − Y k‖ ≤ c · ‖q − Y j‖` for every `j`. -/
def IsDetANNStructure (Pre Qry : PNormReg.Program) {N m : ℕ}
    (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ c Tpre Space Tq : ℝ) : Prop :=
  ∃ t : ℕ,
    (PNormReg.run Pre (inputState Y θ) detTape t).halted = true ∧
    ((PNormReg.run Pre (inputState Y θ) detTape t).work : ℝ) ≤ Tpre ∧
    ((cellsWritten Pre (inputState Y θ) t).card : ℝ) ≤ Space ∧
    ∀ q : EuclideanSpace ℝ (Fin m), ∃ t' : ℕ,
      (PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y θ) detTape t) q)
        detTape t').halted = true ∧
      ((PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y θ) detTape t) q)
        detTape t').work : ℝ) ≤ Tq ∧
      ∃ k : Fin N,
        (PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y θ) detTape t) q)
          detTape t').core.ptrs 0 = (k : ℤ) ∧
        ∀ j : Fin N, ‖q - Y k‖ ≤ c * ‖q - Y j‖

end DetANN


