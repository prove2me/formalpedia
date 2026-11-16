-- Prove2me | Definitions.Def_DetANN_Supplement_BlockConstruction
-- name    : DetANN_Supplement_BlockConstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:17:30.229172+00:00
-- url     : https://prove2.me/theorems/b407f78a-e7bc-4c31-b497-ca85393a724f
-- title:
--   Deterministic construction and evaluation of a $\tau$-balanced block system on the real RAM
-- statement:
--   Theorem 3.2 asserts that a $\tau$-balanced block system "can be deterministically constructed" within a number of arithmetic operations, and that afterwards all $d$ maps "can be evaluated on a vector" within a time bound. The paper fixes no representation of the constructed maps. This definition fixes the reading on the published deterministic real RAM of the base mission (`DetANN.DataStructure`).
--
--   Let $P=(P_0,\dots,P_{n-1})$ be points of $\mathbb R^d$, $\tau\in\mathbb R$, $T_{\mathrm{pre}},b_{\max}\in\mathbb R$, and let $T_{\mathrm{eval}}:\mathbb N\to\mathbb R$. A pair of programs $(\mathrm{Pre},\mathrm{Ev})$ is a **block construction** for $P$ with these bounds when:
--
--   1. $\mathrm{Pre}$, started from the input layout (integer cells $0,1$ hold $n,d$; real cell $0$ holds $\tau$; then the coordinates of the points, row by row), halts with work at most $T_{\mathrm{pre}}$;
--   2. integer cell $0$ of the halted memory then holds a natural number $b\le b_{\max}$;
--   3. there are linear maps $A_1,\dots,A_d:\mathbb R^d\to\mathbb R^b$ forming a $\tau$-balanced block system (Definition 3.1) for the set $\{P_0,\dots,P_{n-1}\}$, such that
--   4. for **every** $z\in\mathbb R^d$, the program $\mathrm{Ev}$, started on the halted memory of $\mathrm{Pre}$ with $z_j$ written into real cell $-1-j$ (program counter, registers, pointers and work reset), halts with work at most $T_{\mathrm{eval}}(b)$, and its real cell $j\cdot b+k$ then holds the $k$th coordinate of $A_jz$, for every block $j$ and every $k<b$.
--
--   The constructed system is thus the one the evaluation program computes; this is what "construct" and "evaluate" mean in the resource clauses of Theorem 3.2.
--
--   **Formalization Note** Time is the machine's work counter, one unit per executed instruction; each instruction performs at most one arithmetic operation, so a bound on steps bounds arithmetic operations. The evaluation bound is a function of $b$ because the paper's bound $O(bd\log n)$ involves $b$.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Theorem 3.2, p.7; Definition 3.1, p.7; §6.1, p.14 (reading: the paper fixes no representation of the constructed maps)

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_BalancedBlocks

namespace DetANN

namespace Supplement

/-!
# Deterministic construction and evaluation of a balanced block system on the real RAM

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), Theorem 3.2, p.7 (with Definition 3.1, p.7, and §6.1,
p.14). Theorem 3.2 says that one can "deterministically construct" a balanced block system, with a
bound on arithmetic operations, and that "after preprocessing, all d maps can be evaluated on a
vector" within a time bound. The paper fixes no representation of the constructed maps; this module
fixes the reading.

**Formalization Note.**
* Machine, program class, input layout and second-program start state are the published ones of
  `DetANN.DataStructure`: `PNormReg.run` on the all-false tape `detTape`; preprocessing starts from
  `inputState P τ` (integer cells `0, 1` hold `n, d`; real cell `0` holds `τ`; real cell `1 + i·d + j`
  holds coordinate `j` of `P i`); the evaluation program starts from `queryState d s z` on the halted
  preprocessing state `s` (real cell `−1 − j` holds `z j`; the rest of the memory is that of `s`;
  program counter, registers, pointers and work are reset).
* The constructed system is the one the evaluation program computes: after preprocessing, integer
  cell `0` holds the block dimension `b`, and for every `z ∈ ℝ^d` the halted evaluation state holds
  `(A j z) k` in real cell `j·b + k` for every `j < d`, `k < b`. The maps `A j` are linear, and they
  are required to form a `τ`-balanced block system for the point set `{P 0, …, P (n−1)}`.
* Time is `work`, one unit per executed instruction; every instruction performs at most one
  arithmetic operation, so a bound on steps bounds the arithmetic operations.
* The evaluation-time bound may depend on `b`; it is passed as a function `Teval : ℕ → ℝ` of `b`.
-/

/-- `Pre` deterministically constructs a `τ`-balanced block system for the points `P` within time
`Tpre`, with block dimension at most `bmax`, and `Ev` evaluates all `d` maps on any vector within time
`Teval b`:
1. `Pre`, run from the input layout `inputState P τ`, halts after some `t` steps with work at most
   `Tpre`;
2. its integer cell `0` then holds a natural number `b ≤ bmax`;
3. there are linear maps `A₁, …, A_d : ℝ^d → ℝ^b` forming a `τ`-balanced block system for the set of
   points of `P`, such that
4. for every `z ∈ ℝ^d`, `Ev`, started from `queryState d s z` on the halted preprocessing state `s`,
   halts with work at most `Teval b`, and its real cell `j·b + k` holds the `k`th coordinate of
   `A j z` for every `j < d`, `k < b`. -/
def IsBlockConstruction (Pre Ev : PNormReg.Program) {n d : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (τ Tpre bmax : ℝ) (Teval : ℕ → ℝ) : Prop :=
  ∃ t : ℕ,
    (PNormReg.run Pre (inputState P τ) detTape t).halted = true ∧
    ((PNormReg.run Pre (inputState P τ) detTape t).work : ℝ) ≤ Tpre ∧
    ∃ b : ℕ, (b : ℝ) ≤ bmax ∧
      (PNormReg.run Pre (inputState P τ) detTape t).integerMemory 0 = (b : ℤ) ∧
      ∃ A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b),
        IsBalancedBlockSystem τ (Finset.univ.image P) A ∧
        ∀ z : EuclideanSpace ℝ (Fin d), ∃ t' : ℕ,
          (PNormReg.run Ev (queryState d (PNormReg.run Pre (inputState P τ) detTape t) z)
            detTape t').halted = true ∧
          ((PNormReg.run Ev (queryState d (PNormReg.run Pre (inputState P τ) detTape t) z)
            detTape t').work : ℝ) ≤ Teval b ∧
          ∀ j : Fin d, ∀ k : Fin b,
            (PNormReg.run Ev (queryState d (PNormReg.run Pre (inputState P τ) detTape t) z)
              detTape t').core.mem ((j : ℤ) * (b : ℤ) + (k : ℤ)) = A j z k

end Supplement

end DetANN


