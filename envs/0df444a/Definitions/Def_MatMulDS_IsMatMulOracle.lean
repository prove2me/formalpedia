-- Prove2me | Definitions.Def_MatMulDS_IsMatMulOracle
-- name    : MatMulDS_IsMatMulOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:05.063405+00:00
-- url     : https://prove2.me/theorems/e7490ca0-63f0-434c-b3ae-ba40f8e55b04
-- title:
--   Conforming oracle for the matrix product on the algebraic RAM
-- statement:
--   Let $O$ be a preprocessing and query program on the published algebraic RAM with no coin instruction, with a fixed list $c$ of constants of $\mathbb F$. It is a **conforming oracle** with range $X$ and time bounds $T_P,T_Q$ if for all $N,D\ge 1$ in $X$, all $A\in\mathbb F^{N\times D}$, $B\in\mathbb F^{D\times N}$ and every word size $w\ge K\lceil\log_2(N+1)\rceil+K$:
--
--   1. preprocessing on the words $N,D$ and the field cells $c,A,B$ halts within $\lceil T_P(N,D)\rceil$ steps and stores at most $T_P(N,D)$ cells;
--   2. every query $(I,J)\in[N]^2$ halts within $\lceil T_Q(N,D)\rceil$ further steps, with $(AB)[I,J]$ in field cell $0$.
--
--   A list of queries is **answered within a budget** if preprocessing and the runs of all queries in the list take at most that many steps in total.
--
--   **Formalization Note** The query's memory depends only on the stored structure and that query, so a bound for every list covers queries chosen adaptively. The list $c$ exists because the machine's only field literals are $0$ and $1$.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 1.1, pp.3–4 (PDF pp.5–6)

import Mathlib
import Definitions.Def_MatMulDS_LinCircuit
import Definitions.Def_MatroidSensOracle_AlgRAM

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS

variable {F : Type} [Field F] [DecidableEq F]

/-- The input word memory of the matrix product oracle: the dimensions `N`, `D`. -/
def inputWords (N D : ℕ) : List ℤ := [(N : ℤ), (D : ℤ)]

/-- The input field memory of the matrix product oracle: the fixed constants `c`, then `A` and then `B`,
each in row-major order. -/
def inputFields {N D : ℕ} (c : List F) (A : Matrix (Fin N) (Fin D) F) (B : Matrix (Fin D) (Fin N) F) :
    List F :=
  c ++ matList A ++ matList B

/-- The query words: the entry `(I, J)`, 0-based. -/
def queryWords {N : ℕ} (I J : Fin N) : List ℤ := [((I : ℕ) : ℤ), ((J : ℕ) : ℤ)]

/-- **A conforming oracle for the matrix product.** `O` is a coin-free preprocessing + query program on
the algebraic RAM with the fixed list of constants `c`. For all `N, D ≥ 1` in the range `X`, all
`A ∈ F^{N×D}`, `B ∈ F^{D×N}` and every word size `w ≥ K⌈log₂(N+1)⌉ + K`: preprocessing halts within
`⌈TP N D⌉` steps and stores at most `TP N D` cells, and every query `(I, J) ∈ [N]²` halts within
`⌈TQ N D⌉` further steps with `(AB)[I, J]` in field cell `0` of the final query memory.
Source: STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 1.1, pp.3–4; "All data structures below
are deterministic and allow adaptive queries", p.3.

**Formalization Note.**
* Machine: the published `MatroidSensOracle_AlgRAM`. Every instruction costs one step, so field operations
  and word operations are counted together, including the construction of whatever circuits are used.
* Deterministic: no instruction is `fcoin`. The coin sequences in `PrepWithin` and `QueryWithin` are then
  irrelevant.
* Adaptive: a query's memory depends only on the stored structure and that query, so answers to earlier
  queries cannot help or hurt a later one.
* Constants: the machine's only field literals are `0` and `1`, so a fixed list `c` of constants of `F` comes
  with the program. It precedes `N` and `D` in every statement, and so does `K`.
* Word size: the program works for every word size above the threshold, so a huge word cannot be
  exploited. -/
structure IsMatMulOracle (O : AOracle) (c : List F) (K : ℕ) (X : ℕ → ℕ → Prop)
    (TP TQ : ℕ → ℕ → ℝ) : Prop where
  no_coin_prep : ∀ i ∈ O.prep, ¬ i.IsCoin
  no_coin_query : ∀ i ∈ O.query, ¬ i.IsCoin
  runs : ∀ N D : ℕ, 1 ≤ N → 1 ≤ D → X N D →
    ∀ (A : Matrix (Fin N) (Fin D) F) (B : Matrix (Fin D) (Fin N) F) (w : ℕ),
      K * Nat.clog 2 (N + 1) + K ≤ w →
      O.PrepWithin w (inputWords N D) (inputFields c A B) ⌈TP N D⌉₊ (TP N D) ∧
      ∀ I J : Fin N,
        O.QueryWithin w (inputWords N D) (inputFields c A B) (queryWords I J) [] ⌈TP N D⌉₊ ⌈TQ N D⌉₊ ∧
        ∀ (ω₁ ω₂ : ℕ → F) (r : ((ℤ → BitVec w) × (ℤ → F)) × ((ℤ → BitVec w) × (ℤ → F))),
          O.run w (inputWords N D) (inputFields c A B) (queryWords I J) [] ⌈TP N D⌉₊ ⌈TQ N D⌉₊ ω₁ ω₂ =
            some r → r.2.2 0 = (A * B) I J

/-- **A list of entries answered within a total budget.** There are step counts `tp` for the preprocessing
and `t q` for each query `q` such that `tp` plus the sum of `t q` over the list `qs` is at most `bound`,
preprocessing halts within `tp` steps, and each query in the list halts within `t q` further steps with the
right entry in field cell `0`.

**Formalization Note** Queries chosen adaptively are covered: a query's memory depends only on the stored
structure and that query, so a bound for every list is a bound for every adaptive rule. -/
def AnswersListWithin (O : AOracle) (c : List F) {N D : ℕ} (w : ℕ) (A : Matrix (Fin N) (Fin D) F)
    (B : Matrix (Fin D) (Fin N) F) (qs : List (Fin N × Fin N)) (bound : ℝ) : Prop :=
  ∃ (tp : ℕ) (t : Fin N × Fin N → ℕ),
    ((tp + (qs.map t).sum : ℕ) : ℝ) ≤ bound ∧
    O.PrepWithin w (inputWords N D) (inputFields c A B) tp bound ∧
    ∀ q ∈ qs,
      O.QueryWithin w (inputWords N D) (inputFields c A B) (queryWords q.1 q.2) [] tp (t q) ∧
      ∀ (ω₁ ω₂ : ℕ → F) (r : ((ℤ → BitVec w) × (ℤ → F)) × ((ℤ → BitVec w) × (ℤ → F))),
        O.run w (inputWords N D) (inputFields c A B) (queryWords q.1 q.2) [] tp (t q) ω₁ ω₂ = some r →
          r.2.2 0 = (A * B) q.1 q.2

end MatMulDS


