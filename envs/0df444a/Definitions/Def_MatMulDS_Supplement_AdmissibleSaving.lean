-- Prove2me | Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
-- name    : MatMulDS_Supplement_AdmissibleSaving
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:12:41.624495+00:00
-- url     : https://prove2.me/theorems/431b9334-0490-4877-b5ab-e19ac9ee2873
-- title:
--   Definition 8.1 — admissible saving $\beta$
-- statement:
--   A real $\beta>0$ is an **admissible saving** if the following hold.
--
--   1. *(Data structure.)* There is a deterministic algorithm that, given $A\in\mathbb F^{N\times D}$ and $B\in\mathbb F^{D\times N}$ with $D\le\lceil\sqrt N\rceil$ over every field $\mathbb F$ of characteristic zero, preprocesses them with $O(N^{2-\beta})$ field operations and then returns any entry of $AB$, chosen adaptively, with $O(N^{1/2-\beta})$ field operations.
--   2. *(Transposed product.)* There is a deterministic algorithm that, given $A\in\mathbb F^{D\times n}$ with $D\le\lceil\sqrt n\rceil$ in dense and $B\in\mathbb F^{n\times n}$ with $m$ nonzero entries in sparse representation, over every field of characteristic zero, computes $AB$ with $O(n^{2-\beta}+mn^{1/2-\beta})$ field operations.
--   3. *(Word RAM.)* The bounds of 1 and 2 also hold on the word RAM, with $\tilde O$ in place of $O$, for Boolean matrices and for integer matrices with entries bounded in absolute value by $N^{O(1)}$ in 1 and by $n^{O(1)}$ in 2.
--
--   This interface is the hypothesis of every application of Section 8 and Appendices C and E; Theorem 7.4 shows that $\beta=0.0002666$ is admissible.
--
--   **Formalization Note** One program with a fixed list of rational constants works over every field of characteristic zero; constants are fixed before $N,D,n,m$; field operations are counted by `fexec`; the word RAM is the mission's machine with word programs and every word size $w\ge K\lceil\log_2(N+1)\rceil+K$. $N^{O(1)}$ is "for every $c$, entries at most $N^c$", with the program chosen after $c$; $\tilde O$ is $C(\log N+1)^{c'}$. The Boolean case of 3 is the integer case with entries in $\{0,1\}$ followed by a positivity test, so it is not a separate clause. Sparse representation (footnote 10): the list of positions of the nonzero entries, each once, in any order.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Definition 8.1, pp.50–51 (PDF pp.52–53), footnote 10

import Mathlib
import Definitions.Def_MatMulDS_IsMatMulOracle
import Definitions.Def_MatMulDS_wordRun
import Definitions.Def_MatMulDS_Supplement_fexec

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- The entries of a matrix over any type, in row-major order (as `MatMulDS.matList`). -/
def entries {R : Type} {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) : List R :=
  (List.finRange a).flatMap fun i => (List.finRange b).map fun j => A i j

/-- **Sparse representation** (footnote 10, p.51): `es` lists the positions of the nonzero entries of `B`, each once,
in any order. -/
def IsSparseRep {R : Type} [Zero R] {a b : ℕ} (B : Matrix (Fin a) (Fin b) R) (es : List (Fin a × Fin b)) : Prop :=
  es.Nodup ∧ ∀ i j, (i, j) ∈ es ↔ B i j ≠ 0

/-- The positions `(i, j)` of a list, as words, 0-based. -/
def posWords {a b : ℕ} (es : List (Fin a × Fin b)) : List ℤ :=
  es.flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)]

variable {F : Type} [Field F] [DecidableEq F]

/-- A coin-free preprocessing + query program with the constants `c` that, for all `N, D ≥ 1` in the range `X`, all
`A ∈ F^{N×D}`, `B ∈ F^{D×N}` and every word size `w ≥ K⌈log₂(N+1)⌉ + K`, preprocesses with at most `TP N D` field
operations and then answers every query `(I, J)` (0-based, adaptive: from the stored structure and that query alone)
with at most `TQ N D` field operations, leaving `(AB)[I, J]` in field cell `0`. Layouts as in `MatMulDS.IsMatMulOracle`. -/
def FieldOpOracle (O : AOracle) (c : List F) (K : ℕ) (X : ℕ → ℕ → Prop) (TP TQ : ℕ → ℕ → ℝ) : Prop :=
  (∀ i ∈ O.prep, ¬ i.IsCoin) ∧ (∀ i ∈ O.query, ¬ i.IsCoin) ∧
  ∀ N D : ℕ, 1 ≤ N → 1 ≤ D → X N D →
    ∀ (A : Matrix (Fin N) (Fin D) F) (B : Matrix (Fin D) (Fin N) F) (w : ℕ),
      K * Nat.clog 2 (N + 1) + K ≤ w →
      (∃ st, FHalts O.prep (aloadWords w (inputWords N D), aloadFields (inputFields c A B)) ⌈TP N D⌉₊ st) ∧
      ∀ st, FHalts O.prep (aloadWords w (inputWords N D), aloadFields (inputFields c A B)) ⌈TP N D⌉₊ st →
        ∀ I J : Fin N,
          (∃ r, FHalts O.query (aQueryMemory st (queryWords I J) []) ⌈TQ N D⌉₊ r) ∧
          ∀ r, FHalts O.query (aQueryMemory st (queryWords I J) []) ⌈TQ N D⌉₊ r → r.2 0 = (A * B) I J

/-- A coin-free program with the constants `c` computing the **transposed product** of Definition 8.1(ii): for all
`n ≥ 1`, `1 ≤ D ≤ ⌈√n⌉`, a dense `A ∈ F^{D×n}` and `B ∈ F^{n×n}` in sparse representation `es` with `m = |es|`, and every
word size `w ≥ K⌈log₂(n+1)⌉ + K`, it halts with at most `⌈C (n^{2−β} + m n^{1/2−β})⌉` field operations, with `AB` in
row-major order in the field cells `0, …, Dn − 1`. Input: the words `n, D, m` and the positions of `es`; the field
elements `c`, then `A` in row-major order, then the entries of `B` at `es`, in the order of `es`. -/
def FieldOpTransposed (P : List AInstr) (c : List F) (K : ℕ) (C β : ℝ) : Prop :=
  (∀ i ∈ P, ¬ i.IsCoin) ∧
  ∀ n D : ℕ, 1 ≤ n → 1 ≤ D → D ≤ ⌈Real.sqrt n⌉₊ →
    ∀ (A : Matrix (Fin D) (Fin n) F) (B : Matrix (Fin n) (Fin n) F) (es : List (Fin n × Fin n)),
      IsSparseRep B es → ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
      let mem := (aloadWords w ([(n : ℤ), (D : ℤ), (es.length : ℤ)] ++ posWords es),
        aloadFields (c ++ matList A ++ es.map fun e => B e.1 e.2))
      let T := ⌈C * ((n : ℝ) ^ (2 - β) + (es.length : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2 - β))⌉₊
      (∃ st, FHalts P mem T st) ∧
      ∀ st, FHalts P mem T st → ∀ k : ℕ, k < D * n → st.2 k = (matList (A * B)).getD k 0

/-- A word-RAM data structure for **integer matrices** with entries of absolute value at most `N^c`: word programs
`O.prep`, `O.query`; for all `N ≥ 1`, `1 ≤ D ≤ ⌈√N⌉`, such `A ∈ ℤ^{N×D}`, `B ∈ ℤ^{D×N}` and every word size
`w ≥ K⌈log₂(N+1)⌉ + K`, the preprocessing halts within `⌈C (log N + 1)^{c'} N^{2−β}⌉` steps and each query `(I, J)`
within `⌈C (log N + 1)^{c'} N^{1/2−β}⌉` further steps with `(AB)[I, J]` in word cell `0`. Input words: `N, D`, then `A`
and `B` in row-major order. -/
def WordOracleOK (O : AOracle) (K c c' : ℕ) (C β : ℝ) : Prop :=
  IsWordProgram O.prep ∧ IsWordProgram O.query ∧
  ∀ N D : ℕ, 1 ≤ N → 1 ≤ D → D ≤ ⌈Real.sqrt N⌉₊ →
    ∀ (A : Matrix (Fin N) (Fin D) ℤ) (B : Matrix (Fin D) (Fin N) ℤ),
      (∀ i j, |A i j| ≤ (N : ℤ) ^ c) → (∀ i j, |B i j| ≤ (N : ℤ) ^ c) →
      ∀ w : ℕ, K * Nat.clog 2 (N + 1) + K ≤ w →
      ∃ st : (ℤ → BitVec w) × (ℤ → ℚ),
        aexec (F := ℚ) O.prep (fun _ => 0) ⌈C * (Real.log N + 1) ^ c' * (N : ℝ) ^ (2 - β)⌉₊ 0 0
          (aloadWords w ([(N : ℤ), (D : ℤ)] ++ entries A ++ entries B)) (aloadFields []) = some st ∧
        ∀ I J : Fin N, ∃ r : (ℤ → BitVec w) × (ℤ → ℚ),
          aexec O.query (fun _ => 0) ⌈C * (Real.log N + 1) ^ c' * (N : ℝ) ^ ((1 : ℝ) / 2 - β)⌉₊ 0 0
            (aQueryMemory st (queryWords I J) []).1 (aQueryMemory st (queryWords I J) []).2 = some r ∧
          (r.1 0).toInt = (A * B) I J

/-- A word-RAM program for the transposed product of **integer matrices** with entries of absolute value at most
`n^c`: for all `n ≥ 1`, `1 ≤ D ≤ ⌈√n⌉`, a dense `A ∈ ℤ^{D×n}`, `B ∈ ℤ^{n×n}` in sparse representation `es` and every word
size `w ≥ K⌈log₂(n+1)⌉ + K`, it halts within `⌈C (log n + 1)^{c'} (n^{2−β} + m n^{1/2−β})⌉` steps with `AB` in row-major
order in the word cells `0, …, Dn − 1`. Input words: `n, D, m`, then `A` in row-major order, then the triples
`(i, j, B[i, j])` of `es`, in the order of `es`. -/
def WordTransposedOK (P : List AInstr) (K c c' : ℕ) (C β : ℝ) : Prop :=
  IsWordProgram P ∧
  ∀ n D : ℕ, 1 ≤ n → 1 ≤ D → D ≤ ⌈Real.sqrt n⌉₊ →
    ∀ (A : Matrix (Fin D) (Fin n) ℤ) (B : Matrix (Fin n) (Fin n) ℤ) (es : List (Fin n × Fin n)),
      IsSparseRep B es → (∀ i j, |A i j| ≤ (n : ℤ) ^ c) → (∀ i j, |B i j| ≤ (n : ℤ) ^ c) →
      ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
      ∃ st : ℤ → BitVec w,
        wordRun P w ([(n : ℤ), (D : ℤ), (es.length : ℤ)] ++ entries A ++
            es.flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ), B e.1 e.2])
          ⌈C * (Real.log n + 1) ^ c' *
            ((n : ℝ) ^ (2 - β) + (es.length : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2 - β))⌉₊ = some st ∧
        ∀ k : ℕ, k < D * n → (st k).toInt = (entries (A * B)).getD k 0

/-- **Admissible saving** (Definition 8.1, pp.50–51, PDF pp.52–53; Alman, Nogler, Vassilevska Williams, STOC 2027
submission, held file sha256 6c5a1c16…). A real `β > 0` is an admissible saving if:
(i) (Data structure.) There is a deterministic algorithm that, given `A ∈ F^{N×D}` and `B ∈ F^{D×N}` with `D ≤ ⌈√N⌉` over
every field `F` of characteristic zero, preprocesses them with `O(N^{2−β})` field operations and then returns any entry of
`AB`, chosen adaptively, with `O(N^{1/2−β})` field operations.
(ii) (Transposed product.) There is a deterministic algorithm that, given `A ∈ F^{D×n}` with `D ≤ ⌈√n⌉` in dense and
`B ∈ F^{n×n}` with `m` nonzero entries in sparse representation over every field `F` of characteristic zero, computes `AB`
with `O(n^{2−β} + m n^{1/2−β})` field operations.
(iii) (Word RAM.) The bounds of (i) and (ii) also hold on the word RAM, with `Õ` in place of `O`, for Boolean matrices and
for integer matrices with entries bounded in absolute value by `N^{O(1)}` in (i) and by `n^{O(1)}` in (ii).

**Formalization Note.**
* "Over every field of characteristic zero": one program, with a fixed list of rational constants, works over every such
  field (`F : Type`); the constants `K`, `C` are fixed before `N`, `D`, `n`, `m`.
* Field operations are counted by `fexec`; the word RAM is the published machine with word programs, all steps counted,
  word size `w ≥ K⌈log₂(N+1)⌉ + K`.
* `N^{O(1)}` is: for every `c`, entries of absolute value at most `N^c`, with the program and constants chosen after `c`.
  `Õ` is `C (log N + 1)^{c'}` times the bound.
* The Boolean case of (iii) is not a separate clause: Boolean matrices are integer matrices with entries in `{0, 1}`, and
  the Boolean product is the test "the integer entry is positive", one more step. -/
def AdmissibleSaving (β : ℝ) : Prop :=
  0 < β ∧
  (∃ (O : AOracle) (cs : List ℚ) (K : ℕ) (C : ℝ), 0 < C ∧
    ∀ (F : Type) [Field F] [CharZero F] [DecidableEq F],
      FieldOpOracle O (cs.map (Rat.cast : ℚ → F)) K (fun N D => D ≤ ⌈Real.sqrt N⌉₊)
        (fun N _ => C * (N : ℝ) ^ (2 - β)) (fun N _ => C * (N : ℝ) ^ ((1 : ℝ) / 2 - β))) ∧
  (∃ (P : List AInstr) (cs : List ℚ) (K : ℕ) (C : ℝ), 0 < C ∧
    ∀ (F : Type) [Field F] [CharZero F] [DecidableEq F],
      FieldOpTransposed P (cs.map (Rat.cast : ℚ → F)) K C β) ∧
  (∀ c : ℕ, ∃ (O : AOracle) (K c' : ℕ) (C : ℝ), 0 < C ∧ WordOracleOK O K c c' C β) ∧
  (∀ c : ℕ, ∃ (P : List AInstr) (K c' : ℕ) (C : ℝ), 0 < C ∧ WordTransposedOK P K c c' C β)

end MatMulDS.Supplement


