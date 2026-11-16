-- Prove2me | Definitions.Def_PelagicFF_Supplement_queryRun
-- name    : PelagicFF_Supplement_queryRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:26:50.922578+00:00
-- url     : https://prove2.me/theorems/f9edd429-5da5-45ef-8a67-1b95ed26a2f4
-- title:
--   Deterministic adaptive query algorithms and the $\mathrm{APFF}_n$ verifier's input word
-- statement:
--   A **deterministic adaptive query algorithm** with oracle access to $f:\{0,1\}^n\to\{-1,1\}$ is given by a step map $\delta$ on binary words. Its configuration is a word $w$: the input word followed by the oracle answers received so far. One step computes $\delta(w)$:
--
--   1. if $\delta(w)$ starts with $0$ and continues with a word $q$, the algorithm queries $f$ at the point of $\{0,1\}^n$ whose bits are the first $n$ bits of $q$ (missing bits read as $0$) and appends the answer bit to $w$;
--   2. if $\delta(w)$ starts with $1,b$, the algorithm halts with decision $b$;
--   3. on any other output it halts with decision $0$.
--
--   `queryRun δ n f F w` runs at most $F$ steps, hence makes at most $F-1$ queries, and returns the decision, or nothing if the algorithm has not halted.
--
--   The **input word** of the $\mathrm{APFF}_n$ verifier on a basis $b_1,\dots,b_\ell$ of $V$ and a candidate $(a,y)$ is $1^n0$ (the number $n$ in unary), followed by the $n$ bits of $a$, the $\ell$ bits of $y$, and the $n$ bits of each $b_i$ in order.
--
--   This is the computation model of the verification clause of Theorem 5.2: a deterministic algorithm given a basis of $V$, the candidate answer and query access to $f$.
--
--   **Formalization Note** The algorithm is deterministic and adaptive: every step is a function of the input and the answers so far. Running time is bounded separately by requiring $\delta$ to be computable in polynomial time by a Turing machine (Mathlib's `Turing.TM2ComputableInPolyTime`).
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem 5.2, p.32 (verification clause)

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Definitions.Def_PelagicFF_Supplement_APFF

namespace PelagicFF.Supplement

/-- The bits of a vector of `F₂ⁿ`, coordinate `0` first. -/
def vecBits {n : ℕ} (v : Fin n → ZMod 2) : List Bool := List.ofFn (toBits v)

/-- The input word of the `APFFₙ` verifier: `n` in unary (`n` ones and a zero), then the bits of
the coset representative `a`, the `ℓ` bits of `y`, and the bits of the basis vectors
`b₁, …, b_ℓ` of `V`, in order. -/
def inputWord (n : ℕ) (b : Fin (ell n) → Fin n → ZMod 2) (a : Fin n → ZMod 2)
    (y : Fin (ell n) → Bool) : List Bool :=
  List.replicate n true ++ [false] ++ vecBits a ++ List.ofFn y ++ (List.ofFn fun i => vecBits (b i)).flatten

/-- A word read as a query point of `{0,1}ⁿ` (missing bits read as `0`). -/
def decodeQuery (n : ℕ) (q : List Bool) : Fin n → Bool := fun i => q.getD i false

/-- **A deterministic adaptive query algorithm with step map `δ`, run with query access to `f`.**

The configuration is a word `w` (the input word followed by the answers received so far). One step
evaluates `δ w`: the output `true :: b :: _` halts with decision `b`; the output `false :: q` queries
`f` at the point `q` and appends the answer `f(q)` to `w`; any other output halts with `false`.
`queryRun δ n f F w` runs at most `F` steps (so at most `F − 1` queries) and is `some b` if the
algorithm halted with decision `b`, and `none` if it did not halt within `F` steps.

arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem 5.2, p.32: "a deterministic algorithm
that, given a basis of V, a candidate answer (a, y), and query access to f, decides whether (a, y)
is a valid answer using O(n²) queries to f and poly(n) time".

**Formalization Note.** Each step recomputes from the whole configuration, so the algorithm is a
function of its input and the answers so far (deterministic and adaptive). The time bound is
imposed on `δ` separately (Mathlib's `Turing.TM2ComputableInPolyTime`). -/
def queryRun (δ : List Bool → List Bool) (n : ℕ) (f : PelagicFF.BoolFn n) :
    ℕ → List Bool → Option Bool
  | 0, _ => none
  | k + 1, w =>
    match δ w with
    | false :: q => queryRun δ n f k (w ++ [f (decodeQuery n q)])
    | true :: b :: _ => some b
    | _ => some false

end PelagicFF.Supplement


