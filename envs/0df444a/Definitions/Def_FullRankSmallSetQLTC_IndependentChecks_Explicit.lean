-- Prove2me | Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Explicit
-- name    : FullRankSmallSetQLTC_IndependentChecks_Explicit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:57.142838+00:00
-- url     : https://prove2.me/theorems/983edfd3-a884-46eb-8506-eebb89f80ab8
-- title:
--   Explicitness: polynomial-time enumeration by a multi-stack Turing machine
-- statement:
--   "Explicit" and "computable in time polynomial in $m$" are expressed with an actual machine model, Mathlib's finite multi-stack Turing machines and their step semantics.
--
--   A function $f:\mathbb N\times\mathbb N\to\mathrm{List}\,\mathbb N$ is **polynomial-time** if one finite machine maps the encoding of every input $(m,j)$ to the encoding of $f(m,j)$ within $p(\text{input length})$ steps, for one polynomial $p$. Inputs encode the family index $m$ in **unary** and the label $j$ in **binary**; outputs encode a list of naturals, each in binary followed by a separator.
--
--   1. A matrix family $(H_m)$ is **row-enumerated** by $f$ from $m_0$ on if, for $m\ge m_0$ and every row label $i$, $f(m,i)$ is a duplicate-free list of exactly the column labels $j$ with $(H_m)_{ij}\neq0$; columns likewise.
--   2. A family of relations between coded vertex sets is **neighbour-enumerated** by $f$ if $f(m,\mathrm{code}(x))$ lists exactly the codes of the neighbours of $x$, without repetition.
--   3. A data family $m\mapsto\mathrm{out}(m)$ is polynomial-time if a polynomial-time $f$ satisfies $f(m,0)=\mathrm{out}(m)$ for $m\ge m_0$.
--
--   Because the index is read in unary, "polynomial in the input length" is "polynomial in $m$" (and, when $m=O(\log N)$, polynomial in $\log N$).
--
--   **Formalization Note** The machine model is `Turing.TM2ComputableInPolyTime` with input encoding `encodingProd unaryEncodingNat encodingNatBool` and an output encoding over `Option Bool`. The machine is part of the existential witness, so finite precomputation depending on fixed parameters is built into it.
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Theorem 1.2 (p. 6), Theorem 5.1(iv) (p. 24), Theorem 5.2 (p. 25) (printed page = PDF page)

import Mathlib

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Computability

/-! # Explicitness: polynomial-time enumeration by an actual Turing machine

"Explicit" and "computable in time polynomial in `m`" are expressed with Mathlib's bundled
multi-stack Turing machines (`Turing.FinTM2`) and their step semantics
(`Turing.TM2ComputableInPolyTime`): one finite machine, chosen before the family member, maps the
encoded input to the encoded output within `p(input length)` steps for a fixed polynomial `p`.

Inputs are pairs `(m, j)`: the family index `m` written in **unary** and a natural number `j`
(a vertex/row/column label) written in **binary**. Outputs are finite lists of natural numbers,
each written in binary and terminated by a separator. -/

/-- Input encoding of `(m, j)`: `m` in unary (letters `Sum.inl`), then `j` in binary
(letters `Sum.inr`). -/
def encIn (p : ℕ × ℕ) : List (Bool ⊕ Bool) :=
  (encodingProd unaryEncodingNat encodingNatBool).encode p

/-- Output encoding of a list of natural numbers: each entry in binary (`some b` letters)
followed by the separator `none`. -/
def encOut (l : List ℕ) : List (Option Bool) :=
  l.flatMap fun n => (encodeNat n).map some ++ [none]

/-- `f` is computed by a finite multi-stack Turing machine in time polynomial in the input
length, with the encodings `encIn` / `encOut`. The machine and the polynomial are part of the
witness; correctness on every input is the machine's actual halting output. -/
def PolyTimeFn (f : ℕ × ℕ → List ℕ) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encIn encOut f)

/-- `f` enumerates the rows of the matrix family `H` from index `m₀` on: on input `(m, i)` with
`m ≥ m₀` and `i` a row label, it returns a duplicate-free list whose entries are exactly the
column labels `j` with `H m i j ≠ 0`. -/
def EnumeratesRows {r c : ℕ → ℕ} (H : ∀ m, Matrix (Fin (r m)) (Fin (c m)) (ZMod 2)) (m₀ : ℕ)
    (f : ℕ × ℕ → List ℕ) : Prop :=
  ∀ m, m₀ ≤ m → ∀ i : Fin (r m), (f (m, i.val)).Nodup ∧
    ∀ j : ℕ, j ∈ f (m, i.val) ↔ ∃ hj : j < c m, H m i ⟨j, hj⟩ ≠ 0

/-- `f` enumerates the columns of the matrix family `H` from index `m₀` on: on input `(m, j)`
it returns a duplicate-free list whose entries are exactly the row labels `i` with
`H m i j ≠ 0`. -/
def EnumeratesCols {r c : ℕ → ℕ} (H : ∀ m, Matrix (Fin (r m)) (Fin (c m)) (ZMod 2)) (m₀ : ℕ)
    (f : ℕ × ℕ → List ℕ) : Prop :=
  ∀ m, m₀ ≤ m → ∀ j : Fin (c m), (f (m, j.val)).Nodup ∧
    ∀ i : ℕ, i ∈ f (m, j.val) ↔ ∃ hi : i < r m, H m ⟨i, hi⟩ j ≠ 0

/-- Every row and every column of the matrix family `H` can be enumerated by one polynomial-time
machine each (from index `m₀` on). -/
def PolyTimeEnumerable {r c : ℕ → ℕ} (H : ∀ m, Matrix (Fin (r m)) (Fin (c m)) (ZMod 2))
    (m₀ : ℕ) : Prop :=
  (∃ f, PolyTimeFn f ∧ EnumeratesRows H m₀ f) ∧ (∃ f, PolyTimeFn f ∧ EnumeratesCols H m₀ f)

/-- `f` enumerates the neighbourhoods of a family of relations `adj m : X m → Y m → Prop`
between coded vertex sets, from index `m₀` on: on input `(m, codeX m x)` it returns a
duplicate-free list whose entries are exactly the codes `codeY m y` of the `y` with
`adj m x y`. -/
def EnumeratesNbrs {X Y : ℕ → Type*} (codeX : ∀ m, X m → ℕ) (codeY : ∀ m, Y m → ℕ)
    (adj : ∀ m, X m → Y m → Prop) (m₀ : ℕ) (f : ℕ × ℕ → List ℕ) : Prop :=
  ∀ m, m₀ ≤ m → ∀ x : X m, (f (m, codeX m x)).Nodup ∧
    ∀ k : ℕ, k ∈ f (m, codeX m x) ↔ ∃ y : Y m, adj m x y ∧ codeY m y = k

/-- The data family `out : ℕ → List ℕ` is computable in time polynomial in `m` from index `m₀`
on: a polynomial-time machine maps `(m, 0)` (that is, `m` in unary) to `out m`. -/
def PolyTimeData (out : ℕ → List ℕ) (m₀ : ℕ) : Prop :=
  ∃ f, PolyTimeFn f ∧ ∀ m, m₀ ≤ m → f (m, 0) = out m

end FullRankSmallSetQLTC.IndependentChecks


