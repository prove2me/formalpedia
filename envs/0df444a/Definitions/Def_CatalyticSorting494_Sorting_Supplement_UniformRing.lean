-- Prove2me | Definitions.Def_CatalyticSorting494_Sorting_Supplement_UniformRing
-- name    : CatalyticSorting494_Sorting_Supplement_UniformRing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:17:40.959206+00:00
-- url     : https://prove2.me/theorems/c18d2b73-8564-4774-a4f9-0da55508af4d
-- title:
--   Definition 4.2 — $(S,T)$-uniform families of finite rings
-- statement:
--   Let $K=(K_n)_{n\in\mathbb N}$ be a family of finite rings (with $1$, not necessarily commutative) and $S,T:\mathbb N\to\mathbb N$. Write $L_n=\lceil\log_2|K_n|\rceil$. The family is **$(S,T)$-uniform** when there is a bijection $e_n$ from $K_n$ onto the lexicographically first $|K_n|$ strings of $\{0,1\}^{L_n}$, together with machines of the base mission's random-access model, each running within $T(n)$ steps and $S(n)$ charged clean bits, that perform the following operations for every $n$:
--
--   1. on read-only input $(1^n,e_n(u),e_n(v),i)$, output bit $i$ of $e_n(u\circ v)$, for each $\circ\in\{+,-,\times\}$;
--   2. on read-only input $(1^n,e_n(v))$ with $e_n(u)$ on a read-write tape, transform $e_n(u)$ in place into $e_n(u+v)$;
--   3. on input $(1^n,i)$, output bit $i$ of $e_n(-1)$, $e_n(0)$, $e_n(1)$ and of $|K_n|$.
--
--   The witness of uniformity consists of the bijections and the seven machines with these properties. It is a hypothesis on the ring family in Theorem 4.3; an algorithm using the ring operations must simulate these machines at the charged cost, never call them for free.
--
--   **Formalization Note** The code $e_n(u)$ is the $L_n$-bit binary numeral of the image of $u$ under a bijection $K_n\to\{0,\dots,|K_n|-1\}$, most significant bit first; in this order the numerals of $0,\dots,|K_n|-1$ are exactly the lexicographically first $|K_n|$ strings. "Output (each bit of)" is a bit query: the position $i$ is part of the input, in binary, and the answer is one bit written into a one-cell work tape that starts at $0$ (the machine may not use catalytic space). $|K_n|$ is output in $L_n+1$ bits, least significant first. The read-write tape of the in-place operation is the machine's work tape, holding exactly $e_n(u)$ at the start and $e_n(u+v)$ at the end. Every input starts with $1^n$ and a separator $0$, in the order of the definition. $|K_n|$ is not assumed to be a power of two.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Definition 4.2, printed p.14 (PDF p.15), after [BCKLS14, Section 4.1]

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine

namespace CatalyticSorting494.Sorting.Supplement

open CatalyticSorting494.Sorting

/-- The `width`-bit binary string of `v`, most significant bit first. For `v < 2 ^ width` these
strings, in increasing order of `v`, are the lexicographically first strings of `{0,1}^width`. -/
def bigEndianBits (width v : ℕ) : List Bool :=
  (List.range width).reverse.map v.testBit

/-- The code length `⌈log₂ |K_n|⌉` of the ring `K_n`. -/
def ringWidth (K : ℕ → Type*) [∀ n, Fintype (K n)] (n : ℕ) : ℕ :=
  Nat.clog 2 (Fintype.card (K n))

/-- The width of the binary field holding a bit position below `ringWidth K n + 1`. -/
def indexWidth (L : ℕ) : ℕ :=
  Nat.log 2 (L + 1) + 1

/-- The three binary ring operations of Definition 4.2. -/
inductive RingOp where
  | add
  | sub
  | mul

/-- The result of a ring operation. -/
def RingOp.apply {R : Type*} [Ring R] : RingOp → R → R → R
  | .add, u, v => u + v
  | .sub, u, v => u - v
  | .mul, u, v => u * v

/-- The machine `M` started on input `x` with catalytic content `z` halts within `T` steps, charged
at most `S` clean bits, with catalytic content `z'`. Used for the in-place addition of
Definition 4.2, where the read-write tape holding `e(u)` is the work tape `z = e(u)` and must end as
`z' = e(u + v)`. -/
def TransformsWithin (M : Machine) (x z z' : List Bool) (T S : ℕ) : Prop :=
  ∃ (t : ℕ) (cfg : M.Config),
    M.configAt x z t = some cfg ∧ M.step x cfg = none ∧ t ≤ T ∧
      Machine.cleanSpace cfg ≤ S ∧ cfg.dirty = z'

/-- An `(S, T)`-uniform ring family (Definition 4.2). `enc n` is a bijection from `K_n` onto
`{0, …, |K_n| - 1}`, and `code n u` writes `enc n u` as a `⌈log₂ |K_n|⌉`-bit string, most significant
bit first, so `code n` is a bijection onto the lexicographically first `|K_n|` strings of that
length. The machines are machines of the published model, with all clean space (index tapes
included) charged; a machine that outputs one bit does so into a one-cell work tape that starts at
`false`. Every input begins with `1^n` followed by a separator `0`; a requested bit position `i` is
given in binary in a field of width `indexWidth`.

1. `opBit o`: on read-only input `(1^n, e(u), e(v), i)`, the `i`-th bit of `e(u ∘ v)`, for
   `∘ ∈ {+, −, ×}`.
2. `addInPlace`: on read-only input `(1^n, e(v))` with `e(u)` on the read-write tape, transforms
   `e(u)` in place into `e(u + v)`.
3. `constBit c` for `c ∈ {−1, 0, 1}` and `cardBit`: on input `(1^n, i)`, the `i`-th bit of `e(c)`,
   respectively of `|K_n|` written with `⌈log₂ |K_n|⌉ + 1` bits, least significant first.

Each runs within `T n` steps and `S n` clean bits, for every `n`. -/
structure UniformRing (K : ℕ → Type*) [∀ n, Ring (K n)] [∀ n, Fintype (K n)]
    (S T : ℕ → ℕ) where
  enc : ∀ n, K n ≃ Fin (Fintype.card (K n))
  opBit : RingOp → Machine
  addInPlace : Machine
  negOneBit : Machine
  zeroBit : Machine
  oneBit : Machine
  cardBit : Machine
  opBit_spec : ∀ (o : RingOp) (n : ℕ) (u v : K n) (i : ℕ), i < ringWidth K n →
    ComputesWithin (opBit o)
      (List.replicate n true ++ [false] ++ bigEndianBits (ringWidth K n) (enc n u) ++
        bigEndianBits (ringWidth K n) (enc n v) ++ natBits (indexWidth (ringWidth K n)) i)
      [false]
      [(bigEndianBits (ringWidth K n) (enc n (o.apply u v))).getD i false]
      (T n) (S n)
  addInPlace_spec : ∀ (n : ℕ) (u v : K n),
    TransformsWithin addInPlace
      (List.replicate n true ++ [false] ++ bigEndianBits (ringWidth K n) (enc n v))
      (bigEndianBits (ringWidth K n) (enc n u))
      (bigEndianBits (ringWidth K n) (enc n (u + v)))
      (T n) (S n)
  negOneBit_spec : ∀ (n i : ℕ), i < ringWidth K n →
    ComputesWithin negOneBit
      (List.replicate n true ++ [false] ++ natBits (indexWidth (ringWidth K n)) i)
      [false] [(bigEndianBits (ringWidth K n) (enc n (-1))).getD i false] (T n) (S n)
  zeroBit_spec : ∀ (n i : ℕ), i < ringWidth K n →
    ComputesWithin zeroBit
      (List.replicate n true ++ [false] ++ natBits (indexWidth (ringWidth K n)) i)
      [false] [(bigEndianBits (ringWidth K n) (enc n 0)).getD i false] (T n) (S n)
  oneBit_spec : ∀ (n i : ℕ), i < ringWidth K n →
    ComputesWithin oneBit
      (List.replicate n true ++ [false] ++ natBits (indexWidth (ringWidth K n)) i)
      [false] [(bigEndianBits (ringWidth K n) (enc n 1)).getD i false] (T n) (S n)
  cardBit_spec : ∀ (n i : ℕ), i < ringWidth K n + 1 →
    ComputesWithin cardBit
      (List.replicate n true ++ [false] ++ natBits (indexWidth (ringWidth K n)) i)
      [false] [(natBits (ringWidth K n + 1) (Fintype.card (K n))).getD i false] (T n) (S n)

/-- The encoding `e_n(u)` of a ring element as a `⌈log₂ |K_n|⌉`-bit string. -/
def UniformRing.code {K : ℕ → Type*} [∀ n, Ring (K n)] [∀ n, Fintype (K n)] {S T : ℕ → ℕ}
    (W : UniformRing K S T) (n : ℕ) (u : K n) : List Bool :=
  bigEndianBits (ringWidth K n) (W.enc n u)

end CatalyticSorting494.Sorting.Supplement


