-- Prove2me | Definitions.Def_TightPQRepetition_Main_Complexity
-- name    : TightPQRepetition_Main_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:32:27.339695+00:00
-- url     : https://prove2.me/theorems/985ecc42-d22b-482d-94d0-3a69f5e615ab
-- title:
--   Complexity vocabulary: negligible functions, polynomial-size families, efficient computability, $B(k,t,\varepsilon)$, trace distance
-- statement:
--   The vocabulary of §3. Throughout, $\lambda$ is the security parameter.
--
--   A function $\mu:\mathbb N\to\mathbb R$ is **negligible** if it is nonnegative and for every $c$ it is eventually below $1/(\lambda+1)^c$. The predicate **InversePoly** allows any positive $\nu$ bounded below by $1/p(\lambda)$ for a positive polynomially bounded integer-valued $p$. It includes reciprocals of positive real polynomials; the resource claims require only that $1/\nu$ is polynomially bounded.
--
--   Efficient classical algorithms are non-uniform: a function on strings is efficient if on inputs of length $n$ it is computed by polynomially many Boolean circuits of size polynomial in $\lambda+n$, which write a self-delimiting encoding of the output. The output length is bounded but may depend on the input, as for a program. Random coins are an explicit input. Lists of strings are encoded by a fixed injective encoding `pack`, with total inverse `unpack`.
--
--   A real function $\varepsilon(\lambda)$ is **efficiently computable** if a polynomial-time Turing machine, given $\lambda$ and $n$ in unary, writes a dyadic approximation of $\varepsilon(\lambda)$ within $2^{-n}$.
--
--   The **threshold binomial function** of Notation 2 is
--   $$B(k,t,\varepsilon)=\sum_{s=t}^{k}\binom ks\varepsilon^s(1-\varepsilon)^{k-s}.$$
--   It is the probability that $k$ i.i.d. Bernoulli($\varepsilon$) variables sum to at least $t$.
--
--   **Trace distance** is $\mathrm{TD}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$.
--
--   **Formalization Note** The threshold of $B$ is an integer, so $B(k,t'-1,\varepsilon)$ at $t'=0$ is $1$ and no truncated subtraction occurs. $B$ is $1$ for $t\le0$ and $0$ for $t>k$. `MIPRE.SAT.Circuit` and `WildeQIT.traceNorm` are reused. `MIPRE.Cost.PolyBounded` is the same polynomial-bound predicate as `PolyBound`, but its module imports a theorem module missing from this workspace, so the one-line definition is restated.
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, §3 and Notation 1, 2, printed pp. 6–7 / PDF pp. 8–9

import Mathlib
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_WildeQIT_traceNorm

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, §3: the complexity vocabulary.

Throughout, `lam` is the security parameter `λ` (`λ` itself is a Lean keyword). Every efficient
classical algorithm of the paper is modelled as a non-uniform family of polynomial-size Boolean
circuits, one per input length, with its random coins an explicit argument. A uniform PPT
algorithm gives such a family, so this is the more general class; all adversaries of the paper
are non-uniform (§3, Remark 5.2).
-/

open QAlgorithms

/-- Classical strings. -/
abbrev Bits := List Bool

/-- A fixed-length string read as an element of `Bits`. -/
def toBits {n : ℕ} (x : Qubits n) : Bits := List.ofFn x

/-- A string read as a fixed-length one, missing bits read `false`. -/
def ofBits (n : ℕ) (b : Bits) : Qubits n := fun i => b.getD i false

/-- The all-zero plaintext of length `n`. -/
def zeros (n : ℕ) : Bits := List.replicate n false

/-- `f` is bounded by a polynomial. -/
def PolyBound (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n

/-- A negligible function: nonnegative, and eventually below the inverse of every polynomial. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ f n) ∧ ∀ c : ℕ, ∃ N, ∀ n, N ≤ n → f n < 1 / ((n : ℝ) + 1) ^ c

/-- A positive parameter bounded below by an inverse polynomial. This includes reciprocals of
positive real polynomials, not just reciprocals of integer-valued functions: the resource bounds
require only that `1 / ν` is polynomially bounded. -/
def InversePoly (ν : ℕ → ℝ) : Prop :=
  (∀ n, 0 < ν n) ∧ ∃ p : ℕ → ℕ, PolyBound p ∧ (∀ n, 0 < p n) ∧
    ∀ n, 1 / (p n : ℝ) ≤ ν n

/-- The self-delimiting encoding of one string: `b ↦ 1b`, closed by a `0`. -/
def packOne (x : Bits) : Bits := x.flatMap (fun b => [true, b]) ++ [false]

/-- The injective encoding of a list of strings as one string. -/
def pack (l : List Bits) : Bits := l.flatMap packOne

/-- Parsing of `pack`; `cur` is the reversed current item. A truncated trailing item is dropped. -/
def unpackAux : Bits → Bits → List Bits
  | [], _ => []
  | false :: rest, cur => cur.reverse :: unpackAux rest []
  | true :: b :: rest, cur => unpackAux rest (b :: cur)
  | [true], _ => []

/-- The inverse of `pack`, total on all strings. -/
def unpack (x : Bits) : List Bits := unpackAux x []

/-- A list of pairs as a list of strings. -/
def flattenPairs (l : List (Bits × Bits)) : List Bits :=
  l.flatMap (fun p => [p.1, p.2])

/-- The inverse of `flattenPairs` (an odd last entry is dropped). -/
def pairUp : List Bits → List (Bits × Bits)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _ => []

/-- On inputs of length `n`, `f` is computed by at most `s` Boolean circuits, one per output wire,
of total size at most `s`: they write the self-delimiting encoding `packOne (f x)`, padded with
`false`. So the length of `f x` is bounded but may depend on `x`, as it does for a program: the
inputs of many functions below are parsed strings, and two strings of the same length can hold a
short and a long message. -/
def ComputedBySize (f : Bits → Bits) (n s : ℕ) : Prop :=
  ∃ (L : ℕ) (C : Fin L → MIPRE.SAT.Circuit), L ≤ s ∧ (∑ i, (C i).size) ≤ s ∧
    ∀ x : Bits, x.length = n →
      (packOne (f x)).length ≤ L ∧ ∀ i : Fin L, (packOne (f x)).getD i false = (C i).evalBits x

/-- A polynomial-size family indexed by the security parameter. -/
def Efficient (f : ℕ → Bits → Bits) : Prop :=
  ∃ s : ℕ → ℕ, PolyBound s ∧ ∀ lam n, ComputedBySize (f lam) n (s (lam + n))

/-- A polynomial-size family indexed by the security parameter and a round number. -/
def Efficient₂ (f : ℕ → ℕ → Bits → Bits) : Prop :=
  ∃ s : ℕ → ℕ, PolyBound s ∧ ∀ lam j n, ComputedBySize (f lam j) n (s (lam + j + n))

/-- The natural number written by a string, least significant bit first. -/
def bitsVal (b : Bits) : ℕ := b.foldr (fun x acc => 2 * acc + x.toNat) 0

/-- `ε(λ)` is efficiently computable: a polynomial-time Turing machine (Mathlib's `TM2` model)
given `1^λ 0 1^n` writes the numerator of a dyadic approximation of `ε(λ)` to within `2^{-n}`. -/
def EfficientlyComputable (ε : ℕ → ℝ) : Prop :=
  ∃ f : Bits → Bits,
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : Bits => x) (fun x : Bits => x) f) ∧
    ∀ lam n : ℕ,
      |ε lam - (bitsVal (f (List.replicate lam true ++ false :: List.replicate n true)) : ℝ) / 2 ^ n|
        ≤ 1 / 2 ^ n

/-- Notation 2, PDF p. 9: `B(k,t,ε) = ∑_{s=t}^{k} C(k,s) ε^s (1-ε)^{k-s}`, with an integer
threshold so that `t' - 1` is not truncated: `B(k,t,ε) = 1` for `t ≤ 0` and `0` for `t > k`. -/
noncomputable def binomTail (k : ℕ) (t : ℤ) (ε : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (k + 1),
    if t ≤ (s : ℤ) then (k.choose s : ℝ) * ε ^ s * (1 - ε) ^ (k - s) else 0

/-- Trace distance `TD(ρ,σ) = ½‖ρ - σ‖₁` (Notation 1). -/
noncomputable def TD {α : Type} [Fintype α] [DecidableEq α] (ρ σ : Matrix α α ℂ) : ℝ :=
  (1 / 2) * WildeQIT.traceNorm (ρ - σ)

end TightPQRepetition.Main


