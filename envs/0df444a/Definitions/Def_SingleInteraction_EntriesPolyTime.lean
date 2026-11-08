-- Prove2me | Definitions.Def_SingleInteraction_EntriesPolyTime
-- name    : SingleInteraction_EntriesPolyTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:41.986575+00:00
-- url     : https://prove2.me/theorems/488ea42a-fa37-4244-8a8a-0bdb7b4d97bc
-- title:
--   Polynomial-time computable entries of a fixed matrix
-- statement:
--   A $k$-qubit matrix $h$ has polynomial-time computable entries when a deterministic Turing machine, given a precision $q$ (in unary) and the indices $s,t$ of an entry, outputs in time polynomial in its input a Gaussian rational $r+r'i$ ($r,r'$ binary rationals with positive denominators) with
--
--   $$|r+r'i-h_{s,t}|\le2^{-q}.$$
--
--   This is Definition 31's requirement on the fixed interaction.
--
--   **Formalization Note** Computation is Mathlib's polynomial-time Turing-machine computability on the published binary codes; for constant $k$ the input length is linear in $q$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, p.29

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- The code of a `k`-qubit basis state `s` as the list of its bits. -/
def basisCode {k : ℕ} (s : Fin k → Fin 2) : List ℕ := List.ofFn (fun j => (s j : ℕ))

/-- Polynomial-time computable entries of a fixed `k`-qubit matrix (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, p.29: "We
require the entries of `h` to be polynomial-time computable. More precisely, there exists a deterministic
algorithm which, given a precision parameter `q`, outputs rational approximations to all entries of `h`
with additive error at most `2^{−q}` in time polynomial in `q`").

There is a function `f`, computed by a Turing machine in polynomial time, that maps `q` (in unary) and
two basis states `s, t` to a pair of binary rationals `(r, r')` with positive denominators and
`|r + r' i − h_{s,t}| ≤ 2^{−q}`.

**Formalization Note** Computation is Mathlib's `Turing.TM2ComputableInPolyTime` on the codes of the
published `OAI.ContinuumCoulomb.BinaryEncoding` combinators. `q` is in unary, so time polynomial in the
input length is time polynomial in `q` for constant `k`. The entry index is part of the input; "rational
approximation" of a complex entry is a Gaussian rational within modulus `2^{−q}`. -/
def EntriesPolyTime {k : ℕ} (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) : Prop :=
  ∃ f : ℕ × (List ℕ × List ℕ) → BinaryRational × BinaryRational,
    Nonempty (Turing.TM2ComputableInPolyTime
      (pair unary (pair (BinaryEncoding.list natural) (BinaryEncoding.list natural))).encode
      (pair binaryRationalCodec binaryRationalCodec).encode f) ∧
    ∀ (q : ℕ) (s t : Fin k → Fin 2),
      0 < (f (q, basisCode s, basisCode t)).1.denominator ∧
      0 < (f (q, basisCode s, basisCode t)).2.denominator ∧
      ‖((f (q, basisCode s, basisCode t)).1.value : ℂ) +
          ((f (q, basisCode s, basisCode t)).2.value : ℂ) * Complex.I - h s t‖ ≤ (1 / 2 : ℝ) ^ q

end SingleInteraction


