-- Prove2me | Definitions.Def_ReplParity_encIn
-- name    : ReplParity_encIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:35.233199+00:00
-- url     : https://prove2.me/theorems/b2f3d04a-baba-4626-992e-061c6ac768cd
-- title:
--   Binary input encoding of the finite-bit model
-- statement:
--   In the finite-bit model (§2.2) all parameters are rational, sample domains are finite, the shared seed is a string of unbiased bits, and an algorithm is polynomial-time if its running time is polynomial in the sample size, the dimension and the encoding lengths of its parameters.
--
--   A learner's input is the tuple $(d,\varepsilon,\delta,\rho,S,r)$: the dimension, three rational parameters, the sample (each example $(x,y)$ written as its $d+1$ bits $x_1,\dots,x_d,y$) and the seed bits. Over the alphabet $\{0,1,\#\}$ it is written as $d$ in binary, each rational as a sign bit, $|\text{numerator}|$ in binary, $\#$, the denominator in binary, then the examples each followed by $\#$, a closing $\#$, and the seed bits, with $\#$ between fields. The encoding size of a rational parameter $q$ is the length of its encoding.
--
--   **Formalization Note** The encoding is fixed in advance, binary and unpadded, so its length is linear in the binary sizes of its parts; it is the input encoding of the polynomial-time clause of Theorem 3.6. Binary numbers are least significant bit first (Mathlib's `Computability.encodeNat`).
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.2, p.11 (PDF p.13); Theorem 3.6, p.19

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

/-- Machine input: `(d, ε, δ, ρ, sample, seed bits)`. Each example is a bit list. -/
abbrev LInput : Type := ℕ × ℚ × ℚ × ℚ × List (List Bool) × List Bool

/-- A natural number in binary (`Computability.encodeNat`, least significant bit first), over the
alphabet `Option Bool`. -/
def encNatSym (k : ℕ) : List (Option Bool) := (Computability.encodeNat k).map some

/-- A rational number: its sign bit, `|numerator|` in binary, a separator, the denominator in
binary. -/
def encRat (q : ℚ) : List (Option Bool) :=
  [some (decide (q < 0))] ++ encNatSym q.num.natAbs ++ [none] ++ encNatSym q.den

/-- The encoding length of a rational parameter. -/
def ratSize (q : ℚ) : ℕ := (encRat q).length

/-- The bits of a labeled example `(x, y)`: `[x₀, …, x_{d−1}, y]`, with `1 ↦ true`, `0 ↦ false`. -/
def exampleBits {d : ℕ} (e : Example d) : List Bool :=
  List.ofFn (fun i => decide (e.1 i = 1)) ++ [decide (e.2 = 1)]

/-- **Binary input encoding of the finite-bit model.** Shen, Zhong, *Replicable Parity Learning:
Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), §2.2, p.11 (PDF p.13): "In the finite-bit model, all parameters are rational, sample
domains are finite, the shared seed is a string of unbiased bits, and every algorithm has a
worst-case bound on its running time. Arithmetic on integers and rationals is charged its bit cost.
An algorithm is polynomial-time if its running time is polynomial in the sample size, the
dimension, and the encoding lengths of its parameters."

Alphabet `Option Bool`: `some b` is a bit, `none` a separator. The input `(d, ε, δ, ρ, S, r)` is
written as `d` in binary, the three rationals, the sample (each example's bits followed by a
separator, then one more separator ending the list) and the seed bits, with separators between
fields.

**Formalization Note.** The encoding is binary, without padding, and of length linear in the
binary sizes of its parts. It is fixed here, independently of any learner. -/
def encIn : LInput → List (Option Bool)
  | (d, ε, δ, ρ, S, r) =>
      encNatSym d ++ [none] ++ encRat ε ++ [none] ++ encRat δ ++ [none] ++ encRat ρ ++ [none] ++
        (S.map (fun s => s.map some ++ [none])).flatten ++ [none] ++ r.map some

end ReplParity


