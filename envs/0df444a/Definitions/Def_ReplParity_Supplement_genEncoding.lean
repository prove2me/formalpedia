-- Prove2me | Definitions.Def_ReplParity_Supplement_genEncoding
-- name    : ReplParity_Supplement_genEncoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:56:34.419017+00:00
-- url     : https://prove2.me/theorems/e38c2dbe-6bef-4d0f-881c-6d31f78da4dc
-- title:
--   Fixed binary encodings of the generator and query programs of Definitions 2.4–2.5
-- statement:
--   The finite-bit model of §2.2 measures running time against a fixed binary encoding. For a generator with parameters $N$ and rationals $\gamma,\zeta$, the input is a header consisting of $N+\lceil1/\gamma\rceil+\lceil\log_2(1/\zeta)\rceil$ written in unary, then $N$, $\gamma$, $\zeta$ in binary, followed by the generator's random bits. Its output is a description bit string $d$ and a rational radius $\eta^*$.
--
--   The query program's input is the same header, the description $d$, a query vector (a list of rationals, each written as sign, numerator and denominator in binary) and the program's random bits. Its output is either "malformed" or a label, a list of rationals.
--
--   Because the header carries $N$, $1/\gamma$ and $\log(1/\zeta)$ in unary, polynomial time in the input length is polynomial time in $N$, $1/\gamma$, $\log(1/\zeta)$, the encoding lengths of $\gamma$, $\zeta$ and of the query, and the number of random bits, as Definition 2.5 requires.
--
--   **Formalization Note** The encodings are fixed here, independently of any generator, over the alphabet of bits plus a separator.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.2, p.11 (PDF p.13) and Definition 2.5, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ReplParity_encIn

set_option autoImplicit false

namespace ReplParity

namespace Supplement

/-- The size `N + ⌈1/γ⌉ + ⌈log₂(1/ζ)⌉` in which Definition 2.5 measures a generator's running time
(`Nat.clog 2 ⌈1/ζ⌉₊ = ⌈log₂(1/ζ)⌉` for `0 < ζ`). -/
def padSize (N : ℕ) (γ ζ : ℚ) : ℕ := N + ⌈1 / γ⌉₊ + Nat.clog 2 ⌈1 / ζ⌉₊

/-- The parameter header `(N, γ, ζ)`: `padSize N γ ζ` ones in unary, then `N`, `γ`, `ζ` in binary
(base mission's `encNatSym`, `encRat`), with separators. -/
def encHeader (N : ℕ) (γ ζ : ℚ) : List (Option Bool) :=
  List.replicate (padSize N γ ζ) (some true) ++ [none] ++ encNatSym N ++ [none] ++ encRat γ ++
    [none] ++ encRat ζ ++ [none]

/-- A list of rationals: each rational (`encRat`) followed by a separator, and one more separator
ending the list. -/
def encRatList (q : List ℚ) : List (Option Bool) :=
  (q.map (fun x => encRat x ++ [none])).flatten ++ [none]

/-- The encoding length of a query vector. -/
def qSize (q : List ℚ) : ℕ := (encRatList q).length

/-- Generator input `(N, γ, ζ, random bits)`. -/
abbrev GenInput : Type := ℕ × ℚ × ℚ × List Bool

/-- Generator output `(description bits, η∗)`. -/
abbrev GenOutput : Type := List Bool × ℚ

/-- Query-program input `(N, γ, ζ, description bits, dyadic query vector, random bits)`. -/
abbrev QInput : Type := ℕ × ℚ × ℚ × List Bool × List ℚ × List Bool

/-- **Binary encodings of the generator and query programs of Definitions 2.4–2.5.** Shen, Zhong,
*Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027
submission (manuscript sha256 40424491…), §2.2, p.11 and Definition 2.5, p.12 (PDF pp.13–14):
"A uniform efficient robust IAT generator … receives N and rationals 0 < γ, ζ < 1/2, runs in time
polynomial in N, 1/γ, and log(1/ζ) … on a query q the running time and the length of the returned
label are polynomial in these quantities and in the encoding length of q."

The generator's input is the header `encHeader N γ ζ` followed by its random bits. Because the
header carries `N + ⌈1/γ⌉ + ⌈log₂(1/ζ)⌉` in unary, polynomial time in the input length (Mathlib's
`TM2ComputableInPolyTime`) is polynomial time in `N, 1/γ, log(1/ζ)`, the encoding lengths of `γ, ζ`
(§2.2) and the number of random bits.

**Formalization Note.** Alphabet `Option Bool` (`some b` a bit, `none` a separator); all encodings
are fixed here, independently of any generator. -/
def encGenIn : GenInput → List (Option Bool)
  | (N, γ, ζ, r) => encHeader N γ ζ ++ r.map some

/-- The generator's output `(d, η∗)`: the description bits, a separator, `η∗` in binary. -/
def encGenOut : GenOutput → List (Option Bool)
  | (d, η) => d.map some ++ [none] ++ encRat η

/-- The query program's input: the same header, the description bits, the query vector (a list of
rationals) and the program's random bits. With the description length bounded by the generator's
time, polynomial time in this input is polynomial in `N, 1/γ, log(1/ζ)`, the encoding lengths of
`γ, ζ, q`, and the number of random bits. -/
def encQIn : QInput → List (Option Bool)
  | (N, γ, ζ, d, q, r) => encHeader N γ ζ ++ d.map some ++ [none] ++ encRatList q ++ r.map some

/-- The query program's output: `[some false]` for a malformed answer, `some true` followed by the
label (a list of rationals) otherwise. -/
def encQOut : Option (List ℚ) → List (Option Bool)
  | none => [some false]
  | some l => some true :: encRatList l

end Supplement

end ReplParity


