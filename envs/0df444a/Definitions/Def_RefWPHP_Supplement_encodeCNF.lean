-- Prove2me | Definitions.Def_RefWPHP_Supplement_encodeCNF
-- name    : RefWPHP_Supplement_encodeCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:24:26.3952+00:00
-- url     : https://prove2.me/theorems/242fc3b5-313b-4930-9320-df9b0864533e
-- title:
--   Binary encodings of CNF formulas (machine input) and of PK derivations (machine output)
-- statement:
--   For the machines of Theorem 5.1, a CNF formula $\varphi = C_1 \wedge \dots \wedge C_m$ over $n$ variables is written as a bit string: $n$ in unary (that many ones and a zero), then the clauses $C_1, \dots, C_m$ in order. A clause is the increasing list of the codes $2i + b$ of its literals ($b = 1$ for $x_i$, $b = 0$ for $\neg x_i$), each code in unary. Every list element is preceded by a one and every list is terminated by a zero. $|\varphi|$ denotes the length of the string.
--
--   A PK-derivation over $x_1, \dots, x_n$ is written in the same way, as a list of cedents, each a list of formulas: a literal is a two-bit tag and its variable index in unary, and a conjunction or disjunction is a two-bit tag and the list of its arguments. The code of a derivation is at least as long as its size and at most $(n + 5)$ times its size plus one.
--
--   **Formalization Note** The paper fixes no encoding. These are explicit and prefix-free, and their lengths are polynomially related to those of any standard encoding, which is all that polynomial-time automatability and running times $2^{o(n)} (n+m)^{O(1)}$ depend on.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, p.15 (PDF p.17); §2.1.4, p.17 (PDF p.19); Theorem 5.1, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_LayeredRef

namespace RefWPHP

namespace Supplement

open PKFormula

/-- A natural number `i` in unary: `i` ones followed by a zero. -/
def encodeNat (i : ℕ) : List Bool := List.replicate i true ++ [false]

/-- The code `2i + b` of the literal `(i, b)` (`b = 1` for `x_i`, `b = 0` for `¬x_i`). -/
def literalCode {n : ℕ} (ℓ : Lit n) : ℕ := 2 * ℓ.1.val + if ℓ.2 then 1 else 0

/-- A clause: the increasing list of its literal codes, each in unary and preceded by a `1`,
terminated by a `0`. -/
def encodeClause {n : ℕ} (C : Finset (Lit n)) : List Bool :=
  (((C.image literalCode).sort (· ≤ ·)).map fun c => true :: encodeNat c).flatten ++ [false]

/-- The binary input encoding of a CNF formula `φ = C_1 ∧ ⋯ ∧ C_m` over `n` variables, for the
machines of Theorem 5.1 of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), p.39 (PDF 41): `n` in unary,
then the clauses `C_1, …, C_m` in order, each preceded by a `1`, terminated by a `0`. `|φ|` is the
length of this string.

**Formalization Note.** The paper fixes no encoding; this one is explicit, prefix-free, and of
length polynomially related to every standard encoding of `φ`, which is all that automatability
and running times of the form `2^{o(n)}·(n+m)^{O(1)}` depend on. -/
def encodeCNF {n m : ℕ} (φ : Fin m → Finset (Lit n)) : List Bool :=
  encodeNat n ++ (List.ofFn fun A => true :: encodeClause (φ A)).flatten ++ [false]

/-- A formula of PK over `Fin n`, prefix-free: `00` + unary `i` for `x_i`, `01` + unary `i` for
`¬x_i`, and `10` (conjunction) or `11` (disjunction) followed by each argument preceded by a `1`
and a final `0`. Its length is between `size φ` and `(n + 3) · size φ`. -/
def encodeFormula {n : ℕ} : PKFormula (Fin n) → List Bool
  | .pos i => false :: false :: encodeNat i.val
  | .neg i => false :: true :: encodeNat i.val
  | .and l => true :: false :: ((l.attach.map fun ⟨ψ, _⟩ => true :: encodeFormula ψ).flatten ++ [false])
  | .or l => true :: true :: ((l.attach.map fun ⟨ψ, _⟩ => true :: encodeFormula ψ).flatten ++ [false])

/-- A cedent: each formula preceded by a `1`, then a `0`. -/
def encodeCedent {n : ℕ} (Γ : Cedent (Fin n)) : List Bool :=
  (Γ.map fun ψ => true :: encodeFormula ψ).flatten ++ [false]

/-- The binary output encoding of a PK-derivation over `Fin n`: each line preceded by a `1`, then a
`0`. Its length is at least `derivSize ρ` and at most `(n + 5) · derivSize ρ + 1`, so it is
polynomially related to the paper's size of a derivation (p.15). -/
def encodeDeriv {n : ℕ} (ρ : List (Cedent (Fin n))) : List Bool :=
  (ρ.map fun Γ => true :: encodeCedent Γ).flatten ++ [false]

end Supplement

end RefWPHP


