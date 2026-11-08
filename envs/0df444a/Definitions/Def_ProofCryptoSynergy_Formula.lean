-- Prove2me | Definitions.Def_ProofCryptoSynergy_Formula
-- name    : ProofCryptoSynergy_Formula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:37.632398+00:00
-- url     : https://prove2.me/theorems/5dde8f43-af67-4744-92e1-30abd3945304
-- title:
--   Propositional formulas and their reading from strings
-- statement:
--   Propositional formulas are built from variables $x_0,x_1,\dots$, constants, $\neg$, $\wedge$ and $\vee$. A bit string is read as a formula as follows: a string $h\,0^k\,1\,t$ is the formula $F$ whose prefix code is $t$ when $h=1$, and $\neg F$ when $h=0$; if $t$ is not a code word then $F$ is the false constant, and the empty string is the false constant.
--
--   The **size** of a formula is the length of the string. The padding gives every formula a string at every sufficiently large length, and every length $n\ge 1$ has both a tautology and an unsatisfiable formula. Flipping the head bit is a length-preserving negation, which is how the paper's "we will usually not distinguish between tautologies and unsatisfiable propositional formulas" is made precise.
--
--   **Formalization Note** The paper's Theorem 10 and Lemma 29 ask for formulas of size exactly $n$ for every $n$, so a code with gaps would not do.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, pp.18–19 (PDF 20–21); Definition 31, p.29 (PDF 31)

import Mathlib

namespace ProofCryptoSynergy

/-- A **propositional formula** over the variables `x₀, x₁, …`, with constants, negation, conjunction
and disjunction (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, p.18 (PDF 20); disjunctions `φ ∨ ψ_λ` are used in Definition 31, p.29 (PDF 31)). -/
inductive Formula where
  | var (i : ℕ)
  | const (b : Bool)
  | not (F : Formula)
  | and (F G : Formula)
  | or (F G : Formula)

/-- The value of a formula under an assignment. -/
def Formula.eval (a : ℕ → Bool) : Formula → Bool
  | .var i => a i
  | .const b => b
  | .not F => !(F.eval a)
  | .and F G => F.eval a && G.eval a
  | .or F G => F.eval a || G.eval a

/-- The prefix code of a formula: a 3-bit tag per connective, variable indices in unary. -/
def Formula.enc : Formula → List Bool
  | .const b => [false, false, b]
  | .var i => [false, true, false] ++ List.replicate i true ++ [false]
  | .not F => [false, true, true] ++ F.enc
  | .and F G => [true, false, false] ++ F.enc ++ G.enc
  | .or F G => [true, false, true] ++ F.enc ++ G.enc

/-- The parser of the prefix code, with a fuel bound: one formula and the unread rest. -/
def Formula.parse : ℕ → List Bool → Option (Formula × List Bool)
  | 0, _ => none
  | _ + 1, false :: false :: b :: r => some (.const b, r)
  | _ + 1, false :: true :: false :: r =>
    match r.drop (r.takeWhile id).length with
    | false :: r' => some (.var (r.takeWhile id).length, r')
    | _ => none
  | n + 1, false :: true :: true :: r =>
    (Formula.parse n r).map (fun p => (.not p.1, p.2))
  | n + 1, true :: false :: b :: r =>
    match Formula.parse n r with
    | some (F, r₁) =>
      match Formula.parse n r₁ with
      | some (G, r₂) => some (if b then .or F G else .and F G, r₂)
      | none => none
    | none => none
  | _ + 1, _ => none

/-- The formula written by a code word; an unparsable string reads as the false constant. -/
def Formula.ofBody (t : List Bool) : Formula :=
  match Formula.parse (t.length + 1) t with
  | some (F, []) => F
  | _ => .const false

/-- **Reading a string as a formula**, total, with a formula at every length
(Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.2, p.19 (PDF 21): "P-uniform family of formulas `{ψ_n}` (of size `n` each)";
p.18 (PDF 20): "We will usually not distinguish between tautologies and unsatisfiable propositional
formulas").

A string `h 0^k 1 t` reads as the formula `F` with code word `t` when `h = 1` and as `¬F` when `h = 0`;
if `t` is no code word, `F` is the false constant. The empty string reads as the false constant.

**Formalization Note** The size of a formula is the length of the string. The padding `0^k 1` gives every
formula a code at every sufficiently large length, and every length `n ≥ 1` has both a tautology and an
unsatisfiable formula. The head bit makes negation length-preserving (`negStr`). -/
def decode : List Bool → Formula
  | [] => .const false
  | h :: t =>
    let F := Formula.ofBody ((t.dropWhile (fun b => !b)).drop 1)
    if h then F else .not F

/-- The shortest string reading as `F`: head bit `1`, empty padding, the code word. -/
def canon (F : Formula) : List Bool := true :: true :: F.enc

/-- The length-preserving negation of a string: flip the head bit. -/
def negStr : List Bool → List Bool
  | [] => []
  | h :: t => (!h) :: t

end ProofCryptoSynergy


