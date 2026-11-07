-- Prove2me | Definitions.Def_ApproxGKR_dyadicVal
-- name    : ApproxGKR_dyadicVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:02.222566+00:00
-- url     : https://prove2.me/theorems/145688bb-af80-46ae-bf3a-c22bd7f0e8fb
-- title:
--   Gaussian dyadic numbers $(A+iB)2^{-p}$ and their bit sizes
-- statement:
--   A **Gaussian dyadic number** is a triple $(A,B,p)$ with $A,B\in\mathbb Z$ and $p\in\mathbb N$, standing for the complex number
--   $$(A+iB)\,2^{-p}.$$
--   "Numbers exchanged or stored by the parties have the form $(A+iB)2^{-p}$ with $A,B\in\mathbb Z$" (p.5); the claimed output is $y=(A+iB)2^{-p}$ (Theorem C.1). The bit size of $(A,B,p)$ is the sum of the binary lengths of $|A|$, $|B|$ and $p$ plus three; the bit size of a rational $\Delta$ or $\varepsilon$ is the binary length of its numerator and denominator plus two. These sizes define the input bit length $b_{\mathrm{in}}$ of the instance.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §2.1, p.5; Theorem C.1, p.33

import Mathlib

namespace ApproxGKR

/-- A Gaussian dyadic number `(A, B, p)`, standing for `(A + iB)2^{−p}` with `A, B ∈ ℤ`. -/
abbrev GaussDyadic := ℤ × ℤ × ℕ

/-- The complex value `(A + iB)2^{−p}` of a Gaussian dyadic `(A, B, p)`.

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §2.1, p.5: "Numbers exchanged or stored by the parties have the form
`(A + iB)2^{−p}` with `A, B ∈ Z`"; Theorem C.1, p.33: "`y = (A + iB)2^{−p}`".

**Formalization Note** The encoding is the triple `(A, B, p)`; its bit size is `dsize`. -/
noncomputable def dyadicVal (z : GaussDyadic) : ℂ :=
  ((z.1 : ℂ) + (z.2.1 : ℂ) * Complex.I) * (2 : ℂ) ^ (-(z.2.2 : ℤ))

/-- The bit size of a Gaussian dyadic `(A, B, p)`: the binary lengths of `|A|`, `|B|` and `p`,
plus three bits (two signs and a separator). -/
def dsize (z : GaussDyadic) : ℕ :=
  Nat.size z.1.natAbs + Nat.size z.2.1.natAbs + Nat.size z.2.2 + 3

/-- The bit size of a rational number given as numerator and denominator ("rational parameters
`∆ > 0` and `0 < ε < 1`", Theorem C.1, p.33). -/
def qsize (q : ℚ) : ℕ :=
  Nat.size q.num.natAbs + Nat.size q.den + 2

end ApproxGKR


