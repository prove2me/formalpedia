-- Prove2me | Definitions.Def_KelnerLinSolve_RatCongr
-- name    : KelnerLinSolve_RatCongr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:25.436953+00:00
-- url     : https://prove2.me/theorems/3238ad50-75ae-48c0-80eb-74af7d02b782
-- title:
--   Congruence of a rational number modulo an integer
-- statement:
--   Let $r \in \mathbb Q$ be written in lowest terms as $a/d$ with $d \ge 1$, let $v \in \mathbb Z$ and $Q \in \mathbb N$. Then $r \equiv v \pmod Q$ means
--
--   $$
--   \gcd(d, Q) = 1 \quad\text{and}\quad a \equiv v\,d \pmod Q .
--   $$
--
--   The congruence is defined only when the reduced denominator is coprime to the modulus; then it says that $a\,d^{-1} \equiv v$ in $\mathbb Z/Q\mathbb Z$. It is the notion of congruence used in the uniqueness statements of rational reconstruction (Theorems 2.1 and 2.3).
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 2.1, p.5; Theorem 2.3, p.7

import Mathlib

namespace KelnerLinSolve

/-- **Congruence of a rational number modulo an integer.** For `r ∈ ℚ` written in lowest terms as
`a / d` with `d ≥ 1`, `r ≡ v (mod Q)` means `gcd(d, Q) = 1` and `a ≡ v d (mod Q)`; "congruence of a
rational number modulo `R^L` is defined only when its reduced denominator is coprime to `R^L`".
Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission
(sha256 d1af55cb…), Theorem 2.1, p.5, and Theorem 2.3, p.7.

**Formalization Note.** A Lean `ℚ` is kept in lowest terms with `r.den ≥ 1`, so `r.num`, `r.den` are
the reduced numerator and denominator. When `gcd(d, Q) = 1`, `a ≡ v d` is the same as
`a · d⁻¹ ≡ v` in `ℤ/Qℤ`. -/
def RatCongr (r : ℚ) (v : ℤ) (Q : ℕ) : Prop :=
  Nat.Coprime r.den Q ∧ (Q : ℤ) ∣ r.num - v * r.den

end KelnerLinSolve


