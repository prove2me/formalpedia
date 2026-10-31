-- Prove2me | Definitions.Def_StengelZeroSum_bound55
-- name    : StengelZeroSum_bound55
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:55.914298+00:00
-- url     : https://prove2.me/theorems/c46cd326-bb3a-4a1a-984f-d52a84b8138f
-- title:
--   The constant $M=\ell!\,\ell\,\alpha^\ell\beta^{\ell^2+\ell}+1$ of (55)
-- statement:
--   For rational data $A\in\mathbb Q^{m\times n}$, $b\in\mathbb Q^m$, $c\in\mathbb Q^n$, let $\alpha$ be the maximum of the absolute values of the numerators of all entries of $A$, $b$ and $c$, let $\beta$ be the maximum of their denominators, and let $\ell=m+n+1$. The constant of (55) is
--
--   $$
--   M=\ell!\,\ell\,\alpha^\ell\beta^{\ell^2+\ell}+1 .
--   $$
--
--   Theorem 7(c) asserts that this $M$ is a suitable choice in Theorem 7.
--
--   **Formalization Note** Numerators and denominators are those of the reduced fractions (denominators $\ge1$). The number is computed in $\mathbb N$ and cast to $\mathbb R$.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 7(c), eq. (55), p.18

import Mathlib

namespace StengelZeroSum

/-- The constant `M = ℓ! ℓ α^ℓ β^(ℓ²+ℓ) + 1` of (55),
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6,
Theorem 7(c), eq. (55), p.18: for rational `A ∈ ℚ^{m×n}`, `b ∈ ℚ^m`, `c ∈ ℚ^n`, "let α be the
maximum of the absolute value of the numerators of these numbers, let β be the maximum
denominator, and ℓ = m + n + 1".

**Formalization Note** Numerators and denominators are those of the reduced form
(`Rat.num`, `Rat.den`, so `den ≥ 1`); the maxima run over all entries of `A`, `b` and `c`
(`Finset.sup` in `ℕ`). The value is computed in `ℕ` and cast to `ℝ`. -/
def bound55 {m n : ℕ} (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ) : ℝ :=
  let ℓ : ℕ := m + n + 1
  let α : ℕ := max (Finset.univ.sup fun p : Fin m × Fin n => (Aq p.1 p.2).num.natAbs)
    (max (Finset.univ.sup fun i => (bq i).num.natAbs) (Finset.univ.sup fun j => (cq j).num.natAbs))
  let β : ℕ := max (Finset.univ.sup fun p : Fin m × Fin n => (Aq p.1 p.2).den)
    (max (Finset.univ.sup fun i => (bq i).den) (Finset.univ.sup fun j => (cq j).den))
  ((ℓ.factorial * ℓ * α ^ ℓ * β ^ (ℓ ^ 2 + ℓ) + 1 : ℕ) : ℝ)

end StengelZeroSum


