-- Prove2me | Definitions.Def_IterRoundDet_StablePoly
-- name    : IterRoundDet_StablePoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:43.662638+00:00
-- url     : https://prove2.me/theorems/6663912e-bb70-43b3-ab04-7662c957fca6
-- title:
--   Homogeneous multiaffine real stable polynomials $p(z)=\sum_S c_S z^S$
-- statement:
--   A homogeneous multiaffine polynomial of degree $d$ on $n$ variables is written
--
--   $$p(z)=\sum_{S\subseteq[n]} c_S z^S,\qquad z^S=\prod_{i\in S} z_i,$$
--
--   with $c_S\neq 0$ only for $|S|=d$. It is **stable** if it has no roots in the upper half-plane: $p(z)\neq 0$ for every $z\in\mathbb C^n$ with $\operatorname{Im} z_i>0$ for all $i$. Following footnote 2 of the paper, the coefficients are taken non-negative.
--
--   The file also fixes the indicator vector $\mathbf 1_S$ and the partial derivative $\partial_i g(x)$ along the coordinate line through $x$. These are the objects every statement of the mission is about.
--
--   **Formalization Note** A polynomial is its coefficient function, so one definition evaluates $p$ over $\mathbb R$, $\mathbb C$ and $\mathbb Q$. Stability excludes $p\equiv 0$ for every $n$, including $n=0$.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), footnote 2, p.2; §3.1, p.12

import Mathlib

set_option autoImplicit false

namespace IterRoundDet

/-!
# Homogeneous multiaffine real stable polynomials

N. Bansal, W. Li, M. Singh, Y. Xu, *Iterative Rounding for Determinant Maximization and Real Stable
Polynomials*, STOC 2027 submission (manuscript sha256 aa18bcee…), footnote 2, p.2, and §3.1, p.12.

**Formalization Note.** A homogeneous multiaffine polynomial of degree `d` on `n` variables is its
coefficient function `c : Finset (Fin n) → R`, with `c S ≠ 0 → S.card = d`; this is footnote 2's form
`p(z) = ∑_{|S|=d} c_S z^S`, in bijection with such polynomials. The ring varies because the paper
evaluates `p` at real points, tests stability at complex points, and queries it at rational points.
-/

variable {n : ℕ}

/-- Footnote 2, p.2: `p(z) = ∑_S c_S z^S`, `z^S = ∏_{i∈S} z_i`, in any commutative semiring. -/
def pEval {R : Type*} [CommSemiring R] (c : Finset (Fin n) → R) (z : Fin n → R) : R :=
  ∑ S, c S * ∏ i ∈ S, z i

/-- The coefficients of a polynomial with rational coefficients, as real numbers. -/
def castCoef (c : Finset (Fin n) → ℚ) : Finset (Fin n) → ℝ := fun S => (c S : ℝ)

/-- The indicator vector `1_S`. -/
def ind (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 else 0

/-- §3.1, p.12: `p` is a multiaffine, `d`-homogeneous polynomial with non-negative coefficients and
no roots in the upper half-plane: `p(z) ≠ 0` for every `z ∈ ℂⁿ` with `Im z_i > 0` for all `i`.

**Formalization Note.** Non-negativity is footnote 2's normalization ("all coefficients have the
same sign (so we can assume they are non-negative)"), and the paper's standing focus in §3.1. The
root-freeness clause excludes `p ≡ 0` for every `n`, including `n = 0`, where it asks `c ∅ ≠ 0`. -/
def IsStablePoly (d : ℕ) (c : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ c S) ∧ (∀ S, c S ≠ 0 → S.card = d) ∧
    ∀ z : Fin n → ℂ, (∀ i, 0 < (z i).im) → pEval (fun S => (c S : ℂ)) z ≠ 0

/-- The partial derivative `∂g/∂z_i` at `x`, on the line through `x` in direction `e_i`. It is used
only on polynomials, where `deriv` is a genuine derivative. -/
noncomputable def partialAt (g : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t => g (Function.update x i t)) (x i)

end IterRoundDet


