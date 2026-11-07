-- Prove2me | Definitions.Def_SigmoidWire_SignRepBy
-- name    : SigmoidWire_SignRepBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:24.228702+00:00
-- url     : https://prove2.me/theorems/c72f7af6-7fc5-4ffc-948a-3a50d78b1fde
-- title:
--   Sign-representation by a rational function of degree at most $D$
-- statement:
--   A rational function $r=P/Q$ with real multivariate polynomials $P,Q$ in $x_1,\dots,x_n$ **sign-represents** $f:\{0,1\}^n\to\{0,1\}$ if $Q(x)\ne0$ at every $x\in\{0,1\}^n$ and $f(x)=\mathrm{sgn}(r(x))$ there, where $\mathrm{sgn}(t)=1$ iff $t>0$. The degree of $P/Q$ is $\max\{\deg P,\deg Q\}$, so the definition asks that both total degrees be at most $D$.
--
--   This is the object that links depth-two circuits to the degree lower bound for parity.
--
--   **Formalization Note** With this $\mathrm{sgn}$, $f(x)=0$ means $P(x)/Q(x)\le0$, and the value $0$ is allowed.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.4, p.19; sgn §3, p.14

import Mathlib
import Definitions.Def_SigmoidWire_bitR

namespace SigmoidWire

/-- **Sign-representation by a rational function of degree at most `D`.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.4, p.19 (PDF p.21):
a rational function `r : {0,1}^n → ℝ` sign-represents `f` if `f(x) = sgn(r(x))` for every
`x ∈ {0,1}^n`, where `sgn(t) = 1` iff `t > 0` (§3, p.14); "the degree of a rational function `p/q`
is defined as `max{deg p, deg q}`" (p.19).

**Formalization Note.** A rational function is a pair `P, Q` of real multivariate polynomials in
`x₁, …, xₙ` with `Q(x) ≠ 0` at every point of `{0,1}^n` (so `P/Q` is defined there); its degree is
bounded by bounding both total degrees by `D`. With the paper's `sgn`, `f(x) = 1` iff
`P(x)/Q(x) > 0`, and `f(x) = 0` iff `P(x)/Q(x) ≤ 0`. -/
def SignRepBy {n : ℕ} (f : (Fin n → Bool) → Bool) (D : ℝ) : Prop :=
  ∃ P Q : MvPolynomial (Fin n) ℝ, (P.totalDegree : ℝ) ≤ D ∧ (Q.totalDegree : ℝ) ≤ D ∧
    ∀ x : Fin n → Bool, MvPolynomial.eval (cubePt x) Q ≠ 0 ∧
      (f x = true ↔ 0 < MvPolynomial.eval (cubePt x) P / MvPolynomial.eval (cubePt x) Q)

end SigmoidWire


