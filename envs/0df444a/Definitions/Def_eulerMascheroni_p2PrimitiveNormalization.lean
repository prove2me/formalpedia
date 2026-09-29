-- Prove2me | Definitions.Def_eulerMascheroni_p2PrimitiveNormalization
-- name    : eulerMascheroni_p2PrimitiveNormalization
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-12T19:37:29.62221+00:00
-- url     : https://prove2.me/theorems/dd6e6396-04ac-4df4-83f9-25fee4784b27
-- title:
--   Primitive integer normalization of the P2 rational approximants
-- statement:
--   For the rational approximants $P_n,Q_n$ of the P2 family, write the reduced fraction
--
--   $$P_n/Q_n=b_n/a_n,\qquad a_n>0,\quad \gcd(a_n,b_n)=1.$$
--
--   Define the integer numerator $b_n$, positive natural denominator $a_n$, and real multiplier
--
--   $$c_n=a_n/Q_n.$$
--
--   The predicate `PrimitiveSaving` records the following candidate condition on these explicit sequences: for every $\varepsilon>0$ and every $N\in\mathbb N$, some $n\ge N$ satisfies
--
--   $$|\sin(\operatorname{phase}(n+1))|\ge\tfrac12,
--   \qquad c_{n+1}\operatorname{fModel}(n+1)<\varepsilon.$$
--
--   The two inequalities must hold at the same indices. This definition does not assert the predicate. Its truth is an open, method-specific research question; the elementary normalization and its conditional consequences can be proved without assuming that this question has a positive answer.
-- source:
--   Derived auxiliary results for the p=2, x=1 family in Van Assche–Wolfs, Rational approximation of Euler’s constant using multiple orthogonal polynomials, arXiv:2404.09799v3, Section 5, displayed binomial formula for F_(n;2)^(I|p), https://arxiv.org/html/2404.09799v3#S5. The reduced-fraction normalization and conditional subsequence criterion are elementary deductions supplied here, not named statements or arithmetic-saving claims in that paper.

import Definitions.Def_eulerMascheroni_p2Approximation

namespace EulerMascheroni.P2

def primitiveP (n : ℕ) : ℤ := (P n / Q n).num
def primitiveQ (n : ℕ) : ℕ := (P n / Q n).den
noncomputable def primitiveScale (n : ℕ) : ℝ := (primitiveQ n : ℝ) / (Q n : ℝ)

/-- A candidate arithmetic obligation, not an asserted theorem. The phase and
small primitive envelope must occur at the same arbitrarily large indices. -/
def PrimitiveSaving : Prop := ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
  ∃ n : ℕ, N ≤ n ∧ (1/2 : ℝ) ≤ |Real.sin (phase (n+1))| ∧
    primitiveScale (n+1) * fModel (n+1) < ε

end EulerMascheroni.P2


