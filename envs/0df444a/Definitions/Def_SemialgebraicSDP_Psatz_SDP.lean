-- Prove2me | Definitions.Def_SemialgebraicSDP_Psatz_SDP
-- name    : SemialgebraicSDP_Psatz_SDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:02.802295+00:00
-- url     : https://prove2.me/theorems/0c4454b6-f003-4e4e-a781-b05c10f18477
-- title:
--   The degree-$d$ Positivstellensatz SDP of the proof of Theorem 5.1
-- statement:
--   Let $f_1,\dots,f_s$, $g_1,\dots,g_t$, $h_1,\dots,h_u\in\mathbb R[x_1,\dots,x_n]$ describe the system (4.4), and let $d\in\mathbb N$ be the level. Put
--   $$
--   G=\sum_{k=1}^t\deg g_k,\qquad N(d)=d\,(2G+1),\qquad g_d=\prod_{k=1}^t g_k^{2d},
--   $$
--   so $g_d=1$ when $t=0$ (empty product). The **degree-$d$ Positivstellensatz SDP** is feasible when there exist
--
--   1. for every subset $T\subseteq\{1,\dots,s\}$ a positive semidefinite real matrix $Q_T$ indexed by the monomials of total degree at most $N(d)$, giving the sum-of-squares multiplier $p_T=z^TQ_Tz$ of the product $\prod_{j\in T}f_j$, and
--   2. polynomials $q_1,\dots,q_u$ of total degree at most $2N(d)$,
--
--   such that
--   $$
--   \sum_{T\subseteq\{1,\dots,s\}} p_T\prod_{j\in T}f_j\;+\;g_d^{\,2}\;+\;\sum_{\ell=1}^u q_\ell h_\ell\;=\;0 .
--   $$
--   The unknowns are the entries of the matrices $Q_T$ and the coefficients of the $q_\ell$, finitely many; the identity is a system of linear equations in them, so the problem is a semidefinite feasibility problem. This is the SDP described in the proof of Theorem 5.1: $f=p_0+p_1f_1+\dots+p_{12\dots s}f_1\cdots f_s$, $g=\prod_i g_i^{2m}$, $h=q_1h_1+\dots+q_uh_u$, with the constraint $f+g^2+h=0$.
--
--   **Formalization Note** The page leaves the degree bookkeeping free ("choosing $m$ such that the degree of $g$ is greater than or equal to $d$", "a degree $d_2\ge d$, $d_2\ge\deg(g)$"). Here $m=d$ and the multipliers have degree at most $d_2=2N(d)=2d(2G+1)$, which satisfies $d_2\ge d$ and $d_2\ge\deg g_d=2dG$ for every system. The literal minimum $d_2=\max(d,\deg g)$ is not used: $g^2$ has degree $2\deg g$, so with that choice the identity can be infeasible at every level.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 306, proof of Theorem 5.1

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

namespace SemialgebraicSDP.Psatz

open MvPolynomial

/-- The half-degree `N(d) = d · (2G + 1)` of the Gram matrices at level `d` of the Positivstellensatz
SDP, where `G = ∑ₖ deg gₖ`. The multipliers then have degree at most `d₂ = 2 N(d)`, which satisfies
the bounds `d₂ ≥ d` and `d₂ ≥ deg g` printed in the proof of Theorem 5.1 (p. 306) for
`g = ∏ₖ gₖ^{2d}`. -/
def sdpHalfDegree {n t : ℕ} (g : Fin t → MvPolynomial (Fin n) ℝ) (d : ℕ) : ℕ :=
  d * (2 * ∑ k, (g k).totalDegree + 1)

/-- Feasibility of the degree-`d` Positivstellensatz SDP of the proof of Theorem 5.1 (p. 306) for the
system (4.4) given by `f` (inequalities `fⱼ ≥ 0`), `g` (inequations `gₖ ≠ 0`) and `h` (equations
`h_ℓ = 0`). With `N = sdpHalfDegree g d` and `g_d = ∏ₖ gₖ^{2d}` (`= 1` when `t = 0`), it asks for
* one positive semidefinite matrix `Q_T`, indexed by the monomials of degree `≤ N`, for every subset
  `T ⊆ {1, …, s}` (the sum-of-squares multiplier `p_T = zᵀ Q_T z` of `∏_{j ∈ T} fⱼ`), and
* polynomials `q_ℓ` of total degree `≤ 2N` (the ideal multipliers),
such that `∑_T p_T ∏_{j ∈ T} fⱼ + g_d² + ∑_ℓ q_ℓ h_ℓ = 0`. The unknowns are the entries of the `Q_T`
and the coefficients of the `q_ℓ`, finitely many; the constraint is affine in them. -/
def PsatzSDPFeasible {n s t u : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (g : Fin t → MvPolynomial (Fin n) ℝ) (h : Fin u → MvPolynomial (Fin n) ℝ) (d : ℕ) : Prop :=
  ∃ (Q : Finset (Fin s) → Matrix (Mon n (sdpHalfDegree g d)) (Mon n (sdpHalfDegree g d)) ℝ)
    (q : Fin u → MvPolynomial (Fin n) ℝ),
    (∀ T, (Q T).PosSemidef) ∧
    (∀ l, (q l).totalDegree ≤ 2 * sdpHalfDegree g d) ∧
    ∑ T : Finset (Fin s), gramPoly (Q T) * ∏ j ∈ T, f j + (∏ k, g k ^ (2 * d)) ^ 2
      + ∑ l, q l * h l = 0

end SemialgebraicSDP.Psatz


