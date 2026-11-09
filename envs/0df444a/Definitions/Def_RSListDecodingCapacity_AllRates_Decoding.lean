-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
-- name    : RSListDecodingCapacity_AllRates_Decoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:54.082326+00:00
-- url     : https://prove2.me/theorems/dd9a4786-2a77-4d80-bbde-a94f57be4678
-- title:
--   Agreement, the list-decoding list and the Hasse-derivative substitution $Q(X,P,P^{[1]},\dots,P^{[d]})$
-- statement:
--   Let $\mathbb F$ be a commutative ring (in this mission $\mathbb F=\mathbb F_q$ for a prime $q$), let $\alpha=(\alpha_1,\dots,\alpha_n)$ be evaluation points and $y=(y_1,\dots,y_n)$ a received word in $\mathbb F^n$.
--
--   1. The **agreement** of a polynomial $P\in\mathbb F[X]$ with $y$ is $\mathrm{agr}(P)=|\{i\in[n]:P(\alpha_i)=y_i\}|$.
--   2. For $k\in\mathbb N$ and a real threshold $\tau$, the **list-decoding list** is
--   $$\mathcal L_k(\alpha,y,\tau)=\{P\in\mathbb F[X]:\deg P<k,\ \mathrm{agr}(P)\ge\tau\},$$
--   with the zero polynomial included whenever it meets the agreement threshold.
--   3. For $Q\in\mathbb F[X,Y_0,\dots,Y_d]$ and $P\in\mathbb F[X]$, the substitution of $P$ and its Hasse derivatives is
--   $$Q\big(X,P(X),P^{[1]}(X),\dots,P^{[d]}(X)\big)\in\mathbb F[X],\qquad P^{[\ell]}(X)=\sum_{i\ge\ell}\binom{i}{\ell}a_iX^{i-\ell}\ \text{ for }P=\sum_i a_iX^i,$$
--   the left side of the polynomial differential equation (10).
--   4. The weights $(1,k-1,k-2,\dots,k-d-1)$ of Theorem 2.1: weight $1$ on $X$ and $k-1-j$ on $Y_j$.
--
--   These are the objects in which every statement of the mission is phrased: the goal and Theorem 4.1 output $\mathcal L_k$, and the interpolation and root-finding steps act through the substitution of item 3.
--
--   **Formalization Note** The variables of $\mathbb F[X,Y_0,\dots,Y_d]$ are indexed by `Option (Fin (d+1))` (`none` is $X$, `some j` is $Y_j$). Hasse derivatives are Mathlib's `Polynomial.hasseDeriv`, defined by the binomial coefficient formula above in every characteristic. Degrees live in `WithBot ℕ`, so the zero polynomial has degree $-\infty$ and satisfies the degree condition for every nonnegative $k$; the agreement condition is still required.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), §2, pp.12–13 (Hasse derivatives, weighted degrees, (10)); list-decoding problem p.3; Corollary 5.1, p.28

import Mathlib

namespace RSListDecodingCapacity.AllRates

open Polynomial

/-- **Agreement** of a polynomial with a received word.
Brakensiek–Chen–Putterman–Zhang–Zheng, *Algorithmic List Decoding of Reed–Solomon Codes up to
Capacity*, STOC 2027 submission #565, Corollary 5.1, p.28 ("the agreement between
`(P(α₁),…,P(αₙ))` and `(y₁,…,yₙ)`") and Proposition 3.13, p.24 ("agreeing with `y` in at least
`A` positions").

`agreement α y P` is the number of positions `i` with `P(αᵢ) = yᵢ`. -/
noncomputable def agreement {F : Type*} [CommRing F] {n : ℕ} (α y : Fin n → F) (P : F[X]) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin n => P.eval (α i) = y i).card

/-- **The list-decoding list** (p.3 and Theorem 4.1, p.26, Corollary 5.1, p.28): all univariate
polynomials `P ∈ F[X]` of degree less than `k` (the zero polynomial included) whose agreement with
the received word `y` at the evaluation points `α` is at least the real threshold `τ`. -/
def listDecodingSet {F : Type*} [CommRing F] {n : ℕ} (k : ℕ) (α y : Fin n → F) (τ : ℝ) :
    Set F[X] :=
  {P | P.degree < (k : WithBot ℕ) ∧ τ ≤ (agreement α y P : ℝ)}

/-- **Substitution of a polynomial and its Hasse derivatives** (§2, p.12–13, (10)).

The variables of `F[X, Y₀, …, Y_d]` are indexed by `Option (Fin (d+1))`: `none` is `X` and
`some j` is `Y_j`. `hasseJetEval d Q P` is `Q(X, P(X), P^{[1]}(X), …, P^{[d]}(X))`, where
`P^{[j]}` is the `j`-th Hasse derivative `∑ᵢ (i choose j) aᵢ X^{i-j}` (Mathlib's
`Polynomial.hasseDeriv`, which is defined by this coefficient formula in every characteristic). -/
noncomputable def hasseJetEval {F : Type*} [CommRing F] (d : ℕ)
    (Q : MvPolynomial (Option (Fin (d + 1))) F) (P : F[X]) : F[X] :=
  MvPolynomial.aeval (fun v : Option (Fin (d + 1)) => Option.elim v X fun j => hasseDeriv (j : ℕ) P) Q

/-- **The weights `(1, k−1, k−2, …, k−d−1)` of Theorem 2.1** (p.13): weight `1` on `X` and weight
`k − 1 − j` on `Y_j` for `j = 0, …, d`. (Theorem 2.1 assumes `k > d`, so no natural subtraction
truncates.) The weighted degree `deg_{1,k−1,…,k−d−1} Q` is Mathlib's
`MvPolynomial.weightedTotalDegree (kopWeight d k) Q`, the maximum weight of a monomial of `Q`. -/
def kopWeight (d k : ℕ) : Option (Fin (d + 1)) → ℕ :=
  fun v => Option.elim v 1 fun j => k - 1 - (j : ℕ)

end RSListDecodingCapacity.AllRates


