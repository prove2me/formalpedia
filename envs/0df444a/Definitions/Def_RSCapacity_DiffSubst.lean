-- Prove2me | Definitions.Def_RSCapacity_DiffSubst
-- name    : RSCapacity_DiffSubst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:47.150218+00:00
-- url     : https://prove2.me/theorems/59604afc-0f5d-4fe6-9d85-848dc1dbdeea
-- title:
--   Hasse derivatives and the differential substitution $Q(X,P,P^{[1]},\dots,P^{[r]})$
-- statement:
--   For a polynomial $P\in F[X]$ over a field $F$, the $j$-th **Hasse derivative** $P^{[j]}$ is defined by
--   $$P(X+T)=\sum_{j\ge 0}P^{[j]}(X)\,T^j .$$
--   For $Q\in F[X,Y_0,\dots,Y_r]$ and $P\in F[X]$, the **differential substitution** is the univariate polynomial
--   $$Q(X,P,P^{[1]},\dots,P^{[r]})\in F[X],$$
--   obtained by substituting $Y_j\mapsto P^{[j]}$. Two degree notions on $F[X,Y_0,\dots,Y_r]$ are used: the **differential weighted degree** $\deg_{(1,K-1,K-2,\dots,K-r-1)}Q$, which gives $X$ weight $1$ and $Y_j$ weight $K-1-j$, and the **total $Y$-degree** $\deg^{\mathrm{tot}}_Y Q$, which gives $X$ weight $0$ and every $Y_j$ weight $1$.
--
--   A polynomial $P$ of degree below $K$ solves the differential equation of $Q$ when $Q(X,P,P^{[1]},\dots,P^{[r]})=0$; the decoders of the mission find all such $P$.
--
--   **Formalization Note** $F[X,Y_0,\dots,Y_r]$ is `MvPolynomial (Fin (r + 2)) F` with variable $0$ for $X$ and variable $j+1$ for $Y_j$. $P^{[j]}$ is Mathlib's `Polynomial.hasseDeriv j P`. The weights are natural numbers; the paper always has $r<K$, so $K-1-j\ge0$.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), §3.1, p.11 (PDF 13), Equation (11); Lemma 4.1, p.13 (PDF 15); Corollary 4.8, p.19 (PDF 21)

import Mathlib

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-!
# Hasse derivatives and the differential substitution Q(X, P, P^{[1]}, …, P^{[r]})

Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): §3.1, p.11
(PDF 13), Equation (11): P(X + T) = ∑_{j ≥ 0} P^{[j]}(X) T^j; Lemma 4.1, p.13 (PDF 15) (the
weighted degree deg_{(1,K−1,K−2,…,K−r−1)}); Corollary 4.8, p.19 and Proposition 6.2, p.23
(deg^tot_Y).

**Formalization Note.**
* F[X, Y_0, …, Y_r] is `MvPolynomial (Fin (r + 2)) F`: variable `0` is X and variable `j + 1` is
  Y_j (0 ≤ j ≤ r).
* P^{[j]} is Mathlib's `Polynomial.hasseDeriv j P`, which satisfies (11).
* deg_X Q is `MvPolynomial.degreeOf 0 Q`, deg_{Y_j} Q is `degreeOf (j + 1) Q`.
* The differential weight gives X weight 1 and Y_j weight K − 1 − j (natural numbers; the paper
  always has r < K, so K − 1 − j ≥ 0). deg_{(1,K−1,…,K−r−1)} Q is `weightedTotalDegree'` with
  this weight, which is `⊥` for Q = 0, so the zero polynomial satisfies every strict bound
  (p.10).
* deg^tot_Y Q is the weighted total degree with weight 0 on X and 1 on every Y_j.
-/

/-- Q(X, P, P^{[1]}, …, P^{[r]}) ∈ F[X]: substitute X ↦ X and Y_j ↦ P^{[j]}. -/
noncomputable def diffEval {F : Type*} [Field F] {r : ℕ} (Q : MvPolynomial (Fin (r + 2)) F)
    (P : F[X]) : F[X] :=
  MvPolynomial.aeval
    (Fin.cases (motive := fun _ => F[X]) X (fun j : Fin (r + 1) => hasseDeriv (j : ℕ) P)) Q

/-- The weight (1, K − 1, K − 2, …, K − r − 1) on (X, Y_0, Y_1, …, Y_r). -/
def diffWeight (K r : ℕ) : Fin (r + 2) → ℕ :=
  Fin.cases 1 (fun j : Fin (r + 1) => K - 1 - (j : ℕ))

/-- The weight (0, 1, …, 1) on (X, Y_0, …, Y_r); its weighted total degree is deg^tot_Y. -/
def yWeight (r : ℕ) : Fin (r + 2) → ℕ :=
  Fin.cases 0 (fun _ : Fin (r + 1) => 1)

end RSCapacity


