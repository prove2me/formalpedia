-- Prove2me | Definitions.Def_SuperBAE_Restriction_Model
-- name    : SuperBAE_Restriction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:43.709642+00:00
-- url     : https://prove2.me/theorems/f7e22809-ba27-44cf-ab7f-b07979cf2a80
-- title:
--   §2, pp. 4–6 — gl(M|N) grading, source terms Λ_i, Q-polynomials, nested BAE (2.9), energy (2.18); §4.1 deletion of two adjacent indices and eqs. (4.2)–(4.6)
-- statement:
--   This file sets up the nested Bethe ansatz equations of the homogeneous $\mathfrak{gl}(M|N)$ spin chain $(V\otimes V^*)^{\otimes L}$ and the data needed for their restriction to $\mathfrak{gl}(M-1|N-1)$.
--
--   **Grading.** Put $d = M+N$ and label the basis vectors $e_1 > \dots > e_d$. A grading assigns to each position $i\in\{1,\dots,d\}$ a parity $|i|\in\{0,1\}$ and the sign $\sigma_i = (-1)^{|i|}$. Then $M$ is the number of even positions, $N$ the number of odd positions, and the loop weight is
--   $$n = \sum_{i=1}^{d}\sigma_i = M-N .$$
--   The simple roots are $\alpha_k=\epsilon_k-\epsilon_{k+1}$, $k = 1,\dots,r$, with rank $r = d-1$.
--
--   **Source terms and $Q$-polynomials.** For a chain of length $L$,
--   $$\Lambda_i(u)=\begin{cases}(u+\sigma_1)^L(u+n/2)^L, & i=1,\\ u^L(u+n/2)^L, & 2\le i\le r,\\ u^L(u+n/2-\sigma_d)^L, & i=d.\end{cases}$$
--   For each type $k=1,\dots,r$ let $\{u^{(k)}_j\}_{j=1}^{\nu^{(k)}}$ be a finite set of pairwise distinct complex Bethe roots and $Q_k(u)=\prod_{j=1}^{\nu^{(k)}}(u-u^{(k)}_j)$, with $Q_0=Q_d=1$.
--
--   **Bethe ansatz equations (2.9).** For $k=1,\dots,r$ and every root $u=u^{(k)}_j$:
--   $$\frac{\Lambda_k(u)}{\Lambda_{k+1}(u)} = -\sigma_k\sigma_{k+1}\,\frac{Q_{k-1}(u)\,Q_k(u+\sigma_{k+1})\,Q_{k+1}(u-\sigma_{k+1})}{Q_{k-1}(u+\sigma_k)\,Q_k(u-\sigma_k)\,Q_{k+1}(u)} .$$
--   A family of root sets is a *solution* if all these equations hold. It is *regular* if at every root $u$ of type $k$ the quantities $\Lambda_k(u)$, $\Lambda_{k+1}(u)$, $Q_{k-1}(u+\sigma_k)$, $Q_k(u-\sigma_k)$, $Q_{k+1}(u)$ are nonzero.
--
--   **Energy.** With the variables (2.11) $x^{(k)}_j = i\,u^{(k)}_j + \tfrac{i}{2}\sum_{l=1}^{k}\sigma_l$, the energy (2.18) is
--   $$E = -\sum_{j=1}^{\nu^{(1)}}\frac{\sigma_1}{(x^{(1)}_j)^2+1/4} - \sum_{j=1}^{\nu^{(r)}}\frac{\sigma_d}{(x^{(r)}_j)^2+1/4} .$$
--
--   **Deletion (§4.1).** For an index $k$, the reduced grading removes positions $k,k+1$ (position $i\ge k$ of the new grading is position $i+2$ of the old one), and the reduced root family removes types $k,k+1$ (type $i\ge k$ of the new family is type $i+2$ of the old one). The reduced system is the same Bethe system for $d-2$ positions, with its own source terms and its own loop weight.
--
--   **Equations (4.2), (4.3), (4.4), (4.6).** For $u$ a complex number,
--   $$\text{(4.2)}\quad \frac{\sigma_{k-1}\Lambda_{k-1}(u)}{\sigma_k\Lambda_k(u)} = -\frac{Q_{k-2}(u)Q_{k-1}(u+\sigma_k)Q_k(u-\sigma_k)}{Q_{k-2}(u+\sigma_{k-1})Q_{k-1}(u-\sigma_{k-1})Q_k(u)},$$
--   $$\text{(4.3)}\quad 1 = \frac{Q_{k-1}(u)Q_{k+1}(u+\sigma_k)}{Q_{k-1}(u+\sigma_k)Q_{k+1}(u)},$$
--   $$\text{(4.4)}\quad \frac{\sigma_k\Lambda_{k+1}(u)}{\sigma_{k+2}\Lambda_{k+2}(u)} = \frac{Q_k(u)Q_{k+1}(u+\sigma_{k+2})Q_{k+2}(u-\sigma_{k+2})}{Q_k(u-\sigma_k)Q_{k+1}(u+\sigma_k)Q_{k+2}(u)},$$
--   $$\text{(4.6)}\quad \frac{\sigma_{k-1}\Lambda_{k-1}(u)}{\sigma_{k+2}\Lambda_{k+2}(u)} = -\frac{Q_{k-2}(u)Q_{k-1}(u+\sigma_{k+2})Q_{k+2}(u-\sigma_{k+2})}{Q_{k-2}(u+\sigma_{k-1})Q_{k-1}(u-\sigma_{k-1})Q_{k+2}(u)} .$$
--
--   These objects are shared by every statement of the mission: the restriction theorem compares the Bethe system of one grading with the same Bethe system of the deleted grading.
--
--   **Formalization Note.** Positions and types are natural numbers read on $1,\dots,d$ and $1,\dots,d-1$; a grading is a Boolean function (`true` = odd) and $\sigma_i\in\{\pm1\}\subset\mathbb{C}$. Root sets are `Finset ℂ`, which encodes "no two Bethe roots of the same type coincide" (p. 5). $Q_k$ is defined to be $1$ outside $1\le k\le d-1$, so $Q_0=Q_d=1$ and the natural-number subtraction $k-1$, $k-2$ at the boundary lands on $Q_0=1$. The equations are in division form over $\mathbb{C}$; since Lean's $x/0=0$, the theorems carry the regularity predicate. Only the homogeneous chain ($y_k=y_{\bar k}=0$) is modelled.
-- source:
--   Candu, Continuum Limit of gl(M|N) Spin Chains, arXiv:1012.0050v1, pp. 4–6 (PDF 5–7), Λ_i and Q_k before (2.8), eqs. (2.9), (2.11), (2.18); §4.1 pp. 17–18 (PDF 18–19), eqs. (4.2)–(4.4), (4.6)

import Mathlib

namespace SuperBAE.Restriction

open scoped BigOperators

/-- The grading sign σ_i = (−1)^{|i|} of the basis vector e_i; `odd i = true` iff e_i is
fermionic (|i| = 1). Only read on positions 1..d, d = M + N. -/
def sgn (odd : ℕ → Bool) (i : ℕ) : ℂ := if odd i then -1 else 1

/-- M = number of even (bosonic) positions among 1..d. -/
def numEven (odd : ℕ → Bool) (d : ℕ) : ℕ :=
  ((Finset.Icc 1 d).filter (fun i => odd i = false)).card

/-- N = number of odd (fermionic) positions among 1..d. -/
def numOdd (odd : ℕ → Bool) (d : ℕ) : ℕ :=
  ((Finset.Icc 1 d).filter (fun i => odd i = true)).card

/-- The loop weight n = Σ_{i=1}^{d} σ_i = M − N. -/
def nLoop (odd : ℕ → Bool) (d : ℕ) : ℂ := ∑ i ∈ Finset.Icc 1 d, sgn odd i

/-- The source terms Λ_i(u) of p. 4 for the homogeneous chain of length L:
Λ_1 = (u + σ_1)^L (u + n/2)^L, Λ_i = u^L (u + n/2)^L for 2 ≤ i ≤ r = d − 1,
Λ_d = u^L (u + n/2 − σ_d)^L. -/
noncomputable def lam (L : ℕ) (odd : ℕ → Bool) (d i : ℕ) (u : ℂ) : ℂ :=
  if i = 1 then (u + sgn odd 1) ^ L * (u + nLoop odd d / 2) ^ L
  else if i = d then u ^ L * (u + nLoop odd d / 2 - sgn odd d) ^ L
  else u ^ L * (u + nLoop odd d / 2) ^ L

/-- The Q-polynomial Q_k(u) = ∏_j (u − u^{(k)}_j) for root types 1 ≤ k ≤ r = d − 1, and
Q_k = 1 otherwise (in particular Q_0 = Q_{M+N} = 1). -/
def Q (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ) (u : ℂ) : ℂ :=
  if 1 ≤ k ∧ k ≤ d - 1 then ∏ x ∈ roots k, (u - x) else 1

/-- The Bethe ansatz equation (2.9) of type k at the root u, in division form:
Λ_k(u)/Λ_{k+1}(u) = −σ_kσ_{k+1} Q_{k−1}(u) Q_k(u+σ_{k+1}) Q_{k+1}(u−σ_{k+1})
  / [Q_{k−1}(u+σ_k) Q_k(u−σ_k) Q_{k+1}(u)]. -/
def bae (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ) (u : ℂ) : Prop :=
  lam L odd d k u / lam L odd d (k + 1) u =
    -(sgn odd k * sgn odd (k + 1)) *
      (Q d roots (k - 1) u * Q d roots k (u + sgn odd (k + 1)) *
          Q d roots (k + 1) (u - sgn odd (k + 1))) /
      (Q d roots (k - 1) (u + sgn odd k) * Q d roots k (u - sgn odd k) * Q d roots (k + 1) u)

/-- The roots (Finsets of pairwise distinct Bethe roots per type) solve the whole nested
system (2.9): for every type k = 1, …, r = d − 1 and every root u of type k. -/
def IsBAESolution (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (d - 1), ∀ u ∈ roots k, bae L odd d roots k u

/-- Non-degeneracy (added): at every root u of type k the source terms Λ_k(u), Λ_{k+1}(u)
and the denominator factors Q_{k−1}(u+σ_k), Q_k(u−σ_k), Q_{k+1}(u) of (2.9) are nonzero. -/
def Regular (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (d - 1), ∀ u ∈ roots k,
    lam L odd d k u ≠ 0 ∧ lam L odd d (k + 1) u ≠ 0 ∧
      Q d roots (k - 1) (u + sgn odd k) ≠ 0 ∧ Q d roots k (u - sgn odd k) ≠ 0 ∧
      Q d roots (k + 1) u ≠ 0

/-- The variables (2.11): x^{(k)} = i u^{(k)} + (i/2) Σ_{l=1}^{k} σ_l. -/
noncomputable def xvar (odd : ℕ → Bool) (k : ℕ) (u : ℂ) : ℂ :=
  Complex.I * u + Complex.I / 2 * ∑ l ∈ Finset.Icc 1 k, sgn odd l

/-- The energy (2.18):
E = −Σ_{u ∈ type 1} σ_1/(x^{(1)}(u)² + 1/4) − Σ_{u ∈ type r} σ_d/(x^{(r)}(u)² + 1/4). -/
noncomputable def energy (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) : ℂ :=
  -(∑ u ∈ roots 1, sgn odd 1 / (xvar odd 1 u ^ 2 + 1 / 4)) -
    ∑ u ∈ roots (d - 1), sgn odd d / (xvar odd (d - 1) u ^ 2 + 1 / 4)

/-- Delete grading positions k and k + 1 (§4.1): position i ≥ k of the new grading is
position i + 2 of the old one. -/
def delGrading (k : ℕ) (odd : ℕ → Bool) : ℕ → Bool :=
  fun i => if i < k then odd i else odd (i + 2)

/-- Delete root types k and k + 1 (§4.1): type i ≥ k of the new system is type i + 2 of the
old one (so old type k + 2 becomes type k). -/
def delRoots (k : ℕ) (roots : ℕ → Finset ℂ) : ℕ → Finset ℂ :=
  fun i => if i < k then roots i else roots (i + 2)

/-- Eq. (4.2), the BAE for α_{k−1} at u, written as on p. 17:
σ_{k−1}Λ_{k−1}(u)/(σ_kΛ_k(u)) = −Q_{k−2}(u)Q_{k−1}(u+σ_k)Q_k(u−σ_k)
  / [Q_{k−2}(u+σ_{k−1})Q_{k−1}(u−σ_{k−1})Q_k(u)]. -/
def eq4_2 (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ) (u : ℂ) : Prop :=
  sgn odd (k - 1) * lam L odd d (k - 1) u / (sgn odd k * lam L odd d k u) =
    -(Q d roots (k - 2) u * Q d roots (k - 1) (u + sgn odd k) * Q d roots k (u - sgn odd k) /
      (Q d roots (k - 2) (u + sgn odd (k - 1)) * Q d roots (k - 1) (u - sgn odd (k - 1)) *
        Q d roots k u))

/-- Eq. (4.3), the BAE for α_k at u, as on p. 17:
1 = Q_{k−1}(u)Q_{k+1}(u+σ_k) / [Q_{k−1}(u+σ_k)Q_{k+1}(u)]. -/
def eq4_3 (d : ℕ) (odd : ℕ → Bool) (roots : ℕ → Finset ℂ) (k : ℕ) (u : ℂ) : Prop :=
  1 = Q d roots (k - 1) u * Q d roots (k + 1) (u + sgn odd k) /
      (Q d roots (k - 1) (u + sgn odd k) * Q d roots (k + 1) u)

/-- Eq. (4.4), the BAE for α_{k+1} at u, as on p. 17:
σ_kΛ_{k+1}(u)/(σ_{k+2}Λ_{k+2}(u)) = Q_k(u)Q_{k+1}(u+σ_{k+2})Q_{k+2}(u−σ_{k+2})
  / [Q_k(u−σ_k)Q_{k+1}(u+σ_k)Q_{k+2}(u)]. -/
def eq4_4 (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ) (u : ℂ) : Prop :=
  sgn odd k * lam L odd d (k + 1) u / (sgn odd (k + 2) * lam L odd d (k + 2) u) =
    Q d roots k u * Q d roots (k + 1) (u + sgn odd (k + 2)) *
        Q d roots (k + 2) (u - sgn odd (k + 2)) /
      (Q d roots k (u - sgn odd k) * Q d roots (k + 1) (u + sgn odd k) * Q d roots (k + 2) u)

/-- Eq. (4.6), the product of the BAE for α_{k−1} and α_{k+1} at u, as on p. 18:
σ_{k−1}Λ_{k−1}(u)/(σ_{k+2}Λ_{k+2}(u)) = −Q_{k−2}(u)Q_{k−1}(u+σ_{k+2})Q_{k+2}(u−σ_{k+2})
  / [Q_{k−2}(u+σ_{k−1})Q_{k−1}(u−σ_{k−1})Q_{k+2}(u)]. -/
def eq4_6 (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ) (u : ℂ) : Prop :=
  sgn odd (k - 1) * lam L odd d (k - 1) u / (sgn odd (k + 2) * lam L odd d (k + 2) u) =
    -(Q d roots (k - 2) u * Q d roots (k - 1) (u + sgn odd (k + 2)) *
          Q d roots (k + 2) (u - sgn odd (k + 2)) /
      (Q d roots (k - 2) (u + sgn odd (k - 1)) * Q d roots (k - 1) (u - sgn odd (k - 1)) *
        Q d roots (k + 2) u))

end SuperBAE.Restriction


