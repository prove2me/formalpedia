-- Prove2me | Definitions.Def_AlbouyKaloshin_CentralConfigurations
-- name    : AlbouyKaloshin_CentralConfigurations
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T20:26:17.107955+00:00
-- url     : https://prove2.me/theorems/f64f78b4-57df-48a5-8c6f-7740f29751db
-- title:
--   Central configurations of the planar $n$-body problem
-- statement:
--   Definitions for the planar $n$-body central configurations of Albouy–Kaloshin (2012). Bodies are indexed by $k\in\{0,\dots,n-1\}$ (the paper's bodies $1,2,\dots$ are indices $0,1,\dots$); write $x_{kl}=x_l-x_k$, $y_{kl}=y_l-y_k$.
--
--   1. **Positive normalized central configuration** (Definition 1, `PosNormalizedCC n m`), for real masses $m_k$: a pair $(x,y)\in\mathbb R^n\times\mathbb R^n$ with all $r_{kl}=\sqrt{x_{kl}^2+y_{kl}^2}>0$ ($k\ne l$), satisfying for every $k$
--   $$x_k=\sum_{l\ne k} m_l\,r_{kl}^{-3}(x_k-x_l),\qquad y_k=\sum_{l\ne k} m_l\,r_{kl}^{-3}(y_k-y_l),$$
--   and the normalisation $y_{12}=0$ (in Lean `y 1 - y 0 = 0`).
--   2. **Normalized central configuration** (Definition 2, `NormalizedCC n m`), for complex masses: a complex solution $(x,y,\delta)$ of system (4), where $\delta=(\delta_{kl})$ is symmetric with zero diagonal, $\delta_{kl}^2(x_{kl}^2+y_{kl}^2)=1$ for $k\ne l$,
--   $$x_k=\sum_{l\ne k} m_l\,\delta_{kl}^3(x_k-x_l),\qquad y_k=\sum_{l\ne k} m_l\,\delta_{kl}^3(y_k-y_l),\qquad y_{12}=0.$$
--   3. **Real normalized central configuration** (Definition 2, `RealNormalizedCC n m`): a normalized central configuration with all $x_k,y_k$ real.
--   4. **Potential** (6), `potential n m`: $U=\sum_{k<l} m_km_l\delta_{kl}$.
--   5. **No zero sub-mass** (standing hypothesis of Section 2, `NoZeroSubMass n m`): $\sum_{k\in I}m_k\ne0$ for every nonempty $I\subseteq\{0,\dots,n-1\}$.
--   6. **Zero locus in the mass space** (`massZeroLocus I`): for an ideal $I\subseteq\mathbb R[m_1,\dots,m_5]$, the set of $m\in\mathbb R^5$ at which every polynomial in $I$ vanishes.
--
--   These are the objects in which the goal (Theorem 2) and every milestone of the mission are stated.
--
--   **Formalization Note** The symmetric, zero-diagonal array $\delta$ encodes the $n(n-1)/2$ unknowns $\delta_{kl}$ ($k<l$) of the paper. The definitions require $n\ne0$ so that the indices $0$ and $1$ exist; for $n=1$ they coincide and the normalisation is vacuous.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 536 Definition 1; p. 540 Definition 2; p. 539 (standing mass hypothesis); p. 541 eq. (6)

import Mathlib

/-!
# Central configurations of the planar `n`-body problem

Definitions from A. Albouy and V. Kaloshin, *Finiteness of central configurations of five
bodies in the plane*, Ann. of Math. 176 (2012), 535–588.

Bodies are indexed by `Fin n`; the paper's bodies `1` and `2` are the indices `0` and `1`.
-/

namespace AlbouyKaloshin

/-- Definition 1 (p. 536): a *positive normalized central configuration* of the planar
`n`-body problem with masses `m`. A configuration is a pair `(x, y)` of coordinate vectors,
body `k` sitting at `(x k, y k) ∈ ℝ²`. It is required that all mutual distances
`r_kl = √((x_l - x_k)² + (y_l - y_k)²)` are positive, that system (1) holds, i.e.
`(x_k, y_k) = ∑_{l ≠ k} m_l r_kl⁻³ (x_k - x_l, y_k - y_l)` for every `k`, and that the
rotation freedom is removed by `y₁₂ = y₂ - y₁ = 0`. -/
def PosNormalizedCC (n : ℕ) [NeZero n] (m : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {q | (∀ k l : Fin n, k ≠ l →
        0 < Real.sqrt ((q.1 l - q.1 k) ^ 2 + (q.2 l - q.2 k) ^ 2)) ∧
    (∀ k : Fin n, q.1 k = ∑ l ∈ Finset.univ.erase k,
        m l * (Real.sqrt ((q.1 l - q.1 k) ^ 2 + (q.2 l - q.2 k) ^ 2))⁻¹ ^ 3 * (q.1 k - q.1 l)) ∧
    (∀ k : Fin n, q.2 k = ∑ l ∈ Finset.univ.erase k,
        m l * (Real.sqrt ((q.1 l - q.1 k) ^ 2 + (q.2 l - q.2 k) ^ 2))⁻¹ ^ 3 * (q.2 k - q.2 l)) ∧
    q.2 1 - q.2 0 = 0}

/-- Definition 2 (p. 540): a *normalized central configuration* is a complex solution of the
polynomial system (4) with (possibly complex) masses `m`. A point is a triple `(x, y, δ)`:
`x k, y k ∈ ℂ` are the coordinates of body `k`, and `δ k l` (for `k ≠ l`) is an inverse of the
mutual distance, subject to `δ_kl² ((x_l - x_k)² + (y_l - y_k)²) = 1`. The array `δ` is
required to be symmetric with zero diagonal, so that it carries exactly the `n(n-1)/2`
unknowns `δ_kl`, `k < l`, of the paper. The equations are
`x_k = ∑_{l ≠ k} m_l δ_kl³ (x_k - x_l)`, `y_k = ∑_{l ≠ k} m_l δ_kl³ (y_k - y_l)`, and
`y₁₂ = y₂ - y₁ = 0`. -/
def NormalizedCC (n : ℕ) [NeZero n] (m : Fin n → ℂ) :
    Set ((Fin n → ℂ) × (Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
  {Q | (∀ k : Fin n, Q.2.2 k k = 0) ∧
    (∀ k l : Fin n, Q.2.2 k l = Q.2.2 l k) ∧
    (∀ k l : Fin n, k ≠ l →
        Q.2.2 k l ^ 2 * ((Q.1 l - Q.1 k) ^ 2 + (Q.2.1 l - Q.2.1 k) ^ 2) = 1) ∧
    (∀ k : Fin n, Q.1 k = ∑ l ∈ Finset.univ.erase k, m l * Q.2.2 k l ^ 3 * (Q.1 k - Q.1 l)) ∧
    (∀ k : Fin n, Q.2.1 k =
        ∑ l ∈ Finset.univ.erase k, m l * Q.2.2 k l ^ 3 * (Q.2.1 k - Q.2.1 l)) ∧
    Q.2.1 1 - Q.2.1 0 = 0}

/-- Definition 2 (p. 540): a *real normalized central configuration* is a normalized central
configuration all of whose position coordinates `x k, y k` are real (zero imaginary part);
the inverse distances `δ k l` are not required to be positive. -/
def RealNormalizedCC (n : ℕ) [NeZero n] (m : Fin n → ℂ) :
    Set ((Fin n → ℂ) × (Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
  {Q | Q ∈ NormalizedCC n m ∧ ∀ k : Fin n, (Q.1 k).im = 0 ∧ (Q.2.1 k).im = 0}

/-- The Newtonian potential (6): `U = ∑_{k < l} m_k m_l δ_kl`, as a function of a point
`(x, y, δ)`. -/
noncomputable def potential (n : ℕ) (m : Fin n → ℂ)
    (Q : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → Fin n → ℂ)) : ℂ :=
  ∑ k : Fin n, ∑ l : Fin n, if k < l then m k * m l * Q.2.2 k l else 0

/-- The standing hypothesis of Section 2 (p. 539) on the masses: no nonempty subset of the
bodies has total mass zero. -/
def NoZeroSubMass (n : ℕ) (m : Fin n → ℂ) : Prop :=
  ∀ I : Finset (Fin n), I.Nonempty → ∑ k ∈ I, m k ≠ 0

/-- The real zero locus in the mass space `ℝ⁵` of an ideal of real polynomials in the five
masses: the closed algebraic subset it defines. -/
def massZeroLocus (I : Ideal (MvPolynomial (Fin 5) ℝ)) : Set (Fin 5 → ℝ) :=
  {m | ∀ p ∈ I, MvPolynomial.eval m p = 0}

end AlbouyKaloshin


