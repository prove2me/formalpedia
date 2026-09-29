-- Prove2me | Definitions.Def_TateCurve_TateFiltrationPrep
-- name    : TateCurve_TateFiltrationPrep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/158ff6e9-3b26-55c4-9f33-a1686f99ede1
-- title:
--   Equivariance of Tate curve series under isometric ring endomorphisms
-- statement:
--   Throughout, $K$ is a nontrivially normed field whose distance is ultrametric, and from the point where $s_1$, `pointX` and `pointY` appear, also complete. The module records how a ring endomorphism $\sigma : K \to_{+*} K$ interacts with the $q$-series entering the Tate parametrisation. A criterion, `isometry_of_forall_nnnorm`, states that $\sigma$ is an isometry as soon as $\lVert \sigma x\rVert = \lVert x\rVert$ for all $x$, and `map_tsum_of_summable` states that an isometric $\sigma$ commutes with the sum of a summable family indexed by any type. The rational functions $x(w) = w/(1-w)^2$ and $y(w) = w^2/(1-w)^3$ satisfy $\sigma(x(w)) = x(\sigma w)$ and $\sigma(y(w)) = y(\sigma w)$ for every ring endomorphism. Under the hypothesis $\sigma q = q$: each term $c_n \, q^n/(1-q^n)$ of a `coeffSum` is fixed (the coefficients being natural numbers), the terms $x(q^n u)$ and $y(q^n u)$, for $n \in \mathbb{Z}$, are sent to $x(q^n \sigma u)$ and $y(q^n \sigma u)$, and, when $\sigma$ is moreover an isometry and $\mathrm{term}\,c\,q$ is summable, $\sigma$ fixes $\mathrm{coeffSum}(c,q)$. With $\lVert q\rVert < 1$ this gives that $\sigma$ fixes $s_1(q) = \sum_n n\,q^n/(1-q^n)$ and the Tate coefficients $a_4(q) = -\sum_n 5n^3 q^n/(1-q^n)$ and $a_6(q) = -\sum_n b_n q^n/(1-q^n)$ with $b_n = (5n^3+7n^5)/12$, hence that the Weierstrass curve $\langle 1,0,0,a_4(q),a_6(q)\rangle$ is carried to itself by $\sigma$. Finally, for $q \neq 0$, $\lVert q \rVert < 1$ and $u \neq 0$, the coordinate series $X(q,u) = \sum_{n \in \mathbb{Z}} x(q^n u) - 2 s_1(q)$ and $Y(q,u) = \sum_{n \in \mathbb{Z}} y(q^n u) + s_1(q)$ satisfy $\sigma(X(q,u)) = X(q,\sigma u)$ and $\sigma(Y(q,u)) = Y(q,\sigma u)$; if in addition $\sigma u = u$, both coordinates are fixed.
--
--   **Relation to Mathlib.** The curve attached to $q$ is a term of Mathlib's `WeierstrassCurve`, and the statement about $\sigma$ is phrased through Mathlib's `WeierstrassCurve.map`; the $q$-series $a_4$, $a_6$, $s_1$ and the coordinate series are the project's own definitions.
--
--   **Where it is used.** These equivariance statements are the first half of the Tate-curve bridge used to analyse the local behaviour of the mod $p$ representation at a prime of multiplicative reduction: combined with the parametrisation of $p$-torsion points by the series $X$, $Y$, they show that an isometric endomorphism of the base field fixing $q$ and a torsion parameter $u$ fixes the corresponding point of the curve, whence the description of the action of inertia on $E[p]$ at such a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_TateFiltrationPrep.lean

import Mathlib
import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem isometry_of_forall_nnnorm {σ : K →+* K} (h : ∀ x, ‖σ x‖₊ = ‖x‖₊) : Isometry ⇑σ :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← coe_nnnorm, ← coe_nnnorm, h]

theorem map_tsum_of_summable {ι : Type*} (σ : K →+* K) (hσ : Isometry ⇑σ) {f : ι → K}
    (hf : Summable f) : σ (∑' i, f i) = ∑' i, σ (f i) := by
  have h := hf.hasSum.map σ hσ.continuous
  simpa [Function.comp] using h.tsum_eq.symm

theorem map_xfun (σ : K →+* K) (w : K) : σ (xfun w) = xfun (σ w) := by
  simp only [xfun, map_div₀, map_pow, map_sub, map_one]

theorem map_yfun (σ : K →+* K) (w : K) : σ (yfun w) = yfun (σ w) := by
  simp only [yfun, map_div₀, map_pow, map_sub, map_one]

theorem map_term (σ : K →+* K) {q : K} (hσq : σ q = q) (c : ℕ → ℕ) (n : ℕ) :
    σ (term c q n) = term c q n := by
  simp only [term, map_mul, map_natCast, map_div₀, map_pow, map_sub, map_one, hσq]

theorem map_xTerm (σ : K →+* K) {q : K} (hσq : σ q = q) (u : K) (n : ℤ) :
    σ (xTerm q u n) = xTerm q (σ u) n := by
  simp only [xTerm, map_xfun, map_mul, map_zpow₀, hσq]

theorem map_yTerm (σ : K →+* K) {q : K} (hσq : σ q = q) (u : K) (n : ℤ) :
    σ (yTerm q u n) = yTerm q (σ u) n := by
  simp only [yTerm, map_yfun, map_mul, map_zpow₀, hσq]

theorem map_coeffSum (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (c : ℕ → ℕ)
    (hsum : Summable (term c q)) : σ (coeffSum c q) = coeffSum c q := by
  have h := map_tsum_of_summable σ hσ hsum
  simp only [coeffSum]
  rw [h]
  exact tsum_congr fun n => map_term σ hσq c n

variable [CompleteSpace K]

theorem map_s₁ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (s₁ q) = s₁ q := by
  simp only [s₁]
  exact map_coeffSum σ hσ hσq _ (summable_term _ hq)

theorem map_a₄ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (a₄ q) = a₄ q := by
  simp only [a₄, map_neg]
  exact congrArg Neg.neg (map_coeffSum σ hσ hσq _ (summable_term _ hq))

theorem map_a₆ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (a₆ q) = a₆ q := by
  simp only [a₆, map_neg]
  exact congrArg Neg.neg (map_coeffSum σ hσ hσq _ (summable_term _ hq))

theorem map_curve (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    (curve q).map σ = curve q := by
  ext <;>
    simp [curve, WeierstrassCurve.map, map_a₄ σ hσ hσq hq, map_a₆ σ hσ hσq hq]

theorem map_pointX (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointX q u) = pointX q (σ u) := by
  simp only [pointX, map_sub, map_mul, map_ofNat]
  rw [map_s₁ σ hσ hσq hq, map_tsum_of_summable σ hσ (summable_xTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => map_xTerm σ hσq u n

theorem map_pointY (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointY q u) = pointY q (σ u) := by
  simp only [pointY, map_add]
  rw [map_s₁ σ hσ hσq hq, map_tsum_of_summable σ hσ (summable_yTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => map_yTerm σ hσq u n

theorem map_pointX_eq_self (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hσu : σ u = u) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointX q u) = pointX q u := by
  rw [map_pointX σ hσ hσq hq0 hq hu0, hσu]

theorem map_pointY_eq_self (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hσu : σ u = u) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointY q u) = pointY q u := by
  rw [map_pointY σ hσ hσq hq0 hq hu0, hσu]

end TateCurve


