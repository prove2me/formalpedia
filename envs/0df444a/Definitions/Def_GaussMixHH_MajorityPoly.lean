-- Prove2me | Definitions.Def_GaussMixHH_MajorityPoly
-- name    : GaussMixHH_MajorityPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:07.61905+00:00
-- url     : https://prove2.me/theorems/a332dc8e-1aac-48e8-a6cd-1704d1447b2a
-- title:
--   The majority polynomial $P_k$ and Lemma 17's approximation bounds
-- statement:
--   For $k\in\mathbb N$ put $h=\lfloor (k+1)/2\rfloor$ (so $h=(k+1)/2$ for odd $k$) and
--
--   $$P_k(x)=\Pr_{B\sim\mathrm{Bin}(k,x)}[B\ge h]=\sum_{\ell=h}^{k}\binom{k}{\ell}x^\ell(1-x)^{k-\ell},$$
--
--   a real polynomial with monomial coefficients $a_j$. For $\eta>0$, $P_k$ satisfies **Lemma 17's approximation bounds** if
--
--   $$|P_k(x)-1|\le\eta/4\quad(e^{-1/4}\le x\le1),\qquad |P_k(x)|\le\eta/4\quad(0\le x\le e^{-1}).$$
--
--   Substituting $x=e^{-r^2/R^2}$ turns $P_k$ into a combination of exponential tests $e^{-jr^2/R^2}$ that approximates the indicator of $[0,R/2]$ on $[0,R/2]\cup[R,\infty)$.
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 17, p.24 (PDF p.26)

import Mathlib

open Polynomial

namespace GaussMixHH

/-!
# The majority polynomial `P_k` (Lemma 17)

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 17, p.24 (PDF p.26).

`P_k(x) = Pr_{B ∼ Bin(k, x)}[B ≥ h] = Σ_{ℓ=h}^{k} C(k, ℓ) x^ℓ (1 − x)^{k−ℓ}` with `h = (k + 1)/2`.

**Formalization Note.** `P_k` is a `Polynomial ℝ`, so its monomial coefficients `a_j` are
`(majorityPoly k).coeff j`. `h` is `(k + 1) / 2` in `ℕ`, the paper's `h` for odd `k`.
-/

/-- `h = (k + 1)/2`. -/
def majorityThreshold (k : ℕ) : ℕ := (k + 1) / 2

/-- `P_k(x) = Σ_{ℓ=h}^{k} C(k, ℓ) x^ℓ (1 − x)^{k−ℓ}`. -/
noncomputable def majorityPoly (k : ℕ) : ℝ[X] :=
  ∑ ℓ ∈ Finset.Icc (majorityThreshold k) k,
    C (k.choose ℓ : ℝ) * X ^ ℓ * (1 - X) ^ (k - ℓ)

/-- The two approximation bounds of Lemma 17 for `P_k` and accuracy `η`:
`|P_k(x) − 1| ≤ η/4` on `[e^{−1/4}, 1]` and `|P_k(x)| ≤ η/4` on `[0, e^{−1}]`. -/
def MajorityApprox (k : ℕ) (η : ℝ) : Prop :=
  (∀ x : ℝ, Real.exp (-1 / 4) ≤ x → x ≤ 1 → |(majorityPoly k).eval x - 1| ≤ η / 4) ∧
  (∀ x : ℝ, 0 ≤ x → x ≤ Real.exp (-1) → |(majorityPoly k).eval x| ≤ η / 4)

end GaussMixHH


