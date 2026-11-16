-- Prove2me | Definitions.Def_HolonomicPositivity_Robust_Supplement_Products
-- name    : HolonomicPositivity_Robust_Supplement_Products
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:53:37.711002+00:00
-- url     : https://prove2.me/theorems/4723fbfd-5b42-4492-9086-6a19b3485c68
-- title:
--   The three product sequences and coefficient robustness of Lemma 5.6
-- statement:
--   Let $\alpha,\beta,\gamma,\delta\in\mathbb R$. For natural $n$ set
--   $$g(n)=\prod_{k=1}^n\left(\frac12+\frac{1+i\alpha}{4k}\right),\qquad h(n)=\prod_{k=1}^n\left(\beta+\frac\gamma k+\frac{\gamma+\delta}{k^2}\right).$$
--   Both empty products equal one. For $v=(s,t,u)\in\mathbb R^3$ the real combination is
--   $$F_v(n)=s\,\operatorname{Re}(g(n)+\overline{g(n)})+t\,\operatorname{Re}\bigl(i(g(n)-\overline{g(n)})\bigr)+u h(n)=2s\operatorname{Re}g(n)-2t\operatorname{Im}g(n)+uh(n).$$
--   It is robustly ultimately positive in its coefficients if some $\varepsilon>0$ makes $F_w$ ultimately positive for every $w$ with $|w_j-v_j|<\varepsilon$ for all three coordinates.
--
--   This is exactly the coefficient perturbation model of Lemma 5.6, independently of a recurrence or any initial values.
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; PDF p.15 (XX:15), Lemma 5.6, equation (16), lines 514-526.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Recurrence

namespace HolonomicPositivity.Robust.Supplement

/-- The complex product g in (16), Lemma 5.6, PDF p.15; g(0)=1. -/
noncomputable def gProduct (α : ℝ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.Icc 1 n, ((1 : ℂ) / 2 + (1 + Complex.I * (α : ℂ)) / (4 * (k : ℂ)))

/-- The real product h in (16). The numerator of k⁻² is γ+δ, not δ. -/
noncomputable def hProduct (β γ δ : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (β + γ / (k : ℝ) + (γ + δ) / (k : ℝ) ^ 2)

/-- Real linear combination of g+conj(g), i(g-conj(g)), and h (PDF p.15 line 525).
The real parts express these two real-valued complex sequences without changing their values. -/
noncomputable def combination (α β γ δ : ℝ) (v : Fin 3 → ℝ) (n : ℕ) : ℝ :=
  v 0 * (gProduct α n + star (gProduct α n)).re +
  v 1 * (Complex.I * (gProduct α n - star (gProduct α n))).re +
  v 2 * hProduct β γ δ n

/-- Robustness with respect to the three combination coefficients in Lemma 5.6,
not with respect to recurrence initial values. Coordinate open balls give the usual topology. -/
def RobustCombination (α β γ δ : ℝ) (v : Fin 3 → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin 3 → ℝ,
    (∀ i, |w i - v i| < ε) → UltimatelyPositive (combination α β γ δ w)

end HolonomicPositivity.Robust.Supplement


