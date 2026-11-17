-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_HasL2Approx
-- name    : EffRobustLearn_Supplement_HasL2Approx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:15:12.486299+00:00
-- url     : https://prove2.me/theorems/60a41986-4490-4069-9a3a-98e2e0ee5bfb
-- title:
--   $L_2(D)$ polynomial approximators of degree $\ell$ (Definition 4.2)
-- statement:
--   Let $D$ be a distribution on $\mathbb R^d$ and $\mathcal C$ a class of concepts $c:\mathbb R^d\to\{\pm1\}$. The class has **$e$-approximate degree $\ell$** with respect to $D$ if for every $c\in\mathcal C$ there is a real polynomial $q$ of degree at most $\ell$ with
--   $$
--   \mathbb E_{x\sim D}\big[(c(x)-q(x))^2\big]\le e .
--   $$
--
--   This is the standard $L_2$ polynomial approximation notion of Kalai, Klivans, Mansour and Servedio. Theorem 4.7 assumes it with $e=\varepsilon^2/1536^2$.
--
--   **Formalization Note** Concepts are Boolean-valued functions read as $\pm1$ through the base mission's `toPM`. The expectation is a lower Lebesgue integral in $[0,\infty]$, so a non-square-integrable error never satisfies the bound. Definition 4.2 restricts $e$ to $(0,1)$; the theorems only pass such values.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition 4.2, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

/-- `L2(D)` polynomial approximators, Definition 4.2 of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.18 (PDF p.19):
the class `C` has `e`-approximate degree `ℓ` with respect to `D` if every `c ∈ C` has a polynomial
`q` of degree at most `ℓ` with `E_{x∼D}[(c(x) − q(x))²] ≤ e`.

**Formalization Note.**
* Concepts are `ℝ^d → Bool`, read as `±1` through the published `toPM`; "degree `ℓ`" is degree at most `ℓ`.
* The expectation is a lower Lebesgue integral in `ℝ≥0∞`, so a non-integrable square error is `⊤` and never
  satisfies the bound.
* Definition 4.2 restricts the error to `(0, 1)`; every theorem passes such a value (`ε²/1536²`). -/
def HasL2Approx {d : ℕ} (D : Measure (Fin d → ℝ)) (C : Set ((Fin d → ℝ) → Bool)) (ℓ : ℕ)
    (e : ℝ) : Prop :=
  ∀ c ∈ C, ∃ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ ℓ ∧
    ∫⁻ x, ENNReal.ofReal ((toPM c x - MvPolynomial.eval x q) ^ 2) ∂D ≤ ENNReal.ofReal e

end Supplement

end EffRobustLearn


