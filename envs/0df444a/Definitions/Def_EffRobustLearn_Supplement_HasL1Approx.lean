-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_HasL1Approx
-- name    : EffRobustLearn_Supplement_HasL1Approx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:15:43.709841+00:00
-- url     : https://prove2.me/theorems/1c636ecf-8345-41f7-855a-cd9522fce4a9
-- title:
--   $L_1(D)$ polynomial approximators of degree $\ell$ and error $e$
-- statement:
--   A concept class $\mathcal C$ of functions $\mathbb R^d\to\{\pm1\}$ admits **$L_1(D)$ polynomial approximators of degree $\ell$ with error $e$** if for every $c\in\mathcal C$ there is a real polynomial $q$ of degree at most $\ell$ with
--   $$
--   \mathbb E_{x\sim D}|q(x)-c(x)|\le e .
--   $$
--
--   This is the $L_1$ analogue of Definition 4.2 used in Theorem 4.10 and Eq. (4.12), with $e=\varepsilon/8$.
--
--   **Formalization Note** Concepts are read as $\pm1$ through `toPM`; the expectation is a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Theorem 4.10 and Eq. (4.12), p.24 (PDF p.25)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

/-- `L1(D)` polynomial approximators of degree `ℓ` and error `e`, as used in Theorem 4.10 and (4.12) of
Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.24 (PDF p.25): every `c ∈ C` has a polynomial `q` of degree at most `ℓ` with
`E_{x∼D}|q(x) − c(x)| ≤ e`.

**Formalization Note.** Concepts are read as `±1` through `toPM`; the expectation is a lower Lebesgue
integral in `ℝ≥0∞` (an infinite error is `⊤`). -/
def HasL1Approx {d : ℕ} (D : Measure (Fin d → ℝ)) (C : Set ((Fin d → ℝ) → Bool)) (ℓ : ℕ)
    (e : ℝ) : Prop :=
  ∀ c ∈ C, ∃ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ ℓ ∧
    ∫⁻ x, ‖MvPolynomial.eval x q - toPM c x‖ₑ ∂D ≤ ENNReal.ofReal e

end Supplement

end EffRobustLearn


