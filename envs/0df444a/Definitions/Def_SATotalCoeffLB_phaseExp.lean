-- Prove2me | Definitions.Def_SATotalCoeffLB_phaseExp
-- name    : SATotalCoeffLB_phaseExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:12.480752+00:00
-- url     : https://prove2.me/theorems/9cd075af-5a7a-423a-981b-4d66fe875637
-- title:
--   Quadratic phase average $\mathbb E_{\bar x}(-1)^{\alpha\cdot\bar x + b(\bar x)}$
-- statement:
--   For $\alpha \in \mathbb F_2^n$ and $b \in Q_n$,
--
--   $$
--   \mathbb E_{\bar x \in \mathbb F_2^n} (-1)^{\alpha\cdot \bar x + b(\bar x)} = \frac{1}{2^n} \sum_{\bar x \in \mathbb F_2^n} (-1)^{\alpha\cdot \bar x + b(\bar x)},
--   $$
--
--   where $\alpha\cdot\bar x = \sum_i \alpha_i \bar x_i \in \mathbb F_2$. This is the value that the functional $L_0$ of Lemma 17 assigns to a low-rank monomial $X^\alpha Y^b$ (Eq. (28)), and Lemma 18 bounds it by $2^{-\operatorname{rank}(b)/2}$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Lemma 18, p.53; Eq. (28), p.52

import Mathlib
import Definitions.Def_SATotalCoeffLB_QForm_eval

namespace SATotalCoeffLB

/-- **The quadratic phase average** `E_{x̄ ∈ F₂ⁿ} (−1)^{α·x̄ + b(x̄)}` for `α ∈ F₂ⁿ` and `b ∈ Q_n`
(Lemma 18, p.53; Eq. (28), p.52, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)): the uniform average over the `2ⁿ` points of `F₂ⁿ`. -/
noncomputable def phaseExp {n : ℕ} (α : Fin n → ZMod 2) (b : QForm n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ xb : Fin n → ZMod 2, (-1 : ℝ) ^ (dotProduct α xb + b.eval xb).val

end SATotalCoeffLB


