-- Prove2me | Definitions.Def_CoverModular_Supplement_alphaBar
-- name    : CoverModular_Supplement_alphaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:16:43.392346+00:00
-- url     : https://prove2.me/theorems/f1eb9930-c07d-53bf-97ab-f45567f8c12d
-- title:
--   The primal-derived dual vector $\bar\alpha^{\mathcal S}$
-- statement:
--   Let $x^{\mathcal S}$ be an optimal solution of the LP (17) for $\mathcal A=\mathcal S$. The paper defines
--
--   $$
--   \bar\alpha^{\mathcal S}_i=\frac{\sum_jp_ja_{ij}x^{\mathcal S}_j}{b_i},\qquad 1\le i\le m.
--   $$
--
--   It is the analogue of the vectors $\bar\alpha^{\mathcal S}$, $\bar\beta^{\mathcal S}$ of display (6) in the flexibility design analysis. It enters the right-hand side of the auxiliary LPs (29) and the dual solution (30) of Lemma 3.
--
--   **Formalization Note** The definition takes any vector $x$ in place of $x^{\mathcal S}$. The paper uses $\bar\alpha^{\mathcal S}$ only under the Appendix A.3 standing assumption $b>0$, and every theorem that uses it assumes $b_i>0$ for all $i$, so Lean's convention $t/0=0$ never applies.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, p.40

import Mathlib

namespace CoverModular.Supplement

/-- The primal-derived dual vector `ᾱ^S` (DeValve, Pekeč, Wei, SSRN 3844987, Appendix A.3, p.40):
for a primal solution `x` (in the paper, the optimal solution `x^S` of (17) for `A = S`),
`ᾱ^S_i = (∑_j p_j a_ij x^S_j) / b_i`.

**Formalization Note** The paper uses this only under the Appendix A.3 standing assumption
`b > 0`; every statement using `alphaBar` carries `∀ i, 0 < b i`, so the Lean division by zero
convention never applies. -/
noncomputable def alphaBar {m n : ℕ} (a : Fin m → Fin n → ℕ) (p : Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  (∑ j, p j * (a i j : ℝ) * x j) / b i

end CoverModular.Supplement


