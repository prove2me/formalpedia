-- Prove2me | Definitions.Def_DRSub4633_gLarge
-- name    : DRSub4633_gLarge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:57.770197+00:00
-- url     : https://prove2.me/theorems/08d14ba0-7cad-4778-8a93-98310c8f03bd
-- title:
--   The large-block field component $g^L_i(t)$
-- statement:
--   For a large coordinate with label $i$,
--   $$A^L_i(t)=\frac{F(a(t),P_i^-)-F(a(t),P_{i-1}^-)}{p_i},\qquad B^L_i(t)=\frac{F(a(t),P_{i-1}^+)-F(a(t),P_i^+)}{1-p_i},$$
--   $$g^L_i(t)=(1-p_i)A^L_i(t)+p_iB^L_i(t).$$
--   Both denominators are positive.
--
--   **Formalization Note** The dummy coordinate's component is zero and is not represented.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eqs. (13)–(14), p.10

import Mathlib
import Definitions.Def_DRSub4633_resid
import Definitions.Def_DRSub4633_mergePt
import Definitions.Def_DRSub4633_aPath
import Definitions.Def_DRSub4633_Pplus
import Definitions.Def_DRSub4633_Pminus
import Definitions.Def_DRSub4633_pLarge
import Definitions.Def_DRSub4633_largePos

namespace DRSub4633

/-- **The large-block field component `g^L_i(t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eqs. (13)–(14), p.10:
`A^L_i(t) = [F(a(t), P⁻ᵢ) − F(a(t), P⁻ᵢ₋₁)]/pᵢ`, `B^L_i(t) = [F(a(t), P⁺ᵢ₋₁) − F(a(t), P⁺ᵢ)]/(1 − pᵢ)`,
`g^L_i(t) = (1 − pᵢ)A^L_i(t) + pᵢB^L_i(t)`.

`gLarge f x t j` is this component for the large coordinate `j`, whose label is
`i = largePos x j ≥ 2`.

**Formalization Note.** The dummy coordinate's component is zero (its secants compare points that
differ only in the dummy coordinate, p.10) and is dropped. The value at a small `j` is not used. -/
noncomputable def gLarge {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (j : Fin n) : ℝ :=
  let i := largePos x j
  let p := pLarge x j
  let A := (resid f x (mergePt x (aPath x t) (Pminus x i)) -
    resid f x (mergePt x (aPath x t) (Pminus x (i - 1)))) / p
  let B := (resid f x (mergePt x (aPath x t) (Pplus x (i - 1))) -
    resid f x (mergePt x (aPath x t) (Pplus x i))) / (1 - p)
  (1 - p) * A + p * B

end DRSub4633


