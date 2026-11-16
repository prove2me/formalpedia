-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_spendJacT
-- name    : AutobidSPPE_Supplement_spendJacT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:44:44.379201+00:00
-- url     : https://prove2.me/theorems/becc91c0-7401-4441-a9ff-d32c8912fe40
-- title:
--   Participation spending Jacobian $J_s(\alpha)$
-- statement:
--   The **participation spending Jacobian** is the $n\times n$ matrix of partial derivatives
--   $$
--   (J_s(\alpha))_{ij}=\frac{\partial s_i}{\partial\alpha_j}(\alpha)
--   $$
--   of the spending polynomial (57).
--
--   **Formalization Note** Each entry is the derivative of the polynomial along the $j$-th coordinate line at $\alpha_j$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Table 2, p.26; (60), p.28; Lemma 3.4, p.30

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_spendPoly

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The participation spending Jacobian `Js(α) = D_α s`, `(Js)ᵢⱼ = ∂sᵢ/∂αⱼ(α)`
(Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Table 2, p.26; Lemma 3.4, p.30; (60), p.28).

**Formalization Note** The partial derivative of the polynomial `spendPoly` in the `j`-th coordinate,
written with `deriv` along the coordinate line (the polynomial is differentiable everywhere). -/
noncomputable def spendJacT {n : ℕ} (vbar : Fin n → ℝ) (α : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => deriv (fun t => spendPoly vbar (Function.update α j t) i) (α j)

end AutobidSPPE.Supplement


