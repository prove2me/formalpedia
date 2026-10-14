-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts
-- name    : OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T15:18:52.980527+00:00
-- url     : https://prove2.me/theorems/adbbdd9e-dab1-41a2-94df-449a05cd66da
-- title:
--   Column and row scales, clearing denominator and logarithmic costs
-- statement:
--   Let $q_i$ be natural denominators and let $a,b$ be natural exponent vectors on $m$ coordinates. Put $w_i=\lceil\log q_i\rceil_+$, where the ceiling is natural. Define the column scale, inverse row scale, and common denominator at real height $H$ and natural truncation orders $T_i$ by
--
--   $$C_q(a)=\prod_i q_i^{a_i},\qquad R_q(b)=C_q(b)^{-1},\qquad D(q,T,H)=\prod_i\operatorname{lcm}(1,\ldots,T_i)^{\lfloor H/w_i\rfloor_+}.$$
--
--   For the original finite row domain $\mathcal R=\mathrm{Row}(K,v_0,\theta,w,H)$ and a column selection $\kappa:\mathcal R\to\mathrm{Column}(w_0,w,H)$, define the logarithmic costs
--
--   $$B=\sum_{\rho\in\mathcal R}\sum_i b_{\rho,i}\log q_i,\qquad A_\kappa=\sum_{\rho\in\mathcal R}\sum_i a_{\kappa(\rho),i}\log q_i.$$
--
--   Here $K$ is natural and $w_0,v_0,\theta,H$ are real domain parameters; $b_{\rho,i}$ and $a_{\kappa(\rho),i}$ are the nonconstant coordinates of the row and selected column exponent vectors. All five quantities are real and are defined without positivity assumptions, using the original finite domains. They provide the scaling and cost data for determinant denominator clearing.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L135-L209

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData

namespace OAI.PiExponent.MatrixArithmetic

open scoped BigOperators

noncomputable def columnScale {m : ℕ} (q : Fin m → ℕ) (a : Fin m → ℕ) : ℝ :=
  ∏ i, (q i : ℝ) ^ a i

noncomputable def rowScale {m : ℕ} (q : Fin m → ℕ) (b : Fin m → ℕ) : ℝ :=
  (columnScale q b)⁻¹

noncomputable def denominator {m : ℕ} (q : Fin m → ℕ) (T : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∏ i, (Nat.lcmUpto (T i) : ℝ) ^ ⌊H / logWeights q i⌋₊

noncomputable def rowCost {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, (ρ.2.1 i.succ : ℝ) * Real.log (q i)

noncomputable def columnCost {m : ℕ} {K : ℕ} {w0 v0 θ : ℝ}
    (q : Fin m → ℕ) {H : ℝ}
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, ((selection ρ).1 i.succ : ℝ) * Real.log (q i)

end OAI.PiExponent.MatrixArithmetic


