-- Prove2me | Definitions.Def_AdaGradDHS_Diag_adagradPsi
-- name    : AdaGradDHS_Diag_adagradPsi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:35.303985+00:00
-- url     : https://prove2.me/theorems/be62158a-8f86-429d-bb09-75f647b2a930
-- title:
--   Diagonal AdaGrad proximal function $\psi_t(x) = \tfrac12\langle x, H_t x\rangle$
-- statement:
--   Let $\delta \ge 0$ and let $s_{t,i} = \|g_{1:t,i}\|_2$ be the accumulated gradient norms. The **diagonal AdaGrad proximal function** at round $t$ is
--   $$\psi_t(x) = \tfrac12 \langle x, H_t x\rangle = \tfrac12 \sum_{i=1}^d (\delta + s_{t,i})\, x_i^2, \qquad H_t = \delta I + \operatorname{diag}(s_t).$$
--
--   It is the data-dependent proximal term of Algorithm 1: coordinates with large accumulated gradients receive a strong proximal term and hence small steps.
--
--   **Formalization Note** This is Figure 1's convention, with the factor $\tfrac12$. The text on p. 2123 and the displays on pp. 2131–2132 write $\psi_t(x) = \langle x, H_t x\rangle$ without it; Theorem 5 is stated for the sequence defined by Algorithm 1, that is, for this $\psi_t$. At $t = 0$, $\psi_0(x) = \tfrac{\delta}{2}\|x\|_2^2$. The definition is made for every real $\delta$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), Figure 1 (Algorithm 1), p. 2130 ("SET Ht = δI + diag(st), ψt(x) = ½⟨x, Ht x⟩")

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_accNorm

namespace AdaGradDHS.Diag

/-- **Diagonal AdaGrad proximal function `ψ_t(x) = ½⟨x, H_t x⟩`, `H_t = δI + diag(s_t)`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), Figure 1 (Algorithm 1), p. 2130: "SET Ht = δI + diag(st), ψt(x) = ½⟨x, Ht x⟩".

`adagradPsi δ g t x = ½ Σ_i (δ + s_{t,i}) x_i²` with `s_{t,i} = accNorm g t i`.

**Formalization Note.** This is Figure 1's convention, with the factor `½`. The text on
p. 2123 and the displays on pp. 2131–2132 write `ψt(x) = ⟨x, Ht x⟩` without it; Theorem 5 is
stated for the sequence "defined by Algorithm 1", i.e. for this `ψ_t`. At `t = 0`, `s_0 = 0`
and `ψ_0(x) = (δ/2)‖x‖₂²`. -/
noncomputable def adagradPsi {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / 2 * ∑ i, (δ + accNorm g t i) * (x i) ^ 2

end AdaGradDHS.Diag


