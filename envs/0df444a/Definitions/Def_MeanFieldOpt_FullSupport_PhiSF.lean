-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_PhiSF
-- name    : MeanFieldOpt_FullSupport_PhiSF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:07:59.105233+00:00
-- url     : https://prove2.me/theorems/f7c62aad-801b-49fe-afff-01bbcf5480b7
-- title:
--   Cole–Hopf solution $\Phi^\gamma$ of the Parisi PDE for $\gamma\in\mathsf{SF}_+$ (Eq. (7.3))
-- statement:
--   Let $\xi$ be a mixture, $f_0$ a terminal condition, and $\gamma = \sum_{i=1}^m \gamma_i \mathbb I_{[t_{i-1},t_i)} \in \mathsf{SF}_+$. Put $r(t) = \xi'(1) - \xi'(t)$ and let $G \sim \mathsf N(0,1)$. The **Cole–Hopf solution** $\Phi = \Phi^\gamma : [0,1] \times \mathbb R \to \mathbb R$ of the Parisi PDE
--
--   $$
--   \partial_t\Phi + \tfrac12 \xi''(t)\bigl(\partial_x^2\Phi + \gamma(t)(\partial_x\Phi)^2\bigr) = 0, \qquad \Phi(1,x) = f_0(x),
--   $$
--
--   is constructed backwards from $\Phi(1,\cdot) = f_0$: for each $i \in \{1,\dots,m\}$ and $t \in [t_{i-1}, t_i)$,
--
--   $$
--   \Phi(t,x) = \frac{1}{\gamma_i} \log \mathbb E \exp\Bigl\{ \gamma_i\, \Phi\bigl(t_i,\, x + \sqrt{r(t) - r(t_i)}\, G\bigr) \Bigr\}
--   $$
--
--   when $\gamma_i > 0$, and, when $\gamma_i = 0$,
--
--   $$
--   \Phi(t,x) = \mathbb E\, \Phi\bigl(t_i,\, x + \sqrt{r(t) - r(t_i)}\, G\bigr).
--   $$
--
--   Note $r(t) - r(t_i) = \xi'(t_i) - \xi'(t) \ge 0$. On each piece this is the explicit classical solution of the PDE, and it is the starting point for defining $\Phi^\gamma$ and the Parisi functional on all of $\mathscr L$.
--
--   **Formalization Note** The paper's formula (7.3) divides by $\gamma_i$; for $\gamma_i = 0$ (allowed in $\mathsf{SF}_+$) the definition uses the limit $\gamma_i \to 0$, the heat semigroup, instead of Lean's $1/0 = 0$. The expectation over $G$ is the integral against `gaussianReal 0 1`. The values $\Phi(t_i,\cdot)$ at the breakpoints are computed by recursion on the pieces (`nodeVal`). For $t \notin [0,1)$ the function is set to $f_0$; only $t = 1$ is meaningful there.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 35, Eq. (7.3) (Cole–Hopf solution); PDE (6.2) on p. 23

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_Mixture
import Definitions.Def_MeanFieldOpt_FullSupport_SFData

open MeasureTheory ProbabilityTheory

namespace MeanFieldOpt.FullSupport

/-- One Cole–Hopf step (arXiv:2001.00904v1, p. 35, Eq. (7.3)): on a piece where `γ ≡ g`, ending
at time `s`, with `φ = Φ(s, ·)`,
`Φ(t, x) = (1/g) log E exp{g φ(x + √(ξ'(s) - ξ'(t)) G)}`, `G ∼ N(0,1)`
(here `r(t) - r(s) = ξ'(s) - ξ'(t)` with `r(t) = ξ'(1) - ξ'(t)`). For `g = 0` the formula is
replaced by its limit `g → 0`, the heat semigroup `Φ(t, x) = E φ(x + √(ξ'(s) - ξ'(t)) G)`. -/
noncomputable def coleHopfStep (ξ : Mixture) (g s : ℝ) (φ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if g = 0 then
    ∫ z, φ (x + Real.sqrt (ξ.d1 s - ξ.d1 t) * z) ∂(gaussianReal 0 1)
  else
    (1 / g) * Real.log (∫ z, Real.exp (g * φ (x + Real.sqrt (ξ.d1 s - ξ.d1 t) * z))
      ∂(gaussianReal 0 1))

/-- `nodeVal ξ f₀ d k = Φ(t_{m-k}, ·)`: the Cole–Hopf solution at the breakpoints, computed
backwards from `Φ(1, ·) = f₀` (`k = 0`), one piece at a time. -/
noncomputable def nodeVal (ξ : Mixture) (f₀ : ℝ → ℝ) (d : SFData) : ℕ → ℝ → ℝ
  | 0 => f₀
  | k + 1 =>
    if h : k < d.m then
      coleHopfStep ξ (d.a ⟨d.m - 1 - k, by omega⟩) (d.t (Fin.succ ⟨d.m - 1 - k, by omega⟩))
        (nodeVal ξ f₀ d k) (d.t (Fin.castSucc ⟨d.m - 1 - k, by omega⟩))
    else nodeVal ξ f₀ d k

/-- The Cole–Hopf solution `Φ^γ : [0,1] × ℝ → ℝ` of the Parisi PDE (6.2) with terminal
condition `Φ(1, x) = f₀(x)` for `γ = d.toFun ∈ SF₊` (arXiv:2001.00904v1, p. 35, Eq. (7.3)).
For `t ∈ [t_{i-1}, t_i)` it is one Cole–Hopf step from `Φ(t_i, ·)`; for `t ∉ [0,1)` it is `f₀`
(only `t = 1` is meaningful there). -/
noncomputable def PhiSF (ξ : Mixture) (f₀ : ℝ → ℝ) (d : SFData) (t x : ℝ) : ℝ :=
  if h : ∃ i : Fin d.m, d.t i.castSucc ≤ t ∧ t < d.t i.succ then
    coleHopfStep ξ (d.a (Classical.choose h)) (d.t (Classical.choose h).succ)
      (nodeVal ξ f₀ d (d.m - 1 - (Classical.choose h).val)) t x
  else f₀ x

end MeanFieldOpt.FullSupport


