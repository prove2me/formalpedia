-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_PhiL
-- name    : MeanFieldOpt_FullSupport_PhiL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:29:59.649081+00:00
-- url     : https://prove2.me/theorems/be10f91d-1cf5-4631-8467-5aaa2d2380a8
-- title:
--   $\Phi^\gamma$ for $\gamma\in\mathscr L$, defined by continuity from $\mathsf{SF}_+$
-- statement:
--   Let $\xi$ be a mixture and $f_0$ a terminal condition. Equip order parameters with the weighted $L^1$ distance $\|\gamma_1 - \gamma_2\|_{1,\xi''} = \int_0^1 \xi''(t)|\gamma_1(t) - \gamma_2(t)|\,dt$, and write $\gamma_n \xrightarrow{L^1_\xi} \gamma$ when this distance tends to $0$. For $\gamma \in \mathscr L$, the solution of the Parisi PDE is defined by continuity:
--
--   $$
--   \Phi^\gamma(t,x) = \lim_{n\to\infty} \Phi^{\gamma_n}(t,x), \qquad \gamma_n \in \mathsf{SF}_+,\ \gamma_n \xrightarrow{L^1_\xi} \gamma,
--   $$
--
--   where $\Phi^{\gamma_n}$ is the Cole–Hopf solution. By the Lipschitz estimate $\|\Phi^{\gamma_1} - \Phi^{\gamma_2}\|_\infty \le \|\xi''(\gamma_1 - \gamma_2)\|_1$ (Proposition 6.1(c)) the limit exists and does not depend on the approximating sequence.
--
--   **Formalization Note** The limit is taken along the filter on step-function data $d$ obtained by pulling back the neighbourhoods of $0$ under $d \mapsto \int_{[0,1)} \xi''(s)|d(s) - \gamma(s)|\,ds$ (`limUnder` of the `comap` filter). This is the limit along every $\mathsf{SF}_+$ sequence converging to $\gamma$ in $L^1_\xi$. The definition does not assume or choose a solution of the PDE.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 24 (definition of Φ^γ by continuity); L^1_ξ distance p. 22 and p. 7

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_PhiSF

open MeasureTheory Filter Topology

namespace MeanFieldOpt.FullSupport

/-- `Φ^γ` for `γ ∈ ℒ`, defined by continuity from `SF₊` (arXiv:2001.00904v1, p. 24):
`Φ^γ(t, x) = lim_n Φ^{γ_n}(t, x)` for `γ_n ∈ SF₊` with `γ_n → γ` in `L¹_ξ`, i.e.
`∫_0^1 ξ''(s) |γ_n(s) - γ(s)| ds → 0`. Encoded as the limit of `PhiSF` along the filter of
step-function data whose `L¹_ξ` distance to `γ` tends to `0`. -/
noncomputable def PhiL (ξ : Mixture) (f₀ : ℝ → ℝ) (γ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  limUnder (Filter.comap (fun d : SFData => ∫ s in Set.Ico (0 : ℝ) 1, ξ.d2 s * |d.toFun s - γ s|)
    (𝓝 0)) (fun d => PhiSF ξ f₀ d t x)

end MeanFieldOpt.FullSupport


