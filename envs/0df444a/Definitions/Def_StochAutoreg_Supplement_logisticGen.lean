-- Prove2me | Definitions.Def_StochAutoreg_Supplement_logisticGen
-- name    : StochAutoreg_Supplement_logisticGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:18:12.877568+00:00
-- url     : https://prove2.me/theorems/13189128-0a7f-4266-9b96-14bbfce38154
-- title:
--   Affine logistic generator $g_{\beta,w}$: $p(s)=\sigma(\beta+\langle w,\mathrm{tail}_d(s)\rangle)$
-- statement:
--   Let $\sigma(a)=1/(1+e^{-a})$ be the sigmoid function. For $d\in\mathbb N$, a bias $\beta\in\mathbb R$ and weights $w\in\mathbb R^d$, the **affine logistic generator** $g_{\beta,w}$ is the stochastic next-token generator with one-step probability
--
--   $$p_{g_{\beta,w}}(s)=\sigma\bigl(\beta+\langle w,\mathrm{tail}_d(s)\rangle\bigr),\qquad s\in\{0,1\}^\star .$$
--
--   The same rule is applied at every step and depends only on the last $d$ tokens. Equivalently, with $\theta=(\beta,w)\in\mathbb R^{d+1}$ and $\varphi_d(s)=(1,\mathrm{tail}_d(s))$, $p_{g_\theta}(s)=\sigma(\langle\theta,\varphi_d(s)\rangle)$. There is no bound on the parameters.
--
--   **Formalization Note** The weight $w_i$ (0-based index $i$) multiplies entry $i$ of the oldest-first window; entry $d-1$ is the newest bit. A bit $1$ contributes $1$ and a bit $0$ contributes $0$ to the inner product.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Eq. (1.2), p.5; §8, p.17

import Mathlib
import Definitions.Def_StochAutoreg_Generator
import Definitions.Def_StochAutoreg_Supplement_tailBits

namespace StochAutoreg

namespace Supplement

/-- The **affine logistic generator** `g_{β,w}` of memory `d`: its one-step probability at a state `s`
is `p_{g_{β,w}}(s) = σ(β + ⟨w, tail_d(s)⟩)` with `σ(a) = 1/(1+e^{-a})`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Eq. (1.2), p.5;
§8, p.17 (`θ = (β, w)`, `φ_d(s) = (1, tail_d(s))`).

**Formalization Note.** `w : Fin d → ℝ` pairs coordinate `i` (0-based) with entry `i` of the
oldest-first window `tailBits d s`; entry `d-1` is the newest bit. A bit `true` counts as `1`.
`unitInterval.sigmoid` is Mathlib's sigmoid with values in `[0,1]`. -/
noncomputable def logisticGen (d : ℕ) (β : ℝ) (w : Fin d → ℝ) : Generator := fun s =>
  unitInterval.sigmoid
    (β + ∑ i : Fin d, w i * (if (tailBits d s).getD (i : ℕ) false then (1 : ℝ) else 0))

end Supplement

end StochAutoreg


