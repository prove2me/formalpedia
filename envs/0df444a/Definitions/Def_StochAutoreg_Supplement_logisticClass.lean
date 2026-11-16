-- Prove2me | Definitions.Def_StochAutoreg_Supplement_logisticClass
-- name    : StochAutoreg_Supplement_logisticClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:18:38.620396+00:00
-- url     : https://prove2.me/theorems/f39f579a-18b3-4206-a2e3-a1cddf8e5f79
-- title:
--   The logistic class $\mathcal F_\sigma(d)$ of Eq. (1.2)
-- statement:
--   For $d\in\mathbb N$, the **logistic class** of memory $d$ is
--
--   $$\mathcal F_\sigma(d)=\{\,g_{\beta,w}:(\beta,w)\in\mathbb R\times\mathbb R^d\,\},$$
--
--   the set of all affine logistic generators of memory $d$, with no bound on the parameters. It is the canonical class of the paper's logistic case study (§8), a finite-memory simplification of the next-token mechanism of autoregressive language models; it has $d+1$ real parameters.
--
--   **Formalization Note** The class is a set of generators (the image of the parameter map), so the base mission's sample complexities $m_{\mathrm{base}}$, $m_{\mathrm{CoT}}$, $m_{\mathrm{e2e}}$ apply to it unchanged. Prompts are arbitrary strings, not only strings of length $d$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Eq. (1.2), p.5

import Mathlib
import Definitions.Def_StochAutoreg_Supplement_logisticGen

namespace StochAutoreg

namespace Supplement

/-- The **logistic class** `F_σ(d) = { g_{β,w} : (β, w) ∈ ℝ × ℝ^d }` of Eq. (1.2): every affine logistic
generator of memory `d`, with no bound on the parameters.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Eq. (1.2), p.5.

**Formalization Note.** A `Set Generator` (the image of the parameter map), so the base mission's
sample complexities `mBase`, `mCoT`, `mE2E` apply to it unchanged. Prompts are arbitrary strings. -/
def logisticClass (d : ℕ) : Set Generator :=
  Set.range fun θ : ℝ × (Fin d → ℝ) => logisticGen d θ.1 θ.2

end Supplement

end StochAutoreg


