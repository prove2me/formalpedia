-- Prove2me | Definitions.Def_StochAutoreg_mBase
-- name    : StochAutoreg_mBase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:53.349217+00:00
-- url     : https://prove2.me/theorems/e8a0d54f-9ef3-4054-989a-9aa2b66c7a92
-- title:
--   Base sample complexity $m^{\mathcal F}_{\mathrm{base}}(\varepsilon,\delta)$
-- statement:
--   $m^{\mathcal F}_{\mathrm{base}}(\varepsilon,\delta)$ is the least $n$ for which $n$ i.i.d. samples $(X_i,Y_i)$, with $X_i\sim P$ and $Y_i\mid X_i\sim\mathrm{Bern}(p_{g_\star}(X_i))$, suffice to $(\varepsilon,\delta)$-learn $p_{g_\star}$, uniformly over $P$ and $g_\star\in\mathcal F$. It is $+\infty$ when no finite $n$ does. Zero samples are allowed.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$, and the infimum of the empty set is $\infty$. The paper defines it for $0<\delta<1$; the Lean definition accepts any real $\delta$ and is used here at $\delta=1/3$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib
import Definitions.Def_StochAutoreg_Learns
import Definitions.Def_StochAutoreg_labelLaw
import Definitions.Def_StochAutoreg_promptMeasurableSpace

namespace StochAutoreg

/-- The base sample complexity `m^F_base(ε, δ)`: the least `n` for which `n` i.i.d. samples `(X_i, Y_i)`, with
`X_i ∼ P` and `Y_i | X_i ∼ Bern(p_{g⋆}(X_i))`, suffice to `(ε, δ)`-learn `p_{g⋆}`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3.

**Formalization Note.** The value lies in `ℕ∞`, and `sInf ∅ = ⊤` is the paper's "If no finite `n` satisfies the
requirement, the sample complexity is `+∞`". Zero is allowed. -/
noncomputable def mBase (F : Set Generator) (ε δ : ℝ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) ''
    {n | Learns F (fun g P => labelLaw P g) (fun g x => (g x : ℝ)) ε δ n})

end StochAutoreg


