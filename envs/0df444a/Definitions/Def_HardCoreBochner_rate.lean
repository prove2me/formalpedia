-- Prove2me | Definitions.Def_HardCoreBochner_rate
-- name    : HardCoreBochner_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:05.010481+00:00
-- url     : https://prove2.me/theorems/0e99fd85-8134-4a0b-872f-45ee99fddea0
-- title:
--   Jump rates $r_v(\sigma)$ of continuous-time Glauber dynamics
-- statement:
--   Let $\mu$ be a distribution with support $X\subseteq\{0,1\}^V$. The **birth rate** of $v$ at $\sigma$ is
--   $$r_v(\sigma)=\begin{cases}\dfrac{\mu(\sigma\cup\{v\})}{\mu(\sigma)} & \text{if } v\notin\sigma \text{ and } \sigma\cup\{v\}\in X,\\[4pt] 0 & \text{otherwise.}\end{cases}$$
--   For the hard-core model at activity $\lambda$ it equals $\lambda$ when $v$ can be added to the independent set $\sigma$ and $0$ otherwise.
--
--   **Formalization Note** "$\sigma\cup\{v\}\in X$" is $\mu(\sigma\cup\{v\})>0$. When $X$ is downward-closed this forces $\mu(\sigma)>0$, so the rate is $0$ at every $\sigma\notin X$.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §1, p.3 (PDF p.3)

import Mathlib

namespace HardCoreBochner

/-- The **jump (birth) rates** of continuous-time Glauber dynamics. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.3:
`r_v(σ) := µ(σ ∪ {v})/µ(σ)` if `v ∉ σ` and `σ ∪ {v} ∈ X`, and `0` otherwise.

**Formalization Note** `X` is the support of `µ`, so "`σ ∪ {v} ∈ X`" is `0 < µ (σ ∪ {v})`, and the
case split is the explicit `if`. For a downward-closed support, `σ ∪ {v} ∈ X` forces `σ ∈ X`, so
the rate is `0` at every `σ ∉ X` and never divides by `µ σ = 0` in a case that matters. -/
noncomputable def rate {V : Type*} [DecidableEq V] (μ : (V → Bool) → ℝ) (v : V)
    (σ : V → Bool) : ℝ :=
  if σ v = false ∧ 0 < μ (Function.update σ v true) then
    μ (Function.update σ v true) / μ σ
  else 0

end HardCoreBochner


