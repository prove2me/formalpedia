-- Prove2me | Definitions.Def_HardCoreBochner_rmax
-- name    : HardCoreBochner_rmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:31:04.106012+00:00
-- url     : https://prove2.me/theorems/649f8a80-90bd-4a06-8d76-ce00c465ce3c
-- title:
--   Maximal jump rate $r_{\max}$
-- statement:
--   For a distribution $\mu$ with support $X$,
--   $$r_{\max}=\max_{\sigma\in X,\ v\in V} r_v(\sigma).$$
--   It controls the comparison between the continuous-time and the discrete-time Glauber dynamics; for the hard-core model at activity $\lambda$ it equals $\lambda$.
--
--   **Formalization Note** The maximum is the supremum over the finite set $X\times V$ (it is $0$ if $V$ is empty).
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), comparison display, p.3 (PDF p.3)

import Definitions.Def_HardCoreBochner_rate

namespace HardCoreBochner

/-- The **maximal jump rate** `r_max = max_{σ∈X, v∈V} r_v(σ)`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), comparison display, p.3.

**Formalization Note** `X` is the support `{σ | 0 < µ σ}`; the supremum is over the finite type
`X × V`, so it is the printed maximum whenever `X` and `V` are non-empty (on an empty `V` it is
`0`). -/
noncomputable def rmax {V : Type*} [DecidableEq V] (μ : (V → Bool) → ℝ) : ℝ :=
  ⨆ p : {σ : V → Bool // 0 < μ σ} × V, rate μ p.2 p.1.1

end HardCoreBochner


