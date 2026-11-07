-- Prove2me | Definitions.Def_HardCoreBochner_muMin
-- name    : HardCoreBochner_muMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:11.233266+00:00
-- url     : https://prove2.me/theorems/13d2d82a-6105-43b1-aa7f-ee80adbe1b3b
-- title:
--   Minimal probability $\mu_{\min}$
-- statement:
--   For a distribution $\mu$ with support $X$ (for the hard-core model, the independent sets),
--   $$\mu_{\min}=\min_{\sigma\in X}\mu(\sigma).$$
--   It enters the mixing-time bound through the initial $\ell^2$ distance from a point mass.
--
--   **Formalization Note** The minimum is the infimum over the support, a finite non-empty set for every probability distribution.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), proof of Theorem 1.1, p.4 (PDF p.4)

import Mathlib

namespace HardCoreBochner

/-- The **minimal probability** `µ_min = min_σ µ(σ)` over the state space of the chain. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof of
Theorem 1.1, p.4: "µmin = minσ µ(σ)".

**Formalization Note** The state space is the support `{σ | 0 < µ σ}` (for the hard-core model, the
independent sets); the infimum over this finite set is its minimum when the support is non-empty,
which holds for every probability distribution. -/
noncomputable def muMin {V : Type*} (μ : (V → Bool) → ℝ) : ℝ :=
  ⨅ σ : {σ : V → Bool // 0 < μ σ}, μ σ.1

end HardCoreBochner


