-- Prove2me | Definitions.Def_HardCoreBochner_dirP
-- name    : HardCoreBochner_dirP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:31:10.712357+00:00
-- url     : https://prove2.me/theorems/fad0c392-e5fc-49ae-b18d-292f5c16c247
-- title:
--   Dirichlet form $\langle f,(I-P)f\rangle_\mu$ of a discrete-time chain
-- statement:
--   For a transition matrix $P$ on $\{0,1\}^V$, a distribution $\mu$ and $f:\{0,1\}^V\to\mathbb R$,
--   $$\langle f,(I-P)f\rangle_\mu=\sum_\sigma\mu(\sigma)f(\sigma)\Big(f(\sigma)-\sum_\tau P(\sigma,\tau)f(\tau)\Big).$$
--   For a chain reversible with respect to $\mu$ this is the Dirichlet form, and a lower bound $\gamma\,\mathrm{Var}_\mu(f)\le\langle f,(I-P)f\rangle_\mu$ for all $f$ is a spectral-gap bound for $P$.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), comparison display, p.3 (PDF p.3)

import Definitions.Def_HardCoreBochner_ip

namespace HardCoreBochner

open scoped BigOperators
open Matrix

/-- The Dirichlet form `⟨f, (I − P)f⟩_µ` of a discrete-time chain `P` on `{0,1}^V`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), comparison
display, p.3: "⟨f, (I − PGD)f⟩µ".

**Formalization Note** `(P f)(σ) = Σ_τ P(σ, τ) f(τ)` is `P *ᵥ f`; the inner product is `ip µ`. -/
def dirP {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (P : Matrix (V → Bool) (V → Bool) ℝ)
    (f : (V → Bool) → ℝ) : ℝ :=
  ip μ f (fun σ => f σ - (P *ᵥ f) σ)

end HardCoreBochner


