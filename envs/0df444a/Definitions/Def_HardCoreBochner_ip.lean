-- Prove2me | Definitions.Def_HardCoreBochner_ip
-- name    : HardCoreBochner_ip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:11.286983+00:00
-- url     : https://prove2.me/theorems/2eccff24-b652-440a-b411-99dea00b66b4
-- title:
--   Expectation $\mathbb E_\mu$, inner product $\langle f,g\rangle_\mu$ and variance $\mathrm{Var}_\mu$
-- statement:
--   For a distribution $\mu$ on $\{0,1\}^V$ and $f,g:\{0,1\}^V\to\mathbb R$:
--   $$\mathbb E_\mu[g]=\sum_\sigma\mu(\sigma)g(\sigma),\qquad \langle f,g\rangle_\mu=\mathbb E_\mu[f(\sigma)g(\sigma)],\qquad \mathrm{Var}_\mu(f)=\mathbb E_\mu\big[(f-\mathbb E_\mu f)^2\big].$$
--   These are the $\ell^2(\mu)$ structure in which the spectral gap (2) and the Dirichlet forms are expressed.
--
--   **Formalization Note** Sums run over all of $\{0,1\}^V$; configurations outside the support have weight $0$.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §1, p.3 (PDF p.3); (2), p.3

import Mathlib

namespace HardCoreBochner

open scoped BigOperators

/-- The expectation `E_µ[g] = Σ_σ µ(σ) g(σ)` of `g : {0,1}^V → ℝ` under `σ ∼ µ`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.3.

**Formalization Note** The sum runs over all of `V → Bool`; configurations outside the support of
`µ` carry weight `0`. -/
def expect {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (g : (V → Bool) → ℝ) : ℝ :=
  ∑ σ, μ σ * g σ

/-- The inner product `⟨f, g⟩_µ := E_µ[f(σ) g(σ)]`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.3. -/
def ip {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (f g : (V → Bool) → ℝ) : ℝ :=
  expect μ (fun σ => f σ * g σ)

/-- The variance `Var_µ(f) = E_µ[(f − E_µ f)²]`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), (2), p.3. -/
def var {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (f : (V → Bool) → ℝ) : ℝ :=
  expect μ (fun σ => (f σ - expect μ f) ^ 2)

end HardCoreBochner


