-- Prove2me | Definitions.Def_TentNoise_noisedLaw
-- name    : TentNoise_noisedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:43:26.794206+00:00
-- url     : https://prove2.me/theorems/77822596-386e-407f-8dd7-ca275fdd2431
-- title:
--   The noised path measures $\mathbb Q^{g,\sigma}_T$ and $\mathbb P^\sigma_T$
-- statement:
--   Let $g$ be a Borel map of $[0,1]$ into itself and $\sigma\ge0$. The **noised fitted kernel** is $L_\sigma(x,dy):=H_\sigma(g(x),dy)$: apply $g$, then add reflected Gaussian noise. The **noised path measure** $\mathbb Q^{g,\sigma}_T$ is the law of $(X_0,\dots,X_T)$ with
--
--   $$
--   X_0\sim\mu,\qquad X_{t+1}\sim L_\sigma(X_t,\cdot).
--   $$
--
--   With $g=f$ the tent map, the kernel is $K_\sigma(x,dy)=H_\sigma(f(x),dy)$ and the law is $\mathbb P^\sigma_T$, the noised true dynamics. With $\sigma=0$ the law $\mathbb Q^g_T:=\mathbb Q^{g,0}_T$ is the deterministic rollout of $g$.
--
--   These are the inference-time-noised rollouts whose distance to $\mathbb P_T$ the mission bounds.
--
--   **Formalization Note** `noisedLaw g hg σ T` takes a proof `hg` that $g:\mathbb R\to\mathbb R$ is Borel measurable, needed to form the kernel $x\mapsto H_\sigma(g(x),\cdot)$. `noisedTentLaw σ T` is $\mathbb P^\sigma_T$. Values of $g$ off $[0,1]$ are never visited when $g([0,1])\subseteq[0,1]$.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definition 2.9, p.5 (PDF p.5), eqs. (8)–(9)

import Mathlib
import Definitions.Def_TentNoise_H
import Definitions.Def_TentNoise_trueLaw

open MeasureTheory ProbabilityTheory TeschlODE.Shared

namespace TentNoise

/-- The noised path measure `ℚ^{g,σ}_T`: the law of `(X₀, …, X_T)` with `X₀ ∼ µ` and
`X_{t+1} ∼ L_σ(X_t, ·) = H_σ(g(X_t), ·)` (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.9, p.5, eq. (9)).
With `g = f` (the tent map) the kernel is `K_σ(x, ·) = H_σ(f(x), ·)` (eq. (8)) and the law is
`ℙ^σ_T`; with `σ = 0` it is the deterministic rollout `ℚ^g_T := ℚ^{g,0}_T`.

**Formalization Note** `g : ℝ → ℝ` carries a proof `hg` that it is Borel measurable (needed to form
the kernel `x ↦ H_σ(g x, ·)`); the paper's `g : [0,1] → [0,1]` is Borel. Values of `g` off `[0, 1]`
are never visited when `g` maps `[0,1]` into itself. -/
noncomputable def noisedLaw (g : ℝ → ℝ) (hg : Measurable g) (σ : ℝ) (T : ℕ) :
    Measure (Fin (T + 1) → ℝ) :=
  pathLaw ((H σ).comap g hg) unifI T

/-- The noised tent-map path measure `ℙ^σ_T` (Definition 2.9, p.5): `X₀ ∼ µ`,
`X_{t+1} ∼ K_σ(X_t, ·) = H_σ(f(X_t), ·)`. -/
noncomputable def noisedTentLaw (σ : ℝ) (T : ℕ) : Measure (Fin (T + 1) → ℝ) :=
  noisedLaw (tentMap 2) measurable_tent σ T

end TentNoise


