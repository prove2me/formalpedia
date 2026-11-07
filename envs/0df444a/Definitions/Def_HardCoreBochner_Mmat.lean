-- Prove2me | Definitions.Def_HardCoreBochner_Mmat
-- name    : HardCoreBochner_Mmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:31:04.876295+00:00
-- url     : https://prove2.me/theorems/9527c029-b542-415b-aac3-842c20f7b467
-- title:
--   Local matrix $M_\sigma$ of Theorem 1.2
-- statement:
--   For a distribution $\mu$ with rates $r$, a parameter $\delta$ and a configuration $\sigma$, the matrix $M_\sigma\in\mathbb R^{V\times V}$ is
--   $$M_\sigma(u,v)=(1-\delta)\,r_v(\sigma)\,\mathbf 1_{u=v}-r_v(\sigma)\big(r_u(\sigma\cup\{v\})-r_u(\sigma)\big).$$
--   The off-diagonal part measures how adding $v$ changes the birth rate of $u$. Positive semidefiniteness of every $M_\sigma$, $\sigma\in X$, is the hypothesis (3) of Theorem 1.2.
--
--   **Formalization Note** Rows are indexed by $u$ and columns by $v$, as printed.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), Theorem 1.2, (3), p.3 (PDF p.3)

import Definitions.Def_HardCoreBochner_rate

namespace HardCoreBochner

/-- The **local matrix** `M_σ ∈ ℝ^{V×V}` of Theorem 1.2. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), (3), p.3:
`M_σ(u, v) = (1 − δ) r_v(σ) 1_{u=v} − r_v(σ) (r_u(σ ∪ {v}) − r_u(σ))`.

**Formalization Note** Rows are indexed by `u`, columns by `v`, as printed. Positive
semidefiniteness is used as the quadratic-form condition `0 ≤ x ⬝ᵥ M_σ *ᵥ x` for all `x`. -/
noncomputable def Mmat {V : Type*} [DecidableEq V] (μ : (V → Bool) → ℝ) (δ : ℝ)
    (σ : V → Bool) : Matrix V V ℝ :=
  fun u v => (1 - δ) * rate μ v σ * (if u = v then 1 else 0)
    - rate μ v σ * (rate μ u (Function.update σ v true) - rate μ u σ)

end HardCoreBochner


