-- Prove2me | Definitions.Def_SelfGuidedALP_vfa
-- name    : SelfGuidedALP_vfa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:36.582641+00:00
-- url     : https://prove2.me/theorems/72dfc36b-1432-4a84-9658-13299de8dac5
-- title:
--   The sampled value function approximation $V(s;\beta)$
-- statement:
--   For bases $\theta^1,\dots,\theta^n$ and a weight vector $\beta=(\beta_0,\beta_1,\dots,\beta_n)\in\mathbb R^{n+1}$, the **sampled value function approximation** is
--   $$
--   V(s;\beta):=\beta_0+\sum_{i=1}^n\beta_i\,\varphi(s;\theta^i).
--   $$
--
--   This is the object the linear programs compute.
--
--   **Formalization Note** Index $0$ of $\beta$ is the intercept, and $\beta_{i}$ is the weight of the $i$-th sampled basis.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §3.1, p.10

import Mathlib
import Definitions.Def_SelfGuidedALP_RBClass
import Definitions.Def_SelfGuidedALP_feat

namespace SelfGuidedALP

/-- The sampled value function approximation `V(s;β) := β₀ + ∑_{i=1}^n βᵢ ϕ(s;θⁱ)`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §3.1, p.10).

**Formalization Note.** A vector `β ∈ ℝ^{n+1}` is a function on `Fin (n + 1)`: index `0` is the
intercept, and `β i.succ` is the weight of the basis with parameter `θs i`. -/
noncomputable def vfa {d n : ℕ} (R : RBClass d) (θs : Fin n → EuclideanSpace ℝ (Fin (d + 1)))
    (β : Fin (n + 1) → ℝ) (s : EuclideanSpace ℝ (Fin d)) : ℝ :=
  β 0 + ∑ i, β i.succ * feat R.ϕ (θs i) s

end SelfGuidedALP


