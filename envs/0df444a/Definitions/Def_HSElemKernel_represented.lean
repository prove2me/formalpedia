-- Prove2me | Definitions.Def_HSElemKernel_represented
-- name    : HSElemKernel_represented
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:24:04.752166+00:00
-- url     : https://prove2.me/theorems/c517481b-beb3-404c-a7ca-770fa2e7be40
-- title:
--   Represented elements $D_{\sigma,v}$ (Eq. (4))
-- statement:
--   Fix a pair $\mathcal F$, an address map $\gamma : W \to \{0,1\}^\ell$, a choice $\sigma : [B] \to [t]$, and an assignment of the table variables: activation variables $a_{c,j}$ and address variables $z_{c,j,\beta}$, $(c, j, \beta) \in [B] \times [q_2] \times [\ell]$. An element $v$ with subbucket $(c, j) = H_\sigma(v)$ is **represented** when
--   $$D_{\sigma,v} = a_{c,j} \wedge \bigwedge_{\beta:\ \gamma(v)_\beta = 1} z_{c,j,\beta} \wedge \bigwedge_{\beta:\ \gamma(v)_\beta = 0} \neg z_{c,j,\beta} \tag{4}$$
--   holds: the subbucket is active and stores the address $\gamma(v)$.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 4.2, Eq. (4), p.11

import Mathlib
import Definitions.Def_HSElemKernel_TwoLevelHash

namespace HSElemKernel

/-- The test `D_{σ,v}` of Eq. (4) (Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…,
Section 4.2, p.11): given `σ : [B] → [t]` and an assignment `a` of the activation variables
`a_{c,j}` and `z` of the address variables `z_{c,j,β}`, the element `v` is represented when its
subbucket `(c, j) = H_σ(v) = (h̃(v), g_{σ(h̃(v))}(v))` has `a_{c,j} = 1` and stores the address
`γ(v) ∈ {0,1}^ℓ`. -/
def represented {α : Type} (F : TwoLevelHash α) {ℓ : ℕ} (γ : α → Fin ℓ → Bool)
    (σ : Fin F.B → Fin F.t) (a : Fin F.B → Fin F.q2 → Bool)
    (z : Fin F.B → Fin F.q2 → Fin ℓ → Bool) (v : α) : Prop :=
  a (F.h v) (F.g (σ (F.h v)) v) = true ∧ ∀ β, z (F.h v) (F.g (σ (F.h v)) v) β = γ v β

end HSElemKernel


