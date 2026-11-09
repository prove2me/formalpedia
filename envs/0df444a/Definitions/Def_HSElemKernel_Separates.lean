-- Prove2me | Definitions.Def_HSElemKernel_Separates
-- name    : HSElemKernel_Separates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:50.355054+00:00
-- url     : https://prove2.me/theorems/b2807876-83c0-4335-b2a5-7cdb92949470
-- title:
--   Two-level separation (Definition 4.1)
-- statement:
--   For a map $\sigma : [B] \to [t]$, each element $v$ is placed at the location
--   $$H_\sigma(v) = \big(\tilde h(v),\ g_{\sigma(\tilde h(v))}(v)\big) \tag{2}$$
--   (its bucket and its subbucket under the candidate chosen by its bucket). The pair $\mathcal F = (\tilde h, \mathcal H_2)$ **separates** a set $T \subseteq W$ if there is a map $\sigma : [B] \to [t]$ such that $H_\sigma$ is injective on $T$; equivalently, for each bucket some candidate sends the elements of $T$ in that bucket to distinct subbuckets.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Definition 4.1, p.9, with Eq. (2), p.8

import Mathlib
import Definitions.Def_HSElemKernel_TwoLevelHash

namespace HSElemKernel

/-- Two-level separation (Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…,
Definition 4.1, p.9, with `H_σ` of Eq. (2), p.8): `F = (h̃, H₂)` separates `T` if some map
`σ : [B] → [t]` makes `H_σ(v) = (h̃(v), g_{σ(h̃(v))}(v))` injective on `T`. -/
def Separates {α : Type} (F : TwoLevelHash α) (T : Finset α) : Prop :=
  ∃ σ : Fin F.B → Fin F.t,
    Set.InjOn (fun v => (F.h v, F.g (σ (F.h v)) v)) (T : Set α)

end HSElemKernel


