-- Prove2me | Definitions.Def_StrictTwoGroups_TwoEquiv_CrossedModule
-- name    : StrictTwoGroups_TwoEquiv_CrossedModule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:11.039983+00:00
-- url     : https://prove2.me/theorems/4c3284b0-11dc-4d32-8683-6455655210b0
-- title:
--   §3, p. 7 — crossed modules
-- statement:
--   A **crossed module** (Porst, §3, p. 7) is a quadruple $\chi=(G,H,\tau,\alpha)$ of two groups $G$ and $H$, a group morphism $\tau:H\to G$ and an action $\alpha:G\times H\to H$ of $G$ on $H$ by group automorphisms, such that $\tau$ is $G$-equivariant and the **Peiffer identity** (13) holds: for all $g\in G$ and $h,h'\in H$,
--   $$\tau(\alpha(g,h))=g\,\tau(h)\,g^{-1},\qquad \alpha(\tau h,h')=h\,h'\,h^{-1}.$$
--
--   Crossed modules are the objects of the 2-category $X\text{-}\mathit{Mod}$.
--
--   **Formalization Note** The action is a group morphism $\alpha:G\to\operatorname{Aut}(H)$ (`G →* MulAut H`): an action by automorphisms, which is what the semidirect product $H\rtimes G$ of §5 requires. Equivariance is a field of the structure `CrossedModule` (it is needed to define the target map of the strict 2-group $S_0(\chi)$); the Peiffer identity is the predicate `IsCrossedModule`. The two together are the paper's definition.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 7, §3 Definition (crossed module) and Peiffer identity (13)

import Mathlib

set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv

universe u

/-- The data of a crossed module (§3, p. 7): groups `G` and `H`, a group morphism
`τ : H → G`, and an action `α` of `G` on `H` by group automorphisms, with `τ` `G`-equivariant:
`τ(α(g, h)) = g τ(h) g⁻¹`. The Peiffer identity (13) is the predicate `IsCrossedModule`. -/
structure CrossedModule where
  G : Type u
  H : Type u
  [grpG : Group G]
  [grpH : Group H]
  τ : H →* G
  α : G →* MulAut H
  equivariant : ∀ (g : G) (h : H), τ (α g h) = g * τ h * g⁻¹

attribute [instance] CrossedModule.grpG CrossedModule.grpH

/-- The Peiffer identity (13): `α(τ h, h') = h h' h⁻¹` for all `h, h' ∈ H`. -/
def IsCrossedModule (χ : CrossedModule.{u}) : Prop :=
  ∀ h h' : χ.H, χ.α (χ.τ h) h' = h * h' * h⁻¹

end StrictTwoGroups.TwoEquiv


