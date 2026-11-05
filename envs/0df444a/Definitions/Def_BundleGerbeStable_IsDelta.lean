-- Prove2me | Definitions.Def_BundleGerbeStable_IsDelta
-- name    : BundleGerbeStable_IsDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:51.518532+00:00
-- url     : https://prove2.me/theorems/dee1ba37-69a2-40be-a450-2539973dd2d5
-- title:
--   The bundle gerbe $\delta(Q)$ and trivial bundle gerbes
-- statement:
--   For a principal $\mathbb C^\times$ bundle $Q\to Y$, the bundle gerbe **$\delta(Q)$** has fibres $\delta(Q)_{(y_1,y_2)}=Q^*_{y_1}\otimes Q_{y_2}$ and product induced by the natural pairing of $Q_{y_2}$ with $Q^*_{y_2}$. The relation `IsDelta G Q` says that $G$ is $\delta(Q)$: there is a smooth map $c(q_1,q_2)=q_1^*\otimes q_2$ on pairs of points of $Q$ over one point of $M$, with
--   $$c(zq_1,q_2)=z^{-1}c(q_1,q_2),\quad c(q_1,zq_2)=z\,c(q_1,q_2),\quad c(q_1,q_2)\,c(q_2,q_3)=c(q_1,q_3).$$
--
--   A bundle gerbe is **trivial** if it is isomorphic to some $\delta(Q)$. Trivial gerbes are the ones with zero Dixmier-Douady class (Theorem 2.1) and the ones used in stable isomorphism.
--
--   **Formalization Note.** `IsTrivial G` is "there is a $Q$ on $Y$ with `IsDelta G Q`". The property transports along isomorphisms, moving $Q$ to the new space, so this is the paper's "isomorphic to $\delta(Q)$".
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3 (δ(Q), trivial bundle gerbes)

import Mathlib
import Definitions.Def_BundleGerbeStable_BundleGerbe

open Diffeology

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M] {S : LocallySplit M}

/-- `G` is the bundle gerbe `δ(Q)` of a ℂ× bundle `Q → Y` (Murray, Stevenson, *Bundle gerbes: stable
isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): `δ(Q)_(y₁,y₂) = Q*_y₁ ⊗ Q_y₂`, with the
product induced by the natural pairing. It is given by the smooth map `c q₁ q₂ = q₁* ⊗ q₂` on pairs with
`π(proj q₁) = π(proj q₂)`, with `c (z • q₁) q₂ = z⁻¹ • c q₁ q₂`, `c q₁ (z • q₂) = z • c q₁ q₂`, and
`c q₁ q₂ · c q₂ q₃ = c q₁ q₃`, which is the natural pairing of `Q_y₂` with `Q*_y₂`.

**Formalization Note.** By the universal property of the contracted product, `c` is a map of ℂ× spaces
from `Q*_y₁ ⊗ Q_y₂`. It is automatically bijective, and a diffeomorphism, as in `IsTensor`. The
multiplicativity axiom is required: without it every gerbe with a bundle on `Y` would be "trivial".
`delta_exists` (§2, p.3) is the existence of such a `G`. -/
def IsDelta (G : BundleGerbe S) (Q : CxBundle S.Y) : Prop :=
  ∃ c : (q₁ q₂ : Q.P) → S.π (Q.proj q₁) = S.π (Q.proj q₂) → G.bdl.P,
    DSmooth (fun r : {r : Q.P × Q.P // S.π (Q.proj r.1) = S.π (Q.proj r.2)} ↦
      c r.1.1 r.1.2 r.2) ∧
    (∀ q₁ q₂ h, G.bdl.src (c q₁ q₂ h) = Q.proj q₁) ∧
    (∀ q₁ q₂ h, G.bdl.tgt (c q₁ q₂ h) = Q.proj q₂) ∧
    (∀ (z : ℂˣ) q₁ q₂ h h', c (z • q₁) q₂ h' = z⁻¹ • c q₁ q₂ h) ∧
    (∀ (z : ℂˣ) q₁ q₂ h h', c q₁ (z • q₂) h' = z • c q₁ q₂ h) ∧
    ∀ q₁ q₂ q₃ h₁ h₂ h₃ hm, G.mul (c q₁ q₂ h₁) (c q₂ q₃ h₂) hm = c q₁ q₃ h₃

/-- A bundle gerbe is **trivial** (arXiv:math/9908135v1, §2, p.3: "A bundle gerbe which is isomorphic
to a bundle gerbe of the form δ(Q) is called trivial") if there is a ℂ× bundle `Q` on `Y` with
`IsDelta G Q`.

**Formalization Note.** `IsDelta G Q` is a property of `G` that transports along an isomorphism of
gerbes over `Y`, and an isomorphism `G ≅ δ(Q')` over a different `Y'` transports `Q'` to a bundle on
`Y`, so this is the paper's "isomorphic to δ(Q)". -/
def IsTrivial (G : BundleGerbe S) : Prop :=
  ∃ Q : CxBundle S.Y, IsDelta G Q

end BundleGerbeStable


