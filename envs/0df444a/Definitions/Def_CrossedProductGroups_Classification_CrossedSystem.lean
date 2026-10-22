-- Prove2me | Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
-- name    : CrossedProductGroups_Classification_CrossedSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:20.930285+00:00
-- url     : https://prove2.me/theorems/d1a19df0-1298-4f05-bae7-97a0a3dde3d2
-- title:
--   Definition 1.1 and (8), pp. 3–4 — crossed systems, normalized crossed systems Crossed(H, G) and the crossed product multiplication
-- statement:
--   Let $H$ and $G$ be groups. For a map $\alpha : G \to \mathrm{Aut}(H)$ write $g \triangleright h := \alpha(g)(h)$. Since each $\alpha(g)$ is an automorphism, $g \triangleright 1 = 1$, $g \triangleright (h_1h_2) = (g \triangleright h_1)(g \triangleright h_2)$ and $g \triangleright h^{-1} = (g \triangleright h)^{-1}$; but $\alpha$ need not be a group homomorphism.
--
--   1. **Crossed system** (Definition 1.1). The quadruple $(H, G, \alpha, f)$, with $f : G \times G \to H$ a map, is a crossed system if for all $g_1, g_2, g_3 \in G$ and $h \in H$
--   $$
--   g_1 \triangleright (g_2 \triangleright h) = f(g_1, g_2)\,\big((g_1g_2) \triangleright h\big)\,f(g_1, g_2)^{-1}, \qquad
--   f(g_1, g_2)\, f(g_1g_2, g_3) = \big(g_1 \triangleright f(g_2, g_3)\big)\, f(g_1, g_2g_3).
--   $$
--   The map $\alpha$ is then called a *weak action* and $f$ an *$\alpha$-cocycle*.
--   2. **Normalized systems.** The crossed system is normalized if $f(1, 1) = 1$, and $\mathrm{Crossed}(H, G)$ denotes the set of pairs $(\alpha, f)$ forming a normalized crossed system.
--   3. **Crossed product multiplication** (8). On the set $H \#_\alpha^f G := H \times G$ define
--   $$
--   (h_1, g_1) \cdot (h_2, g_2) := \big(h_1\,(g_1 \triangleright h_2)\, f(g_1, g_2),\; g_1g_2\big).
--   $$
--   4. **Morphism quadruples** (the conditions of Corollary 2.3). Given two crossed systems $(\alpha, f)$ and $(\alpha', f')$ (write $\triangleright'$ for $\alpha'$), a quadruple $(u, r, v, s)$ of maps $u : H \to H$, $r : G \to H$, $v : G \to G$ and a group morphism $s : H \to G$ satisfies the compatibility conditions if, for all $g, g_1, g_2 \in G$ and $h, h_1, h_2 \in H$,
--   $$
--   \begin{aligned}
--   v(g_1)v(g_2) &= s(f(g_1,g_2))\,v(g_1g_2),\\
--   v(g)s(h) &= s(g \triangleright h)\,v(g),\\
--   u(h_1h_2) &= u(h_1)\big(s(h_1) \triangleright' u(h_2)\big) f'(s(h_1), s(h_2)),\\
--   u(g \triangleright h)\big(s(g \triangleright h) \triangleright' r(g)\big) f'\big(s(g \triangleright h), v(g)\big) &= r(g)\big(v(g) \triangleright' u(h)\big) f'(v(g), s(h)),\\
--   r(g_1)\big(v(g_1) \triangleright' r(g_2)\big) f'(v(g_1), v(g_2)) &= u(f(g_1,g_2))\big(s(f(g_1,g_2)) \triangleright' r(g_1g_2)\big) f'\big(s(f(g_1,g_2)), v(g_1g_2)\big).
--   \end{aligned}
--   $$
--
--   These are the basic objects of nonabelian Schreier theory: every group extension of $H$ by $G$ is, up to isomorphism, a crossed product $H \#_\alpha^f G$, and the whole paper is phrased in terms of the data $(\alpha, f)$.
--
--   **Formalization Note.** The weak action is a plain function `α : G → MulAut H` (not a homomorphism and not a `MulAction`), and the cocycle is curried, `f g₁ g₂ = f(g₁, g₂)`. `Crossed H G` is a subtype of pairs. The crossed-product multiplication is a separate function `crossedMul α f` on `H × G`; no group instance is put on it (the type `H × G` keeps its direct-product structure, which is never used for the crossed product). The predicate `IsMorphismQuadruple` records the five displayed conditions of Corollary 2.3 (p. 14), with the factors in the printed order; the page writes "$\alpha(g)(h) = g \triangleright' h$" two lines above Corollary 2.3, meaning $\alpha'$.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, pp. 3–4, Definition 1.1, (1), (8), Crossed(H, G); p. 14, the conditions of Corollary 2.3

import Mathlib

namespace CrossedProductGroups.Classification

/-- Agore–Militaru, Definition 1.1 (pp. 3–4): `(H, G, α, f)` is a *crossed system* when the weak
action `α : G → Aut(H)` (written `g ⊲ h = α g h`) and the `α`-cocycle `f : G × G → H` satisfy
(2) `g₁ ⊲ (g₂ ⊲ h) = f(g₁, g₂) ((g₁g₂) ⊲ h) f(g₁, g₂)⁻¹` and
(3) `f(g₁, g₂) f(g₁g₂, g₃) = (g₁ ⊲ f(g₂, g₃)) f(g₁, g₂g₃)`.
`α` is a plain map into `MulAut H`, not a homomorphism. -/
structure IsCrossedSystem {H G : Type*} [Group H] [Group G]
    (α : G → MulAut H) (f : G → G → H) : Prop where
  twisted : ∀ g₁ g₂ : G, ∀ h : H, α g₁ (α g₂ h) = f g₁ g₂ * α (g₁ * g₂) h * (f g₁ g₂)⁻¹
  cocycle : ∀ g₁ g₂ g₃ : G, f g₁ g₂ * f (g₁ * g₂) g₃ = α g₁ (f g₂ g₃) * f g₁ (g₂ * g₃)

/-- `Crossed(H, G)` (p. 4): the set of normalized crossed systems, as pairs `(α, f)` with
`(H, G, α, f)` a crossed system and `f(1, 1) = 1`. -/
def Crossed (H G : Type*) [Group H] [Group G] : Type _ :=
  {p : (G → MulAut H) × (G → G → H) // IsCrossedSystem p.1 p.2 ∧ p.2 1 1 = 1}

/-- The multiplication (8) of `H #^f_α G := H × G` (p. 4):
`(h₁, g₁) · (h₂, g₂) = (h₁ (g₁ ⊲ h₂) f(g₁, g₂), g₁g₂)`. It is a separate operation, not the
product-group multiplication of `H × G`. -/
def crossedMul {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H)
    (x y : H × G) : H × G :=
  (x.1 * α x.2 y.1 * f x.2 y.2, x.2 * y.2)

/-- Corollary 2.3 (p. 14): the compatibility conditions on a quadruple `(u, r, v, s)`, with
`u : H → H`, `r : G → H`, `v : G → G` maps and `s : H → G` a morphism of groups, relative to two
crossed systems `(α, f)` (written `⊲`) and `(α', f')` (written `⊲'`). -/
structure IsMorphismQuadruple {H G : Type*} [Group H] [Group G]
    (α : G → MulAut H) (f : G → G → H) (α' : G → MulAut H) (f' : G → G → H)
    (u : H → H) (r : G → H) (v : G → G) (s : H →* G) : Prop where
  cond1 : ∀ g₁ g₂ : G, v g₁ * v g₂ = s (f g₁ g₂) * v (g₁ * g₂)
  cond2 : ∀ g : G, ∀ h : H, v g * s h = s (α g h) * v g
  cond3 : ∀ h₁ h₂ : H, u (h₁ * h₂) = u h₁ * α' (s h₁) (u h₂) * f' (s h₁) (s h₂)
  cond4 : ∀ g : G, ∀ h : H,
    u (α g h) * α' (s (α g h)) (r g) * f' (s (α g h)) (v g) = r g * α' (v g) (u h) * f' (v g) (s h)
  cond5 : ∀ g₁ g₂ : G,
    r g₁ * α' (v g₁) (r g₂) * f' (v g₁) (v g₂) =
      u (f g₁ g₂) * α' (s (f g₁ g₂)) (r (g₁ * g₂)) * f' (s (f g₁ g₂)) (v (g₁ * g₂))

end CrossedProductGroups.Classification


