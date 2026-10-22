-- Prove2me | Definitions.Def_CrossedProductGroups_Classification_E2
-- name    : CrossedProductGroups_Classification_E2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:58.575794+00:00
-- url     : https://prove2.me/theorems/7384f6f5-4bd7-49c8-ba4c-3d0bb78616bb
-- title:
--   §3, p. 18 and Definition 3.7, p. 21 — the category E2(H, G) of crossed products and 2-equivalence of crossed systems
-- statement:
--   Fix groups $H$ and $G$. For normalized crossed systems $(\alpha, f)$ and $(\alpha', f')$ write $\triangleright$, $\triangleright'$ for the weak actions and $H \#_\alpha^f G$, $H \#_{\alpha'}^{f'} G$ for the crossed products.
--
--   1. **Morphisms of crossed products.** A map $\psi : H \times G \to H \times G$ is a morphism of groups $H \#_\alpha^f G \to H \#_{\alpha'}^{f'} G$ if $\psi(x \cdot y) = \psi(x) \cdot' \psi(y)$ for all $x, y$, where $\cdot$ and $\cdot'$ are the crossed-product multiplications.
--   2. **The category $\mathcal{E}_2(H, G)$** (p. 18). Its objects are the normalized crossed systems, i.e. the elements of $\mathrm{Crossed}(H, G)$. A morphism $(\eta, \psi, \gamma) : (\alpha, f) \to (\alpha', f')$ consists of group morphisms $\eta : H \to H$, $\gamma : G \to G$ and $\psi : H \#_\alpha^f G \to H \#_{\alpha'}^{f'} G$ making the diagram
--   $$
--   \begin{array}{ccccccccc}
--   1 & \to & H & \xrightarrow{i_H} & H \#_\alpha^f G & \xrightarrow{\pi_G} & G & \to & 1\\
--   & & \downarrow \eta & & \downarrow \psi & & \downarrow \gamma & & \\
--   1 & \to & H & \xrightarrow{i'_H} & H \#_{\alpha'}^{f'} G & \xrightarrow{\pi'_G} & G & \to & 1
--   \end{array}
--   $$
--   commute, where $i_H(h) = (h, 1)$ and $\pi_G(h, g) = g$. Composition and identities are componentwise.
--   3. **2-equivalence** (Definition 3.7). $(\alpha, f) \approx_2 (\alpha', f')$ if there are group isomorphisms $\eta : H \to H$, $\gamma : G \to G$ and a map $t : G \to H$ such that for all $g, g_1, g_2 \in G$ and $h \in H$
--   $$
--   g \triangleright' h = \eta\Big(t(g)\,\big(\gamma^{-1}(g) \triangleright \eta^{-1}(h)\big)\,t(g)^{-1}\Big), \qquad
--   f'(g_1, g_2) = \eta\Big(t(g_1)\,\big(\gamma^{-1}(g_1) \triangleright t(g_2)\big)\, f\big(\gamma^{-1}(g_1), \gamma^{-1}(g_2)\big)\, t(g_1g_2)^{-1}\Big).
--   $$
--   These are conditions (38) and (39) of the paper.
--
--   The category $\mathcal{E}_2(H, G)$ is the setting of the paper's main classification result: its isomorphism classes of objects are exactly the $\approx_2$-classes of normalized crossed systems.
--
--   **Formalization Note.** `E2 H G` is a type synonym for `Crossed H G` carrying a Mathlib `CategoryTheory.Category` instance; a morphism is the structure `E2Hom` with fields `η : H →* H`, `γ : G →* G`, a map `ψ : H × G → H × G` that preserves the crossed-product multiplications (`IsCrossedHom`), and the two commutativity conditions `ψ (h, 1) = (η h, 1)` and `(ψ x).2 = γ x.2`. The paper's canonical inclusion is $i_H(h) = (h f(1,1)^{-1}, 1)$ (Corollary 1.4, p. 6), which equals $(h, 1)$ on normalized systems, the only objects of $\mathcal{E}_2(H, G)$; $(h, 1)$ is used. Since the crossed product of a normalized system is a group (Theorem 1.3), a map preserving the multiplication is a group morphism. In `Equiv2`, $\gamma^{-1}$ and $\eta^{-1}$ are `γ.symm` and `η.symm`.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 18, definition of E2(H, G) and diagram (34); p. 21, Definition 3.7 with (38), (39) from p. 20

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem

namespace CrossedProductGroups.Classification

/-- `ψ : H #^f_α G → H #^{f'}_{α'} G` is a morphism of groups: it carries the multiplication (8)
of `(α, f)` to the multiplication (8) of `(α', f')`. -/
def IsCrossedHom {H G : Type*} [Group H] [Group G]
    (α : G → MulAut H) (f : G → G → H) (α' : G → MulAut H) (f' : G → G → H)
    (ψ : H × G → H × G) : Prop :=
  ∀ x y : H × G, ψ (crossedMul α f x y) = crossedMul α' f' (ψ x) (ψ y)

/-- The category `E₂(H, G)` (p. 18): its objects are the normalized crossed systems. -/
def E2 (H G : Type*) [Group H] [Group G] : Type _ := Crossed H G

/-- A morphism `(η, ψ, γ) : (α, f) → (α', f')` of `E₂(H, G)` (p. 18): group morphisms
`η : H → H`, `γ : G → G` and `ψ : H #^f_α G → H #^{f'}_{α'} G` making diagram (34) commute,
i.e. `ψ ∘ i_H = i'_H ∘ η` and `π'_G ∘ ψ = γ ∘ π_G`, with `i_H(h) = (h, 1)` (the objects are
normalized) and `π_G(h, g) = g`. -/
@[ext] structure E2Hom {H G : Type*} [Group H] [Group G] (c c' : Crossed H G) where
  η : H →* H
  γ : G →* G
  ψ : H × G → H × G
  map_mul : IsCrossedHom c.1.1 c.1.2 c'.1.1 c'.1.2 ψ
  comm_inl : ∀ h : H, ψ (h, 1) = (η h, 1)
  comm_snd : ∀ x : H × G, (ψ x).2 = γ x.2

/-- The identity morphism `(Id_H, Id, Id_G)`. -/
def E2Hom.id {H G : Type*} [Group H] [Group G] (c : Crossed H G) : E2Hom c c where
  η := MonoidHom.id H
  γ := MonoidHom.id G
  ψ := fun x => x
  map_mul := fun _ _ => rfl
  comm_inl := fun _ => rfl
  comm_snd := fun _ => rfl

/-- Composition of morphisms, componentwise. -/
def E2Hom.comp {H G : Type*} [Group H] [Group G] {c c' c'' : Crossed H G}
    (m : E2Hom c c') (m' : E2Hom c' c'') : E2Hom c c'' where
  η := m'.η.comp m.η
  γ := m'.γ.comp m.γ
  ψ := fun x => m'.ψ (m.ψ x)
  map_mul := fun x y => by
    show m'.ψ (m.ψ _) = _
    rw [m.map_mul x y, m'.map_mul]
  comm_inl := fun h => by
    show m'.ψ (m.ψ (h, 1)) = _
    rw [m.comm_inl h, m'.comm_inl]
    rfl
  comm_snd := fun x => by
    show (m'.ψ (m.ψ x)).2 = _
    rw [m'.comm_snd, m.comm_snd]
    rfl

instance (H G : Type*) [Group H] [Group G] : CategoryTheory.Category (E2 H G) where
  Hom c c' := E2Hom c c'
  id c := E2Hom.id c
  comp m m' := E2Hom.comp m m'
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Definition 3.7 (p. 21): `(α, f) ≈₂ (α', f')` if there are group isomorphisms `η : H → H`,
`γ : G → G` and a map `t : G → H` with
(38) `g ⊲' h = η(t(g) (γ⁻¹(g) ⊲ η⁻¹(h)) t(g)⁻¹)` and
(39) `f'(g₁, g₂) = η(t(g₁) (γ⁻¹(g₁) ⊲ t(g₂)) f(γ⁻¹(g₁), γ⁻¹(g₂)) t(g₁g₂)⁻¹)`. -/
def Equiv2 {H G : Type*} [Group H] [Group G] (c c' : Crossed H G) : Prop :=
  ∃ (η : H ≃* H) (γ : G ≃* G) (t : G → H),
    (∀ g : G, ∀ h : H, c'.1.1 g h = η (t g * c.1.1 (γ.symm g) (η.symm h) * (t g)⁻¹)) ∧
    (∀ g₁ g₂ : G, c'.1.2 g₁ g₂ =
      η (t g₁ * c.1.1 (γ.symm g₁) (t g₂) * c.1.2 (γ.symm g₁) (γ.symm g₂) * (t (g₁ * g₂))⁻¹))

end CrossedProductGroups.Classification


