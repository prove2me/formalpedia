-- Prove2me | Definitions.Def_StrictTwoGroups_TwoEquiv_Functors
-- name    : StrictTwoGroups_TwoEquiv_Functors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:40.939538+00:00
-- url     : https://prove2.me/theorems/5b12cd02-71d1-4156-abb2-bae9d1ee09a8
-- title:
--   §4–§5, pp. 10–15 — the 2-functors T : 2-Grp → X-Mod and S : X-Mod → 2-Grp
-- statement:
--   **The 2-functor $T$** (Porst, §4, pp. 10–12). For a strict 2-group $\mathcal G$,
--   $$T_0(\mathcal G)=(G_0,\ \ker s,\ \tau=t|_{\ker s},\ \alpha(g,h)=\mathrm{Ad}_{ig}h=ig\,h\,(ig)^{-1}).$$
--   For a morphism $(f_0,f_1)$, $T_1(f_0,f_1)=(f_0,f_1|_{\ker s})$. For a 2-morphism $\vartheta:F\Rightarrow E$, $T_2\vartheta=\pi_1\varphi'\vartheta$, i.e. $g\mapsto\vartheta g\;i's'(\vartheta g)^{-1}$, where $\varphi(a)=(a\,i(sa)^{-1},sa)$ is the isomorphism (11).
--
--   **The 2-functor $S$** (Porst, §5, pp. 12–15). For a crossed module $\chi=(G,H,\tau,\alpha)$, $S_0(\chi)=(G,\ H\rtimes G,\ s,t,i)$ where $H\rtimes G$ has multiplication $(h,g)(h',g')=(h\,\alpha(g,h'),gg')$ and
--   $$s(h,g)=g,\qquad t(h,g)=\tau h\,g,\qquad i(g)=(e,g),\qquad (j,\tau h\,g)\circ(h,g)=(jh,g).$$
--   For a morphism $(\gamma,\delta)$, $S_1(\gamma,\delta)=(\gamma,(\delta,\gamma))$, i.e. $(h,g)\mapsto(\delta h,\gamma g)$; for a 2-morphism $\eta:(\gamma,\delta)\Rightarrow(\Gamma,\Delta)$, $S_2\eta=(g\mapsto(\eta g,\gamma g))$.
--
--   **Formalization Note** $\ker s$ is Mathlib's `G.s.ker`, the semidirect products are Mathlib's `N ⋊[φ] G` (same multiplication as the paper's), and $\mathrm{Ad}\circ i$ is `MulAut.conjNormal.comp G.i`. The composition of $S_0(\chi)$ is the total function $(b,a)\mapsto(b_1a_1,a_2)$, which is the paper's formula on composable pairs. $T_1$'s second component is written $h\mapsto\pi_1\varphi'(f_1h)=f_1h\;i'(s'(f_1h))^{-1}$, which is defined for every pair of functions and equals the restriction $f_1|_{\ker s}$ whenever $(f_0,f_1)$ is a morphism of strict 2-groups (then $s'(f_1h)=f_0(sh)=e$).
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, pp. 10–12, §4 (T0, T1, T2); pp. 12–14, §5 (S0, S1, S2)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_TwoGrp
import Definitions.Def_StrictTwoGroups_TwoEquiv_XMod

set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv

universe u

/-- `π₁ ϕ(a) = a · i(s a)⁻¹ ∈ ker s` (§2, p. 7, (11); §4, p. 10): the first component of the
isomorphism `ϕ : G₁ → ker s ⋊ G₀`. -/
def kerProj (G : StrictTwoGroup.{u}) (a : G.G1) : ↥G.s.ker :=
  ⟨a * (G.i (G.s a))⁻¹, by simp [MonoidHom.mem_ker, G.s_i]⟩

/-- `T₀` (§4, p. 10): the crossed module `(G₀, ker s, τ = t|_{ker s}, α(g, h) = Ad_{i g} h)`
of a strict 2-group. -/
def toXMod (G : StrictTwoGroup.{u}) : CrossedModule.{u} where
  G := G.G0
  H := ↥G.s.ker
  τ := G.t.comp G.s.ker.subtype
  α := MulAut.conjNormal.comp G.i
  equivariant g h := by
    simp [MulAut.conjNormal_apply, G.t_i]

/-- The 2-functor `T = (T₀, T₁, T₂) : 2-Grp → X-Mod` (§4, pp. 10–12):
`T₁(f₀, f₁) = (f₀, f₁|_{ker s})`, written as `h ↦ π₁ϕ'(f₁ h) = f₁ h · i'(s'(f₁ h))⁻¹`, which is
`f₁ h` whenever `(f₀, f₁)` is a morphism of strict 2-groups; and `T₂ ϑ = π₁ϕ' ϑ`, i.e.
`g ↦ ϑ g · i'(s'(ϑ g))⁻¹`. -/
def T : Raw2Functor twoGrp.{u} xMod.{u} where
  obj := toXMod
  map1 {G G' : StrictTwoGroup.{u}} F := (F.1, fun h : ↥G.s.ker => kerProj G' (F.2 h))
  map2 {_ G' : StrictTwoGroup.{u}} _ _ ϑ := fun g => kerProj G' (ϑ g)

/-- `S₀` (§5, pp. 12–13): the strict 2-group `(G, H ⋊ G, s, t, i)` of a crossed module, with
`s(h, g) = g`, `t(h, g) = τ(h) g`, `i(g) = (e, g)` and composition
`(j, τ(h) g) ∘ (h, g) = (j h, g)`. The semidirect product is taken with respect to `α`:
`(h, g)(h', g') = (h α(g, h'), g g')`. -/
def toTwoGrp (χ : CrossedModule.{u}) : StrictTwoGroup.{u} where
  G0 := χ.G
  G1 := χ.H ⋊[χ.α] χ.G
  s := SemidirectProduct.rightHom
  t := SemidirectProduct.lift χ.τ (MonoidHom.id _) (fun g => by
    ext h
    simp [χ.equivariant])
  i := SemidirectProduct.inr
  comp b a := ⟨b.left * a.left, a.right⟩
  s_i g := by simp
  t_i g := by simp

/-- The 2-functor `S = (S₀, S₁, S₂) : X-Mod → 2-Grp` (§5, pp. 12–15):
`S₁(γ, δ) = (γ, (δ, γ))`, i.e. `(h, g) ↦ (δ h, γ g)`, and, for `η : (γ, δ) ⇒ (Γ, Δ)`,
`S₂ η = (g ↦ (η g, γ g))`. -/
def S : Raw2Functor xMod.{u} twoGrp.{u} where
  obj := toTwoGrp
  map1 {χ χ' : CrossedModule.{u}} f := (f.1, fun x : χ.H ⋊[χ.α] χ.G =>
    (⟨f.2 x.left, f.1 x.right⟩ : χ'.H ⋊[χ'.α] χ'.G))
  map2 {_ χ' : CrossedModule.{u}} f _ η := fun g => (⟨η g, f.1 g⟩ : χ'.H ⋊[χ'.α] χ'.G)

end StrictTwoGroups.TwoEquiv


