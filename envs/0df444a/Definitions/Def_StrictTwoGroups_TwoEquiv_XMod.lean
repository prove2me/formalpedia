-- Prove2me | Definitions.Def_StrictTwoGroups_TwoEquiv_XMod
-- name    : StrictTwoGroups_TwoEquiv_XMod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:48.07698+00:00
-- url     : https://prove2.me/theorems/c6e52ea2-5ddb-4135-bda7-e490a3667a0e
-- title:
--   §3, pp. 8–10 — the 2-category X-Mod of crossed modules
-- statement:
--   The 2-category $X\text{-}\mathit{Mod}$ (Porst, §3, pp. 8–10) has crossed modules as objects. A **morphism** $(\gamma,\delta):(G,H,\tau,\alpha)\to(G',H',\tau',\alpha')$ is a pair of group morphisms $\gamma:G\to G'$, $\delta:H\to H'$ with
--   $$\text{(14a)}\ \ \tau'\delta=\gamma\tau,\qquad \text{(14b)}\ \ \delta(\alpha(g,h))=\alpha'(\gamma g,\delta h).$$
--   A **2-morphism** $\eta:(\gamma,\delta)\Rightarrow(\Gamma,\Delta)$ is a map $\eta:G\to H'$ (not necessarily a group morphism) with
--   $$\text{(15)}\ \ \eta(g\tilde g)=\eta g\;\alpha'(\gamma g,\eta\tilde g),\qquad \text{(16a)}\ \ \tau'\eta(g)=\Gamma g\,(\gamma g)^{-1},\qquad \text{(16b)}\ \ \eta\tau(h)=\Delta h\,(\delta h)^{-1}.$$
--   1-cells compose componentwise, the identity 2-cell is the constant map $g\mapsto e$, the vertical composite of $\eta:(\gamma,\delta)\Rightarrow(\Gamma,\Delta)$ and $\bar\eta:(\Gamma,\Delta)\Rightarrow(\bar\Gamma,\bar\Delta)$ is $g\mapsto\bar\eta g\,\eta g$, and the horizontal composite of $\eta$ (on $\chi\to\chi'$) and $\eta':(\gamma',\delta')\Rightarrow(\Gamma',\Delta')$ (on $\chi'\to\chi''$) is
--   $$(\eta'\circ\eta)(g)=\Delta'(\eta g)\cdot\eta'(\gamma g).$$
--
--   **Formalization Note** `xMod` is a `Raw2Cat`: lawful objects satisfy `IsCrossedModule`, lawful 1-cells `IsXModHom` (multiplicativity of both components, (14a), (14b)), lawful 2-cells `IsXModTwoHom` ((15), (16a), (16b)). 1-cells are pairs of plain functions. Compositions are diagrammatic; the factor order in $H'$ and $H''$ is exactly the paper's (second 2-cell's value first in the vertical composite; the first form $\Delta'\eta\cdot\eta'\gamma$ of the horizontal composite on p. 9).
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, pp. 8–10, §3 Definitions (morphism (14a)-(14b), 2-morphism (15)-(16b)), vertical composition p. 8, units and horizontal composition p. 9, unit functor p. 10

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Raw2Cat
import Definitions.Def_StrictTwoGroups_TwoEquiv_CrossedModule

set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv

universe u

/-- A morphism `(γ, δ) : χ → χ'` of crossed modules (§3, p. 8): group morphisms
`γ : G → G'`, `δ : H → H'` with (14a) `τ' δ = γ τ` and (14b) `δ(α(g, h)) = α'(γ g, δ h)`. -/
def IsXModHom {χ χ' : CrossedModule.{u}} (f : (χ.G → χ'.G) × (χ.H → χ'.H)) : Prop :=
  (∀ x y : χ.G, f.1 (x * y) = f.1 x * f.1 y) ∧
  (∀ h k : χ.H, f.2 (h * k) = f.2 h * f.2 k) ∧
  (∀ h : χ.H, χ'.τ (f.2 h) = f.1 (χ.τ h)) ∧
  (∀ (g : χ.G) (h : χ.H), f.2 (χ.α g h) = χ'.α (f.1 g) (f.2 h))

/-- A 2-morphism `η : (γ, δ) ⇒ (Γ, Δ)` of crossed modules (§3, p. 8): a map `η : G → H'`
with (15) `η(g g̃) = η g · α'(γ g, η g̃)`, (16a) `τ' η(g) = Γ g · (γ g)⁻¹` and
(16b) `η τ(h) = Δ h · (δ h)⁻¹`. -/
def IsXModTwoHom {χ χ' : CrossedModule.{u}} (f g : (χ.G → χ'.G) × (χ.H → χ'.H))
    (η : χ.G → χ'.H) : Prop :=
  (∀ x y : χ.G, η (x * y) = η x * χ'.α (f.1 x) (η y)) ∧
  (∀ x : χ.G, χ'.τ (η x) = g.1 x * (f.1 x)⁻¹) ∧
  (∀ h : χ.H, η (χ.τ h) = g.2 h * (f.2 h)⁻¹)

/-- The 2-category `X-Mod` of crossed modules (§3, pp. 8–10). 1-cells compose componentwise;
the identity 2-cell is the constant map `g ↦ e`; the vertical composite of `η : (γ, δ) ⇒ (Γ, Δ)`
and `η̄ : (Γ, Δ) ⇒ (Γ̄, Δ̄)` is `g ↦ η̄ g · η g`; the horizontal composite of
`η : (γ, δ) ⇒ (Γ, Δ)` (on `χ → χ'`) and `η' : (γ', δ') ⇒ (Γ', Δ')` (on `χ' → χ''`) is
`g ↦ Δ'(η g) · η'(γ g)`. -/
def xMod : Raw2Cat.{u} where
  Ob := CrossedModule.{u}
  Hom1 χ χ' := (χ.G → χ'.G) × (χ.H → χ'.H)
  Hom2 χ χ' := χ.G → χ'.H
  IsOb := IsCrossedModule
  Is1 f := IsXModHom f
  Is2 f g η := IsXModTwoHom f g η
  id1 _ := (fun x => x, fun h => h)
  comp1 f f' := (fun x => f'.1 (f.1 x), fun h => f'.2 (f.2 h))
  id2 _ := fun _ => 1
  vcomp _ _ _ η η' := fun x => η' x * η x
  hcomp f _ _ g' η η' := fun x => g'.2 (η x) * η' (f.1 x)

end StrictTwoGroups.TwoEquiv


