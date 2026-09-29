-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
-- name    : AlgebraicGeometry_ModulesPullbackLocalSection
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f6136bc0-0ad1-51a4-b966-ac5df05c4afe
-- title:
--   Pulled-back local sections of a module sheaf
-- statement:
--   Fix a morphism of schemes $\varphi \colon X \to Y$, a sheaf of $\mathcal{O}_Y$-modules $L$ (an object of `Y.Modules`) and an open $U \subseteq Y$. The definition `pullbackLocalSection` sends a section $s \in \Gamma(L, U)$ to its image under the component at $U$ of the unit of the adjunction `Modules.pullbackPushforwardAdjunction φ` evaluated at $L$, that is, under the map $\Gamma(L,U) \to \Gamma(\varphi_*\varphi^*L, U) = \Gamma(\varphi^*L, \varphi^{-1}U)$; the result is thus an element of $\Gamma((\mathrm{Modules.pullback}\ \varphi).\mathrm{obj}\ L,\ \varphi^{-1}U)$, written $\varphi^* s$ below. A companion lemma records this description by definitional unfolding.
--
--   The remaining declarations are the elementary calculus of this operation. It is additive and preserves $0$, negation, differences and finite sums indexed by a `Finset`; it is semilinear over the structure sheaves, $\varphi^*(g \cdot s) = \varphi^{\sharp}_U(g) \cdot \varphi^* s$ for $g \in \Gamma(Y,U)$, where $\varphi^{\sharp}_U$ is the map `φ.app U`; and it commutes with restriction: for any inclusion $i \colon V \to U$ of opens of $Y$, restricting $\varphi^* s$ along the induced inclusion $\varphi^{-1}V \subseteq \varphi^{-1}U$ gives $\varphi^*(s|_V)$, with a variant stated for `homOfLE` of an inequality $V \le U$. It is natural in the module: for $\theta \colon L \to L'$ one has $\varphi^*(\theta_U s) = ((\mathrm{Modules.pullback}\ \varphi).\mathrm{map}\ \theta)_{\varphi^{-1}U}(\varphi^* s)$. Two lemmas compute transposes under the adjunction bijection: for $g \colon \varphi^*L \to N$, $g_{\varphi^{-1}U}(\varphi^* s)$ is the value at $s$ of the adjoint $L \to \varphi_* N$, and dually for a morphism $k \colon L \to \varphi_* N$ and its transpose. The right triangle identity is recorded at the level of sections: the counit at $N$ carries $\varphi^* n$ back to $n$ for $n \in \Gamma(\varphi_* N, U) = \Gamma(N, \varphi^{-1}U)$. Finally, `pullback_hom_ext` is an extensionality principle: two morphisms $g_1, g_2 \colon \varphi^*L \to N$ that agree on $\varphi^* s$ for every open $U$ of $Y$ and every $s \in \Gamma(L,U)$ are equal.
--
--   **Relation to Mathlib.** The scheme-theoretic module categories, the pullback functor `Modules.pullback` and the adjunction `Modules.pullbackPushforwardAdjunction` are taken from Mathlib; what is added here is the section-level operation extracted from the unit of that adjunction together with its additivity, semilinearity, restriction, naturality, transpose, triangle-identity and extensionality lemmas.
--
--   **Where it is used.** These lemmas form part of the basic toolkit for handling sheaves of modules on schemes in the formalisation, allowing computations with pullbacks of sheaves to be carried out on local sections rather than through the abstract adjunction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesPullbackLocalSection.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (φ : X ⟶ Y)

section

variable {L : Y.Modules} {U : Y.Opens}

def pullbackLocalSection (s : Γ(L, U)) : Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U) :=
  ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s

lemma pullbackLocalSection_def (s : Γ(L, U)) :
    pullbackLocalSection φ s = ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s := rfl

@[simp] lemma pullbackLocalSection_add (s s' : Γ(L, U)) :
    pullbackLocalSection φ (s + s') = pullbackLocalSection φ s + pullbackLocalSection φ s' :=
  map_add (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s s'

@[simp] lemma pullbackLocalSection_zero : pullbackLocalSection φ (0 : Γ(L, U)) = 0 :=
  map_zero (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom

@[simp] lemma pullbackLocalSection_neg (s : Γ(L, U)) : pullbackLocalSection φ (-s) = -pullbackLocalSection φ s :=
  map_neg (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s

@[simp] lemma pullbackLocalSection_sub (s s' : Γ(L, U)) :
    pullbackLocalSection φ (s - s') = pullbackLocalSection φ s - pullbackLocalSection φ s' :=
  map_sub (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s s'

lemma pullbackLocalSection_sum {ι : Type*} (S : Finset ι) (s : ι → Γ(L, U)) :
    pullbackLocalSection φ (∑ i ∈ S, s i) = ∑ i ∈ S, pullbackLocalSection φ (s i) :=
  map_sum (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s S

lemma pullbackLocalSection_smul (g : Γ(Y, U)) (s : Γ(L, U)) :
    pullbackLocalSection φ (g • s) = φ.app U g • pullbackLocalSection φ s := by
  rw [pullbackLocalSection_def, Scheme.Modules.Hom.app_smul]
  rfl

lemma map_pullbackLocalSection {V : Y.Opens} (i : V ⟶ U) (s : Γ(L, U)) :
    ((Modules.pullback φ).obj L).presheaf.map ((Opens.map φ.base).map i).op (pullbackLocalSection φ s) =
      pullbackLocalSection φ (L.presheaf.map i.op s) := by
  have h := (((Modules.pullbackPushforwardAdjunction φ).unit.app L).mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f :
    Γ(L, U) → Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ V))) h) s).symm

lemma map_homOfLE_pullbackLocalSection {V : Y.Opens} (hVU : V ≤ U) (s : Γ(L, U)) :
    ((Modules.pullback φ).obj L).presheaf.map
        (homOfLE (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hx => hVU hx)).op (pullbackLocalSection φ s) =
      pullbackLocalSection φ (L.presheaf.map (homOfLE hVU).op s) :=
  map_pullbackLocalSection φ (homOfLE hVU) s

lemma pullbackLocalSection_app {L' : Y.Modules} (θ : L ⟶ L') (s : Γ(L, U)) :
    pullbackLocalSection φ (θ.app U s) = ((Modules.pullback φ).map θ).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U s)
    ((Modules.pullbackPushforwardAdjunction φ).unit.naturality θ)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply] at h
  exact h

lemma app_pullbackLocalSection {N : X.Modules} (g : (Modules.pullback φ).obj L ⟶ N) (s : Γ(L, U)) :
    g.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) =
      (((Modules.pullbackPushforwardAdjunction φ).homEquiv L N g).app U s : Γ(N, φ ⁻¹ᵁ U)) := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma homEquiv_symm_app_pullbackLocalSection {N : X.Modules} (k : L ⟶ (Modules.pushforward φ).obj N)
    (s : Γ(L, U)) :
    (((Modules.pullbackPushforwardAdjunction φ).homEquiv L N).symm k).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) =
      (k.app U s : Γ(N, φ ⁻¹ᵁ U)) := by
  rw [app_pullbackLocalSection, Equiv.apply_symm_apply]

end

lemma counit_app_pullbackLocalSection {N : X.Modules} {U : Y.Opens} (n : Γ((Modules.pushforward φ).obj N, U)) :
    ((Modules.pullbackPushforwardAdjunction φ).counit.app N).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ n) =
      (n : Γ(N, φ ⁻¹ᵁ U)) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U n)
    ((Modules.pullbackPushforwardAdjunction φ).right_triangle_components N)
  simp only [Functor.id_obj, Functor.comp_obj, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
  exact h

theorem pullback_hom_ext {L : Y.Modules} {N : X.Modules} {g₁ g₂ : (Modules.pullback φ).obj L ⟶ N}
    (h : ∀ (U : Y.Opens) (s : Γ(L, U)),
      g₁.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) = g₂.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s)) :
    g₁ = g₂ := by
  apply ((Modules.pullbackPushforwardAdjunction φ).homEquiv L N).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  have h₁ := app_pullbackLocalSection φ g₁ s
  have h₂ := app_pullbackLocalSection φ g₂ s
  rw [h U s] at h₁
  exact h₁.symm.trans h₂

end AlgebraicGeometry.Scheme.Modules

end


