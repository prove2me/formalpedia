-- Prove2me | Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
-- name    : AlgebraicGeometry_RelEffCartierDivSupportedIn
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/0af7e8bd-4084-5784-bdc6-91130446ac65
-- title:
--   Relative effective Cartier divisors supported in an open subset
-- statement:
--   Fix a morphism of schemes $f \colon \mathcal{C} \to S$, a natural number $r$, and, for $g \colon T \to S$, a datum $D$ of type `RelEffCartierDiv f r g`: an ideal sheaf datum $D.I$ on $\mathcal{C} \times_S T$ whose associated closed subscheme, mapped to $T$ by the closed immersion $D.I.subschemeι$ followed by the second projection, is finite, flat and locally of finite presentation with flat rank $r$ at every point of $T$. For an open $U \subseteq \mathcal{C}$, the predicate `SupportedIn D U` asserts the purely topological condition that the support of $D.I$, as a subset of $\mathcal{C} \times_S T$, is contained in the preimage of $U$ under the first projection; `supportedIn_iff` restates this pointwise, and it is monotone in $U$, automatic for $U = \top$, and stable under the pullback $D \mapsto D.pullbackAlong \varphi$ along an $S$-morphism $\varphi$ (the pullback being given by the comap of $D.I$ along the induced map of products), since taking supports commutes with comap.
--
--   Secondly, `supportedInLocus D U` is the subset of $T$ consisting of those $t$ such that every point $z$ of the closed subscheme attached to $D.I$ lying over $t$ has first projection in $U$; this set is open, being the complement of the image of the closed complement of the preimage of $U$ under a finite, hence closed, map to $T$. It satisfies `supportedIn_pullbackAlong_iff`: for $\varphi \colon T' \to T$ over $S$, the pullback $\varphi^{*}D$ is supported in $U$ precisely when the set-theoretic range of $\varphi$ lies in `supportedInLocus D U`; in particular $D$ itself is supported in $U$ exactly when this locus is all of $T$.
--
--   Finally, `supportedIn f r U` packages these conditions as a subfunctor of the functor $T \mapsto \Sigma_{g \colon T \to S} \mathrm{RelEffCartierDiv}\, f\, r\, g$ on $\mathrm{Scheme}^{\mathrm{op}}$, consisting of those pairs $(g, D)$ with $D$ supported in $U$; it is monotone in $U$ and equals the whole functor for $U = \mathcal{C}$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — ideal sheaf data on a scheme with their supports, associated closed subschemes and comaps, finite and flat morphisms, and `CategoryTheory.Subfunctor` — while the functor of relative effective Cartier divisors and the condition of being supported in an open subset are the project's own.
--
--   **Where it is used.** The open condition `SupportedIn`, together with the open locus in the base over which it holds, provides the local pieces from which the functor of relative effective divisors of a curve is studied: the inclusion of `supportedIn f r U` into the divisor functor is an open condition on the base, so representability may be checked on charts indexed by open subsets $U \subseteq \mathcal{C}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDivSupportedIn.lean

import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}

def SupportedIn {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) : Prop :=
  (D.I.support : Set ↥(pullback f g)) ⊆ ((pullback.fst f g) ⁻¹ᵁ U : (pullback f g).Opens)

lemma supportedIn_iff {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) :
    D.SupportedIn U ↔ ∀ x ∈ D.I.support, pullback.fst f g x ∈ U :=
  Iff.rfl

lemma SupportedIn.mono {T : Scheme.{u}} {g : T ⟶ S} {D : RelEffCartierDiv f r g} {U U' : 𝒞.Opens}
    (h : D.SupportedIn U) (hUU' : U ≤ U') : D.SupportedIn U' :=
  fun _ hx => hUU' (h hx)

@[simp] lemma supportedIn_top {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    D.SupportedIn ⊤ :=
  fun _ _ => trivial

lemma SupportedIn.pullbackAlong {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    {D : RelEffCartierDiv f r g'} {U : 𝒞.Opens} (h : D.SupportedIn U) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) : (D.pullbackAlong φ hφ).SupportedIn U := by
  intro x hx
  change x ∈ (D.I.comap (mapOnProdOver f φ hφ)).support at hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  have hx' : pullback.fst f g' (mapOnProdOver f φ hφ x) ∈ U := h hx
  rwa [← Scheme.Hom.comp_apply, mapOnProdOver_fst] at hx'

section Locus

variable {T : Scheme.{u}} {g : T ⟶ S}

def supportedInLocus (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) : T.Opens where
  carrier := {t | ∀ z : ↥D.I.subscheme, (D.I.subschemeι ≫ pullback.snd f g) z = t →
    pullback.fst f g (D.I.subschemeι z) ∈ U}
  is_open' := by
    have := D.isFinite
    have hcl : IsClosed ((D.I.subschemeι ≫ pullback.snd f g) ''
        ((D.I.subschemeι ≫ pullback.fst f g) ⁻¹ᵁ U : Set ↥D.I.subscheme)ᶜ) :=
      (D.I.subschemeι ≫ pullback.snd f g).isClosedMap _
        ((D.I.subschemeι ≫ pullback.fst f g) ⁻¹ᵁ U).2.isClosed_compl
    convert hcl.isOpen_compl using 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    exact ⟨fun h z hz hzt => hz (by simpa [Scheme.Hom.comp_apply] using h z hzt),
      fun h z hzt => by
        by_contra hz
        exact h z (by simpa [Scheme.Hom.comp_apply] using hz) hzt⟩

lemma mem_supportedInLocus_iff (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) (t : T) :
    t ∈ D.supportedInLocus U ↔ ∀ z : ↥D.I.subscheme, (D.I.subschemeι ≫ pullback.snd f g) z = t →
      pullback.fst f g (D.I.subschemeι z) ∈ U :=
  Iff.rfl

lemma supportedIn_pullbackAlong_iff (D : RelEffCartierDiv f r g) (U : 𝒞.Opens)
    {T' : Scheme.{u}} {g' : T' ⟶ S} (φ : T' ⟶ T) (hφ : φ ≫ g = g') :
    (D.pullbackAlong φ hφ).SupportedIn U ↔ Set.range φ ⊆ (D.supportedInLocus U : Set T) := by
  have hsupp : ((D.pullbackAlong φ hφ).I.support : Set ↥(pullback f g')) =
      mapOnProdOver f φ hφ ⁻¹' Set.range D.I.subschemeι := by
    rw [show (D.pullbackAlong φ hφ).I = D.I.comap (mapOnProdOver f φ hφ) from rfl,
      Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.range_subschemeι]
    rfl
  constructor
  · rintro h _ ⟨t', rfl⟩ z hz

    obtain ⟨w, hw₁, hw₂⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_mapOnProdOver f φ hφ) (D.I.subschemeι z) t'
      (by simpa [Scheme.Hom.comp_apply] using hz)
    have hw : w ∈ ((D.pullbackAlong φ hφ).I.support : Set _) := by
      rw [hsupp]; exact ⟨z, hw₁.symm⟩
    have := h hw
    change pullback.fst f g' w ∈ U at this
    rwa [← mapOnProdOver_fst f φ hφ, Scheme.Hom.comp_apply, hw₁] at this
  · intro h w hw
    rw [hsupp] at hw
    obtain ⟨z, hz⟩ := hw
    have ht : φ (pullback.snd f g' w) ∈ D.supportedInLocus U := h ⟨_, rfl⟩
    have := ht z (by
      rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, mapOnProdOver_snd,
        Scheme.Hom.comp_apply])
    change pullback.fst f g' w ∈ U
    rwa [hz, ← Scheme.Hom.comp_apply, mapOnProdOver_fst] at this

lemma supportedIn_iff_supportedInLocus_eq_top (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) :
    D.SupportedIn U ↔ D.supportedInLocus U = ⊤ := by
  rw [← D.pullbackAlong_id, supportedIn_pullbackAlong_iff, D.pullbackAlong_id]
  constructor
  · intro h
    exact top_le_iff.mp fun t _ => h ⟨t, rfl⟩
  · rintro h - ⟨t, rfl⟩
    exact h.symm ▸ trivial

end Locus

variable (f r)

def supportedIn (U : 𝒞.Opens) : Subfunctor (RelEffCartierDiv.functor f r) where
  obj T := {x | x.2.SupportedIn U}
  map {T T'} φ := by
    rintro ⟨g, D⟩ (hD : D.SupportedIn U)
    exact hD.pullbackAlong φ.unop rfl

variable {f r}

@[simp] lemma mem_supportedIn_iff {U : 𝒞.Opens} {T : Scheme.{u}ᵒᵖ}
    (x : (RelEffCartierDiv.functor f r).obj T) :
    x ∈ (supportedIn f r U).obj T ↔ x.2.SupportedIn U :=
  Iff.rfl

lemma supportedIn_mono {U U' : 𝒞.Opens} (h : U ≤ U') : supportedIn f r U ≤ supportedIn f r U' :=
  fun _ _ hx => SupportedIn.mono hx h

@[simp] lemma supportedIn_top_eq : supportedIn f r (⊤ : 𝒞.Opens) = ⊤ :=
  top_le_iff.mp fun _ x _ => supportedIn_top x.2

end AlgebraicGeometry.RelEffCartierDiv


