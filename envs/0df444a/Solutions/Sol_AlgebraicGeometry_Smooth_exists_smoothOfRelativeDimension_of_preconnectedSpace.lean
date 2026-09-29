-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1f0d8111-24ce-5cc9-8a54-b4309e610196

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace

set_option autoImplicit false

universe u

namespace R1NeronObjE7

open AlgebraicGeometry CategoryTheory RingHom

section descend

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

theorem appLE_basicOpen_basicOpen
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) (h : P (f.appLE U V e).hom)
    (r : Γ(Y, U)) (s : Γ(X, X.basicOpen (f.appLE U V e r)))
    (e' : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r) :
    P (f.appLE (Y.basicOpen r) (X.basicOpen s) e').hom := by
  have ha : IsAffineOpen (X.basicOpen (f.appLE U V e r)) := V.2.basicOpen _
  haveI := V.2.isLocalization_basicOpen (f.appLE U V e r)
  haveI := U.2.isLocalization_basicOpen r
  haveI := ha.isLocalization_basicOpen s
  have heq : f.appLE (Y.basicOpen r) (X.basicOpen s) e' =
      f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) ≫
        CommRingCat.ofHom (algebraMap _ _) := by
    simp only [Scheme.Hom.appLE, homOfLE_leOfHom, Category.assoc]
    congr
    apply X.presheaf.map_comp
  rw [heq]
  apply hPa _ s _
  rw [U.2.appLE_eq_away_map f V.2]
  exact hPl _ _ _ _ h

end descend

theorem eq_of_isStandardSmoothOfRelativeDimension_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {n n' : ℕ}
    (U : Y.affineOpens) (V : X.affineOpens) (hx : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n)
    (U' : Y.affineOpens) (V' : X.affineOpens) (hx' : x ∈ V'.1) (e' : V'.1 ≤ f ⁻¹ᵁ U'.1)
    (h' : (f.appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension n') : n = n' := by
  have hPa : ∀ m : ℕ, StableUnderCompositionWithLocalizationAwayTarget
      (IsStandardSmoothOfRelativeDimension m) :=
    fun m => (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
  have hPl : ∀ m : ℕ, LocalizationAwayPreserves (IsStandardSmoothOfRelativeDimension m) :=
    fun m => (isStandardSmoothOfRelativeDimension_localizationPreserves m).away

  obtain ⟨r, s, hxs, ers, hA⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa n) (hPl n)
    x U' U V' V hx' hx e h (e' hx')
  let Br : Y.affineOpens := ⟨Y.basicOpen r, U'.2.basicOpen r⟩
  let Bs : X.affineOpens := ⟨X.basicOpen s, V'.2.basicOpen s⟩

  have hfx : f x ∈ Br.1 := ers hxs
  obtain ⟨r₂, s₂, hxs₂, ers₂, hB⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa n')
    (hPl n') x Br U' Bs V' hxs hx' e' h' hfx

  let B' : X.Opens := X.basicOpen (f.appLE Br.1 Bs.1 ers r₂)
  have hle : X.basicOpen s₂ ≤ B' := by
    change X.basicOpen s₂ ≤ X.basicOpen (f.appLE Br.1 Bs.1 ers r₂)
    rw [Scheme.basicOpen_appLE]
    exact le_inf (X.basicOpen_le s₂) ers₂
  have hB'le : B' ≤ X.basicOpen s := X.basicOpen_le _
  let s₂' : Γ(X, B') := X.presheaf.map (homOfLE hB'le).op s₂
  have hBs₂ : X.basicOpen s₂' = X.basicOpen s₂ := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.mpr hle
  have ers₂' : X.basicOpen s₂' ≤ f ⁻¹ᵁ Y.basicOpen r₂ := hBs₂ ▸ ers₂
  have hC : (f.appLE (Y.basicOpen r₂) (X.basicOpen s₂')
      ers₂').hom.IsStandardSmoothOfRelativeDimension n :=
    appLE_basicOpen_basicOpen (hPa n) (hPl n) f Br Bs ers hA r₂ s₂' ers₂'
  have hC' : (f.appLE (Y.basicOpen r₂) (X.basicOpen s₂)
      ers₂).hom.IsStandardSmoothOfRelativeDimension n :=
    (f.appLE_congr ers₂' rfl hBs₂ (fun g => g.hom.IsStandardSmoothOfRelativeDimension n)).mp hC

  haveI : Nonempty (X.basicOpen s₂) := ⟨⟨x, hxs₂⟩⟩
  haveI : Nontrivial Γ(X, X.basicOpen s₂) := inferInstance
  algebraize [(f.appLE (Y.basicOpen r₂) (X.basicOpen s₂) ers₂).hom]
  have h1 : Module.rank Γ(X, X.basicOpen s₂) Ω[Γ(X, X.basicOpen s₂)⁄Γ(Y, Y.basicOpen r₂)] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have h2 : Module.rank Γ(X, X.basicOpen s₂) Ω[Γ(X, X.basicOpen s₂)⁄Γ(Y, Y.basicOpen r₂)] = n' :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n'
  exact_mod_cast h1.symm.trans h2

theorem exists_chart {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  algebraize [(f.appLE U V e).hom]
  obtain ⟨ι, σ, _, hfin, ⟨P⟩⟩ := hstd.out
  exact ⟨P.dimension, ⟨U, hU⟩, ⟨V, hV⟩, hx, e, ⟨⟨ι, σ, ‹_›, hfin, P, rfl⟩⟩⟩

theorem exists_smoothOfRelativeDimension_of_preconnectedSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [PreconnectedSpace X] : ∃ n : ℕ, SmoothOfRelativeDimension n f := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, ⟨fun x => (IsEmpty.false x).elim⟩⟩
  obtain ⟨n₀, U₀, V₀, hx₀, e₀, h₀⟩ := exists_chart f x₀
  let S : Set X := {x | ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
    (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n₀}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨U, V, hxV, e, h⟩
    exact ⟨V.1, fun y hy => ⟨U, V, hy, e, h⟩, V.1.isOpen, hxV⟩
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hxS
    obtain ⟨m, U, V, hxV, e, h⟩ := exists_chart f x
    refine ⟨V.1, fun y hy hyS => ?_, V.1.isOpen, hxV⟩
    obtain ⟨U', V', hyV', e', h'⟩ := hyS
    have hm : m = n₀ :=
      eq_of_isStandardSmoothOfRelativeDimension_appLE f y U V hy e h U' V' hyV' e' h'
    subst hm
    exact hxS ⟨U, V, hxV, e, h⟩
  have hS : S = Set.univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨x₀, U₀, V₀, hx₀, e₀, h₀⟩
  refine ⟨n₀, ⟨fun x => ?_⟩⟩
  have hxS : x ∈ S := hS ▸ Set.mem_univ x
  obtain ⟨U, V, hxV, e, h⟩ := hxS
  exact ⟨U.1, U.2, V.1, V.2, hxV, e, h⟩

end R1NeronObjE7

open AlgebraicGeometry CategoryTheory in
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [PreconnectedSpace X] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f :=
  R1NeronObjE7.exists_smoothOfRelativeDimension_of_preconnectedSpace f

end S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace (solution)
