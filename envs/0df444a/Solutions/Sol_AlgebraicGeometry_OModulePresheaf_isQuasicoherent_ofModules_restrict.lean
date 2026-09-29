-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/69971035-6071-5a40-a518-92bd6b13c796

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_restrict

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace K1SOL
open AlgebraicGeometry.OModulePresheaf

theorem main
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (N : X.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent) (W : X.Opens) :
    (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).IsQuasicoherent := by
  intro O f
  have hO' : IsAffineOpen (W.ι ''ᵁ O.1) := O.2.image_of_isOpenImmersion W.ι

  set f' : Γ(X, W.ι ''ᵁ O.1) := (W.ι.appIso O.1).inv.hom f with hf'
  have key := hN ⟨W.ι ''ᵁ O.1, hO'⟩ f'

  have hhom : ∀ {V₁ V₂ : (↑W : Scheme).Opens} (h : V₁ ≤ V₂),
      (W.ι.opensFunctor.map (homOfLE h)).op = (homOfLE (W.ι.image_mono h)).op :=
    fun h => Subsingleton.elim _ _

  have gen : ∀ (V : X.Opens) (hV : V ≤ W.ι ''ᵁ O.1), V = X.basicOpen f' →
      (∀ x : Γ(N, V), ∃ (n : ℕ) (y : Γ(N, W.ι ''ᵁ O.1)),
          N.presheaf.map (homOfLE hV).op y = (X.presheaf.map (homOfLE hV).op).hom (f' ^ n) • x) ∧
      (∀ y : Γ(N, W.ι ''ᵁ O.1), N.presheaf.map (homOfLE hV).op y = 0 →
          ∃ n : ℕ, (f' ^ n : Γ(X, W.ι ''ᵁ O.1)) • y = 0) := by
    rintro V hV rfl
    exact key
  obtain ⟨hA, hB⟩ := gen (W.ι ''ᵁ (↑W : Scheme).basicOpen f)
    (W.ι.image_mono ((↑W : Scheme).basicOpen_le f)) (Scheme.image_basicOpen W.ι f)

  have hnat : ∀ n : ℕ, (W.ι.appIso ((↑W : Scheme).basicOpen f)).inv.hom
      (((↑W : Scheme).presheaf.map (homOfLE ((↑W : Scheme).basicOpen_le f)).op).hom (f ^ n)) =
      (X.presheaf.map (homOfLE (W.ι.image_mono ((↑W : Scheme).basicOpen_le f))).op).hom (f' ^ n) := by
    intro n
    have nat := W.ι.appIso_inv_naturality (homOfLE ((↑W : Scheme).basicOpen_le f)).op
    rw [Functor.op_map, Quiver.Hom.unop_op, hhom] at nat
    have nat' := congrArg (fun φ => φ.hom (f ^ n)) nat
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at nat'
    rw [nat']
    show (X.presheaf.map _).hom ((W.ι.appIso O.1).inv.hom (f ^ n)) = _
    congr 1
    rw [map_pow]
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := hA x
    refine ⟨n, y, ?_⟩
    change N.presheaf.map (W.ι.opensFunctor.map (homOfLE ((↑W : Scheme).basicOpen_le f))).op y =
      ((W.ι.appIso ((↑W : Scheme).basicOpen f)).inv.hom
        (((↑W : Scheme).presheaf.map (homOfLE ((↑W : Scheme).basicOpen_le f)).op).hom (f ^ n)) :
          Γ(X, W.ι ''ᵁ (↑W : Scheme).basicOpen f)) •
        (show Γ(N, W.ι ''ᵁ (↑W : Scheme).basicOpen f) from x)
    rw [hhom, hy, hnat]
  · intro y hy
    change N.presheaf.map (W.ι.opensFunctor.map (homOfLE ((↑W : Scheme).basicOpen_le f))).op y = 0 at hy
    rw [hhom] at hy
    obtain ⟨n, hn⟩ := hB y hy
    refine ⟨n, ?_⟩
    change ((W.ι.appIso O.1).inv.hom (f ^ n) : Γ(X, W.ι ''ᵁ O.1)) • (show Γ(N, W.ι ''ᵁ O.1) from y) = 0
    rw [map_pow]
    exact hn

end K1SOL

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (N : X.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent) (W : X.Opens) :
    (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).IsQuasicoherent :=
  K1SOL.main π N hN W

end S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_restrict
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_restrict (solution)
