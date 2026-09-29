-- Prove2me | solution 1 for AlgebraicGeometry.isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d21e2f35-45e1-580e-a186-03c3e063a849

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_AlgebraicGeometry_exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage

namespace FlatPushoutAux

theorem pullbackFst_surjective {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ''s : Function.Surjective φ'') :
    Function.Surjective (pullbackFst φ' φ'') := by
  intro b'
  obtain ⟨b'', hb''⟩ := hφ''s (φ' b')
  refine ⟨⟨(b', b''), ?_⟩, rfl⟩
  show (φ'.comp (RingHom.fst B' B'')) (b', b'') = (φ''.comp (RingHom.snd B' B'')) (b', b'')
  simp [hb'']

theorem isNilpotent_ker_pullbackFst {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ''n : IsNilpotent (RingHom.ker φ'')) :
    IsNilpotent (RingHom.ker (pullbackFst φ' φ'')) := by
  obtain ⟨n, hn⟩ := hφ''n
  have hmap : Ideal.map (pullbackSnd φ' φ'') (RingHom.ker (pullbackFst φ' φ'')) ≤ RingHom.ker φ'' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx' : φ' x.1.1 = φ'' x.1.2 := x.2
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change φ'' x.1.2 = 0
    rw [← hx']
    have hx0 : (x : B' × B'').1 = 0 := hx
    rw [hx0, map_zero]
  refine ⟨n + 1, ?_⟩
  rw [Submodule.zero_eq_bot, eq_bot_iff]
  intro x hx
  have h1 : x ∈ RingHom.ker (pullbackFst φ' φ'') := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
  have h2 : pullbackSnd φ' φ'' x ∈ Ideal.map (pullbackSnd φ' φ'') (RingHom.ker (pullbackFst φ' φ'') ^ (n + 1)) :=
    Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h2
  have h3 : (Ideal.map (pullbackSnd φ' φ'') (RingHom.ker (pullbackFst φ' φ''))) ^ (n + 1) ≤ ⊥ := by
    calc _ ≤ RingHom.ker φ'' ^ (n + 1) := Ideal.pow_right_mono hmap _
      _ ≤ RingHom.ker φ'' ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := by rw [hn, Submodule.zero_eq_bot]
  have h4 : pullbackSnd φ' φ'' x = 0 := by simpa using h3 h2
  rw [RingHom.mem_ker] at h1
  rw [Submodule.mem_bot]
  apply Subtype.ext
  exact Prod.ext h1 h4

end FlatPushoutAux

theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {Y Y' Y'' Y₀ : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat f]
    (f' : Y' ⟶ Spec (CommRingCat.of B')) (f'' : Y'' ⟶ Spec (CommRingCat.of B'')) (f₀ : Y₀ ⟶ Spec (CommRingCat.of B))
    (k' : Y' ⟶ Y) (hk' : IsPullback k' f' f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (k'' : Y'' ⟶ Y) (hk'' : IsPullback k'' f'' f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (h' : Y₀ ⟶ Y') (hh' : IsPullback h' f₀ f' (Spec.map (CommRingCat.ofHom φ')))
    (h'' : Y₀ ⟶ Y'') (hh'' : IsPullback h'' f₀ f'' (Spec.map (CommRingCat.ofHom φ'')))
    (hcomm : h' ≫ k' = h'' ≫ k'') :
    IsPushout h' h'' k' k'' := by
  have hF' : Flat f' := MorphismProperty.of_isPullback hk' inferInstance
  have hF'' : Flat f'' := MorphismProperty.of_isPullback hk'' inferInstance
  obtain ⟨X, fX, l', l'', hl', hl'', -, hpoX, -, -, -, -, hflat, -, -⟩ :=
    AlgebraicGeometry.exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent
      φ' φ'' hφ's hφ''s hφ'n hφ''n f' f'' f₀ h' hh' h'' hh''
  haveI : Flat fX := hflat hF' hF''
  have hc' : l' ≫ hpoX.desc k' k'' hcomm = k' := hpoX.inl_desc _ _ _
  have hc'' : l'' ≫ hpoX.desc k' k'' hcomm = k'' := hpoX.inr_desc _ _ _
  have hcf : hpoX.desc k' k'' hcomm ≫ f = fX := by
    apply hpoX.hom_ext
    · rw [← Category.assoc, hc', hk'.w, hl'.w]
    · rw [← Category.assoc, hc'', hk''.w, hl''.w]
  haveI : IsIso (hpoX.desc k' k'' hcomm) :=
    AlgebraicGeometry.isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left
      (pullbackFst φ' φ'') (FlatPushoutAux.pullbackFst_surjective φ' φ'' hφ''s)
      (FlatPushoutAux.isNilpotent_ker_pullbackFst φ' φ'' hφ''n)
      fX f (hpoX.desc k' k'' hcomm) hcf f' f' l' hl' k' hk' (𝟙 Y') (by rw [hc', Category.id_comp])
  exact hpoX.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (hpoX.desc k' k'' hcomm))
    (by simp) (by simp) (by simpa using hc') (by simpa using hc'')

end S_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
end P2MW
export P2MW.S_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd (solution)
