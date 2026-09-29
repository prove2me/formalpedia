-- Prove2me | solution 1 for AlgebraicGeometry.exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/52d57ef1-169c-528a-ac69-03a908b1b7c1

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage

namespace P2mPushoutThickeningReduce

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] (φ' : B' →+* B) (φ'' : B'' →+* B)

lemma mem_pullbackRing_iff (x : B' × B'') : x ∈ pullbackRing φ' φ'' ↔ φ' x.1 = φ'' x.2 := Iff.rfl

lemma pullbackFst_apply (x : pullbackRing φ' φ'') : pullbackFst φ' φ'' x = x.1.1 := rfl
lemma pullbackSnd_apply (x : pullbackRing φ' φ'') : pullbackSnd φ' φ'' x = x.1.2 := rfl

lemma surjective_pullbackFst (h : Function.Surjective φ'') : Function.Surjective (pullbackFst φ' φ'') := by
  intro b'
  obtain ⟨b'', hb''⟩ := h (φ' b')
  exact ⟨⟨(b', b''), (mem_pullbackRing_iff φ' φ'' _).2 hb''.symm⟩, rfl⟩

lemma surjective_pullbackSnd (h : Function.Surjective φ') : Function.Surjective (pullbackSnd φ' φ'') := by
  intro b''
  obtain ⟨b', hb'⟩ := h (φ'' b'')
  exact ⟨⟨(b', b''), (mem_pullbackRing_iff φ' φ'' _).2 hb'⟩, rfl⟩

lemma ker_pullbackFst_inf_ker_pullbackSnd :
    RingHom.ker (pullbackFst φ' φ'') ⊓ RingHom.ker (pullbackSnd φ' φ'') = ⊥ := by
  refine le_bot_iff.mp fun x hx => ?_
  have h1 : pullbackFst φ' φ'' x = 0 := (Ideal.mem_inf.mp hx).1
  have h2 : pullbackSnd φ' φ'' x = 0 := (Ideal.mem_inf.mp hx).2
  rw [Ideal.mem_bot]
  exact Subtype.ext (Prod.ext h1 h2)

lemma ker_pullbackFst_le : RingHom.ker (pullbackFst φ' φ'') ≤ (RingHom.ker φ'').comap (pullbackSnd φ' φ'') := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [Ideal.mem_comap, RingHom.mem_ker, pullbackSnd_apply, ← (mem_pullbackRing_iff φ' φ'' x.1).1 x.2,
    ← pullbackFst_apply, hx, map_zero]

lemma ker_pullbackSnd_le : RingHom.ker (pullbackSnd φ' φ'') ≤ (RingHom.ker φ').comap (pullbackFst φ' φ'') := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [Ideal.mem_comap, RingHom.mem_ker, pullbackFst_apply, (mem_pullbackRing_iff φ' φ'' x.1).1 x.2,
    ← pullbackSnd_apply, hx, map_zero]

lemma isNilpotent_ker_pullbackFst (h : IsNilpotent (RingHom.ker φ'')) :
    IsNilpotent (RingHom.ker (pullbackFst φ' φ'')) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← ker_pullbackFst_inf_ker_pullbackSnd φ' φ'']
  refine le_inf (Ideal.pow_le_self (Nat.succ_ne_zero n)) ?_
  calc RingHom.ker (pullbackFst φ' φ'') ^ (n + 1) ≤ RingHom.ker (pullbackFst φ' φ'') ^ n :=
        Ideal.pow_le_pow_right (Nat.le_succ n)
    _ ≤ ((RingHom.ker φ'').comap (pullbackSnd φ' φ'')) ^ n := Ideal.pow_right_mono (ker_pullbackFst_le φ' φ'') n
    _ ≤ ((RingHom.ker φ'') ^ n).comap (pullbackSnd φ' φ'') := Ideal.le_comap_pow _ n
    _ = RingHom.ker (pullbackSnd φ' φ'') := by rw [hn, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]

lemma isNilpotent_ker_pullbackSnd (h : IsNilpotent (RingHom.ker φ')) :
    IsNilpotent (RingHom.ker (pullbackSnd φ' φ'')) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← ker_pullbackFst_inf_ker_pullbackSnd φ' φ'']
  refine le_inf ?_ (Ideal.pow_le_self (Nat.succ_ne_zero n))
  calc RingHom.ker (pullbackSnd φ' φ'') ^ (n + 1) ≤ RingHom.ker (pullbackSnd φ' φ'') ^ n :=
        Ideal.pow_le_pow_right (Nat.le_succ n)
    _ ≤ ((RingHom.ker φ').comap (pullbackFst φ' φ'')) ^ n := Ideal.pow_right_mono (ker_pullbackSnd_le φ' φ'') n
    _ ≤ ((RingHom.ker φ') ^ n).comap (pullbackFst φ' φ'') := Ideal.le_comap_pow _ n
    _ = RingHom.ker (pullbackFst φ' φ'') := by rw [hn, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]

end P2mPushoutThickeningReduce

open P2mPushoutThickeningReduce in
theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {X' X'' Z : Scheme.{0}} (f' : X' ⟶ Spec (CommRingCat.of B')) (f'' : X'' ⟶ Spec (CommRingCat.of B''))
    (fZ : Z ⟶ Spec (CommRingCat.of B))
    (h' : Z ⟶ X') (hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ')))
    (h'' : Z ⟶ X'') (hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ''))) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (k' : X' ⟶ X) (k'' : X'' ⟶ X),
      IsPullback k' f' f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
      IsPullback k'' f'' f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ∧
      h' ≫ k' = h'' ≫ k'' ∧ IsPushout h' h'' k' k'' ∧
      IsClosedImmersion k' ∧ IsClosedImmersion k'' ∧ Function.Bijective k'.base ∧ Function.Bijective k''.base ∧
      (Flat f' → Flat f'' → Flat f) ∧ (IsProper f' → IsProper f) ∧ (Smooth f' → Smooth f'' → Smooth f) := by
  obtain ⟨X, f, k', k'', h1, h2, h3, h4, hfl, hfp⟩ :=
    AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
      φ' φ'' hφ's hφ''s hφ'n hφ''n f' f'' fZ h' hh' h'' hh''
  have T' := AlgebraicGeometry.isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
    (pullbackFst φ' φ'') (surjective_pullbackFst φ' φ'' hφ''s) (isNilpotent_ker_pullbackFst φ' φ'' hφ''n)
    f f' k' h1
  have T'' := AlgebraicGeometry.isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
    (pullbackSnd φ' φ'') (surjective_pullbackSnd φ' φ'' hφ's) (isNilpotent_ker_pullbackSnd φ' φ'' hφ'n)
    f f'' k'' h2
  refine ⟨X, f, k', k'', h1, h2, h3, h4, T'.1.1, T''.1.1, T'.1.2, T''.1.2, hfl, T'.2.2.1, fun hs' hs'' => ?_⟩
  haveI := hs'; haveI := hs''
  have hf : Flat f := hfl inferInstance inferInstance
  have hp : LocallyOfFinitePresentation f := hfp inferInstance inferInstance inferInstance inferInstance
  exact T'.2.2.2 hf hp hs'

end S_AlgebraicGeometry_exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent (solution)
