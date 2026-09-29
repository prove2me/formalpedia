-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/83325b3e-e3f9-5fb8-a0f2-9f483ea5d198

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace B30NI

theorem eq_top_of_sup_smul_top_eq_top {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (I : Ideal S) (hI : IsNilpotent I) (N : Submodule S M) (h : N ⊔ I • ⊤ = ⊤) : N = ⊤ := by
  obtain ⟨n, hn⟩ := hI
  have key : ∀ k : ℕ, N ⊔ I ^ k • ⊤ = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      apply le_antisymm le_top
      calc (⊤ : Submodule S M) = N ⊔ I ^ k • ⊤ := ih.symm
        _ = N ⊔ I ^ k • (N ⊔ I • ⊤) := by rw [h]
        _ = N ⊔ (I ^ k • N ⊔ I ^ (k + 1) • ⊤) := by rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
        _ ≤ N ⊔ I ^ (k + 1) • ⊤ := by
          apply sup_le (le_sup_left) (sup_le ?_ le_sup_right)
          exact le_sup_of_le_left Submodule.smul_le_right
  have := key n
  rwa [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this

theorem bijective_of_flat_of_isNilpotent
    {P S A : Type*} [CommRing P] [CommRing S] [CommRing A] [Algebra P S] [Algebra P A] [Module.Flat P A]
    (I : Ideal P) (hI : IsNilpotent I)
    (φ : S →+* A) (hφ : φ.comp (algebraMap P S) = algebraMap P A)
    (hsurj : ∀ a : A, ∃ s : S, φ s - a ∈ I.map (algebraMap P A))
    (hinj : ∀ s : S, φ s ∈ I.map (algebraMap P A) → s ∈ I.map (algebraMap P S)) :
    Function.Bijective φ := by
  classical
  obtain ⟨n, hn⟩ := hI
  have hISn : (I.map (algebraMap P S)) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
  have hIA : I.map (algebraMap P A) = (I.map (algebraMap P S)).map φ := by rw [Ideal.map_map, hφ]

  have hsurjφ : Function.Surjective φ := by
    letI : Algebra S A := φ.toAlgebra
    have h1 : LinearMap.range (Algebra.linearMap S A) ⊔ (I.map (algebraMap P S)) • ⊤ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      obtain ⟨s, hs⟩ := hsurj a
      rw [hIA] at hs
      have : a = φ s - (φ s - a) := by ring
      rw [this]
      refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨s, rfl⟩) (Submodule.mem_sup_right ?_)
      rw [Ideal.smul_top_eq_map]
      exact hs
    have h2 := eq_top_of_sup_smul_top_eq_top (I.map (algebraMap P S)) ⟨n, by rw [hISn, Ideal.zero_eq_bot]⟩ _ h1
    intro a
    have : a ∈ LinearMap.range (Algebra.linearMap S A) := h2 ▸ Submodule.mem_top
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hs⟩
  refine ⟨?_, hsurjφ⟩
  rw [RingHom.injective_iff_ker_eq_bot]

  have hK : RingHom.ker φ ≤ I.map (algebraMap P S) * RingHom.ker φ := by
    intro x hx
    have hx0 : φ x = 0 := hx
    have hxI : x ∈ I.map (algebraMap P S) := hinj x (by rw [hx0]; exact zero_mem _)
    rw [Ideal.map] at hxI
    obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hxI
    have hg : ∀ j, ∃ i ∈ I, (algebraMap P S) i = (g j : S) := fun j => (g j).2
    choose i0 hi0I hi0 using hg

    have hrel : ∑ j, (i0 j) • φ (c j) = 0 := by
      have h := congrArg φ hsum
      rw [hx0, map_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, map_mul, ← hi0 j, ← RingHom.comp_apply, hφ, Algebra.smul_def, mul_comm]
    obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := P) (M := A) (f := i0) (x := fun j => φ (c j)) hrel
    choose t ht using fun l => hsurjφ (y l)
    have hκ : ∀ j, c j - ∑ l, (algebraMap P S) (a j l) * t l ∈ RingHom.ker φ := by
      intro j
      have hyj : φ (c j) = ∑ l, a j l • y l := hy j
      rw [RingHom.mem_ker, map_sub, map_sum, sub_eq_zero, hyj]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, ← RingHom.comp_apply, hφ, ht, Algebra.smul_def]
    have hzero : ∑ j, (algebraMap P S) (i0 j) * ∑ l, (algebraMap P S) (a j l) * t l = 0 := by
      calc ∑ j, (algebraMap P S) (i0 j) * ∑ l, (algebraMap P S) (a j l) * t l = ∑ j, ∑ l, (algebraMap P S) (i0 j) * ((algebraMap P S) (a j l) * t l) := by
            simp_rw [Finset.mul_sum]
        _ = ∑ l, ∑ j, (algebraMap P S) (i0 j) * ((algebraMap P S) (a j l) * t l) := Finset.sum_comm
        _ = ∑ l, (algebraMap P S) (∑ j, i0 j * a j l) * t l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, mul_assoc]
        _ = 0 := by simp [ha]
    have hxeq : x = ∑ j, (algebraMap P S) (i0 j) * (c j - ∑ l, (algebraMap P S) (a j l) * t l) := by
      rw [← hsum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hzero, sub_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, ← hi0 j, mul_comm]
    rw [hxeq]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap P S) (hi0I j)) (hκ j)
  have hle : ∀ k, RingHom.ker φ ≤ (I.map (algebraMap P S)) ^ k * RingHom.ker φ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc RingHom.ker φ ≤ I.map (algebraMap P S) * RingHom.ker φ := hK
        _ ≤ I.map (algebraMap P S) * ((I.map (algebraMap P S)) ^ k * RingHom.ker φ) := Ideal.mul_mono_right ih
        _ = (I.map (algebraMap P S)) ^ (k + 1) * RingHom.ker φ := by rw [← mul_assoc, ← pow_succ']
  exact le_bot_iff.mp (by simpa [hISn] using hle n)

theorem surjective_specMap_of_surjective_of_isNilpotent {P B' : Type} [CommRing P] [CommRing B']
    (π : P →+* B') (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) :
    Surjective (Spec.map (CommRingCat.ofHom π)) := by
  refine ⟨fun p => ?_⟩
  have hker : RingHom.ker π ≤ p.asIdeal := by
    intro i hi
    obtain ⟨n, hn⟩ := hn
    have h : i ^ n ∈ (RingHom.ker π) ^ n := Ideal.pow_mem_pow hi n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
    exact p.isPrime.mem_of_pow_mem n (h ▸ p.asIdeal.zero_mem)
  haveI hprime : (Ideal.map π p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hπ hker
  refine ⟨⟨Ideal.map π p.asIdeal, hprime⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (CommRingCat.ofHom π).hom (Ideal.map π p.asIdeal) = p.asIdeal
  rw [CommRingCat.hom_ofHom, Ideal.comap_map_of_surjective _ hπ, sup_eq_left]
  exact hker

section strMap

variable {P : Type} [CommRing P] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of P))

noncomputable def strMap (x : X) : CommRingCat.of P ⟶ X.presheaf.stalk x :=
  StructureSheaf.toStalk P (fX.base x) ≫ fX.stalkMap x

theorem strMap_eq (x : X) :
    strMap fX x = (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ fX.appTop ≫ X.presheaf.germ ⊤ x trivial := by
  simp only [strMap, StructureSheaf.toStalk, Category.assoc]
  erw [Scheme.Hom.germ_stalkMap fX ⊤ x trivial]
  rfl

theorem flat_strMap [Flat fX] (x : X) : (strMap fX x).hom.Flat := by
  have h1 : (StructureSheaf.toStalk P (fX.base x)).hom.Flat := by
    have : Module.Flat P ((Spec.structureSheaf P).presheaf.stalk (fX.base x)) :=
      IsLocalization.flat _ (fX.base x).asIdeal.primeCompl
    exact this
  have h2 : (fX.stalkMap x).hom.Flat := Flat.stalkMap fX x
  rw [strMap, CommRingCat.hom_comp]
  exact h1.comp h2

end strMap

section kernel

variable {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    {X X' : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of P)) (fX' : X' ⟶ Spec (CommRingCat.of B')) (iX : X' ⟶ X)
    (hiX : IsPullback iX fX' fX (Spec.map (CommRingCat.ofHom π)))

include hiX in
@[reassoc]
theorem appTop_comp_appTop : fX.appTop ≫ iX.appTop = (Spec.map (CommRingCat.ofHom π)).appTop ≫ fX'.appTop := by
  rw [← Scheme.Hom.comp_appTop, hiX.w, Scheme.Hom.comp_appTop]

include hiX in

theorem strMap_comp_stalkMap₁ (x' : X') :
    strMap fX (iX.base x') ≫ iX.stalkMap x' =
      CommRingCat.ofHom π ≫ strMap fX' x' := by
  rw [strMap_eq, strMap_eq]
  simp only [Category.assoc, Scheme.Hom.germ_stalkMap]
  erw [appTop_comp_appTop_assoc π fX fX' iX hiX]
  rw [Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

include hiX in

theorem strMap_comp_stalkMap₂ (x' : X') :
    strMap fX (iX.base x') ≫ iX.stalkMap x' =
      CommRingCat.ofHom π ≫ strMap fX' x' := by
  rw [strMap_eq, strMap_eq]
  simp only [Category.assoc, Scheme.Hom.germ_stalkMap]
  change (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ fX.appTop ≫ iX.appTop ≫ X'.presheaf.germ ⊤ x' trivial = _
  rw [appTop_comp_appTop_assoc π fX fX' iX hiX, Scheme.ΓSpecIso_inv_naturality_assoc]

include hiX in

theorem strMap_comp_stalkMap_apply (x' : X') (i : P) :
    (iX.stalkMap x') (strMap fX (iX.base x') i) = strMap fX' x' (π i) := by
  have h := congrArg (fun k => (k : CommRingCat.of P ⟶ _) i) (strMap_comp_stalkMap₂ π fX fX' iX hiX x')
  simpa using h

include hiX in

theorem map_ker_le_ker_stalkMap (x' : X') :
    Ideal.map (strMap fX (iX.base x')).hom (RingHom.ker π) ≤ RingHom.ker (iX.stalkMap x').hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro i hi
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have h := strMap_comp_stalkMap_apply π fX fX' iX hiX x' i
  rw [RingHom.mem_ker.mp hi, map_zero] at h
  exact h

end kernel

section kernel2

variable {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B') (hπ : Function.Surjective π)
    {X X' : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of P)) (fX' : X' ⟶ Spec (CommRingCat.of B')) (iX : X' ⟶ X)
    (hiX : IsPullback iX fX' fX (Spec.map (CommRingCat.ofHom π)))

theorem fromSpecStalk_comp (x : X) : X.fromSpecStalk x ≫ fX = Spec.map (strMap fX x) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq']
  exact (Spec.map_comp (StructureSheaf.toStalk P (fX.base x)) (fX.stalkMap x)).symm

include hπ hiX in

theorem ker_stalkMap_le_map [IsClosedImmersion iX] (x' : X') :
    RingHom.ker (iX.stalkMap x').hom ≤ Ideal.map (strMap fX (iX.base x')).hom (RingHom.ker π) := by
  classical
  set x := iX.base x' with hx
  set J : Ideal (X.presheaf.stalk x) := Ideal.map (strMap fX x).hom (RingHom.ker π) with hJ
  have hJle : J ≤ RingHom.ker (iX.stalkMap x').hom := map_ker_le_ker_stalkMap π fX fX' iX hiX x'
  have hJtop : J ≠ ⊤ := fun h =>
    (RingHom.ker_ne_top (iX.stalkMap x').hom) (top_le_iff.mp (h ▸ hJle))
  haveI : Nontrivial ((X.presheaf.stalk x) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI : IsLocalRing ((X.presheaf.stalk x) ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  set qJ : X.presheaf.stalk x ⟶ CommRingCat.of ((X.presheaf.stalk x) ⧸ J) :=
    CommRingCat.ofHom (Ideal.Quotient.mk J) with hqJ
  have hloc : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom qJ.hom := by rw [hqJ]; exact hloc

  set t : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ J)) ⟶ X := Spec.map qJ ≫ X.fromSpecStalk x with ht
  have hkill : RingHom.ker π ≤ RingHom.ker ((Ideal.Quotient.mk J).comp (strMap fX x).hom) := by
    intro i hi
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hi
  set β : B' →+* (X.presheaf.stalk x) ⧸ J :=
    π.liftOfSurjective hπ ⟨(Ideal.Quotient.mk J).comp (strMap fX x).hom, hkill⟩ with hβdef
  have hβ : β.comp π = (Ideal.Quotient.mk J).comp (strMap fX x).hom := π.liftOfSurjective_comp hπ _
  set g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ J)) ⟶ Spec (CommRingCat.of B') :=
    Spec.map (CommRingCat.ofHom β) with hg
  have htg : t ≫ fX = g ≫ Spec.map (CommRingCat.ofHom π) := by
    rw [ht, hg, Category.assoc, fromSpecStalk_comp fX x, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext i
    change (Ideal.Quotient.mk J) ((strMap fX x) i) = β (π i)
    rw [← RingHom.comp_apply, ← hβ, RingHom.comp_apply]
  have hz := hiX.lift_fst t g htg
  set z := hiX.lift t g htg with hzdef

  have htpt : t.base (IsLocalRing.closedPoint ((X.presheaf.stalk x) ⧸ J)) = x := by
    rw [ht, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hzpt : z.base (IsLocalRing.closedPoint ((X.presheaf.stalk x) ⧸ J)) = x' := by
    apply iX.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hz, htpt]

  intro r hr
  rw [RingHom.mem_ker] at hr
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.germ_exist r
  have key : ∀ (f : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ J)) ⟶ X)
      (hf : f = Spec.map qJ ≫ X.fromSpecStalk x)
      (hU : f.base (IsLocalRing.closedPoint ((X.presheaf.stalk x) ⧸ J)) ∈ U),
      X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f = X.presheaf.germ U x hxU ≫ qJ := by
    rintro f rfl hU
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk qJ U hU
  have hU' : (z ≫ iX).base (IsLocalRing.closedPoint ((X.presheaf.stalk x) ⧸ J)) ∈ U := by
    rw [Scheme.Hom.comp_apply, hzpt]; exact hxU
  have k1 := key (z ≫ iX) (by rw [hz, ht]) hU'
  rw [Scheme.stalkClosedPointTo_comp] at k1
  have k1' : (Scheme.stalkClosedPointTo z).hom ((iX.stalkMap (z.base (IsLocalRing.closedPoint ((X.presheaf.stalk x) ⧸ J)))).hom
      ((X.presheaf.germ U _ hU').hom s)) = qJ.hom ((X.presheaf.germ U x hxU).hom s) := by
    have h := congrArg (fun k => k.hom s) k1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h

  have hvan : ∀ (w : X') (hw : iX.base w ∈ U), w = x' →
      (iX.stalkMap w).hom ((X.presheaf.germ U (iX.base w) hw).hom s) = 0 := by
    rintro w hw rfl
    exact hr
  have h0 : (iX.stalkMap (z.base (IsLocalRing.closedPoint ((X.presheaf.stalk x) ⧸ J)))).hom
      ((X.presheaf.germ U _ hU').hom s) = 0 := hvan _ hU' hzpt
  rw [h0, map_zero] at k1'

  rw [hJ, ← Ideal.Quotient.eq_zero_iff_mem]
  exact k1'.symm

end kernel2

section congr

variable {P : Type} [CommRing P] {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of P))

theorem strMap_stalkCongr {y₁ y₂ : Y} (h : Inseparable y₁ y₂) :
    strMap fY y₁ ≫ (Y.presheaf.stalkCongr h).hom = strMap fY y₂ := by
  rw [strMap_eq, strMap_eq]
  simp only [Category.assoc]
  erw [TopCat.Presheaf.germ_stalkSpecializes]
  exact h.ge

end congr

section main

variable {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B') (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π))
    {X Y X' Y' : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of P)) [Flat fX] (fY : Y ⟶ Spec (CommRingCat.of P))
    (u : X ⟶ Y) (hu : u ≫ fY = fX)
    (fX' : X' ⟶ Spec (CommRingCat.of B')) (fY' : Y' ⟶ Spec (CommRingCat.of B'))
    (iX : X' ⟶ X) (hiX : IsPullback iX fX' fX (Spec.map (CommRingCat.ofHom π)))
    (iY : Y' ⟶ Y) (hiY : IsPullback iY fY' fY (Spec.map (CommRingCat.ofHom π)))
    (u' : X' ⟶ Y') (hu' : iX ≫ u = u' ≫ iY) [IsIso u']

omit [Flat fX] in
include hu in

theorem strMap_comp_stalkMap_u (x : X) : strMap fY (u.base x) ≫ u.stalkMap x = strMap fX x := by
  rw [strMap_eq, strMap_eq]
  simp only [Category.assoc, Scheme.Hom.germ_stalkMap]
  change (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ fY.appTop ≫ u.appTop ≫ X.presheaf.germ ⊤ x trivial = _
  rw [← Scheme.Hom.comp_appTop_assoc, hu]

include hπ hn hu hiX hiY hu' in

theorem isIso_stalkMap [IsClosedImmersion iX] [IsClosedImmersion iY] (x' : X') :
    IsIso (u.stalkMap (iX.base x')) := by
  classical
  letI algX : Algebra P (X.presheaf.stalk (iX.base x')) := (strMap fX (iX.base x')).hom.toAlgebra
  letI algY : Algebra P (Y.presheaf.stalk (u.base (iX.base x'))) := (strMap fY (u.base (iX.base x'))).hom.toAlgebra
  haveI : Module.Flat P (X.presheaf.stalk (iX.base x')) := flat_strMap fX (iX.base x')

  have sq := Scheme.Hom.stalkMap_congr_hom (iX ≫ u) (u' ≫ iY) hu' x'
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at sq

  set c := Y.presheaf.stalkCongr
    (.of_eq (congrArg (fun k => k.base x') hu') : Inseparable ((iX ≫ u).base x') ((u' ≫ iY).base x')) with hc
  have sq' : ∀ s, (iX.stalkMap x').hom ((u.stalkMap (iX.base x')).hom s) =
      (u'.stalkMap x').hom ((iY.stalkMap (u'.base x')).hom (c.hom.hom s)) := by
    intro s
    have h := congrArg (fun k => k.hom s) sq
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h

  have hcσ : strMap fY (u.base (iX.base x')) ≫ c.hom = strMap fY (iY.base (u'.base x')) :=
    strMap_stalkCongr fY _

  have hKX := ker_stalkMap_le_map π hπ fX fX' iX hiX x'
  have hKX' := map_ker_le_ker_stalkMap π fX fX' iX hiX x'
  have hKY := ker_stalkMap_le_map π hπ fY fY' iY hiY (u'.base x')

  have hu'bij := ConcreteCategory.bijective_of_isIso (u'.stalkMap x')
  have hiYsurj := iY.stalkMap_surjective (u'.base x')
  have hcbij := ConcreteCategory.bijective_of_isIso c.hom
  have hbij : Function.Bijective (u.stalkMap (iX.base x')).hom := by
    refine bijective_of_flat_of_isNilpotent (P := P) (RingHom.ker π) hn (u.stalkMap (iX.base x')).hom ?_ ?_ ?_
    ·
      change (u.stalkMap (iX.base x')).hom.comp (strMap fY (u.base (iX.base x'))).hom = (strMap fX (iX.base x')).hom
      rw [← CommRingCat.hom_comp, strMap_comp_stalkMap_u fX fY u hu]
    ·
      intro a
      obtain ⟨b, hb⟩ := hu'bij.2 ((iX.stalkMap x').hom a)
      obtain ⟨b', hb'⟩ := hiYsurj b
      obtain ⟨s, hs⟩ := hcbij.2 b'
      refine ⟨s, hKX ?_⟩
      rw [RingHom.mem_ker, map_sub, sub_eq_zero, sq' s]
      change (u'.stalkMap x').hom ((iY.stalkMap (u'.base x')).hom (c.hom.hom s)) = (iX.stalkMap x').hom a
      rw [show c.hom.hom s = b' from hs, show (iY.stalkMap (u'.base x')).hom b' = b from hb', hb]
    ·
      intro s hs
      have h1 : (iX.stalkMap x').hom ((u.stalkMap (iX.base x')).hom s) = 0 := hKX' hs
      rw [sq' s] at h1
      have h2 : (iY.stalkMap (u'.base x')).hom (c.hom.hom s) = 0 :=
        hu'bij.1 (by rw [h1, map_zero])
      have h3 : c.hom.hom s ∈ Ideal.map (strMap fY (iY.base (u'.base x'))).hom (RingHom.ker π) := hKY h2
      have hle : Ideal.map (strMap fY (iY.base (u'.base x'))).hom (RingHom.ker π) ≤
          Ideal.map c.hom.hom (Ideal.map (strMap fY (u.base (iX.base x'))).hom (RingHom.ker π)) := by
        rw [Ideal.map_le_iff_le_comap]
        intro k hk
        rw [Ideal.mem_comap]
        have e : (strMap fY (iY.base (u'.base x'))).hom k =
            c.hom.hom ((strMap fY (u.base (iX.base x'))).hom k) := by
          rw [← hcσ]; rfl
        rw [e]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hk)
      obtain ⟨s₀, hs₀, hs₀e⟩ := (Ideal.mem_map_iff_of_surjective c.hom.hom hcbij.2).mp (hle h3)
      obtain rfl : s₀ = s := hcbij.1 hs₀e
      exact hs₀
  exact (ConcreteCategory.isIso_iff_bijective (u.stalkMap (iX.base x'))).mpr hbij

include hπ hn hu hiX hiY hu' in
theorem isIso_main : IsIso u := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : Surjective (Spec.map (CommRingCat.ofHom π)) := surjective_specMap_of_surjective_of_isNilpotent π hπ hn
  haveI : IsClosedImmersion iX := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hiX.flip inferInstance
  haveI : IsClosedImmersion iY := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hiY.flip inferInstance
  haveI : Surjective iX := MorphismProperty.of_isPullback (P := @Surjective) hiX.flip inferInstance
  haveI : Surjective iY := MorphismProperty.of_isPullback (P := @Surjective) hiY.flip inferInstance
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, fun x => ?_⟩
  · have e1 : IsIso iX.base := (TopCat.isIso_iff_isHomeomorph _).mpr
      (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨iX.isClosedEmbedding.isEmbedding, iX.surjective⟩)
    have e2 : IsIso iY.base := (TopCat.isIso_iff_isHomeomorph _).mpr
      (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨iY.isClosedEmbedding.isEmbedding, iY.surjective⟩)
    have e0 : IsIso u'.base := (TopCat.isIso_iff_isHomeomorph _).mpr (Scheme.homeoOfIso (asIso u')).isHomeomorph
    have e3 : IsIso (iX.base ≫ u.base) := by
      rw [← Scheme.Hom.comp_base, hu', Scheme.Hom.comp_base]
      infer_instance
    exact IsIso.of_isIso_comp_left iX.base u.base
  · obtain ⟨x', rfl⟩ := iX.surjective x
    exact isIso_stalkMap π hπ hn fX fY u hu fX' fY' iX hiX iY hiY u' hu' x'

end main

end B30NI

theorem solution
    {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B') (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π))
    {X Y X' Y' : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of P)) [Flat fX] (fY : Y ⟶ Spec (CommRingCat.of P))
    (u : X ⟶ Y) (hu : u ≫ fY = fX)
    (fX' : X' ⟶ Spec (CommRingCat.of B')) (fY' : Y' ⟶ Spec (CommRingCat.of B'))
    (iX : X' ⟶ X) (hiX : IsPullback iX fX' fX (Spec.map (CommRingCat.ofHom π)))
    (iY : Y' ⟶ Y) (hiY : IsPullback iY fY' fY (Spec.map (CommRingCat.ofHom π)))
    (u' : X' ⟶ Y') (hu' : iX ≫ u = u' ≫ iY) [IsIso u'] :
    IsIso u :=
  B30NI.isIso_main π hπ hn fX fY u hu fX' fY' iX hiX iY hiY u' hu'

end S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left (solution)
