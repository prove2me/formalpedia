-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/43a502d4-530d-5a87-a104-b329e70440da

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk

set_option autoImplicit false

universe u

open TensorProduct

namespace FibreStalkBCRight

variable {A S R L : Type*} [CommRing A] [CommRing S] [CommRing R] [CommRing L]
  [Algebra A S] [Algebra A R] [Algebra A L] [Algebra R L] [IsScalarTower A R L]

@[reducible] noncomputable def tensorAlgebra : Algebra (S ⊗[A] R) (S ⊗[A] L) :=
  (Algebra.TensorProduct.map (AlgHom.id A S) (IsScalarTower.toAlgHom A R L)).toRingHom.toAlgebra

attribute [local instance] tensorAlgebra

theorem algebraMap_tensor_tmul (s : S) (r : R) :
    algebraMap (S ⊗[A] R) (S ⊗[A] L) (s ⊗ₜ r) = s ⊗ₜ algebraMap R L r := rfl

theorem isScalarTower_tensor : IsScalarTower S (S ⊗[A] R) (S ⊗[A] L) :=
  IsScalarTower.of_algebraMap_eq (R := S) (S := S ⊗[A] R) (A := S ⊗[A] L) fun s => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, algebraMap_tensor_tmul, map_one]

theorem isLocalization_tensor (M : Submonoid R) [IsLocalization M L] :
    IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R))) (S ⊗[A] L) := by
  haveI := isScalarTower_tensor (A := A) (S := S) (R := R) (L := L)
  refine IsLocalization.tensorProduct_tensorProduct_right A S M L ?_
  ext r
  rfl

theorem core (𝔭 : Ideal R) [𝔭.IsPrime] [IsLocalization.AtPrime L 𝔭]
    (𝔔 : Ideal (S ⊗[A] R)) [h𝔔 : 𝔔.IsPrime]
    (hQp : 𝔔.comap (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R)).toRingHom = 𝔭)
    (Tq : Type*) [CommRing Tq] [Algebra (S ⊗[A] R) Tq] [IsLocalization.AtPrime Tq 𝔔]
    (φ : L →+* Tq) (hφ : ∀ r : R, φ (algebraMap R L r) = algebraMap (S ⊗[A] R) Tq (1 ⊗ₜ r)) :
    ∃ (𝔮 : Ideal (S ⊗[A] L)) (_ : 𝔮.IsPrime) (e : Tq ≃+* Localization.AtPrime 𝔮),
      (∀ s : S, e (algebraMap (S ⊗[A] R) Tq (s ⊗ₜ[A] (1 : R))) =
        algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ l : L, e (φ l) = algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) ((1 : S) ⊗ₜ[A] l)) := by
  haveI := isScalarTower_tensor (A := A) (S := S) (R := R) (L := L)
  set T := S ⊗[A] R
  set M : Submonoid T := 𝔭.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R)) with hM
  haveI hloc : IsLocalization M (S ⊗[A] L) := isLocalization_tensor 𝔭.primeCompl

  have hdisj : Disjoint (M : Set T) (𝔔 : Set T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    apply hr
    rw [← hQp]
    exact hrQ

  let 𝔮 : Ideal (S ⊗[A] L) := 𝔔.map (algebraMap T (S ⊗[A] L))
  haveI h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (S ⊗[A] L) 𝔔 h𝔔 hdisj
  have hunder : 𝔮.comap (algebraMap T (S ⊗[A] L)) = 𝔔 :=
    IsLocalization.under_map_of_isPrime_disjoint M (S ⊗[A] L) h𝔔 hdisj

  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) (𝔮.comap (algebraMap T (S ⊗[A] L))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔮) 𝔮
  have hN : 𝔔.primeCompl = (Ideal.comap (algebraMap T (S ⊗[A] L)) 𝔮).primeCompl := by
    ext x
    change x ∉ 𝔔 ↔ x ∉ Ideal.comap (algebraMap T (S ⊗[A] L)) 𝔮
    rw [hunder]
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) 𝔔 := by
    change IsLocalization 𝔔.primeCompl (Localization.AtPrime 𝔮)
    rw [hN]
    exact this
  let e : Tq ≃ₐ[T] Localization.AtPrime 𝔮 := IsLocalization.algEquiv 𝔔.primeCompl Tq (Localization.AtPrime 𝔮)
  refine ⟨𝔮, h𝔮, e.toRingEquiv, ?_, ?_⟩
  ·
    intro s
    change e (algebraMap T Tq (s ⊗ₜ[A] (1 : R))) = _
    rw [e.commutes (s ⊗ₜ[A] (1 : R)), IsScalarTower.algebraMap_apply T (S ⊗[A] L) (Localization.AtPrime 𝔮),
      algebraMap_tensor_tmul, map_one]
  ·
    intro l
    suffices h : (e.toRingEquiv.toRingHom.comp φ) =
        (algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮)).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := L)).toRingHom by
      exact congrArg (fun f : L →+* Localization.AtPrime 𝔮 => f l) h
    refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
    ext r
    change e (φ (algebraMap R L r)) = algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) ((1 : S) ⊗ₜ[A] algebraMap R L r)
    rw [hφ, ← algebraMap_tensor_tmul, ← IsScalarTower.algebraMap_apply]
    exact e.commutes ((1 : S) ⊗ₜ r)

end FibreStalkBCRight

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace StalkPB

variable {R : Type u} [CommRing R] {X Z : Scheme.{u}}
  (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (U : Z.Opens) (hU : IsAffineOpen U)

@[reducible] def algU : Algebra R Γ(Z, U) :=
  ((z.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

lemma isoSpec_hom_algU : letI := algU z U
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U))) = U.ι ≫ z := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec z (isAffineOpen_top _) hU (le_top : U ≤ z ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← IsAffineOpen.isoSpec_inv_ι] at h
  change hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ z.appLE ⊤ U le_top).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, h, Category.assoc, Iso.hom_inv_id_assoc]

omit U hU in
lemma algebraMap_stalk_eq {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) (y : Y) [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) (r : R) :
    algebraMap R (Y.presheaf.stalk y) r =
      Y.presheaf.germ ⊤ y trivial (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) := by
  have h1 : Y.fromSpecStalk y ≫ g ≫ (Spec (CommRingCat.of R)).toSpecΓ =
      Spec.map (g.appTop ≫ Y.presheaf.germ ⊤ y trivial) := by
    rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
  rw [← Category.assoc, halg, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Spec.map_inj] at h1

  have h2 := congrArg (fun φ : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Y.presheaf.stalk y =>
    φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  erw [Iso.inv_hom_id_apply] at h2
  exact h2

omit U hU in
lemma fe_wrapper (k : Type u) [CommRing k] [Algebra R k] (g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap R k)))
    (x : ↥(pullback f g))
    [inst : Algebra R (X.presheaf.stalk ((pullback.fst f g).base x))]
    (hinst : inst = ((X.presheaf.germ ⊤ ((pullback.fst f g).base x) trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra) :
    ∃ (𝔮 : Ideal ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k)) (_ : 𝔮.IsPrime)
      (e : (pullback f g).presheaf.stalk x ≃+* Localization.AtPrime 𝔮),
      (∀ s : X.presheaf.stalk ((pullback.fst f g).base x),
        e (((pullback.fst f g).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[R] 1)) ∧
      (∀ c : k,
        e ((pullback f g).presheaf.germ ⊤ x trivial ((pullback.snd f g).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
          algebraMap ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k) (Localization.AtPrime 𝔮) (1 ⊗ₜ[R] c)) := by
  subst hg hinst
  obtain ⟨𝔮, h𝔮, e, -, h1, h2⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd X f k x
  exact ⟨𝔮, h𝔮, e, h1, h2⟩

variable [Algebra R Γ(Z, U)]
  (hφU : hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U))) = U.ι ≫ z)

include hφU

def φ : Spec Γ(Z, U) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U)))

lemma fromSpec_φ : (hU.isoSpec.inv ≫ U.ι) ≫ z = φ (R := R) U := by
  rw [Category.assoc, ← hφU, Iso.inv_hom_id_assoc]; rfl

def jmap : pullback (φ (R := R) U) f ⟶ pullback z f :=
  pullback.map (φ (R := R) U) f z f (hU.isoSpec.inv ≫ U.ι) (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, fromSpec_φ z U hU hφU]) (by simp)

def j : pullback f (φ (R := R) U) ⟶ pullback z f := (pullbackSymmetry f (φ (R := R) U)).hom ≫ jmap z f U hU hφU

scoped instance : IsOpenImmersion (jmap z f U hU hφU) := by unfold jmap; infer_instance
scoped instance : IsOpenImmersion (j z f U hU hφU) := by unfold j; infer_instance

lemma j_fst : j z f U hU hφU ≫ pullback.fst z f = pullback.snd f (φ (R := R) U) ≫ hU.isoSpec.inv ≫ U.ι := by
  simp only [j, jmap, pullback.map, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]

lemma j_snd : j z f U hU hφU ≫ pullback.snd z f = pullback.fst f (φ (R := R) U) := by
  simp only [j, jmap, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [pullbackSymmetry_hom_comp_snd]

lemma exists_j_eq (p : ↥(pullback z f)) (hpU : (pullback.fst z f).base p ∈ U) :
    ∃ q, (j z f U hU hφU).base q = p := by
  have : p ∈ Set.range (jmap z f U hU hφU).base := by
    unfold jmap
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · change (pullback.fst z f).base p ∈ Set.range (hU.isoSpec.inv ≫ U.ι).base
      rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.range_fromSpec]
      exact hpU
    · change (pullback.snd z f).base p ∈ Set.range (𝟙 X : X ⟶ X).base
      simp
  obtain ⟨q', hq'⟩ := this
  refine ⟨(pullbackSymmetry f (φ (R := R) U)).inv.base q', ?_⟩
  unfold j
  change ((pullbackSymmetry f (φ (R := R) U)).inv ≫ (pullbackSymmetry f (φ (R := R) U)).hom ≫ jmap z f U hU hφU).base q' = p
  rw [Iso.inv_hom_id_assoc]
  exact hq'

include hU in
set_option maxHeartbeats 6400000 in
theorem main
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    (hpU : (pullback.fst z f).base p ∈ U)
    (halgU : ∀ r : R, algebraMap R Γ(Z, U) r = (z.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t)) := by
  classical
  obtain ⟨q, rfl⟩ := exists_j_eq z f U hU hφU p hpU

  have hxx' : (pullback.snd z f).base ((j z f U hU hφU).base q) = (pullback.fst f (φ (R := R) U)).base q := by
    change ((j z f U hU hφU) ≫ pullback.snd z f).base q = _
    rw [j_snd z f U hU hφU]

  letI aB' : Algebra R (X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) :=
    ((X.presheaf.germ ⊤ ((pullback.fst f (φ (R := R) U)).base q) trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  let c : X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q)) ≅ X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q) := X.presheaf.stalkCongr (.of_eq hxx')
  have hc_germ : ∀ (W : X.Opens) (hW : (pullback.snd z f).base ((j z f U hU hφU).base q) ∈ W) (s : Γ(X, W)),
      c.hom (X.presheaf.germ W _ hW s) = X.presheaf.germ W ((pullback.fst f (φ (R := R) U)).base q) (hxx' ▸ hW) s := by
    intro W hW s
    change (X.presheaf.germ W _ hW ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm)) s = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have hc_alg : ∀ r : R, c.hom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q))) r) = algebraMap R (X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) r := by
    intro r
    rw [algebraMap_stalk_eq f _ halgX r, hc_germ]
    rfl
  let cA : X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q)) ≃ₐ[R] X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q) := AlgEquiv.ofRingEquiv (f := c.commRingCatIsoToRingEquiv) hc_alg

  have E1 : ∀ t : X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q)), (j z f U hU hφU).stalkMap q (((pullback.snd z f).stalkMap ((j z f U hU hφU).base q)).hom t) =
      ((pullback.fst f (φ (R := R) U)).stalkMap q).hom (c.hom t) := by
    intro t
    have h := Scheme.Hom.stalkMap_congr_hom ((j z f U hU hφU) ≫ pullback.snd z f) (pullback.fst f (φ (R := R) U)) (j_snd z f U hU hφU) q
    rw [Scheme.Hom.stalkMap_comp] at h
    exact CategoryTheory.ConcreteCategory.congr_hom h t

  have hjf : (j z f U hU hφU) ≫ pullback.fst z f = pullback.snd f (φ (R := R) U) ≫ hU.fromSpec := by
    rw [j_fst, IsAffineOpen.isoSpec_inv_ι]
  have E2 : ∀ a : Γ(Z, U), (j z f U hU hφU).stalkMap q ((pullback z f).presheaf.germ ((pullback.fst z f) ⁻¹ᵁ U)
      ((j z f U hU hφU).base q) hpU ((pullback.fst z f).app U a)) =
      (pullback f (φ (R := R) U)).presheaf.germ ⊤ q trivial
        ((pullback.snd f (φ (R := R) U)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z, U))).inv a)) := by
    intro a
    rw [Scheme.Hom.germ_stalkMap_apply]
    have t := CategoryTheory.ConcreteCategory.congr_hom (Scheme.Hom.congr_app hjf U) a
    rw [Scheme.Hom.comp_app] at t
    erw [CommRingCat.comp_apply, CommRingCat.comp_apply] at t
    erw [t, TopCat.Presheaf.germ_res_apply]
    rw [Scheme.Hom.comp_app, IsAffineOpen.fromSpec_app_self]
    erw [CommRingCat.comp_apply, CommRingCat.comp_apply]
    have n := CategoryTheory.ConcreteCategory.congr_hom
      ((pullback.snd f (φ (R := R) U)).naturality (eqToHom hU.fromSpec_preimage_self).op)
      ((Scheme.ΓSpecIso Γ(Z, U)).inv a)
    erw [CommRingCat.comp_apply, CommRingCat.comp_apply] at n
    erw [n, TopCat.Presheaf.germ_res_apply]
    rfl

  have E1' : ∀ t, ((j z f U hU hφU).stalkMap q).hom (((pullback.snd z f).stalkMap ((j z f U hU hφU).base q)).hom t) =
      ((pullback.fst f (φ (R := R) U)).stalkMap q).hom (c.hom t) := fun t => E1 t
  have E2' : ∀ a : Γ(Z, U), ((j z f U hU hφU).stalkMap q).hom (((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom
      ((Z.presheaf.germ U _ hpU).hom a)) =
      (pullback f (φ (R := R) U)).presheaf.germ ⊤ q trivial
        ((pullback.snd f (φ (R := R) U)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z, U))).inv a)) := by
    intro a
    have g1 := CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.Hom.germ_stalkMap (pullback.fst z f) U ((j z f U hU hφU).base q) hpU) a
    exact (congrArg (fun y => ((j z f U hU hφU).stalkMap q).hom y) g1).trans (E2 a)

  have few := fe_wrapper (R := R) f Γ(Z, U) (φ (R := R) U) rfl q (inst := aB') rfl
  obtain ⟨𝔮₀, h𝔮₀, e₀, he₀X, he₀A⟩ := few
  haveI : 𝔮₀.IsPrime := h𝔮₀

  let ζU : ↥U := ⟨(pullback.fst z f).base ((j z f U hU hφU).base q), hpU⟩
  letI aZ : Algebra Γ(Z, U) (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q))) :=
    (Z.presheaf.germ U _ hpU).hom.toAlgebra
  haveI hlocZ : IsLocalization.AtPrime (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q)))
      (hU.primeIdealOf ζU).asIdeal := hU.isLocalization_stalk ζU
  haveI : IsScalarTower R Γ(Z, U) (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q))) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [algebraMap_stalk_eq z _ halgZ r, halgU r]
    change _ = Z.presheaf.germ U _ hpU ((z.app ⊤ ≫ Z.presheaf.map (homOfLE le_top).op)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    rw [CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply]
    rfl

  let φL : Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q)) →+* Localization.AtPrime 𝔮₀ :=
    e₀.toRingHom.comp (((j z f U hU hφU).stalkMap q).hom.comp ((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom)
  have hφL : ∀ a : Γ(Z, U), φL (algebraMap Γ(Z, U) _ a) =
      algebraMap _ (Localization.AtPrime 𝔮₀)
        ((1 : X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) ⊗ₜ[R] a) := by
    intro a
    exact (congrArg e₀ (E2' a)).trans (he₀A a)
  have hφLu : ∀ y, IsUnit (φL y) ↔ IsUnit y := by
    intro y
    have he : ∀ w, IsUnit (e₀ w) ↔ IsUnit w := fun w =>
      ⟨fun h => by simpa using h.map e₀.symm, fun h => h.map e₀⟩
    exact (he _).trans ((isUnit_map_iff ((j z f U hU hφU).stalkMap q).hom _).trans
      (isUnit_map_iff ((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom y))

  have hQp : 𝔮₀.comap (Algebra.TensorProduct.includeRight (R := R)
      (A := X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) (B := Γ(Z, U))).toRingHom = (hU.primeIdealOf ζU).asIdeal := by
    ext a
    rw [Ideal.mem_comap]
    change ((1 : X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) ⊗ₜ[R] a ∈ 𝔮₀) ↔ a ∈ (hU.primeIdealOf ζU).asIdeal
    have h1 : ((1 : X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) ⊗ₜ[R] a ∈ 𝔮₀) ↔
        ¬ IsUnit (algebraMap _ (Localization.AtPrime 𝔮₀) ((1 : X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) ⊗ₜ[R] a)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮₀) 𝔮₀]
      exact not_not.symm
    have h2 : a ∈ (hU.primeIdealOf ζU).asIdeal ↔
        ¬ IsUnit (algebraMap Γ(Z, U) (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q))) a) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (hU.primeIdealOf ζU).asIdeal]
      exact not_not.symm
    rw [h1, h2, ← hφL a, not_iff_not]
    exact hφLu _

  have cr := FibreStalkBCRight.core (A := R)
    (S := X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q)) (R := Γ(Z, U))
    (L := Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q)))
    (hU.primeIdealOf ζU).asIdeal 𝔮₀ hQp (Localization.AtPrime 𝔮₀) φL hφL
  obtain ⟨𝔮₁, h𝔮₁, e₁, he₁S, he₁L⟩ := cr
  haveI : 𝔮₁.IsPrime := h𝔮₁

  have hψx : ∃ ψ : (Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q)) ⊗[R]
      X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q))) ≃ₐ[R]
      (X.presheaf.stalk ((pullback.fst f (φ (R := R) U)).base q) ⊗[R]
        Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q))),
      ∀ l t, ψ (l ⊗ₜ t) = c.hom t ⊗ₜ l :=
    ⟨(Algebra.TensorProduct.congr AlgEquiv.refl cA).trans (Algebra.TensorProduct.comm R _ _), fun l t => by
      simp [cA, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.comm_tmul]
      rfl⟩
  obtain ⟨ψ, hψ⟩ := hψx
  let 𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base ((j z f U hU hφU).base q)) ⊗[R]
      X.presheaf.stalk ((pullback.snd z f).base ((j z f U hU hφU).base q)))) := 𝔮₁.comap ψ.toRingEquiv.toRingHom
  haveI h𝔔 : 𝔔.IsPrime := Ideal.comap_isPrime _ _
  have H : 𝔔.primeCompl.map ψ.toRingEquiv.toMonoidHom = 𝔮₁.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      refine ⟨ψ.toRingEquiv.symm y, ?_, ψ.toRingEquiv.apply_symm_apply y⟩
      change ψ.toRingEquiv (ψ.toRingEquiv.symm y) ∉ 𝔮₁
      rw [ψ.toRingEquiv.apply_symm_apply]; exact hy
  have hℓx : ∃ ℓ : Localization.AtPrime 𝔔 ≃+* Localization.AtPrime 𝔮₁,
      ∀ w, ℓ (algebraMap _ (Localization.AtPrime 𝔔) w) = algebraMap _ (Localization.AtPrime 𝔮₁) (ψ w) :=
    ⟨IsLocalization.ringEquivOfRingEquiv (M := 𝔔.primeCompl) (T := 𝔮₁.primeCompl)
      (Localization.AtPrime 𝔔) (Localization.AtPrime 𝔮₁) ψ.toRingEquiv H,
      fun w => IsLocalization.ringEquivOfRingEquiv_eq H w⟩
  obtain ⟨ℓ, hℓ⟩ := hℓx
  clear_value 𝔔

  have hφL_def : ∀ s, φL s = e₀ (((j z f U hU hφU).stalkMap q).hom
      (((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom s)) := fun s => rfl
  clear_value φL
  haveI : IsIso ((j z f U hU hφU).stalkMap q) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 q
  refine ⟨𝔔, h𝔔, ((((asIso ((j z f U hU hφU).stalkMap q)).commRingCatIsoToRingEquiv).trans e₀).trans e₁).trans ℓ.symm,
    fun s => ?_, fun t => ?_⟩
  · show ℓ.symm (e₁ (e₀ (((j z f U hU hφU).stalkMap q).hom
      (((pullback.fst z f).stalkMap ((j z f U hU hφU).base q)).hom s)))) = _
    rw [RingEquiv.symm_apply_eq, ← hφL_def, he₁L s, hℓ, hψ, map_one]
  · show ℓ.symm (e₁ (e₀ (((j z f U hU hφU).stalkMap q).hom
      (((pullback.snd z f).stalkMap ((j z f U hU hφU).base q)).hom t)))) = _
    rw [RingEquiv.symm_apply_eq, E1' t, he₀X (c.hom t), he₁S, hℓ, hψ]

end StalkPB
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.StalkPB"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.StalkPB"

theorem solution
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p))))) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((pullback.fst z f).base p)) isOpen_univ
  letI : Algebra R Γ(Z, U) := StalkPB.algU z U
  exact StalkPB.main z f U hU (StalkPB.isoSpec_hom_algU z U hU) p halgZ halgX hpU (fun r => rfl)

end S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk (solution)
