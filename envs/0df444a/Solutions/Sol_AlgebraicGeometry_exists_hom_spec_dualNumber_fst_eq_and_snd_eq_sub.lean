-- Prove2me | solution 1 for AlgebraicGeometry.exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dffce6c7-7424-539a-812b-b6314ec8786f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub.AlgebraicGeometry Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Hom Scheme.Hom.appLE_comp_appLE IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv Scheme.Hom.preimage_top exists_isAffineOpen_mem_and_subset isAffineOpen_top Spec.map_id IsAffineOpen Scheme.Hom.app_eq_appLE Scheme.ΓSpecIso_naturality Scheme.Hom.comp_preimage Scheme.Hom.comp_apply Scheme.Hom.appLE Scheme.ΓSpecIso"
namespace S3TangentDiff
p2m_open "AlgebraicGeometry"

theorem eq_closedPoint_dualNumber (k : Type u) [Field k] (y : PrimeSpectrum (DualNumber k)) :
    y = IsLocalRing.closedPoint (DualNumber k) := by
  apply PrimeSpectrum.ext
  have h1 : Ideal.span {(DualNumber.eps : DualNumber k)} ≤ y.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : (DualNumber.eps : DualNumber k) * DualNumber.eps ∈ y.asIdeal := by
      rw [DualNumber.eps_mul_eps]; exact zero_mem _
    exact (y.isPrime.mem_or_mem this).elim id id
  have h2 := DualNumber.isMaximal_span_singleton_eps.eq_of_le y.isPrime.ne_top h1
  show y.asIdeal = IsLocalRing.maximalIdeal (DualNumber k)
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, h2]

theorem top_le_preimage_of_mem {k : Type u} [Field k] {X : Scheme.{u}}
    (T : Spec (CommRingCat.of (DualNumber k)) ⟶ X) (W : X.Opens)
    (h : T.base (IsLocalRing.closedPoint (DualNumber k)) ∈ W) : ⊤ ≤ T ⁻¹ᵁ W := by
  intro y _
  have hy : y = IsLocalRing.closedPoint (DualNumber k) := eq_closedPoint_dualNumber k y
  show T.base y ∈ W
  rw [hy]; exact h

theorem appLE_hom_eq_of_eq {X Y : Scheme.{u}} {F G : X ⟶ Y} (hFG : F = G) (U : Y.Opens) (V : X.Opens)
    (h1 : V ≤ F ⁻¹ᵁ U) (h2 : V ≤ G ⁻¹ᵁ U) (y : Γ(Y, U)) :
    (F.appLE U V h1).hom y = (G.appLE U V h2).hom y := by
  subst hFG; rfl

theorem appLE_top_hom_eq {X Y : Scheme.{u}} (F : X ⟶ Y) (h : (⊤ : X.Opens) ≤ F ⁻¹ᵁ ⊤) (y : Γ(Y, ⊤)) :
    (F.appLE ⊤ ⊤ h).hom y = F.appTop.hom y := by
  have e := Scheme.Hom.app_eq_appLE (f := F) (U := ⊤)
  show (F.appLE ⊤ ⊤ h).hom y = (F.app ⊤).hom y
  rw [e]
  rfl

theorem comp_appLE_top_hom {X Y Z : Scheme.{u}} (o : X ⟶ Y) (D : Y ⟶ Z) (U : Z.Opens)
    (h1 : (⊤ : X.Opens) ≤ (o ≫ D) ⁻¹ᵁ U) (h2 : (⊤ : Y.Opens) ≤ D ⁻¹ᵁ U) (g : Γ(Z, U)) :
    ((o ≫ D).appLE U ⊤ h1).hom g = o.appTop.hom ((D.appLE U ⊤ h2).hom g) := by
  have e := Scheme.Hom.appLE_comp_appLE o D U ⊤ ⊤ h2 le_top
  rw [← appLE_top_hom_eq o le_top, ← CategoryTheory.comp_apply, e]

theorem appLE_hom_eq_appLE_hom_map {X Y : Scheme.{u}} (T : X ⟶ Y) {U W : Y.Opens} (hWU : W ≤ U)
    (hU : (⊤ : X.Opens) ≤ T ⁻¹ᵁ U) (hW : (⊤ : X.Opens) ≤ T ⁻¹ᵁ W) (g : Γ(Y, U)) :
    (T.appLE U ⊤ hU).hom g = (T.appLE W ⊤ hW).hom ((Y.presheaf.map (homOfLE hWU).op).hom g) := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]

theorem ΓSpecIso_appLE_specMap_comp {X : Scheme.{u}} {B B' : Type u} [CommRing B] [CommRing B'] (σ : B →+* B')
    (T : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : (⊤ : (Spec (CommRingCat.of B')).Opens) ≤ (Spec.map (CommRingCat.ofHom σ) ≫ T) ⁻¹ᵁ U)
    (h' : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ T ⁻¹ᵁ U) (g : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of B')).hom.hom (((Spec.map (CommRingCat.ofHom σ) ≫ T).appLE U ⊤ h).hom g) =
      σ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((T.appLE U ⊤ h').hom g)) := by
  rw [comp_appLE_top_hom _ T U h h', ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
  rfl

theorem ΓSpecIso_appLE_appLE_ΓSpecIso_inv {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (T : Spec (CommRingCat.of B) ⟶ X)
    (hT : T ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B))) (U : X.Opens) (hU : ⊤ ≤ T ⁻¹ᵁ U) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((T.appLE U ⊤ hU).hom
      ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R B r := by
  have e1 : (T.appLE U ⊤ hU).hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      ((T ≫ f).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom (algebraMap R B) := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have key' := congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of B => m.hom r) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key'
  rw [e1, appLE_hom_eq_of_eq hT ⊤ ⊤ _ le_top, appLE_top_hom_eq]
  exact key'

theorem fromSpec_appLE_top_hom {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) (g : Γ(X, U)) :
    (hU.fromSpec.appLE U ⊤ h1).hom g = (Scheme.ΓSpecIso Γ(X, U)).inv.hom g := by
  have e : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE h1 ≫ eqToHom hU.fromSpec_preimage_self) (𝟙 _), op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [e]

theorem top_le_preimage_specMap_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {B : Type u} [CommRing B] (ψ : Γ(X, U) →+* B) :
    (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  exact le_rfl

theorem ΓSpecIso_appLE_specMap_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {B : Type u} [CommRing B] (ψ : Γ(X, U) →+* B)
    (h : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ⁻¹ᵁ U) (g : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (((Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec).appLE U ⊤ h).hom g) =
      ψ g := by
  have h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have e1 : ((Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec).appLE U ⊤ h).hom g =
      ((Spec.map (CommRingCat.ofHom ψ)).appLE ⊤ ⊤ le_top).hom ((hU.fromSpec.appLE U ⊤ h1).hom g) := by
    rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [e1, fromSpec_appLE_top_hom, appLE_top_hom_eq, ← RingHom.comp_apply, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
  show ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).hom ≫
    CommRingCat.ofHom ψ).hom g = ψ g
  rw [Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]

theorem eq_specMap_comp_fromSpec {X : Scheme.{u}} {B : Type u} [CommRing B] (T : Spec (CommRingCat.of B) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (h : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ T ⁻¹ᵁ U) :
    T = Spec.map (T.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) ≫ hU.fromSpec := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec T hU (isAffineOpen_top (Spec (CommRingCat.of B))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  symm
  rw [Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem eq_of_forall_ΓSpecIso_appLE_eq {X : Scheme.{u}} {B : Type u} [CommRing B] (T₁ T₂ : Spec (CommRingCat.of B) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (h₁ : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ T₁ ⁻¹ᵁ U)
    (h₂ : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ T₂ ⁻¹ᵁ U)
    (heq : ∀ g : Γ(X, U), (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((T₁.appLE U ⊤ h₁).hom g) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((T₂.appLE U ⊤ h₂).hom g)) : T₁ = T₂ := by
  rw [eq_specMap_comp_fromSpec T₁ hU h₁, eq_specMap_comp_fromSpec T₂ hU h₂]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro g
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using heq g

def diffHom {A : Type u} [CommRing A] {k : Type u} [Field k] (α β : A →+* DualNumber k)
    (h : ∀ a, (α a).fst = (β a).fst) : A →+* DualNumber k where
  toFun a := TrivSqZeroExt.inl (α a).fst + TrivSqZeroExt.inr ((α a).snd - (β a).snd)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp [TrivSqZeroExt.fst_mul]
    · simp only [map_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, h]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext
    · simp
    · simp only [map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      ring

theorem fst_diffHom {A : Type u} [CommRing A] {k : Type u} [Field k] (α β : A →+* DualNumber k)
    (h : ∀ a, (α a).fst = (β a).fst) (a : A) : (diffHom α β h a).fst = (α a).fst := by
  simp [diffHom]

theorem snd_diffHom {A : Type u} [CommRing A] {k : Type u} [Field k] (α β : A →+* DualNumber k)
    (h : ∀ a, (α a).fst = (β a).fst) (a : A) : (diffHom α β h a).snd = (α a).snd - (β a).snd := by
  simp [diffHom]

theorem fst_ΓSpecIso_appLE_eq {k : Type u} [Field k] {X : Scheme.{u}} (W : X.Opens)
    (T₁ T₂ : Spec (CommRingCat.of (DualNumber k)) ⟶ X) (h₁ : ⊤ ≤ T₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ T₂ ⁻¹ᵁ W)
    (ho₁ : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ T₁) ⁻¹ᵁ W) (ho₂ : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ T₂) ⁻¹ᵁ W)
    (hT : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ T₁ = (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ T₂) (g : Γ(X, W)) :
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((T₁.appLE W ⊤ h₁).hom g)).fst = ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((T₂.appLE W ⊤ h₂).hom g)).fst := by
  have e1 := ΓSpecIso_appLE_specMap_comp (TrivSqZeroExt.fstHom k k k).toRingHom T₁ W ho₁ h₁ g
  have e2 := ΓSpecIso_appLE_specMap_comp (TrivSqZeroExt.fstHom k k k).toRingHom T₂ W ho₂ h₂ g
  rw [appLE_hom_eq_of_eq hT W ⊤ ho₁ ho₂] at e1
  exact e1.symm.trans e2

theorem snd_ΓSpecIso_appLE_basicOpen {k : Type u} [Field k] {X : Scheme.{u}} {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀)
    (P Q D : Spec (CommRingCat.of (DualNumber k)) ⟶ X)
    (hPU₀ : ⊤ ≤ P ⁻¹ᵁ U₀) (hQU₀ : ⊤ ≤ Q ⁻¹ᵁ U₀) (hDU₀ : ⊤ ≤ D ⁻¹ᵁ U₀)
    (hfst : ∀ g, ((((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (P.appLE U₀ ⊤ hPU₀).hom) g).fst = ((((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (Q.appLE U₀ ⊤ hQU₀).hom) g).fst)
    (hDev : ∀ g, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE U₀ ⊤ hDU₀).hom g) =
      diffHom (((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (P.appLE U₀ ⊤ hPU₀).hom) (((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (Q.appLE U₀ ⊤ hQU₀).hom) hfst g)
    (r : Γ(X, U₀)) (hPV : ⊤ ≤ P ⁻¹ᵁ X.basicOpen r) (hQV : ⊤ ≤ Q ⁻¹ᵁ X.basicOpen r) (hDV : ⊤ ≤ D ⁻¹ᵁ X.basicOpen r)
    (hfstV : ∀ g', ((((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (P.appLE (X.basicOpen r) ⊤ hPV).hom) g').fst =
      ((((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (Q.appLE (X.basicOpen r) ⊤ hQV).hom) g').fst)
    (g' : Γ(X, X.basicOpen r)) :
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE (X.basicOpen r) ⊤ hDV).hom g')).snd =
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((P.appLE (X.basicOpen r) ⊤ hPV).hom g')).snd - ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((Q.appLE (X.basicOpen r) ⊤ hQV).hom g')).snd := by
  haveI : IsLocalization.Away r Γ(X, X.basicOpen r) := hU₀.isLocalization_basicOpen r
  have hρ : ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (D.appLE (X.basicOpen r) ⊤ hDV).hom =
      diffHom (((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (P.appLE (X.basicOpen r) ⊤ hPV).hom) (((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (Q.appLE (X.basicOpen r) ⊤ hQV).hom) hfstV := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro g
    have halg : algebraMap Γ(X, U₀) Γ(X, X.basicOpen r) g =
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom g := rfl
    simp only [RingHom.comp_apply]
    rw [halg]
    apply TrivSqZeroExt.ext
    · rw [fst_diffHom, RingHom.comp_apply, ← appLE_hom_eq_appLE_hom_map D (X.basicOpen_le r) hDU₀ hDV,
        ← appLE_hom_eq_appLE_hom_map P (X.basicOpen_le r) hPU₀ hPV, hDev, fst_diffHom, RingHom.comp_apply]
    · rw [snd_diffHom, RingHom.comp_apply, RingHom.comp_apply,
        ← appLE_hom_eq_appLE_hom_map D (X.basicOpen_le r) hDU₀ hDV,
        ← appLE_hom_eq_appLE_hom_map P (X.basicOpen_le r) hPU₀ hPV,
        ← appLE_hom_eq_appLE_hom_map Q (X.basicOpen_le r) hQU₀ hQV, hDev, snd_diffHom, RingHom.comp_apply,
        RingHom.comp_apply]
  have hfin := congrArg (fun φ : Γ(X, X.basicOpen r) →+* DualNumber k => (φ g').snd) hρ
  simp only [RingHom.comp_apply, snd_diffHom] at hfin
  exact hfin

end AlgebraicGeometry.S3TangentDiff

open AlgebraicGeometry.S3TangentDiff

theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X)
    (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hQ : Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (h0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q) :
    ∃ D : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      D ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ D =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P ∧
      (∀ (U : X.Opens) (hPU : ⊤ ≤ P ⁻¹ᵁ U) (hQU : ⊤ ≤ Q ⁻¹ᵁ U) (hDU : ⊤ ≤ D ⁻¹ᵁ U) (g : Γ(X, U)),
        TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE U ⊤ hDU).hom g)) =
          TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((P.appLE U ⊤ hPU).hom g)) ∧
        TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE U ⊤ hDU).hom g)) =
          TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((P.appLE U ⊤ hPU).hom g)) -
          TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((Q.appLE U ⊤ hQU).hom g))) ∧
      (D = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
          (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ D) ↔ P = Q) := by
  classical

  have hox₀ : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint (DualNumber k) := eq_closedPoint_dualNumber k _
  have hQP : Q.base (IsLocalRing.closedPoint (DualNumber k)) = P.base (IsLocalRing.closedPoint (DualNumber k)) := by
    rw [← hox₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h0]
  obtain ⟨U₀, hU₀, haU₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := P.base (IsLocalRing.closedPoint (DualNumber k)))
    (U := ⊤) trivial
  have hPU₀ : ⊤ ≤ P ⁻¹ᵁ U₀ := top_le_preimage_of_mem P U₀ haU₀
  have hQU₀ : ⊤ ≤ Q ⁻¹ᵁ U₀ := top_le_preimage_of_mem Q U₀ (by rw [hQP]; exact haU₀)
  have hoP : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ P) ⁻¹ᵁ U₀ := fun y _ => by
    show P.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ U₀
    rw [Subsingleton.elim y (IsLocalRing.closedPoint k), hox₀]; exact haU₀
  have hoQ : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ Q) ⁻¹ᵁ U₀ := fun y _ => by
    show Q.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ U₀
    rw [Subsingleton.elim y (IsLocalRing.closedPoint k), hox₀, hQP]; exact haU₀
  have hfstHom : ∀ x : (DualNumber k), (TrivSqZeroExt.fstHom k k k).toRingHom x = x.fst := fun _ => rfl

  let φP : Γ(X, U₀) →+* (DualNumber k) := ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (P.appLE U₀ ⊤ hPU₀).hom
  let φQ : Γ(X, U₀) →+* (DualNumber k) := ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom).comp (Q.appLE U₀ ⊤ hQU₀).hom
  have hfst : ∀ g, (φP g).fst = (φQ g).fst := fun g => fst_ΓSpecIso_appLE_eq U₀ P Q hPU₀ hQU₀ hoP hoQ h0 g
  have hPκ : ∀ c : k, φP ((f.appLE ⊤ U₀ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) =
      algebraMap k (DualNumber k) c := fun c => ΓSpecIso_appLE_appLE_ΓSpecIso_inv f P hP U₀ hPU₀ c
  have hQκ : ∀ c : k, φQ ((f.appLE ⊤ U₀ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) =
      algebraMap k (DualNumber k) c := fun c => ΓSpecIso_appLE_appLE_ΓSpecIso_inv f Q hQ U₀ hQU₀ c

  let ψ : Γ(X, U₀) →+* (DualNumber k) := diffHom φP φQ hfst
  let D : Spec (CommRingCat.of (DualNumber k)) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ hU₀.fromSpec
  have hDU₀ : ⊤ ≤ D ⁻¹ᵁ U₀ := top_le_preimage_specMap_comp_fromSpec hU₀ ψ
  have hDev : ∀ g, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE U₀ ⊤ hDU₀).hom g) = ψ g := fun g =>
    ΓSpecIso_appLE_specMap_comp_fromSpec hU₀ ψ hDU₀ g
  have hoD : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D) ⁻¹ᵁ U₀ := fun y _ => by
    show D.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ U₀
    exact hDU₀ trivial

  have hbase : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D = (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ P := by
    apply eq_of_forall_ΓSpecIso_appLE_eq _ _ hU₀ hoD hoP
    intro g
    rw [ΓSpecIso_appLE_specMap_comp _ D U₀ hoD hDU₀, ΓSpecIso_appLE_specMap_comp _ P U₀ hoP hPU₀, hDev]
    exact fst_diffHom φP φQ hfst g
  have hDP : D.base (IsLocalRing.closedPoint (DualNumber k)) = P.base (IsLocalRing.closedPoint (DualNumber k)) := by
    rw [← hox₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbase]

  have hDf : D ≫ f = (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) := by
    apply eq_of_forall_ΓSpecIso_appLE_eq _ _ (isAffineOpen_top (Spec (CommRingCat.of k)))
      (le_of_eq (Scheme.Hom.preimage_top _).symm) (le_of_eq (Scheme.Hom.preimage_top _).symm)
    intro g
    obtain ⟨c, rfl⟩ : ∃ c : k, g = (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom g, by
        rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id]; rfl⟩
    have e1 : ((D ≫ f).appLE ⊤ ⊤ (le_of_eq (Scheme.Hom.preimage_top _).symm)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) =
        (D.appLE U₀ ⊤ hDU₀).hom ((f.appLE ⊤ U₀ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) := by
      rw [← CategoryTheory.comp_apply (f.appLE ⊤ U₀ le_top), Scheme.Hom.appLE_comp_appLE]
    have e2 : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom (((Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))).appLE ⊤ ⊤ (le_of_eq (Scheme.Hom.preimage_top _).symm)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) = algebraMap k (DualNumber k) c := by
      rw [appLE_top_hom_eq, ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
        ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]
    rw [e1, hDev, e2]
    show diffHom φP φQ hfst _ = _
    ext
    · rw [fst_diffHom, hPκ]
    · rw [snd_diffHom, hPκ, hQκ, sub_self, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

  have hιoD : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ≫ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D)) ⁻¹ᵁ U₀ := fun y _ => by
    show D.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base ((Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))).base y)) ∈ U₀
    exact hDU₀ trivial
  have hconst : ∀ g, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((((Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ≫ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D)).appLE U₀ ⊤ hιoD).hom g) = algebraMap k (DualNumber k) ((ψ g).fst) := by
    intro g
    rw [ΓSpecIso_appLE_specMap_comp (algebraMap k (DualNumber k)) ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D) U₀ hιoD hoD g,
      ΓSpecIso_appLE_specMap_comp _ D U₀ hoD hDU₀ g, hDev]
    rfl
  refine ⟨D, hDf, hbase, ?_, ?_⟩
  ·
    intro U hPU hQU hDU g
    have hoDU : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D) ⁻¹ᵁ U := fun y _ => by
      show D.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ U
      exact hDU trivial
    have hoPU : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ P) ⁻¹ᵁ U := fun y _ => by
      show P.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ U
      exact hPU trivial
    have hoQU : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ Q) ⁻¹ᵁ U := fun y _ => by
      show Q.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ U
      exact hQU trivial
    refine ⟨fst_ΓSpecIso_appLE_eq U D P hDU hPU hoDU hoPU hbase g, ?_⟩

    have haU : P.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U := hPU trivial
    obtain ⟨r, hrU, har⟩ := hU₀.exists_basicOpen_le ⟨P.base (IsLocalRing.closedPoint (DualNumber k)), haU⟩ haU₀
    have hPV : ⊤ ≤ P ⁻¹ᵁ X.basicOpen r := top_le_preimage_of_mem P _ har
    have hQV : ⊤ ≤ Q ⁻¹ᵁ X.basicOpen r := top_le_preimage_of_mem Q _ (by rw [hQP]; exact har)
    have hDV : ⊤ ≤ D ⁻¹ᵁ X.basicOpen r := top_le_preimage_of_mem D _ (by rw [hDP]; exact har)
    have hoPV : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ P) ⁻¹ᵁ X.basicOpen r := fun y _ => by
      show P.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ X.basicOpen r
      exact hPV trivial
    have hoQV : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ Q) ⁻¹ᵁ X.basicOpen r := fun y _ => by
      show Q.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y) ∈ X.basicOpen r
      exact hQV trivial
    have hfstV := fun g' => fst_ΓSpecIso_appLE_eq (X.basicOpen r) P Q hPV hQV hoPV hoQV h0 g'
    rw [appLE_hom_eq_appLE_hom_map D hrU hDU hDV, appLE_hom_eq_appLE_hom_map P hrU hPU hPV,
      appLE_hom_eq_appLE_hom_map Q hrU hQU hQV]
    exact snd_ΓSpecIso_appLE_basicOpen hU₀ P Q D hPU₀ hQU₀ hDU₀ hfst hDev r hPV hQV hDV hfstV _
  ·
    constructor
    · intro hD
      apply eq_of_forall_ΓSpecIso_appLE_eq P Q hU₀ hPU₀ hQU₀
      intro g
      show φP g = φQ g
      have e := hDev g
      rw [appLE_hom_eq_of_eq hD U₀ ⊤ hDU₀ hιoD, hconst] at e

      have hsnd : (ψ g).snd = 0 := by
        rw [← e, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      ext
      · exact hfst g
      · have := snd_diffHom φP φQ hfst g
        rw [show diffHom φP φQ hfst g = ψ g from rfl, hsnd] at this
        exact (sub_eq_zero.mp this.symm)
    · intro hPQ
      apply eq_of_forall_ΓSpecIso_appLE_eq _ _ hU₀ hDU₀ hιoD
      intro g
      rw [hDev, hconst]
      have hsnd : (ψ g).snd = 0 := by
        show (diffHom φP φQ hfst g).snd = 0
        rw [snd_diffHom]
        have : φP g = φQ g := by
          show (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((P.appLE U₀ ⊤ hPU₀).hom g) = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((Q.appLE U₀ ⊤ hQU₀).hom g)
          rw [appLE_hom_eq_of_eq hPQ U₀ ⊤ hPU₀ hQU₀]
        rw [this, sub_self]
      ext
      · rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
      · rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, hsnd]

end S_AlgebraicGeometry_exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub
end P2MW
export P2MW.S_AlgebraicGeometry_exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub (solution)
