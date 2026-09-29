-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_fppfSubsheafFlag_of_bialgHomFlag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ba141192-0b04-5d42-9781-73d167a1e5c7

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag

namespace FppfSubsheafFlagSol

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open WithConv

section Algebra

variable {R : Type*} [CommRing R]

noncomputable def antipodeAlgHom (B : Type*) [CommRing B] [HopfAlgebra R B] : B →ₐ[R] B :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R (A := B)) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

@[scoped simp] lemma antipodeAlgHom_apply (B : Type*) [CommRing B] [HopfAlgebra R B] (b : B) :
    antipodeAlgHom (R := R) B b = HopfAlgebra.antipode R b := rfl

variable {H B A : Type*} [CommRing H] [HopfAlgebra R H] [CommRing B] [HopfAlgebra R B]
  [CommRing A] [Algebra R A]

lemma antipode_convMul (g : B →ₐ[R] A) :
    toConv (g.comp (antipodeAlgHom (R := R) B)) * toConv g = 1 := by
  refine WithConv.ext (AlgHom.ext fun c => ?_)
  change (toConv (g.comp (antipodeAlgHom (R := R) B)) * toConv g) c =
    (1 : WithConv (B →ₐ[R] A)) c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R c
  rw [← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, antipodeAlgHom_apply]
  rw [← g.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ℛ, map_sum]
  simp only [map_mul]

lemma convMul_antipode (g : B →ₐ[R] A) :
    toConv g * toConv (g.comp (antipodeAlgHom (R := R) B)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun c => ?_)
  change (toConv g * toConv (g.comp (antipodeAlgHom (R := R) B))) c =
    (1 : WithConv (B →ₐ[R] A)) c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R c
  rw [← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, antipodeAlgHom_apply]
  rw [← g.commutes, ← HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit ℛ, map_sum]
  simp only [map_mul]

variable (A) in

noncomputable def precomp (π : H →ₐc[R] B) : WithConv (B →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun g := toConv (g.ofConv.comp (π : H →ₐ[R] B))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    refine WithConv.ext ?_
    exact AlgHom.convMul_comp_bialgHom_distrib f g π

@[scoped simp] lemma precomp_apply_apply (π : H →ₐc[R] B) (g : WithConv (B →ₐ[R] A)) (h : H) :
    precomp A π g h = g (π h) := rfl

lemma ofConv_precomp (π : H →ₐc[R] B) (g : WithConv (B →ₐ[R] A)) :
    (precomp A π g).ofConv = g.ofConv.comp (π : H →ₐ[R] B) := rfl

lemma precomp_injective (π : H →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Injective (precomp A π) := by
  intro g₁ g₂ h
  refine WithConv.ext (AlgHom.ext fun b => ?_)
  obtain ⟨x, rfl⟩ := hπ b
  exact congrArg (fun t : WithConv (H →ₐ[R] A) => t x) h

lemma precomp_precomp_of_comp_eq {B' : Type*} [CommRing B'] [HopfAlgebra R B']
    (π : H →ₐc[R] B) (π' : H →ₐc[R] B') (φ : B' →ₐc[R] B) (hφ : φ.comp π' = π)
    (g : WithConv (B →ₐ[R] A)) :
    precomp A π' (precomp A φ g) = precomp A π g := by
  refine WithConv.ext (AlgHom.ext fun h => ?_)
  change g (φ (π' h)) = g (π h)
  rw [← hφ]
  rfl

end Algebra

section IntAlgebra

variable {H B A : Type*} [CommRing H] [HopfAlgebra ℤ H] [CommRing B] [HopfAlgebra ℤ B]
  [CommRing A]

lemma exists_precomp_eq_of_forall (π : H →ₐc[ℤ] B) (hπ : Function.Surjective π)
    (a : WithConv (H →ₐ[ℤ] A)) (ha : ∀ h : H, π h = 0 → a h = 0) :
    ∃ g : WithConv (B →ₐ[ℤ] A), precomp A π g = a := by
  have hker : RingHom.ker (π : H →ₐ[ℤ] B).toRingHom ≤ RingHom.ker a.ofConv.toRingHom := by
    intro h hh
    simp only [RingHom.mem_ker] at hh ⊢
    exact ha h hh
  refine ⟨toConv (AlgHom.liftOfSurjective (π : H →ₐ[ℤ] B) hπ a.ofConv hker), ?_⟩
  refine WithConv.ext ?_
  rw [ofConv_precomp, ofConv_toConv]
  exact AlgHom.liftOfSurjective_comp _ hπ _ hker

end IntAlgebra

section Geometry

universe u

noncomputable def gammaRepresentableBy :
    (Scheme.Γ.{u} ⋙ forget CommRingCat).RepresentableBy
      (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) where
  homEquiv {X} := (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (X := X)).trans
    (Equiv.funUnique PUnit.{u + 1} _)
  homEquiv_comp f g := by
    change AffineSpace.toSpecMvPolyIntEquiv _ (f ≫ g) PUnit.unit = _
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
    rfl

theorem presieve_isSheaf_fppf_gammaForget :
    Presieve.IsSheaf Scheme.fppfTopology.{u} (Scheme.Γ ⋙ forget CommRingCat) :=
  have : (Scheme.Γ.{u} ⋙ forget CommRingCat).IsRepresentable :=
    gammaRepresentableBy.{u}.isRepresentable
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

theorem sections_ext_of_mem_fppfTopology {X : Scheme.{u}} {R : Sieve X}
    (hR : R ∈ Scheme.fppfTopology X) {x y : Γ(X, ⊤)}
    (h : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X), R g → Scheme.Γ.map g.op x = Scheme.Γ.map g.op y) :
    x = y :=
  (presieve_isSheaf_fppf_gammaForget.{u} R hR).isSeparatedFor.ext fun Y g hg => by
    exact h g hg

theorem sections_ext_of_mem_smallFppfTopology {S : Scheme.{u}} {U : S.Fppf} {R : Sieve U}
    (hR : R ∈ smallFppfTopology S U) {x y : Γ(U.left, ⊤)}
    (h : ∀ ⦃V : S.Fppf⦄ (f : V ⟶ U), R f →
      Scheme.Γ.map f.left.op x = Scheme.Γ.map f.left.op y) :
    x = y := by
  rw [smallFppfTopology_eq_restrictedTopology, Functor.mem_restrictedTopology_iff,
    GrothendieckTopology.mem_over_iff] at hR
  refine sections_ext_of_mem_fppfTopology hR fun Y g hg => ?_
  rw [Sieve.overEquiv_iff] at hg
  obtain ⟨V, f, k, hf, hfac⟩ := hg
  have e : ∀ z, Scheme.Γ.map g.op z =
      Scheme.Γ.map k.left.op (Scheme.Γ.map ((Fppf.forget S).map f).left.op z) := fun z => by
    have hg' := congrArg (fun t => Scheme.Γ.map (CommaMorphism.left t).op z) hfac
    simp only [Over.homMk_left, Over.comp_left, Over.mk_left, op_comp, Functor.map_comp] at hg'
    exact hg'
  rw [e, e]
  exact congrArg (Scheme.Γ.map k.left.op) (h f hf)

end Geometry

section Sheaves

variable {S : Scheme.{0}} (𝒥 : Sheaf (smallFppfTopology S) Ab.{1})
  {H : Type} [CommRing H] [HopfAlgebra ℤ H]
  (e : ∀ U : S.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
  (he : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
    (Additive.toMul (e U (𝒥.1.map f.op s))) h
      = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) h))
  {B : Type} [CommRing B] [HopfAlgebra ℤ B] (π : H →ₐc[ℤ] B) (hπ : Function.Surjective π)

def P (U : S.Fppf) : AddSubgroup (𝒥.1.obj (op U)) where
  carrier := {s | ∃ g : WithConv (B →ₐ[ℤ] Γ(U.left, ⊤)), precomp _ π g = Additive.toMul (e U s)}
  zero_mem' := ⟨1, by rw [map_one, map_zero, toMul_zero]⟩
  add_mem' := by
    rintro s t ⟨g, hg⟩ ⟨g', hg'⟩
    exact ⟨g * g', by rw [map_mul, hg, hg', map_add, toMul_add]⟩
  neg_mem' := by
    rintro s ⟨⟨g⟩, hg⟩
    refine ⟨toConv (g.comp (antipodeAlgHom (R := ℤ) B)), ?_⟩
    have h1 : precomp _ π (toConv (g.comp (antipodeAlgHom (R := ℤ) B))) * precomp _ π (toConv g)
        = 1 := by
      rw [← map_mul, antipode_convMul, map_one]
    have h2 : Additive.toMul (e U s) * Additive.toMul (e U (-s)) = 1 := by
      rw [← toMul_add, ← map_add, add_neg_cancel, map_zero, toMul_zero]
    calc precomp _ π (toConv (g.comp (antipodeAlgHom (R := ℤ) B)))
        = precomp _ π (toConv (g.comp (antipodeAlgHom (R := ℤ) B))) *
            (Additive.toMul (e U s) * Additive.toMul (e U (-s))) := by rw [h2, mul_one]
      _ = Additive.toMul (e U (-s)) := by rw [← mul_assoc, ← hg, h1, one_mul]

variable {𝒥 e π} in
include he in
lemma map_mem_P {U V : S.Fppf} (f : U ⟶ V) {s : 𝒥.1.obj (op V)} (hs : s ∈ P 𝒥 e π V) :
    𝒥.1.map f.op s ∈ P 𝒥 e π U := by
  obtain ⟨⟨g⟩, hg⟩ := hs
  refine ⟨toConv ((Scheme.Γ.map f.left.op).hom.toIntAlgHom.comp g), ?_⟩
  refine WithConv.ext (AlgHom.ext fun h => ?_)
  change (Scheme.Γ.map f.left.op) (g (π h)) = (Additive.toMul (e U (𝒥.1.map f.op s))) h
  rw [he f s h, ← hg]
  rfl

def subpresheaf : (S.Fppf)ᵒᵖ ⥤ Ab.{1} where
  obj U := AddCommGrpCat.of (P 𝒥 e π (unop U))
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨𝒥.1.map f s.1, map_mem_P he f.unop s.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun s t => Subtype.ext (by simp) }
  map_id U := by
    refine AddCommGrpCat.ext fun s => Subtype.ext ?_
    simp
  map_comp f g := by
    refine AddCommGrpCat.ext fun s => Subtype.ext ?_
    simp

@[scoped simp] lemma subpresheaf_map_apply_coe {U V : (S.Fppf)ᵒᵖ} (f : U ⟶ V)
    (s : P 𝒥 e π (unop U)) :
    ((subpresheaf 𝒥 e he π).map f s).1 = 𝒥.1.map f s.1 := rfl

lemma presieve_isSheaf_forget :
    Presieve.IsSheaf (smallFppfTopology S) (𝒥.1 ⋙ forget Ab.{1}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology S) 𝒥.1 (forget Ab.{1})).mp 𝒥.2)

include hπ in

lemma isSheaf_subpresheaf : Presheaf.IsSheaf (smallFppfTopology S) (subpresheaf 𝒥 e he π) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology S) _ (forget Ab.{1}),
    isSheaf_iff_isSheaf_of_type]
  intro U R hR x hx
  have h𝒥 := presieve_isSheaf_forget 𝒥
  let y : Presieve.FamilyOfElements (𝒥.1 ⋙ forget Ab.{1}) R.arrows :=
    fun V f hf => (x f hf : P 𝒥 e π V).1
  have hy : y.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w =>
    congrArg Subtype.val (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨s, hs, huniq⟩ := h𝒥 R hR y hy
  have hs' : ∀ ⦃V : S.Fppf⦄ (f : V ⟶ U) (hf : R f), 𝒥.1.map f.op s = (x f hf : P 𝒥 e π V).1 :=
    fun V f hf => hs f hf
  have hsP : s ∈ P 𝒥 e π U := by
    apply exists_precomp_eq_of_forall π hπ
    intro h hh
    apply sections_ext_of_mem_smallFppfTopology hR
    intro V f hf
    obtain ⟨⟨g⟩, hg⟩ := (x f hf : P 𝒥 e π V).2
    have key : (Scheme.Γ.map f.left.op) ((Additive.toMul (e U s)) h) = 0 := by
      rw [← he f s h, hs' f hf,
        ← congrArg (fun t : WithConv (H →ₐ[ℤ] Γ(V.left, ⊤)) => t h) hg]
      change g (π h) = 0
      rw [hh, map_zero]
    exact key.trans (map_zero (Scheme.Γ.map f.left.op).hom).symm
  refine ⟨(⟨s, hsP⟩ : P 𝒥 e π U), fun V f hf => Subtype.ext (hs f hf), fun t ht => ?_⟩
  exact Subtype.ext (huniq (t : P 𝒥 e π U).1 fun V f hf => congrArg Subtype.val (ht f hf))

def subsheaf : Sheaf (smallFppfTopology S) Ab.{1} :=
  ⟨subpresheaf 𝒥 e he π, isSheaf_subpresheaf 𝒥 e he π hπ⟩

def subι : subsheaf 𝒥 e he π hπ ⟶ 𝒥 :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom (P 𝒥 e π (unop U)).subtype
      naturality := fun U V f => by
        refine AddCommGrpCat.ext fun s => ?_
        rfl }

@[scoped simp] lemma subι_app_apply (U : (S.Fppf)ᵒᵖ) (s : P 𝒥 e π (unop U)) :
    (subι 𝒥 e he π hπ).hom.app U s = s.1 := rfl

scoped instance mono_subι : Mono (subι 𝒥 e he π hπ) := by
  haveI : ∀ U, Mono ((subι 𝒥 e he π hπ).hom.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (subι 𝒥 e he π hπ).hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

noncomputable def lift {U : S.Fppf} (s : P 𝒥 e π U) : WithConv (B →ₐ[ℤ] Γ(U.left, ⊤)) :=
  Classical.choose s.2

lemma precomp_lift {U : S.Fppf} (s : P 𝒥 e π U) :
    precomp _ π (lift 𝒥 e π s) = Additive.toMul (e U s.1) :=
  Classical.choose_spec s.2

include hπ in
lemma lift_eq {U : S.Fppf} (s : P 𝒥 e π U) (g : WithConv (B →ₐ[ℤ] Γ(U.left, ⊤)))
    (hg : precomp _ π g = Additive.toMul (e U s.1)) : lift 𝒥 e π s = g :=
  precomp_injective π hπ ((precomp_lift 𝒥 e π s).trans hg.symm)

noncomputable def PEquiv (U : S.Fppf) :
    P 𝒥 e π U ≃+ Additive (WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))) where
  toFun s := Additive.ofMul (lift 𝒥 e π s)
  invFun g := ⟨(e U).symm (Additive.ofMul (precomp _ π (Additive.toMul g))),
    Additive.toMul g, by simp⟩
  left_inv s := by
    apply Subtype.ext
    change (e U).symm (Additive.ofMul (precomp _ π (lift 𝒥 e π s))) = s.1
    rw [precomp_lift, ofMul_toMul, AddEquiv.symm_apply_apply]
  right_inv g := by
    change Additive.ofMul (lift 𝒥 e π _) = g
    rw [lift_eq 𝒥 e π hπ _ (Additive.toMul g) (by simp), ofMul_toMul]
  map_add' s t := by
    rw [← ofMul_mul, lift_eq 𝒥 e π hπ (s + t) (lift 𝒥 e π s * lift 𝒥 e π t)]
    rw [map_mul, precomp_lift, precomp_lift, ← toMul_add, ← map_add]
    rfl

lemma toMul_PEquiv_apply {U : S.Fppf} (s : P 𝒥 e π U) (h : H) :
    WithConv.ofConv (Additive.toMul (e U s.1)) h =
      WithConv.ofConv (Additive.toMul (PEquiv 𝒥 e π hπ U s)) (π h) := by
  rw [← precomp_lift 𝒥 e π s]
  rfl

lemma mem_P_of_bijective (hb : Function.Bijective π) (U : S.Fppf) (s : 𝒥.1.obj (op U)) :
    s ∈ P 𝒥 e π U := by
  apply exists_precomp_eq_of_forall π hb.2
  intro h hh
  rw [(map_eq_zero_iff (π : H →ₐc[ℤ] B) hb.1).mp hh, map_zero]

lemma isIso_subι (hb : Function.Bijective π) : IsIso (subι 𝒥 e he π hπ) := by
  haveI : ∀ U, IsIso ((subι 𝒥 e he π hπ).hom.app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨Subtype.val_injective, fun s => ⟨⟨s, mem_P_of_bijective 𝒥 e π hb _ s⟩, rfl⟩⟩
  haveI : IsIso (subι 𝒥 e he π hπ).hom := NatIso.isIso_of_isIso_app _
  have h2 : IsIso ((sheafToPresheaf (smallFppfTopology S) Ab.{1}).map (subι 𝒥 e he π hπ)) :=
    this
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

variable {B' : Type} [CommRing B'] [HopfAlgebra ℤ B'] (π' : H →ₐc[ℤ] B')
  (hπ' : Function.Surjective π') (φ : B' →ₐc[ℤ] B) (hφ : φ.comp π' = π)

include hφ in
lemma P_le (U : S.Fppf) : P 𝒥 e π U ≤ P 𝒥 e π' U := by
  rintro s ⟨g, hg⟩
  exact ⟨precomp _ φ g, by rw [precomp_precomp_of_comp_eq π π' φ hφ, hg]⟩

def incl : subsheaf 𝒥 e he π hπ ⟶ subsheaf 𝒥 e he π' hπ' :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom (AddSubgroup.inclusion (P_le 𝒥 e π π' φ hφ (unop U)))
      naturality := fun U V f => by
        refine AddCommGrpCat.ext fun s => Subtype.ext ?_
        rfl }

lemma incl_comp_subι :
    incl 𝒥 e he π hπ π' hπ' φ hφ ≫ subι 𝒥 e he π' hπ' = subι 𝒥 e he π hπ := by
  ext U s
  rfl

end Sheaves

end FppfSubsheafFlagSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag.FppfSubsheafFlagSol"

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

theorem solution
    (S : Scheme.{0}) (𝒥 : Sheaf (smallFppfTopology S) Ab.{1})
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (sectionsEquiv : ∀ U : S.Fppf,
      𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (sectionsNat : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sectionsEquiv U (𝒥.1.map f.op s))) h
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (sectionsEquiv V s)) h))
    (n : ℕ) (B : Fin (n + 1) → Type) [∀ i, CommRing (B i)] [∀ i, HopfAlgebra ℤ (B i)]
    (π : ∀ i, H →ₐc[ℤ] B i) (hπ : ∀ i, Function.Surjective (π i))
    (φ : ∀ i : Fin n, B i.succ →ₐc[ℤ] B i.castSucc)
    (hφ : ∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc)
    (hlast : Function.Bijective (π (Fin.last n))) :
    ∃ (F : Fin (n + 1) → Sheaf (smallFppfTopology S) Ab.{1})
      (ι : ∀ i, F i ⟶ 𝒥) (incl : ∀ i : Fin n, F i.castSucc ⟶ F i.succ)
      (FE : ∀ (i : Fin (n + 1)) (U : S.Fppf),
        (F i).1.obj (op U) ≃+ Additive (WithConv (B i →ₐ[ℤ] Γ(U.left, ⊤)))),
      (∀ i, Mono (ι i)) ∧ (∀ i : Fin n, incl i ≫ ι i.succ = ι i.castSucc) ∧
      IsIso (ι (Fin.last n)) ∧
      ∀ (i : Fin (n + 1)) (U : S.Fppf) (s : (F i).1.obj (op U)) (h : H),
        WithConv.ofConv (Additive.toMul (sectionsEquiv U ((ι i).1.app (op U) s))) h
          = WithConv.ofConv (Additive.toMul (FE i U s)) (π i h) := by
  refine ⟨fun i => FppfSubsheafFlagSol.subsheaf 𝒥 sectionsEquiv sectionsNat (π i) (hπ i),
    fun i => FppfSubsheafFlagSol.subι 𝒥 sectionsEquiv sectionsNat (π i) (hπ i),
    fun i => FppfSubsheafFlagSol.incl 𝒥 sectionsEquiv sectionsNat (π i.castSucc) (hπ _)
      (π i.succ) (hπ _) (φ i) (hφ i),
    fun i U => FppfSubsheafFlagSol.PEquiv 𝒥 sectionsEquiv (π i) (hπ i) U,
    fun i => inferInstance,
    fun i => FppfSubsheafFlagSol.incl_comp_subι 𝒥 sectionsEquiv sectionsNat _ _ _ _ _ _,
    FppfSubsheafFlagSol.isIso_subι 𝒥 sectionsEquiv sectionsNat _ (hπ _) hlast,
    fun i U s h => FppfSubsheafFlagSol.toMul_PEquiv_apply 𝒥 sectionsEquiv (π i) (hπ i) s h⟩

end S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag (solution)
