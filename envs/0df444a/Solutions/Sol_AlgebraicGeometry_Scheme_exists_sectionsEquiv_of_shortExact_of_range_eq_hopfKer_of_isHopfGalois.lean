-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1d3bae21-5134-5f84-aae2-9ec494b8656f

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois

set_option autoImplicit false

namespace FppfHopfQuotientSol

open WithConv
open scoped TensorProduct

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

noncomputable scoped instance instGroupWithConv : Group (WithConv (B →ₐ[R] A)) :=
  { (inferInstance : Monoid (WithConv (B →ₐ[R] A))) with
    inv := fun g => toConv (g.ofConv.comp (antipodeAlgHom (R := R) B))
    inv_mul_cancel := fun g => antipode_convMul g.ofConv }

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

variable (H) in

noncomputable def postcomp {A' : Type*} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A') :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] A') where
  toFun g := toConv (φ.comp g.ofConv)
  map_one' := by
    refine WithConv.ext (AlgHom.ext fun h => ?_)
    simp [AlgHom.convOne_def]
  map_mul' f g := by
    refine WithConv.ext ?_
    rw [ofConv_toConv, AlgHom.comp_convMul_distrib]

@[scoped simp] lemma postcomp_apply_apply {A' : Type*} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A')
    (g : WithConv (H →ₐ[R] A)) (h : H) : postcomp H φ g h = φ (g h) := rfl

lemma precomp_postcomp {A' : Type*} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A')
    (π : H →ₐc[R] B) (g : WithConv (B →ₐ[R] A)) :
    precomp A' π (postcomp B φ g) = postcomp H φ (precomp A π g) := rfl

lemma map_eq_algebraMap_counit_of_mem_hopfKer (π : H →ₐc[R] B) {a : H}
    (ha : a ∈ HopfAlgebra.hopfKer π) : π a = algebraMap R B (Coalgebra.counit a) := by
  have h := HopfAlgebra.coaction_eq_of_mem π ha
  rw [HopfAlgebra.coaction_apply] at h

  let T : H ⊗[R] B →ₗ[R] B := (TensorProduct.lid R B).toLinearMap ∘ₗ (Coalgebra.counit.rTensor B)
  have h1 : T (Algebra.TensorProduct.map (AlgHom.id R H) (π : H →ₐ[R] B) (Coalgebra.comul a)) = π a := by
    have : (Algebra.TensorProduct.map (AlgHom.id R H) (π : H →ₐ[R] B)).toLinearMap =
        ((π : H →ₐ[R] B).toLinearMap.lTensor H) := by
      ext x y; simp
    change T ((Algebra.TensorProduct.map (AlgHom.id R H) (π : H →ₐ[R] B)).toLinearMap
      (Coalgebra.comul a)) = _
    rw [this]
    change (T ∘ₗ (π : H →ₐ[R] B).toLinearMap.lTensor H) (Coalgebra.comul a) = _
    have hT : T ∘ₗ (π : H →ₐ[R] B).toLinearMap.lTensor H =
        (TensorProduct.lid R B).toLinearMap ∘ₗ (π : H →ₐ[R] B).toLinearMap.lTensor R ∘ₗ
          Coalgebra.counit.rTensor H := by
      ext x y; simp [T]
    rw [hT, LinearMap.comp_apply, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
    simp
  have h2 : T (a ⊗ₜ[R] (1 : B)) = algebraMap R B (Coalgebra.counit a) := by
    simp [T, Algebra.algebraMap_eq_smul_one]
  rw [← h1, h, h2]

end Algebra

section IntHopf

variable {R A B K Γ : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B]
  [HopfAlgebra R B] [CommRing K] [HopfAlgebra R K] [CommRing Γ] [Algebra R Γ]
  (qc : A →ₐc[R] B) (j : K →ₐc[R] A)

lemma precomp_precomp_eq_one (hrange : (j : K →ₐ[R] A).range ≤ HopfAlgebra.hopfKer qc)
    (g : WithConv (B →ₐ[R] Γ)) : precomp Γ j (precomp Γ qc g) = 1 := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  have hk : j k ∈ HopfAlgebra.hopfKer qc := hrange ⟨k, rfl⟩
  change g (qc (j k)) = (1 : WithConv (K →ₐ[R] Γ)) k
  rw [map_eq_algebraMap_counit_of_mem_hopfKer qc hk, AlgHom.commutes,
    AlgHom.convOne_apply]
  congr 1
  exact CoalgHomClass.counit_comp_apply j k

lemma exists_lift_comp_coaction_eq (π : A →ₐc[R] B) (hπ : HopfAlgebra.IsHopfGalois π)
    (ψ ψ' : A →ₐ[R] Γ) (h : ∀ a ∈ HopfAlgebra.hopfKer π, ψ a = ψ' a) :
    ∃ χ : B →ₐ[R] Γ,
      (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
        (HopfAlgebra.coaction π) = ψ' := by
  let Ψ : A ⊗[R] A →ₐ[R] Γ := Algebra.TensorProduct.lift ψ ψ' (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective (HopfAlgebra.canAlgHom π) := hπ.1
  have hspan : ∀ z ∈ Submodule.span R (HopfAlgebra.balancingRelations π), Ψ z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, k, a', hk, rfl⟩ := hx
      simp only [Ψ, map_sub, Algebra.TensorProduct.lift_tmul, map_mul, h k hk]
      ring
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [map_smul, hx, smul_zero]
  have hker : RingHom.ker (HopfAlgebra.canAlgHom π).toRingHom ≤ RingHom.ker Ψ.toRingHom :=
    fun z hz => hspan z (hπ.2 z hz)
  let Φ : A ⊗[R] B →ₐ[R] Γ := AlgHom.liftOfSurjective _ hsurj Ψ hker
  have hΦ : ∀ z, Φ (HopfAlgebra.canAlgHom π z) = Ψ z := fun z =>
    AlgHom.liftOfSurjective_apply _ hsurj Ψ hker z
  refine ⟨Φ.comp Algebra.TensorProduct.includeRight, ?_⟩
  have hlift : Algebra.TensorProduct.lift ψ (Φ.comp Algebra.TensorProduct.includeRight)
      (fun _ _ => Commute.all _ _) = Φ := by
    refine Algebra.TensorProduct.ext ?_ ?_
    · rw [Algebra.TensorProduct.lift_comp_includeLeft]
      refine AlgHom.ext fun a => ?_
      have h1 : HopfAlgebra.canAlgHom π (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
        rw [HopfAlgebra.canAlgHom_tmul, map_one, mul_one]
      have h2 := hΦ (a ⊗ₜ[R] 1)
      rw [h1] at h2
      change ψ a = Φ (a ⊗ₜ[R] 1)
      rw [h2]
      simp [Ψ]
    · rw [Algebra.TensorProduct.lift_comp_includeRight]
      rfl
  rw [hlift]
  refine AlgHom.ext fun a' => ?_
  have h1 : HopfAlgebra.canAlgHom π (1 ⊗ₜ[R] a') = HopfAlgebra.coaction π a' := by
    rw [HopfAlgebra.canAlgHom_tmul, ← Algebra.TensorProduct.one_def, one_mul]
  change Φ (HopfAlgebra.coaction π a') = ψ' a'
  rw [← h1, hΦ]
  simp [Ψ]

lemma exists_precomp_eq_of_precomp_eq_one (hHG : HopfAlgebra.IsHopfGalois qc)
    (hrange : (j : K →ₐ[R] A).range = HopfAlgebra.hopfKer qc)
    (a : WithConv (A →ₐ[R] Γ)) (ha : precomp Γ j a = 1) :
    ∃ χ : WithConv (B →ₐ[R] Γ), precomp Γ qc χ = a := by
  set ψ : A →ₐ[R] Γ := (Algebra.ofId R Γ).comp (Bialgebra.counitAlgHom R A) with hψ
  have hagree : ∀ x ∈ HopfAlgebra.hopfKer qc, ψ x = a.ofConv x := by
    intro x hx
    obtain ⟨k, hk⟩ : x ∈ (j : K →ₐ[R] A).range := by rw [hrange]; exact hx
    have hk2 : j k = x := hk
    have hk' := congrArg (fun t : WithConv (K →ₐ[R] Γ) => t k) ha
    change a (j k) = (1 : WithConv (K →ₐ[R] Γ)) k at hk'
    change ψ x = a x
    rw [← hk2, hk', AlgHom.convOne_apply, hψ]
    change algebraMap R Γ (Coalgebra.counit (j k)) = _
    rw [CoalgHomClass.counit_comp_apply]
  obtain ⟨χ, hχ⟩ := exists_lift_comp_coaction_eq qc hHG ψ a.ofConv hagree
  refine ⟨toConv χ, ?_⟩

  have hmul : (1 * precomp Γ qc (toConv χ)).ofConv =
      (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
        (HopfAlgebra.coaction qc) := by
    refine AlgHom.ext fun x => ?_
    rw [AlgHom.convMul_apply]
    change Algebra.TensorProduct.lift ψ (χ.comp (qc : A →ₐ[R] B)) (fun _ _ => Commute.all _ _)
        (Coalgebra.comul x) =
      Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _) (HopfAlgebra.coaction qc x)
    rw [HopfAlgebra.coaction_apply]
    have hl : Algebra.TensorProduct.lift ψ (χ.comp (qc : A →ₐ[R] B)) (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
          (Algebra.TensorProduct.map (AlgHom.id R A) (qc : A →ₐ[R] B)) := by
      ext y <;> simp
    rw [hl]
    rfl
  rw [one_mul] at hmul
  exact WithConv.ext (hmul.trans hχ)

end IntHopf

section Geometry

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

abbrev overFppfComapPrecoverage : Precoverage (Over S) :=
  fppfPrecoverage.comap (Over.forget S)

abbrev smallFppfComapPrecoverage : Precoverage S.Fppf :=
  fppfPrecoverage.comap (Fppf.forget S ⋙ Over.forget S)

example : (overFppfComapPrecoverage S).HasIsos := inferInstance
example : (overFppfComapPrecoverage S).IsStableUnderComposition := inferInstance
example : (overFppfComapPrecoverage S).IsStableUnderBaseChange := inferInstance
example : (overFppfComapPrecoverage S).HasPullbacks := inferInstance

variable {S}

theorem mem_smallFppfComapPrecoverage_iff {U : S.Fppf} (R : Presieve U) :
    R ∈ smallFppfComapPrecoverage S U ↔
      R.map (Fppf.forget S ⋙ Over.forget S) ∈ fppfPrecoverage U.left :=
  Iff.rfl

theorem fppfProperty_left_of_mem {U : S.Fppf} {R : Presieve U}
    (hR : R ∈ smallFppfComapPrecoverage S U) {W : S.Fppf} {g : W ⟶ U} (hg : R g) :
    fppfProperty g.left := by
  have hle : fppfPrecoverage.{u} ≤ fppfProperty.{u}.precoverage := inf_le_right
  exact hle _ hR (Presieve.map_map hg)

def Fppf.ofOver (X : Over S) (hX : fppfProperty X.hom) : S.Fppf :=
  ⟨X, hX⟩

@[scoped simp]
theorem Fppf.forget_obj_ofOver (X : Over S) (hX : fppfProperty X.hom) :
    (Fppf.forget S).obj (Fppf.ofOver X hX) = X :=
  rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf"
section MasterPullback

variable {U W V : S.Fppf} (g : W ⟶ U) (f : V ⟶ U)

theorem fppfProperty_pullback_hom (hg : fppfProperty g.left) :
    fppfProperty (pullback ((Fppf.forget S).map g) ((Fppf.forget S).map f)).hom := by
  have sq : IsPullback
      ((pullback.fst ((Fppf.forget S).map g) ((Fppf.forget S).map f)).left)
      ((pullback.snd ((Fppf.forget S).map g) ((Fppf.forget S).map f)).left)
      g.left f.left :=
    (Over.forget S).map_isPullback
      (IsPullback.of_hasPullback ((Fppf.forget S).map g) ((Fppf.forget S).map f))
  have hsnd : fppfProperty
      ((pullback.snd ((Fppf.forget S).map g) ((Fppf.forget S).map f)).left) :=
    fppfProperty.of_isPullback sq hg
  rw [← Over.w (pullback.snd ((Fppf.forget S).map g) ((Fppf.forget S).map f))]
  exact fppfProperty.comp_mem _ _ hsnd V.prop

noncomputable def fppfPullback (hg : fppfProperty g.left) : S.Fppf :=
  Fppf.ofOver (pullback ((Fppf.forget S).map g) ((Fppf.forget S).map f))
    (fppfProperty_pullback_hom g f hg)

@[scoped simp]
theorem fppfForget_obj_fppfPullback (hg : fppfProperty g.left) :
    (Fppf.forget S).obj (fppfPullback g f hg) =
      pullback ((Fppf.forget S).map g) ((Fppf.forget S).map f) :=
  rfl

@[implicit_reducible]
noncomputable def createsLimitCospanOfFppfLeft (hg : fppfProperty g.left) :
    CreatesLimit (cospan g f) (Fppf.forget S) :=
  createsLimitOfFullyFaithfulOfIso (fppfPullback g f hg)
    (HasLimit.isoOfNatIso (cospanCompIso (Fppf.forget S) g f).symm)

theorem hasPullback_of_fppf_left (hg : fppfProperty g.left) : HasPullback g f :=
  letI := createsLimitCospanOfFppfLeft g f hg
  hasLimit_of_created (cospan g f) (Fppf.forget S)

theorem preservesLimit_cospan_of_fppf_left (hg : fppfProperty g.left) :
    PreservesLimit (cospan g f) (Fppf.forget S) :=
  letI := createsLimitCospanOfFppfLeft g f hg
  inferInstance

theorem hasPullback_of_fppf_right (hf : fppfProperty f.left) : HasPullback g f :=
  haveI := hasPullback_of_fppf_left f g hf
  hasPullback_symmetry f g

theorem preservesLimit_cospan_of_fppf_right (hf : fppfProperty f.left) :
    PreservesLimit (cospan g f) (Fppf.forget S) :=
  haveI := preservesLimit_cospan_of_fppf_left f g hf
  preservesPullback_symmetry (Fppf.forget S) f g

theorem preservesLimit_cospan_comp_of_fppf_right (hf : fppfProperty f.left) :
    PreservesLimit (cospan g f) (Fppf.forget S ⋙ Over.forget S) :=
  haveI := preservesLimit_cospan_of_fppf_right g f hf
  inferInstance

end MasterPullback
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf"

scoped instance smallFppfComapPrecoverage_hasPullbacks : (smallFppfComapPrecoverage S).HasPullbacks where
  hasPullbacks_of_mem {X Y} R f hR := by
    constructor
    intro Z g hg
    exact hasPullback_of_fppf_left g f (fppfProperty_left_of_mem hR hg)

scoped instance smallFppfComapPrecoverage_pullbacksPreservedBy :
    (smallFppfComapPrecoverage S).PullbacksPreservedBy (Fppf.forget S) where
  preservesPairwisePullbacks_of_mem {X} R hR := by
    constructor
    intro Y Z f g hf _
    exact preservesLimit_cospan_of_fppf_left f g (fppfProperty_left_of_mem hR hf)

scoped instance smallFppfComapPrecoverage_isStableUnderBaseChange :
    (smallFppfComapPrecoverage S).IsStableUnderBaseChange where
  mem_coverings_of_isPullback := by
    intro ι X Y f hf Z g P p₁ p₂ h
    have hle : fppfPrecoverage.{u} ≤ fppfProperty.{u}.precoverage := inf_le_right
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hf ⊢
    have hflat (i : ι) : fppfProperty (f i).left := hle _ hf (Presieve.ofArrows.mk i)
    haveI (i : ι) : PreservesLimit (cospan g (f i)) (Fppf.forget S ⋙ Over.forget S) :=
      preservesLimit_cospan_comp_of_fppf_right g (f i) (hflat i)
    exact Precoverage.mem_coverings_of_isPullback _ hf _ _ _
      (fun i => Functor.map_isPullback (Fppf.forget S ⋙ Over.forget S) (h i))

variable (S)

theorem toGrothendieck_overFppfComapPrecoverage :
    (overFppfComapPrecoverage S).toGrothendieck = fppfTopology.{u}.over S :=
  (over_toGrothendieck_eq_toGrothendieck_comap_forget fppfPrecoverage S).symm

theorem toGrothendieck_smallFppfComapPrecoverage :
    (smallFppfComapPrecoverage S).toGrothendieck = smallFppfTopology S :=
  MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology fppfPrecoverage inf_le_right

scoped instance fppfForget_isContinuous :
    (Fppf.forget S).IsContinuous (smallFppfTopology S) (fppfTopology.{u}.over S) := by
  have h := Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (Fppf.forget S)
    (smallFppfComapPrecoverage S) (overFppfComapPrecoverage S)
    (le_of_eq (Precoverage.comap_comp (Fppf.forget S) (Over.forget S) fppfPrecoverage))
  rwa [toGrothendieck_smallFppfComapPrecoverage, toGrothendieck_overFppfComapPrecoverage] at h

scoped instance fppfForgetForget_isContinuous :
    (Fppf.forget S ⋙ Over.forget S).IsContinuous (smallFppfTopology S) fppfTopology.{u} :=
  Functor.isContinuous_comp (Fppf.forget S) (Over.forget S) (smallFppfTopology S) (fppfTopology.{u}.over S) fppfTopology.{u}

theorem isSheaf_yoneda_comp (X : Scheme.{u}) :
    Presieve.IsSheaf (smallFppfTopology S) ((Fppf.forget S ⋙ Over.forget S).op ⋙ yoneda.obj X) := by
  have h : Presheaf.IsSheaf fppfTopology.{u} (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))
  exact (Fppf.forget S ⋙ Over.forget S).op_comp_isSheaf_of_types (smallFppfTopology S)
    fppfTopology.{u} ⟨_, h⟩

theorem generate_singleton_mem {U W : S.Fppf} (g : W ⟶ U) [Flat g.left]
    [LocallyOfFinitePresentation g.left] [Surjective g.left] :
    Sieve.generate (Presieve.singleton g) ∈ smallFppfTopology S U := by
  rw [← toGrothendieck_smallFppfComapPrecoverage]
  apply Precoverage.generate_mem_toGrothendieck
  rw [mem_smallFppfComapPrecoverage_iff, Presieve.map_singleton]
  exact Scheme.Hom.singleton_mem_fppfPrecoverage g.left

variable {S}

noncomputable def homOfRingHom {X : Scheme.{u}} {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) :
    X ⟶ Spec R :=
  X.toSpecΓ ≫ Spec.map φ

noncomputable def ringHomOfHom {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

theorem ringHomOfHom_homOfRingHom {X : Scheme.{u}} {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) :
    ringHomOfHom (homOfRingHom φ) = φ := by
  simp only [ringHomOfHom, homOfRingHom, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem homOfRingHom_ringHomOfHom {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    homOfRingHom (ringHomOfHom f) = f := by
  simp only [ringHomOfHom, homOfRingHom, Spec.map_comp]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem homOfRingHom_comp {X : Scheme.{u}} {R R' : CommRingCat.{u}} (ψ : R' ⟶ R)
    (φ : R ⟶ Γ(X, ⊤)) : homOfRingHom (ψ ≫ φ) = homOfRingHom φ ≫ Spec.map ψ := by
  simp only [homOfRingHom, Spec.map_comp, Category.assoc]

theorem homOfRingHom_comp_Γmap {X Y : Scheme.{u}} (g : Y ⟶ X) {R : CommRingCat.{u}}
    (φ : R ⟶ Γ(X, ⊤)) : homOfRingHom (φ ≫ Scheme.Γ.map g.op) = g ≫ homOfRingHom φ := by
  simp only [homOfRingHom, Spec.map_comp, Scheme.Γ_map_op]
  rw [Scheme.toSpecΓ_naturality_assoc]

theorem ringHomOfHom_comp {X Y : Scheme.{u}} (g : Y ⟶ X) {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) : ringHomOfHom (g ≫ f) = ringHomOfHom f ≫ Scheme.Γ.map g.op := by
  simp only [ringHomOfHom, Scheme.Γ_map_op, Category.assoc]
  rfl

theorem homOfRingHom_injective {X : Scheme.{u}} {R : CommRingCat.{u}} :
    Function.Injective (homOfRingHom (X := X) (R := R)) := fun φ ψ h => by
  rw [← ringHomOfHom_homOfRingHom φ, h, ringHomOfHom_homOfRingHom]

theorem exists_cover_lift {R A : CommRingCat.{u}} (ι : R ⟶ A) [Flat (Spec.map ι)]
    [LocallyOfFinitePresentation (Spec.map ι)] [Surjective (Spec.map ι)]
    (U : S.Fppf) (x : R ⟶ Γ(U.left, ⊤)) :
    ∃ (W : S.Fppf) (g : W ⟶ U), Flat g.left ∧ LocallyOfFinitePresentation g.left ∧
      Surjective g.left ∧ ∃ a : A ⟶ Γ(W.left, ⊤), ι ≫ a = x ≫ Scheme.Γ.map g.left.op := by
  let y : U.left ⟶ Spec R := homOfRingHom x
  let g₀ := pullback.fst y (Spec.map ι)
  haveI : Flat g₀ := MorphismProperty.pullback_fst _ _ inferInstance
  have hW : fppfProperty (g₀ ≫ U.hom) :=
    fppfProperty.comp_mem _ _ ⟨inferInstanceAs (Flat g₀),
      inferInstanceAs (LocallyOfFinitePresentation g₀)⟩ U.prop
  let W : S.Fppf := Fppf.ofOver (Over.mk (g₀ ≫ U.hom)) hW
  let g : W ⟶ U := MorphismProperty.Over.homMk (A := W) (B := U) g₀ rfl
  refine ⟨W, g, inferInstanceAs (Flat g₀), inferInstanceAs (LocallyOfFinitePresentation g₀),
    inferInstanceAs (Surjective g₀), ringHomOfHom (pullback.snd y (Spec.map ι)), ?_⟩
  apply homOfRingHom_injective
  have h1 : homOfRingHom (x ≫ Scheme.Γ.map g.left.op) = g₀ ≫ y := homOfRingHom_comp_Γmap g₀ x
  rw [homOfRingHom_comp, homOfRingHom_ringHomOfHom]
  exact (pullback.condition).symm.trans h1.symm

end Geometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf"

section Points

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{0}} (K : Type) [CommRing K] [HopfAlgebra ℤ K]

abbrev Pts (U : S.Fppf) : Type := WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))

noncomputable def res {U V : S.Fppf} (f : U ⟶ V) : Pts K V →* Pts K U :=
  postcomp K (Scheme.Γ.map f.left.op).hom.toIntAlgHom

@[scoped simp] lemma res_apply_apply {U V : S.Fppf} (f : U ⟶ V) (x : Pts K V) (k : K) :
    res K f x k = (Scheme.Γ.map f.left.op) (x k) := rfl

lemma res_id (U : S.Fppf) (x : Pts K U) : res K (𝟙 U) x = x := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  change (Scheme.Γ.map (𝟙 U.left).op) (x k) = x k
  rw [op_id, Scheme.Γ.map_id]
  rfl

lemma res_comp {U V W : S.Fppf} (f : U ⟶ V) (g : V ⟶ W) (x : Pts K W) :
    res K (f ≫ g) x = res K f (res K g x) := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  change (Scheme.Γ.map (f.left ≫ g.left).op) (x k) = (Scheme.Γ.map f.left.op) ((Scheme.Γ.map g.left.op) (x k))
  rw [op_comp, Scheme.Γ.map_comp]
  rfl

lemma precomp_res {A : Type} [CommRing A] [HopfAlgebra ℤ A] (j : K →ₐc[ℤ] A) {U V : S.Fppf}
    (f : U ⟶ V) (a : Pts A V) : precomp _ j (res A f a) = res K f (precomp _ j a) := rfl

variable (S) in

class PtsComm : Prop where
  comm : ∀ (U : S.Fppf) (x y : Pts K U), x * y = y * x

noncomputable scoped instance instCommGroupPts [PtsComm S K] (U : S.Fppf) :
    CommGroup (Pts K U) :=
  { instGroupWithConv with mul_comm := PtsComm.comm U }

abbrev PtsCarrier [PtsComm S K] (U : S.Fppf) : Type 1 := ULift.{1} (Additive (Pts K U))

noncomputable def resAdd [PtsComm S K] {U V : S.Fppf} (f : U ⟶ V) :
    PtsCarrier K V →+ PtsCarrier K U :=
  (AddEquiv.ulift.symm.toAddMonoidHom.comp (MonoidHom.toAdditive (res K f))).comp
    AddEquiv.ulift.toAddMonoidHom

@[scoped simp] lemma resAdd_apply [PtsComm S K] {U V : S.Fppf} (f : U ⟶ V) (x : PtsCarrier K V) :
    resAdd K f x = ⟨Additive.ofMul (res K f (Additive.toMul x.down))⟩ := rfl

noncomputable def ptsPresheaf [PtsComm S K] : (S.Fppf)ᵒᵖ ⥤ Ab.{1} where
  obj U := AddCommGrpCat.of (PtsCarrier K (unop U))
  map f := AddCommGrpCat.ofHom (resAdd K f.unop)
  map_id U := by
    refine AddCommGrpCat.ext fun x => ?_
    change resAdd K (𝟙 (unop U)) x = x
    rw [resAdd_apply, res_id]
    rfl
  map_comp f g := by
    refine AddCommGrpCat.ext fun x => ?_
    change resAdd K (g.unop ≫ f.unop) x = resAdd K g.unop (resAdd K f.unop x)
    rw [resAdd_apply, resAdd_apply, resAdd_apply, res_comp]
    rfl

@[scoped simp] lemma ptsPresheaf_map_apply [PtsComm S K] {U V : (S.Fppf)ᵒᵖ} (f : U ⟶ V)
    (x : PtsCarrier K (unop U)) :
    (ptsPresheaf K).map f x = ⟨Additive.ofMul (res K f.unop (Additive.toMul x.down))⟩ := rfl

def algHomInt {K' Γ' : Type*} [Ring K'] [Ring Γ'] [Algebra ℤ K'] [Algebra ℤ Γ'] (φ : K' →+* Γ') :
    K' →ₐ[ℤ] Γ' :=
  { φ with commutes' := fun n => by simp }

@[scoped simp] lemma algHomInt_apply {K' Γ' : Type*} [Ring K'] [Ring Γ'] [Algebra ℤ K'] [Algebra ℤ Γ']
    (φ : K' →+* Γ') (k : K') : algHomInt φ k = φ k := rfl

noncomputable def ptOfHom {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) : WithConv (K →ₐ[ℤ] Γ(X, ⊤)) :=
  WithConv.toConv (algHomInt ((ringHomOfHom f).hom : K →+* Γ(X, ⊤)) : K →ₐ[ℤ] Γ(X, ⊤))

noncomputable def homOfPt {X : Scheme.{0}} (x : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) : X ⟶ Spec (.of K) :=
  homOfRingHom (CommRingCat.ofHom (x.ofConv.toRingHom : K →+* Γ(X, ⊤)))

lemma homOfPt_ptOfHom {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) : homOfPt K (ptOfHom K f) = f := by
  unfold homOfPt ptOfHom
  have h : (algHomInt ((ringHomOfHom f).hom : K →+* Γ(X, ⊤)) : K →ₐ[ℤ] Γ(X, ⊤)).toRingHom =
      (ringHomOfHom f).hom := RingHom.ext fun _ => rfl
  rw [WithConv.ofConv_toConv, h, CommRingCat.ofHom_hom, homOfRingHom_ringHomOfHom]

lemma ptOfHom_homOfPt {X : Scheme.{0}} (x : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) :
    ptOfHom K (homOfPt K x) = x := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  unfold homOfPt ptOfHom
  rw [ringHomOfHom_homOfRingHom]
  rfl

lemma ptOfHom_comp {X Y : Scheme.{0}} (g : Y ⟶ X) (f : X ⟶ Spec (.of K)) :
    ptOfHom K (g ≫ f) = postcomp K (Scheme.Γ.map g.op).hom.toIntAlgHom (ptOfHom K f) := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  unfold ptOfHom
  rw [ringHomOfHom_comp]
  rfl

noncomputable def ptEquiv (X : Scheme.{0}) :
    (X ⟶ Spec (.of K)) ≃ Additive (WithConv (K →ₐ[ℤ] Γ(X, ⊤))) where
  toFun f := Additive.ofMul (ptOfHom K f)
  invFun a := homOfPt K (Additive.toMul a)
  left_inv f := by
    change homOfPt K (ptOfHom K f) = f
    exact homOfPt_ptOfHom K f
  right_inv a := by
    change Additive.ofMul (ptOfHom K (homOfPt K (Additive.toMul a))) = a
    rw [ptOfHom_homOfPt]
    rfl

theorem ptsPresheaf_isSheaf [PtsComm S K] :
    Presheaf.IsSheaf (smallFppfTopology S) (ptsPresheaf K) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology S) _ (forget Ab.{1}),
    isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_of_nat_equiv
    (P₁ := (Fppf.forget S ⋙ Over.forget S).op ⋙ yoneda.obj (Spec (.of K)))
    (P₂ := ptsPresheaf K ⋙ forget Ab.{1})
    (fun U : S.Fppf => (ptEquiv K U.left).trans Equiv.ulift.symm) ?_
    (isSheaf_yoneda_comp S (Spec (.of K)))
  intro U V f g
  change (⟨Additive.ofMul (ptOfHom K (f.left ≫ g))⟩ : PtsCarrier K U) =
    (ptsPresheaf K).map f.op ⟨Additive.ofMul (ptOfHom K g)⟩
  rw [ptsPresheaf_map_apply, ptOfHom_comp]
  rfl

noncomputable def ptsSheaf [PtsComm S K] : Sheaf (smallFppfTopology S) Ab.{1} :=
  ⟨ptsPresheaf K, ptsPresheaf_isSheaf K⟩

end Points
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf"

section Main

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

lemma homOfPt_injective (K : Type) [CommRing K] [HopfAlgebra ℤ K] {X : Scheme.{0}} :
    Function.Injective (homOfPt K (X := X)) := fun x y h => by
  rw [← ptOfHom_homOfPt K x, h, ptOfHom_homOfPt]

lemma homOfPt_res (K : Type) [CommRing K] [HopfAlgebra ℤ K] {S : Scheme.{0}} {U V : S.Fppf}
    (g : U ⟶ V) (x : Pts K V) : homOfPt K (res K g x) = g.left ≫ homOfPt K x := by
  rw [← homOfPt_ptOfHom K (g.left ≫ homOfPt K x), ptOfHom_comp, ptOfHom_homOfPt]
  rfl

lemma mul_comm_of_addEquiv {G M : Type*} [AddCommGroup G] [Monoid M] (e : G ≃+ Additive M)
    (a b : M) : a * b = b * a := by
  have h := add_comm (e.symm (Additive.ofMul a)) (e.symm (Additive.ofMul b))
  apply_fun e at h
  rw [map_add, map_add, e.apply_symm_apply, e.apply_symm_apply] at h
  exact congrArg Additive.toMul h

structure LayerData (S : Scheme.{0}) (K A B : Type) [CommRing K] [HopfAlgebra ℤ K] [CommRing A]
    [HopfAlgebra ℤ A] [CommRing B] [HopfAlgebra ℤ B] where
  qc : A →ₐc[ℤ] B
  j : K →ₐc[ℤ] A
  F₀ : Sheaf (smallFppfTopology S) Ab.{1}
  F₁ : Sheaf (smallFppfTopology S) Ab.{1}
  L : Sheaf (smallFppfTopology S) Ab.{1}
  incl : F₀ ⟶ F₁
  pr : F₁ ⟶ L
  hzero : incl ≫ pr = 0
  hses : (ShortComplex.mk incl pr hzero).ShortExact
  e₁ : ∀ U : S.Fppf, F₁.1.obj (op U) ≃+ Additive (Pts A U)
  he₁ : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : F₁.1.obj (op V)),
    Additive.toMul (e₁ U (F₁.1.map f.op s)) = res A f (Additive.toMul (e₁ V s))
  e₀ : ∀ U : S.Fppf, F₀.1.obj (op U) ≃+ Additive (Pts B U)
  hincl : ∀ (U : S.Fppf) (s : F₀.1.obj (op U)),
    Additive.toMul (e₁ U (incl.1.app (op U) s)) = precomp _ qc (Additive.toMul (e₀ U s))
  hrange : (j : K →ₐ[ℤ] A).range = HopfAlgebra.hopfKer qc
  hHG : HopfAlgebra.IsHopfGalois qc
  hlift : ∀ (U : S.Fppf) (x : Pts K U), ∃ (W : S.Fppf) (g : W ⟶ U),
    Flat g.left ∧ LocallyOfFinitePresentation g.left ∧ Surjective g.left ∧
      ∃ a : Pts A W, precomp _ j a = res K g x

namespace LayerData

variable {S : Scheme.{0}} {K A B : Type} [CommRing K] [HopfAlgebra ℤ K] [CommRing A]
    [HopfAlgebra ℤ A] [CommRing B] [HopfAlgebra ℤ B] (D : LayerData S K A B)

lemma comm_A (D : LayerData S K A B) (U : S.Fppf) (a b : Pts A U) : a * b = b * a :=
  mul_comm_of_addEquiv (D.e₁ U) a b

theorem ptsComm (D : LayerData S K A B) : PtsComm S K := by
  refine ⟨fun U x y => ?_⟩
  obtain ⟨W, g, hg1, hg2, hg3, a, ha⟩ := D.hlift U x
  obtain ⟨W', g', hg1', hg2', hg3', b, hb⟩ := D.hlift W (res K g y)
  have key : res K (g' ≫ g) (x * y) = res K (g' ≫ g) (y * x) := by
    rw [res_comp, res_comp, map_mul, map_mul, map_mul, map_mul, ← ha, ← hb, ← precomp_res,
      ← map_mul, ← map_mul, D.comm_A W']
  haveI : Flat (g' ≫ g).left := inferInstanceAs (Flat (g'.left ≫ g.left))
  haveI : LocallyOfFinitePresentation (g' ≫ g).left :=
    inferInstanceAs (LocallyOfFinitePresentation (g'.left ≫ g.left))
  haveI : Surjective (g' ≫ g).left := inferInstanceAs (Surjective (g'.left ≫ g.left))
  apply homOfPt_injective K
  refine (isSheaf_yoneda_comp S (Spec (.of K)) _
    (generate_singleton_mem S (g' ≫ g))).isSeparatedFor.ext ?_
  rintro V f ⟨V', f', f'', ⟨⟩, rfl⟩
  change (f' ≫ g' ≫ g).left ≫ homOfPt K (x * y) = (f' ≫ g' ≫ g).left ≫ homOfPt K (y * x)
  rw [← homOfPt_res, ← homOfPt_res, res_comp, key, ← res_comp]

section

variable [PtsComm S K]

noncomputable def theta (U : S.Fppf) : D.F₁.1.obj (op U) →+ PtsCarrier K U :=
  (AddEquiv.ulift.symm.toAddMonoidHom.comp (MonoidHom.toAdditive (precomp _ D.j))).comp
    (D.e₁ U).toAddMonoidHom

@[scoped simp] lemma theta_apply (U : S.Fppf) (s : D.F₁.1.obj (op U)) :
    D.theta U s = ⟨Additive.ofMul (precomp _ D.j (Additive.toMul (D.e₁ U s)))⟩ := rfl

noncomputable def phi : D.F₁ ⟶ ptsSheaf K :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom (D.theta (unop U))
      naturality := fun U V f => by
        refine AddCommGrpCat.ext fun s => ?_
        change D.theta (unop V) (D.F₁.1.map f.unop.op s) =
          (ptsPresheaf K).map f (D.theta (unop U) s)
        rw [ptsPresheaf_map_apply, theta_apply, theta_apply, D.he₁]
        rfl }

@[scoped simp] lemma phi_app_apply (U : S.Fppf) (s : D.F₁.1.obj (op U)) :
    D.phi.1.app (op U) s = D.theta U s := rfl

lemma incl_phi : D.incl ≫ D.phi = 0 := by
  ext U s
  change D.theta (unop U) (D.incl.1.app U s) = 0
  rw [theta_apply, D.hincl, precomp_precomp_eq_one D.qc D.j D.hrange.le]
  rfl

noncomputable def psi : D.L ⟶ ptsSheaf K :=
  D.hses.gIsCokernel.desc (CokernelCofork.ofπ D.phi D.incl_phi)

lemma pr_psi : D.pr ≫ D.psi = D.phi :=
  Cofork.IsColimit.π_desc D.hses.gIsCokernel

lemma psi_pr_apply (U : S.Fppf) (s : D.F₁.1.obj (op U)) :
    D.psi.1.app (op U) (D.pr.1.app (op U) s) = D.theta U s := by
  have h := congrArg (fun η => η.1.app (op U)) D.pr_psi
  have h' := ConcreteCategory.congr_hom h s
  simpa using h'

lemma exists_incl_eq (U : S.Fppf) (s : D.F₁.1.obj (op U)) (h : D.theta U s = 0) :
    ∃ r, D.incl.1.app (op U) r = s := by
  have h1 : precomp _ D.j (Additive.toMul (D.e₁ U s)) = 1 := by
    have := congrArg (fun t : PtsCarrier K U => Additive.toMul t.down) h
    simpa using this
  obtain ⟨χ, hχ⟩ := exists_precomp_eq_of_precomp_eq_one D.qc D.j D.hHG D.hrange _ h1
  refine ⟨(D.e₀ U).symm (Additive.ofMul χ), (D.e₁ U).injective ?_⟩
  apply Additive.toMul.injective
  rw [D.hincl, AddEquiv.apply_symm_apply, toMul_ofMul, hχ]

lemma presieve_isSheaf_forget (F : Sheaf (smallFppfTopology S) Ab.{1}) :
    Presieve.IsSheaf (smallFppfTopology S) (F.1 ⋙ forget Ab.{1}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology S) F.1 (forget Ab.{1})).mp F.2)

lemma psi_injective (U : S.Fppf) : Function.Injective (D.psi.1.app (op U)) := by
  haveI : Sheaf.IsLocallySurjective D.pr :=
    (Sheaf.isLocallySurjective_iff_epi' (A := Ab.{1}) D.pr).mpr D.hses.epi_g
  intro t t' htt
  rw [← sub_eq_zero] at htt ⊢
  rw [← map_sub] at htt
  set u := t - t' with hu

  refine (presieve_isSheaf_forget D.L _
    (Presheaf.imageSieve_mem (smallFppfTopology S) D.pr.1 u)).isSeparatedFor.ext ?_
  rintro V f ⟨s, hs⟩
  change D.L.1.map f.op u = D.L.1.map f.op 0
  rw [map_zero, ← hs]

  have hθ : D.theta V s = 0 := by
    rw [← psi_pr_apply, hs]
    have := ConcreteCategory.congr_hom (D.psi.1.naturality f.op) u
    simp only [ConcreteCategory.comp_apply] at this
    change D.psi.1.app (op V) (D.L.1.map f.op u) = (ptsPresheaf K).map f.op (D.psi.1.app (op U) u)
      at this
    rw [this, htt]
    exact map_zero _
  obtain ⟨r, rfl⟩ := D.exists_incl_eq V s hθ
  have h0 := ConcreteCategory.congr_hom (congrArg (fun η => η.1.app (op V)) D.hzero) r
  simpa using h0

scoped instance mono_psi : Mono D.psi := by
  haveI : ∀ U, Mono (D.psi.1.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).mpr (D.psi_injective (unop U))
  haveI : Mono D.psi.1 := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

scoped instance isLocallySurjective_phi : Sheaf.IsLocallySurjective D.phi := by
  refine ⟨fun {U} x => ?_⟩
  obtain ⟨W, g, hg1, hg2, hg3, a, ha⟩ := D.hlift U (Additive.toMul x.down)
  refine (smallFppfTopology S).superset_covering ?_ (generate_singleton_mem S g)
  rw [Sieve.generate_le_iff]
  rintro V f ⟨⟩
  refine ⟨(D.e₁ W).symm (Additive.ofMul a), ?_⟩
  change D.theta W ((D.e₁ W).symm (Additive.ofMul a)) = (ptsPresheaf K).map g.op x
  rw [theta_apply, AddEquiv.apply_symm_apply, toMul_ofMul, ha, ptsPresheaf_map_apply]
  rfl

scoped instance epi_psi : Epi D.psi := by
  haveI : Epi D.phi := Sheaf.epi_of_isLocallySurjective D.phi
  exact epi_of_epi_fac D.pr_psi

scoped instance isIso_psi : IsIso D.psi := isIso_of_mono_of_epi D.psi

scoped instance isIso_psi_val : IsIso D.psi.1 :=
  inferInstanceAs (IsIso ((sheafToPresheaf _ _).map D.psi))

noncomputable def equiv (U : S.Fppf) : D.L.1.obj (op U) ≃+ Additive (Pts K U) :=
  (asIso (D.psi.1.app (op U))).addCommGroupIsoToAddEquiv.trans
    { toFun := fun x => x.down
      invFun := fun x => ⟨x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

lemma equiv_apply (U : S.Fppf) (t : D.L.1.obj (op U)) :
    D.equiv U t = (D.psi.1.app (op U) t).down := rfl

lemma equiv_natural {U V : S.Fppf} (f : U ⟶ V) (s : D.L.1.obj (op V)) (k : K) :
    (Additive.toMul (D.equiv U (D.L.1.map f.op s))) k =
      (Scheme.Γ.map f.left.op) ((Additive.toMul (D.equiv V s)) k) := by
  rw [equiv_apply, equiv_apply]
  have := ConcreteCategory.congr_hom (D.psi.1.naturality f.op) s
  simp only [ConcreteCategory.comp_apply] at this
  change D.psi.1.app (op U) (D.L.1.map f.op s) = (ptsPresheaf K).map f.op (D.psi.1.app (op V) s)
    at this
  rw [this, ptsPresheaf_map_apply]
  rfl

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf"

end LayerData
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.LayerData"

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.LayerData"

section Lift

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

theorem exists_lift {S : Scheme.{0}} {K A B : Type} [CommRing K] [HopfAlgebra ℤ K]
    [Algebra.FiniteType ℤ K] [CommRing A] [HopfAlgebra ℤ A] [Algebra.FiniteType ℤ A]
    [CommRing B] [HopfAlgebra ℤ B]
    (qc : A →ₐc[ℤ] B) (j : K →ₐc[ℤ] A) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] A).range = HopfAlgebra.hopfKer qc)
    (hff : Module.FaithfullyFlat (HopfAlgebra.hopfKer qc) A)
    (U : S.Fppf) (x : Pts K U) :
    ∃ (W : S.Fppf) (g : W ⟶ U), Flat g.left ∧ LocallyOfFinitePresentation g.left ∧
      Surjective g.left ∧ ∃ a : Pts A W, precomp _ j a = res K g x := by
  set K' : Subalgebra ℤ A := HopfAlgebra.hopfKer qc with hK'
  let e : K ≃ₐ[ℤ] K' :=
    (AlgEquiv.ofInjective (j : K →ₐ[ℤ] A) hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  have he : ∀ k, ((e k : K') : A) = j k := fun k => rfl
  haveI : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing ℤ K
  haveI : IsNoetherianRing K' := isNoetherianRing_of_ringEquiv K e.toRingEquiv
  haveI : Algebra.FiniteType K' A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ K' A
  haveI : Algebra.FinitePresentation K' A := (Algebra.FinitePresentation.of_finiteType).mp ‹_›
  let ι : CommRingCat.of K' ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap K' A)
  haveI : Flat (Spec.map ι) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : LocallyOfFinitePresentation (Spec.map ι) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr ‹_›)
  haveI : Surjective (Spec.map ι) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K') (B := A)⟩
  let x' : K' →+* Γ(U.left, ⊤) := x.ofConv.toRingHom.comp e.symm.toRingEquiv.toRingHom
  obtain ⟨W, g, h1, h2, h3, a', ha'⟩ := exists_cover_lift ι U (CommRingCat.ofHom x')
  refine ⟨W, g, h1, h2, h3,
    WithConv.toConv (algHomInt (a'.hom : A →+* Γ(W.left, ⊤)) : A →ₐ[ℤ] Γ(W.left, ⊤)), ?_⟩
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  have h := congrArg (fun φ : CommRingCat.of K' ⟶ Γ(W.left, ⊤) => φ.hom (e k)) ha'
  change a'.hom (algebraMap K' A (e k)) = (Scheme.Γ.map g.left.op).hom (x' (e k)) at h
  have hx' : x' (e k) = x.ofConv k := by
    change x.ofConv (e.symm (e k)) = x.ofConv k
    rw [AlgEquiv.symm_apply_apply]
  rw [hx'] at h
  change a'.hom (j k) = (Scheme.Γ.map g.left.op) (x k)
  rw [← he k]
  exact h

end Lift
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.LayerData"

section Assembly

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable def mkLayerData (S : Scheme.{0})
    (A : Type) [CommRing A] [HopfAlgebra ℤ A] [Algebra.FiniteType ℤ A]
    (B : Type) [CommRing B] [HopfAlgebra ℤ B] (qc : A →ₐc[ℤ] B)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K]
    (j : K →ₐc[ℤ] A) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] A).range = HopfAlgebra.hopfKer qc)
    (hHG : HopfAlgebra.IsHopfGalois qc)
    (hff : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) A)
    (F₀ F₁ L : Sheaf (smallFppfTopology S) Ab.{1})
    (incl : F₀ ⟶ F₁) (pr : F₁ ⟶ L) (hzero : incl ≫ pr = 0)
    (hses : (ShortComplex.mk incl pr hzero).ShortExact)
    (e₁ : ∀ U : S.Fppf, F₁.1.obj (op U) ≃+ Additive (WithConv (A →ₐ[ℤ] Γ(U.left, ⊤))))
    (he₁ : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : F₁.1.obj (op V)) (a : A),
      (Additive.toMul (e₁ U (F₁.1.map f.op s))) a
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e₁ V s)) a))
    (e₀ : ∀ U : S.Fppf, F₀.1.obj (op U) ≃+ Additive (WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))))
    (hincl : ∀ (U : S.Fppf) (s : F₀.1.obj (op U)) (a : A),
      (Additive.toMul (e₁ U (incl.1.app (op U) s))) a = (Additive.toMul (e₀ U s)) (qc a)) :
    LayerData S K A B where
  qc := qc
  j := j
  F₀ := F₀
  F₁ := F₁
  L := L
  incl := incl
  pr := pr
  hzero := hzero
  hses := hses
  e₁ := e₁
  he₁ := fun f s => WithConv.ext (AlgHom.ext fun a => he₁ f s a)
  e₀ := e₀
  hincl := fun U s => WithConv.ext (AlgHom.ext fun a => hincl U s a)
  hrange := hrange
  hHG := hHG
  hlift := exists_lift qc j hinj hrange hff

end Assembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.LayerData"

end FppfHopfQuotientSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.Fppf P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol.LayerData P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.FppfHopfQuotientSol"

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

theorem solution
    (S : Scheme.{0})
    (A : Type) [CommRing A] [HopfAlgebra ℤ A] [Algebra.FiniteType ℤ A]
    (B : Type) [CommRing B] [HopfAlgebra ℤ B] (qc : A →ₐc[ℤ] B)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K]
    (j : K →ₐc[ℤ] A) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] A).range = HopfAlgebra.hopfKer qc)
    (hHG : HopfAlgebra.IsHopfGalois qc)
    (hff : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) A)
    (F₀ F₁ L : Sheaf (smallFppfTopology S) Ab.{1})
    (incl : F₀ ⟶ F₁) (pr : F₁ ⟶ L) (hzero : incl ≫ pr = 0)
    (hses : (ShortComplex.mk incl pr hzero).ShortExact)
    (e₁ : ∀ U : S.Fppf, F₁.1.obj (op U) ≃+ Additive (WithConv (A →ₐ[ℤ] Γ(U.left, ⊤))))
    (he₁ : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : F₁.1.obj (op V)) (a : A),
      (Additive.toMul (e₁ U (F₁.1.map f.op s))) a
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e₁ V s)) a))
    (e₀ : ∀ U : S.Fppf, F₀.1.obj (op U) ≃+ Additive (WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))))
    (hincl : ∀ (U : S.Fppf) (s : F₀.1.obj (op U)) (a : A),
      (Additive.toMul (e₁ U (incl.1.app (op U) s))) a = (Additive.toMul (e₀ U s)) (qc a)) :
    ∃ e : ∀ U : S.Fppf, L.1.obj (op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))),
      (∀ (U : S.Fppf) (s : F₁.1.obj (op U)) (k : K),
        (Additive.toMul (e U (pr.1.app (op U) s))) k = (Additive.toMul (e₁ U s)) (j k)) ∧
      ∀ {U V : S.Fppf} (f : U ⟶ V) (s : L.1.obj (op V)) (k : K),
        (Additive.toMul (e U (L.1.map f.op s))) k
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k) := by
  let D := FppfHopfQuotientSol.mkLayerData S A B qc K j hinj hrange hHG hff F₀ F₁ L incl pr hzero
    hses e₁ he₁ e₀ hincl
  haveI := D.ptsComm
  refine ⟨fun U => D.equiv U, fun U s k => ?_, fun f s k => D.equiv_natural f s k⟩
  change (Additive.toMul (D.equiv U (D.pr.1.app (op U) s))) k = _
  rw [D.equiv_apply, D.psi_pr_apply, D.theta_apply]
  rfl

end S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois (solution)
