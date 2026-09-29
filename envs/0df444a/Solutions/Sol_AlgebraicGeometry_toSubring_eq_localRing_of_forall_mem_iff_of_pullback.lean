-- Prove2me | solution 1 for AlgebraicGeometry.toSubring_eq_localRing_of_forall_mem_iff_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/17abc7ff-8c78-5204-8a64-c7bfdc34c366

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback.AlgebraicGeometry AlgebraicCurve IsLocalRing"
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "LocallyRingedSpace LocallyRingedSpace.notMem_prime_iff_unit_in_stalk Scheme.germToFunctionField IsProper isPushout_appTop_of_isPullback Scheme.Hom Scheme.Hom.germ_stalkMap_apply isPullback_morphismRestrict IsAffineOpen.isoSpec_hom Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.Opens.toSpecΓ_naturality Scheme.toSpecΓ_appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat SpecMap_ΓSpecIso_hom IsAffineOpen.comap_primeIdealOf_appLE IsAffineOpen.isLocalization_stalk IsAffineOpen IsAffineOpen.fromSpec_primeIdealOf Scheme.Opens Scheme.ΓSpecIso_naturality IsAffineHom toSpecΓ Scheme.ΓSpecIso functionField_isScalarTower Scheme.Hom.appLE_eq_app"
namespace ValCentre
p2m_open "AlgebraicGeometry"

section Pull

variable {X Y : Scheme.{0}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

theorem pull_germ [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

end Pull

section Chart

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)

theorem fromSpec_appTop_ΓSpecIso_hom :
    hU.fromSpec.appTop ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = X.presheaf.map (homOfLE le_top).op := by
  have h : (hU.fromSpec ≫ X.toSpecΓ).appTop =
      (Spec.map (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)).appTop := by
    rw [hU.fromSpec_toSpecΓ]
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
  have h2 := Scheme.ΓSpecIso_naturality (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
  rw [← h, Category.assoc] at h2
  exact (cancel_epi _).mp h2

end Chart

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U) (b : Γ(X, U)) :
    b ∈ (hU.primeIdealOf x).asIdeal ↔ ¬ IsUnit (X.presheaf.germ U x x.2 b) := by
  rw [hU.primeIdealOf_eq_map_closedPoint]
  change b ∈ Ideal.comap (X.presheaf.germ U x x.2).hom (closedPoint (X.presheaf.stalk x)).asIdeal ↔ _
  rw [Ideal.mem_comap]
  change (X.presheaf.germ U x x.2).hom b ∈ maximalIdeal _ ↔ _
  rw [mem_maximalIdeal, mem_nonunits_iff]

theorem mem_base_asIdeal_iff {X : Scheme.{0}} {A : Type} [CommRing A] (f : X ⟶ Spec (CommRingCat.of A))
    (x : X) (a : A) :
    a ∈ (f.base x).asIdeal ↔
      ¬ IsUnit (X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) := by
  have hnat := Scheme.toSpecΓ_naturality f
  rw [← SpecMap_ΓSpecIso_hom] at hnat
  have hpt := congrArg (fun g => g.base x) hnat
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hpt
  have h1 : (Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom).base (f.base x) =
      PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (f.base x) := rfl
  have h2 : (Spec.map f.appTop).base (X.toSpecΓ.base x) =
      PrimeSpectrum.comap f.appTop.hom (X.toSpecΓ.base x) := rfl
  rw [h1, h2] at hpt
  have key : ∀ s : Γ(Spec (CommRingCat.of A), ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s ∈ (f.base x).asIdeal ↔
        f.appTop.hom s ∈ (X.toSpecΓ.base x).asIdeal := by
    intro s
    have := congrArg (fun p : PrimeSpectrum _ => s ∈ p.asIdeal) hpt
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using this.to_iff
  have e : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = a := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have key' := key ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
  rw [e] at key'
  rw [key']
  have h3 := AlgebraicGeometry.LocallyRingedSpace.notMem_prime_iff_unit_in_stalk X.toLocallyRingedSpace
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) x
  rw [← not_iff_not, not_not]
  exact h3

theorem isUnit_iff_ne_zero_and_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {y : F} (hy : y ∈ O) :
    IsUnit (⟨y, hy⟩ : O) ↔ y ≠ 0 ∧ y⁻¹ ∈ O := by
  constructor
  · rintro ⟨u, hu⟩
    have hy0 : y ≠ 0 := by
      intro h0
      apply u.ne_zero
      rw [hu]
      exact Subtype.ext h0
    refine ⟨hy0, ?_⟩
    have e : ((↑(u⁻¹) : O) : F) = y⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun z : O => (z : F)) u.inv_mul
      simpa [hu] using this
    rw [← e]; exact (↑(u⁻¹) : O).2
  · rintro ⟨hy0, hinv⟩
    exact ⟨⟨⟨y, hy⟩, ⟨y⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy0), Subtype.ext (inv_mul_cancel₀ hy0)⟩, rfl⟩

theorem eq_of_le_of_forall_inv_mem {F : Type*} [Field F] (V O : ValuationSubring F) (hle : V ≤ O)
    (h : ∀ (y : F) (hy : y ∈ V), IsUnit (⟨y, hle hy⟩ : O) → y⁻¹ ∈ V) : O = V := by
  refine le_antisymm ?_ hle
  intro x hx
  by_contra hxV
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxV V.zero_mem
  have hu : IsUnit (⟨x⁻¹, hle hxinv⟩ : O) :=
    (isUnit_iff_ne_zero_and_inv_mem O (hle hxinv)).mpr ⟨inv_ne_zero hx0, by rw [inv_inv]; exact hx⟩
  have := h x⁻¹ hxinv hu
  rw [inv_inv] at this
  exact hxV this

theorem notMem_iff_inv_mem_range {R S K : Type*} [CommRing R] [IsDomain R] [CommRing S] [Field K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K] [IsFractionRing R K]
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime S P] (r : R) :
    r ∉ P ↔ r ≠ 0 ∧ (algebraMap R K r)⁻¹ ∈ (algebraMap S K).range := by
  constructor
  · intro hr
    have hr0 : r ≠ 0 := fun h => hr (h ▸ P.zero_mem)
    refine ⟨hr0, IsLocalization.mk' S (1 : R) ⟨r, show r ∈ P.primeCompl from hr⟩, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    have h1 := IsLocalization.mk'_spec S (1 : R) (⟨r, show r ∈ P.primeCompl from hr⟩ : P.primeCompl)
    have h2 := congrArg (algebraMap S K) h1
    rw [map_mul, map_one] at h2
    simpa [← IsScalarTower.algebraMap_apply] using h2
  · rintro ⟨hr0, z, hz⟩ hrP
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    have h1 := IsLocalization.mk'_spec S b s
    have h2 := congrArg (algebraMap S K) h1
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hz] at h2

    have hr0' : algebraMap R K r ≠ 0 :=
      fun h => hr0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) r h)
    have h3 : algebraMap R K (s : R) = algebraMap R K (r * b) := by
      rw [map_mul, ← h2, ← mul_assoc, mul_inv_cancel₀ hr0', one_mul]
    have h4 : (s : R) = r * b := IsFractionRing.injective R K h3
    exact s.2 (h4 ▸ P.mul_mem_right b hrP)

theorem linearIndependent_pow_of_mem_maximalIdeal
    {L : Type*} [Field L] (A : ValuationSubring L) (k : Subfield L) (hk : ∀ z ∈ k, z ∈ A)
    [Algebra k A] [IsScalarTower k A L]
    (t : A) (ht : t ∈ maximalIdeal A) (ht0 : t ≠ 0) (n : ℕ) :
    LinearIndependent k (fun i : Fin n => t ^ (i : ℕ)) := by
  classical

  refine LinearIndependent.of_comp (IsScalarTower.toAlgHom k A L).toLinearMap ?_
  have hcomp : ((IsScalarTower.toAlgHom k A L).toLinearMap ∘ fun i : Fin n => t ^ (i : ℕ)) =
      fun i : Fin n => (t : L) ^ (i : ℕ) := by
    funext i
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, map_pow]
    rfl
  rw [hcomp, Fintype.linearIndependent_iff]
  intro c hc

  let p : Polynomial k := ∑ i : Fin n, Polynomial.monomial (i : ℕ) (c i)
  have hp : Polynomial.aeval (t : L) p = 0 := by
    rw [← hc]
    simp only [p, map_sum, Polynomial.aeval_monomial, Algebra.smul_def]
  have hcoeff : ∀ i : Fin n, p.coeff (i : ℕ) = c i := by
    intro i
    simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg]
      exact fun h => hji (Fin.ext h)
    · intro hi; exact absurd (Finset.mem_univ i) hi
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hp0 : p ≠ 0 := by
    intro h0
    apply hi
    rw [← hcoeff i, h0, Polynomial.coeff_zero]
  have halg : IsAlgebraic k (t : L) := ⟨p, hp0, hp⟩

  let A' : Subalgebra k L :=
    { carrier := A
      mul_mem' := fun ha hb => A.mul_mem _ _ ha hb
      one_mem' := A.one_mem
      add_mem' := fun ha hb => A.add_mem _ _ ha hb
      zero_mem' := A.zero_mem
      algebraMap_mem' := fun z => hk z z.2 }
  have hadj : Algebra.adjoin k {(t : L)} ≤ A' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr t.2)
  have hinv : (t : L)⁻¹ ∈ Algebra.adjoin k {(t : L)} := by
    have := Subalgebra.inv_mem_of_algebraic (A := Algebra.adjoin k {(t : L)})
      (x := ⟨t, Algebra.self_mem_adjoin_singleton k (t : L)⟩) halg
    exact this
  have hinvA : (t : L)⁻¹ ∈ A := hadj hinv
  have ht0' : (t : L) ≠ 0 := fun h => ht0 (Subtype.ext h)
  apply (mem_maximalIdeal _).mp ht
  exact ⟨⟨t, ⟨(t : L)⁻¹, hinvA⟩, Subtype.ext (mul_inv_cancel₀ ht0'), Subtype.ext (inv_mul_cancel₀ ht0')⟩, rfl⟩

theorem one_tmul_eq_zero_of_sum_pow_tmul
    {A₀ k S R : Type} [CommRing A₀] [Field k] [CommRing S] [CommRing R]
    [Algebra A₀ k] [Algebra k S] [Algebra A₀ S] [IsScalarTower A₀ k S] [Algebra A₀ R]
    (t : S) (n : ℕ) (hlin : LinearIndependent k (fun i : Fin n => t ^ (i : ℕ)))
    (r : Fin n → R) (hrel : ∑ i : Fin n, (t ^ (i : ℕ)) ⊗ₜ[A₀] r i = (0 : S ⊗[A₀] R)) :
    ∀ i, (1 : S) ⊗ₜ[A₀] r i = (0 : S ⊗[A₀] R) := by
  classical
  have hS : ∀ c : A₀, (1 : k ⊗[A₀] R) ⊗ₜ[k] (algebraMap A₀ S c) =
      algebraMap A₀ ((k ⊗[A₀] R) ⊗[k] S) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply A₀ k S, Algebra.algebraMap_eq_smul_one (A := S), TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
    rfl
  let fS : S →ₐ[A₀] (k ⊗[A₀] R) ⊗[k] S :=
    { toRingHom := (Algebra.TensorProduct.includeRight : S →ₐ[k] (k ⊗[A₀] R) ⊗[k] S).toRingHom
      commutes' := fun c => hS c }
  have hR : ∀ c : A₀, ((1 : k) ⊗ₜ[A₀] (algebraMap A₀ R c)) ⊗ₜ[k] (1 : S) =
      algebraMap A₀ ((k ⊗[A₀] R) ⊗[k] S) c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one (A := R) c, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
  let gR : R →ₐ[A₀] (k ⊗[A₀] R) ⊗[k] S :=
    { toRingHom := ((Algebra.TensorProduct.includeLeft : k ⊗[A₀] R →ₐ[k] (k ⊗[A₀] R) ⊗[k] S).toRingHom.comp
        (Algebra.TensorProduct.includeRight : R →ₐ[A₀] k ⊗[A₀] R).toRingHom)
      commutes' := fun c => hR c }
  let G : S ⊗[A₀] R →ₐ[A₀] (k ⊗[A₀] R) ⊗[k] S := Algebra.TensorProduct.lift fS gR (fun x y => Commute.all (fS x) (gR y))
  have hG : ∀ (s : S) (x : R), G (s ⊗ₜ x) = ((1 : k) ⊗ₜ[A₀] x) ⊗ₜ[k] s := by
    intro s x
    rw [Algebra.TensorProduct.lift_tmul]
    change ((1 : k ⊗[A₀] R) ⊗ₜ[k] s) * (((1 : k) ⊗ₜ[A₀] x) ⊗ₜ[k] (1 : S)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hrel' : ∑ i, ((1 : k) ⊗ₜ[A₀] r i) • ((1 : k ⊗[A₀] R) ⊗ₜ[k] (t ^ (i : ℕ))) =
      (0 : (k ⊗[A₀] R) ⊗[k] S) := by
    have := congrArg G hrel
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hli : LinearIndependent (k ⊗[A₀] R) (fun i : Fin n => (1 : k ⊗[A₀] R) ⊗ₜ[k] (t ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hlin
  have hzero : ∀ i, (1 : k) ⊗ₜ[A₀] r i = (0 : k ⊗[A₀] R) := fun i =>
    Fintype.linearIndependent_iff.mp hli (fun i => (1 : k) ⊗ₜ[A₀] r i) hrel' i
  intro i
  have := congrArg (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A₀ k S) (AlgHom.id A₀ R)) (hzero i)
  rw [Algebra.TensorProduct.map_tmul, map_zero, map_one] at this
  simpa using this

theorem coe_unit_inv {L : Type*} [Field L] (A : ValuationSubring L) (u : (↥A)ˣ) :
    ((↑(u⁻¹) : ↥A) : L) = ((u : ↥A) : L)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have := congrArg (fun z : ↥A => (z : L)) u.inv_mul
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
  exact this

end AlgebraicGeometry.ValCentre

end

open AlgebraicGeometry.ValCentre in
theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] (ι : A₀ →+* ↥A)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X₀]
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X] [IsProper toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hgen : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) = genericPoint X₀)
    (j₀ : X₀.functionField →+* F)
    (hj₀ : ∀ g : X₀.functionField, φ (j₀ g) =
      ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint X)).hom
        ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g))
    (halgF : ∀ f : F, IsAlgebraic ↥(j₀.range) f)
    (η : X) (hη : toBase.base η = closedPoint ↥A)
    (hfib : ∀ x : X, toBase.base x = closedPoint ↥A →
      (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x =
        (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η → x = η)
    (hV : ∃ V : ValuationSubring F, V.toSubring = SemistableModel.localRing X φ η)
    (O : ValuationSubring F) (hOA : ∀ a : ↥A, algebraMap L F (a : L) ∈ O)
    (hOtr : ∀ g : X₀.functionField, j₀ g ∈ O ↔
      g ∈ (algebraMap (X₀.presheaf.stalk
              ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η))
            X₀.functionField).range) :
    O.toSubring = SemistableModel.localRing X φ η := by
  classical
  set pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι)) with hpr
  set y₀ : X₀ := pr.base η with hy₀def

  have hP : IsPullback pr toBase toBase₀ (Spec.map (CommRingCat.ofHom ι)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso rfl hiso
    rw [hpr, Category.assoc, pullback.condition, ← Category.assoc, hiso]
  haveI : IsAffineHom pr :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip inferInstance
  have hgen' : pr.base (genericPoint X) ⤳ genericPoint X₀ := specializes_of_eq hgen
  let φ₀ : X₀.functionField →+* X.functionField := (pull pr hgen').hom
  have hφgerm : ∀ (U : X₀.Opens) (hU : genericPoint X₀ ∈ U) (s : Γ(X₀, U)),
      φ₀ (X₀.presheaf.germ U (genericPoint X₀) hU s) =
        X.presheaf.germ (pr ⁻¹ᵁ U) (genericPoint X) (hgen'.mem_open U.isOpen hU) (pr.app U s) :=
    fun U hU s => pull_germ pr hgen' U hU s

  obtain ⟨U, hU, hy₀U⟩ : ∃ U : X₀.Opens, IsAffineOpen U ∧ y₀ ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y₀) isOpen_univ
    exact ⟨U, hU, hxU⟩
  have hxU : genericPoint X₀ ∈ U :=
    ((genericPoint_spec X₀).mem_open_set_iff U.isOpen).mpr ⟨y₀, Set.mem_univ _, hy₀U⟩
  set W : X.Opens := pr ⁻¹ᵁ U with hWdef
  have hηW : η ∈ W := hy₀U
  have hyV : genericPoint X ∈ W := hgen'.mem_open U.isOpen hxU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : Nonempty W := ⟨⟨_, hyV⟩⟩
  have hW : IsAffineOpen W := hU.preimage pr
  haveI := functionField_isFractionRing_of_isAffineOpen X₀ U hU
  haveI := functionField_isFractionRing_of_isAffineOpen X W hW

  have hP1 : IsPullback (pr ∣_ U) (W.ι ≫ toBase) (U.ι ≫ toBase₀) (Spec.map (CommRingCat.ofHom ι)) :=
    (isPullback_morphismRestrict pr U).paste_vert hP
  have hP2 : IsPullback (Spec.map (pr.app U)) (hW.fromSpec ≫ toBase) (hU.fromSpec ≫ toBase₀)
      (Spec.map (CommRingCat.ofHom ι)) := by
    refine hP1.of_iso hW.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
      exact (Scheme.Opens.toSpecΓ_naturality pr U).symm
    · simp [IsAffineOpen.isoSpec_hom]
    · simp [IsAffineOpen.isoSpec_hom]
    · simp
  have hPO := isPushout_appTop_of_isPullback hP2
  let gA : A₀ →+* Γ(X₀, U) :=
    ((Scheme.ΓSpecIso (.of A₀)).inv ≫ toBase₀.appTop ≫ X₀.presheaf.map (homOfLE le_top).op).hom
  let βB : ↥A →+* Γ(X, W) :=
    ((Scheme.ΓSpecIso (.of ↥A)).inv ≫ toBase.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom
  let α : Γ(X₀, U) →+* Γ(X, W) := (pr.app U).hom
  letI instAlg₀ : Algebra A₀ ↥A := ι.toAlgebra
  letI instAlg₁ : Algebra A₀ Γ(X₀, U) := gA.toAlgebra
  have hPO' : IsPushout (CommRingCat.ofHom (algebraMap A₀ ↥A)) (CommRingCat.ofHom (algebraMap A₀ Γ(X₀, U)))
      (CommRingCat.ofHom βB) (pr.app U) := by
    refine hPO.flip.of_iso (Scheme.ΓSpecIso (.of A₀)) (Scheme.ΓSpecIso (.of ↥A))
      (Scheme.ΓSpecIso Γ(X₀, U)) (Scheme.ΓSpecIso Γ(X, W)) ?_ ?_ ?_ ?_
    · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ι)
    · rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpec_appTop_ΓSpecIso_hom]
      change _ = (Scheme.ΓSpecIso (.of A₀)).hom ≫ (Scheme.ΓSpecIso (.of A₀)).inv ≫ toBase₀.appTop ≫
        X₀.presheaf.map (homOfLE le_top).op
      rw [Iso.hom_inv_id_assoc]
    · rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpec_appTop_ΓSpecIso_hom]
      change _ = (Scheme.ΓSpecIso (.of ↥A)).hom ≫ (Scheme.ΓSpecIso (.of ↥A)).inv ≫ toBase.appTop ≫
        X.presheaf.map (homOfLE le_top).op
      rw [Iso.hom_inv_id_assoc]
    · exact Scheme.ΓSpecIso_naturality (pr.app U)
  let Θ : CommRingCat.of (↥A ⊗[A₀] Γ(X₀, U)) ≅ Γ(X, W) :=
    (CommRingCat.isPushout_tensorProduct A₀ ↥A Γ(X₀, U)).isoIsPushout _ _ hPO'
  let Λ : ↥A ⊗[A₀] Γ(X₀, U) ≃+* Γ(X, W) := Θ.commRingCatIsoToRingEquiv
  have hΛl : ∀ t : ↥A, Λ (t ⊗ₜ 1) = βB t := fun t => by
    have := congrArg (fun ψ => ψ.hom t)
      ((CommRingCat.isPushout_tensorProduct A₀ ↥A Γ(X₀, U)).inl_isoIsPushout_hom _ _ hPO')
    exact this
  have hΛr : ∀ a : Γ(X₀, U), Λ (1 ⊗ₜ a) = α a := fun a => by
    have := congrArg (fun ψ => ψ.hom a)
      ((CommRingCat.isPushout_tensorProduct A₀ ↥A Γ(X₀, U)).inr_isoIsPushout_hom _ _ hPO')
    exact this
  have hΛ : ∀ (t : ↥A) (a : Γ(X₀, U)), Λ (t ⊗ₜ a) = βB t * α a := by
    intro t a
    rw [show t ⊗ₜ[A₀] a = (t ⊗ₜ[A₀] (1 : Γ(X₀, U))) * ((1 : ↥A) ⊗ₜ[A₀] a) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    rw [map_mul, hΛl, hΛr]
  have hsq : ∀ a : A₀, βB (ι a) = α (gA a) := fun a => by
    have := congrArg (fun ψ => ψ.hom a) hPO'.w
    exact this

  have hKX₀ : ∀ a : A₀, SemistableModel.baseToFunctionField toBase₀ a =
      algebraMap Γ(X₀, U) X₀.functionField (gA a) := by
    intro a
    change SemistableModel.baseToFunctionField toBase₀ a =
      X₀.germToFunctionField U
        ((X₀.presheaf.map (homOfLE le_top).op) (toBase₀.appTop ((Scheme.ΓSpecIso (.of A₀)).inv a)))
    dsimp only [SemistableModel.baseToFunctionField, Scheme.germToFunctionField, RingHom.coe_comp,
      Function.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
  have hKX : ∀ t : ↥A, SemistableModel.baseToFunctionField toBase t =
      algebraMap Γ(X, W) X.functionField (βB t) := by
    intro t
    change SemistableModel.baseToFunctionField toBase t =
      X.germToFunctionField W
        ((X.presheaf.map (homOfLE le_top).op) (toBase.appTop ((Scheme.ΓSpecIso (.of ↥A)).inv t)))
    dsimp only [SemistableModel.baseToFunctionField, Scheme.germToFunctionField, RingHom.coe_comp,
      Function.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
  have hφA : ∀ a : Γ(X₀, U), φ₀ (algebraMap Γ(X₀, U) X₀.functionField a) =
      algebraMap Γ(X, W) X.functionField (α a) :=
    fun a => hφgerm U _ a

  let bt : Γ(X, W) →+* F := φ.symm.toRingHom.comp (algebraMap Γ(X, W) X.functionField)
  have hbt : ∀ b, bt b = φ.symm (algebraMap Γ(X, W) X.functionField b) := fun b => rfl
  have hbtinj : Function.Injective bt :=
    φ.symm.injective.comp (IsFractionRing.injective Γ(X, W) X.functionField)
  have hbtβ : ∀ t : ↥A, bt (βB t) = algebraMap L F (t : L) := by
    intro t
    rw [hbt, ← hKX, ← hφ, RingEquiv.symm_apply_apply]
  have hbtα : ∀ r : Γ(X₀, U), bt (α r) = j₀ (algebraMap Γ(X₀, U) X₀.functionField r) := by
    intro r
    rw [hbt, ← hφA, RingEquiv.symm_apply_eq]
    exact (hj₀ _).symm

  have hαinj : Function.Injective α := by
    intro a b hab
    have h1 : j₀ (algebraMap Γ(X₀, U) X₀.functionField a) = j₀ (algebraMap Γ(X₀, U) X₀.functionField b) := by
      rw [← hbtα, ← hbtα, hab]
    exact IsFractionRing.injective Γ(X₀, U) X₀.functionField (j₀.injective h1)

  let yU : U := ⟨y₀, hy₀U⟩
  let ηW : W := ⟨η, hηW⟩
  letI algy := TopCat.Presheaf.algebra_section_stalk X₀.presheaf yU
  letI algη := TopCat.Presheaf.algebra_section_stalk X.presheaf ηW
  haveI hlocy := hU.isLocalization_stalk yU
  haveI hlocη := hW.isLocalization_stalk ηW
  haveI hsty := functionField_isScalarTower X₀ U yU
  haveI hstη := functionField_isScalarTower X W ηW
  set 𝔭₀ := hU.primeIdealOf yU with h𝔭₀def
  set 𝔮 := hW.primeIdealOf ηW with h𝔮def

  have hOtr' : ∀ r : Γ(X₀, U), r ∉ 𝔭₀.asIdeal ↔
      r ≠ 0 ∧ (algebraMap Γ(X₀, U) X₀.functionField r)⁻¹ ∈
        (algebraMap (X₀.presheaf.stalk (yU : X₀)) X₀.functionField).range :=
    fun r => notMem_iff_inv_mem_range (S := X₀.presheaf.stalk (yU : X₀)) 𝔭₀.asIdeal r

  have hbtO : ∀ b : Γ(X, W), bt b ∈ O := by
    intro b
    obtain ⟨z, rfl⟩ := Λ.surjective b
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact O.zero_mem
    | tmul t a =>
      rw [hΛ, map_mul, hbtβ, hbtα]
      refine O.mul_mem _ _ (hOA t) ((hOtr _).mpr ?_)
      exact ⟨algebraMap Γ(X₀, U) (X₀.presheaf.stalk (yU : X₀)) a,
        (IsScalarTower.algebraMap_apply Γ(X₀, U) (X₀.presheaf.stalk (yU : X₀)) X₀.functionField a).symm⟩
    | add x y hx hy =>
      rw [map_add, map_add]
      exact O.add_mem _ _ hx hy
  let btO : Γ(X, W) →+* ↥O := bt.codRestrict O.toSubring hbtO
  have hbtO_coe : ∀ b, ((btO b : ↥O) : F) = bt b := fun b => rfl

  let 𝔭 : Ideal Γ(X, W) := (maximalIdeal ↥O).comap btO
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime btO _
  have hmem𝔭 : ∀ b : Γ(X, W), b ∈ 𝔭 ↔ ¬ (bt b ≠ 0 ∧ (bt b)⁻¹ ∈ O) := by
    intro b
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (⟨bt b, hbtO b⟩ : ↥O) ↔ _
    rw [isUnit_iff_ne_zero_and_inv_mem O (hbtO b)]

  have hα𝔭 : ∀ r : Γ(X₀, U), α r ∈ 𝔭 ↔ r ∈ 𝔭₀.asIdeal := by
    intro r
    rw [hmem𝔭, hbtα, ← not_iff_not, not_not, hOtr']
    refine and_congr ?_ ?_
    · rw [map_ne_zero_iff j₀ j₀.injective,
        map_ne_zero_iff _ (IsFractionRing.injective Γ(X₀, U) X₀.functionField)]
    · rw [← map_inv₀, hOtr]

  by_cases hcase : ∀ t : ↥A, t ∈ maximalIdeal ↥A → ¬ IsUnit (⟨algebraMap L F (t : L), hOA t⟩ : ↥O)
  ·

    have hβ𝔭 : ∀ t : ↥A, βB t ∈ 𝔭 ↔ t ∈ maximalIdeal ↥A := by
      intro t
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      have e : btO (βB t) = ⟨algebraMap L F (t : L), hOA t⟩ := Subtype.ext (hbtβ t)
      rw [e]
      constructor
      · intro hnu
        by_contra ht
        apply hnu
        have htu : IsUnit t := by
          by_contra h; exact ht ((mem_maximalIdeal _).mpr h)
        obtain ⟨u, rfl⟩ := htu
        have ht0 : ((u : ↥A) : L) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
        refine (isUnit_iff_ne_zero_and_inv_mem O (hOA _)).mpr ⟨?_, ?_⟩
        · exact (map_ne_zero _).mpr ht0
        · rw [← map_inv₀, ← coe_unit_inv A u]
          exact hOA _
      · intro ht; exact hcase t ht

    let 𝔭pt : PrimeSpectrum Γ(X, W) := ⟨𝔭, h𝔭prime⟩
    let x : X := hW.fromSpec.base 𝔭pt
    have hxW : x ∈ W := (Set.ext_iff.mp hW.range_fromSpec x).mp ⟨𝔭pt, rfl⟩
    have h𝔭x : hW.primeIdealOf ⟨x, hxW⟩ = 𝔭pt := by
      apply hW.fromSpec.isOpenEmbedding.injective
      rw [hW.fromSpec_primeIdealOf ⟨x, hxW⟩]

    have hxsp : toBase.base x = closedPoint ↥A := by
      apply PrimeSpectrum.ext
      ext a
      rw [mem_base_asIdeal_iff]
      change _ ↔ a ∈ maximalIdeal ↥A
      rw [← hβ𝔭, show 𝔭 = (hW.primeIdealOf ⟨x, hxW⟩).asIdeal by rw [h𝔭x],
        mem_primeIdealOf_iff hW ⟨x, hxW⟩ (βB a)]
      change ¬ IsUnit (X.presheaf.germ ⊤ x trivial (toBase.appTop ((Scheme.ΓSpecIso (.of ↥A)).inv a))) ↔
        ¬ IsUnit (X.presheaf.germ W x hxW
          ((X.presheaf.map (homOfLE le_top).op) (toBase.appTop ((Scheme.ΓSpecIso (.of ↥A)).inv a))))
      rw [TopCat.Presheaf.germ_res_apply]

    have hprxU : pr.base x ∈ U := hxW
    have hprx : pr.base x = y₀ := by
      have h1 : hU.primeIdealOf ⟨pr.base x, hprxU⟩ = hU.primeIdealOf yU := by
        rw [← IsAffineOpen.comap_primeIdealOf_appLE U hU W hW le_rfl hxW, h𝔭x]
        apply PrimeSpectrum.ext
        ext r
        rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Scheme.Hom.appLE_eq_app]
        exact hα𝔭 r
      have h2 := congrArg (fun p => hU.fromSpec.base p) h1
      simp only [IsAffineOpen.fromSpec_primeIdealOf] at h2
      exact h2
    have hxη : x = η := hfib x hxsp hprx
    have h𝔭𝔮 : 𝔭 = 𝔮.asIdeal := by
      have : hW.primeIdealOf ⟨x, hxW⟩ = 𝔮 := by
        rw [h𝔮def]; congr 1; exact Subtype.ext hxη
      rw [← this, h𝔭x]

    obtain ⟨V, hVeq⟩ := hV

    have hstalk : ∀ z : X.presheaf.stalk η, ∃ (b s : Γ(X, W)), s ∉ 𝔭 ∧ bt s ≠ 0 ∧
        φ.symm (algebraMap (X.presheaf.stalk η) X.functionField z) = bt b * (bt s)⁻¹ := by
      intro z
      obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔮.asIdeal.primeCompl z
      have hs : (s : Γ(X, W)) ∉ 𝔭 := by rw [h𝔭𝔮]; exact s.2
      have hs0 : bt s ≠ 0 := by
        intro h0
        apply hs
        rw [show (s : Γ(X, W)) = 0 from hbtinj (by rw [h0, map_zero])]
        exact 𝔭.zero_mem
      refine ⟨b, s, hs, hs0, ?_⟩
      have h1 := IsLocalization.mk'_spec (X.presheaf.stalk (ηW : X)) b s
      have h2 := congrArg (fun w => φ.symm (algebraMap (X.presheaf.stalk (ηW : X)) X.functionField w)) h1
      simp only [map_mul] at h2
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
      change _ * bt s = bt b at h2
      rw [← h2, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    have hVle : V ≤ O := by
      intro v hv
      have hv' : v ∈ V.toSubring := hv
      rw [hVeq] at hv'
      obtain ⟨z, rfl⟩ := hv'
      obtain ⟨b, s, hs, hs0, e⟩ := hstalk z
      change φ.symm (algebraMap (X.presheaf.stalk η) X.functionField z) ∈ O
      rw [e]
      have hsu : bt s ≠ 0 ∧ (bt s)⁻¹ ∈ O := by
        have := (hmem𝔭 s).not.mp hs
        push Not at this
        exact this
      exact O.mul_mem _ _ (hbtO b) hsu.2
    have hVinv : ∀ (v : F) (hv : v ∈ V), IsUnit (⟨v, hVle hv⟩ : ↥O) → v⁻¹ ∈ V := by
      intro v hv hu
      have hv' : v ∈ V.toSubring := hv
      rw [hVeq] at hv'
      obtain ⟨z, hz⟩ := hv'
      obtain ⟨b, s, hs, hs0, e⟩ := hstalk z
      change φ.symm (algebraMap (X.presheaf.stalk η) X.functionField z) = v at hz
      rw [hz] at e

      have hb : b ∉ 𝔭 := by
        intro hb
        rw [isUnit_iff_ne_zero_and_inv_mem O (hVle hv)] at hu
        have hbm : btO b ∈ maximalIdeal ↥O := hb

        have hsu : (bt s)⁻¹ ∈ O := by
          have := (hmem𝔭 s).not.mp hs
          push Not at this
          exact this.2
        have hvm : (⟨v, hVle hv⟩ : ↥O) ∈ maximalIdeal ↥O := by
          have : (⟨v, hVle hv⟩ : ↥O) = btO b * ⟨(bt s)⁻¹, hsu⟩ := Subtype.ext e
          rw [this]
          exact Ideal.mul_mem_right _ _ hbm
        exact ((mem_maximalIdeal _).mp hvm) ((isUnit_iff_ne_zero_and_inv_mem O (hVle hv)).mpr hu)
      have hb0 : bt b ≠ 0 := by
        intro h0
        apply hb
        rw [show b = 0 from hbtinj (by rw [h0, map_zero])]
        exact 𝔭.zero_mem

      have hb' : b ∈ 𝔮.asIdeal.primeCompl := by
        show b ∉ 𝔮.asIdeal
        rw [← h𝔭𝔮]; exact hb
      have : v⁻¹ ∈ V.toSubring := by
        rw [hVeq]
        refine ⟨IsLocalization.mk' (X.presheaf.stalk (ηW : X)) s ⟨b, hb'⟩, ?_⟩
        change φ.symm (algebraMap (X.presheaf.stalk η) X.functionField _) = v⁻¹
        have h1 := IsLocalization.mk'_spec (X.presheaf.stalk (ηW : X)) s ⟨b, hb'⟩
        have h2 := congrArg (fun w => φ.symm (algebraMap (X.presheaf.stalk (ηW : X)) X.functionField w)) h1
        simp only [map_mul] at h2
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
        change _ * bt b = bt s at h2
        rw [e, mul_inv, inv_inv, eq_inv_mul_iff_mul_eq₀ hb0, mul_comm]
        exact h2
      exact this
    have hOV : O = V := eq_of_le_of_forall_inv_mem V O hVle hVinv
    rw [hOV, hVeq]
  ·

    exfalso
    push Not at hcase
    obtain ⟨t, htm, htu⟩ := hcase
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at htu
      apply htu.ne_zero
      apply Subtype.ext
      simp

    have hβ𝔭 : ∀ a : ↥A, βB a ∈ 𝔭 → a = 0 := by
      intro a ha
      by_contra ha0
      have ham : a ∈ maximalIdeal ↥A := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hau
        have : IsUnit (btO (βB a)) := hau.map (btO.comp βB)
        exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp ha)) this
      obtain ⟨n, c, hc⟩ := hrk t a htm ha0
      have htn : βB t ^ n ∈ 𝔭 := by
        rw [← map_pow, hc, map_mul]
        exact 𝔭.mul_mem_right _ ha
      have ht𝔭 : βB t ∈ 𝔭 := h𝔭prime.mem_of_pow_mem n htn
      have : ¬ IsUnit (btO (βB t)) := (mem_maximalIdeal _).mp (Ideal.mem_comap.mp ht𝔭)
      apply this
      have e : btO (βB t) = ⟨algebraMap L F (t : L), hOA t⟩ := Subtype.ext (hbtβ t)
      rw [e]; exact htu

    have hβ𝔮 : ∀ a : ↥A, βB a ∈ 𝔮.asIdeal ↔ a ∈ maximalIdeal ↥A := by
      intro a
      rw [mem_primeIdealOf_iff hW ηW (βB a)]
      have := mem_base_asIdeal_iff toBase η a
      rw [hη] at this
      change (a ∈ maximalIdeal ↥A ↔ _) at this
      rw [this]
      change ¬ IsUnit (X.presheaf.germ W η hηW
          ((X.presheaf.map (homOfLE le_top).op) (toBase.appTop ((Scheme.ΓSpecIso (.of ↥A)).inv a)))) ↔ _
      rw [TopCat.Presheaf.germ_res_apply]
    have hα𝔮 : ∀ r : Γ(X₀, U), α r ∈ 𝔮.asIdeal ↔ r ∈ 𝔭₀.asIdeal := by
      intro r
      have h := IsAffineOpen.comap_primeIdealOf_appLE U hU W hW le_rfl hηW

      have h' : PrimeSpectrum.comap α 𝔮 = 𝔭₀ := by
        rw [h𝔭₀def, h𝔮def]
        rw [Scheme.Hom.appLE_eq_app] at h
        exact h
      rw [← h', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]

    have hιunit : ∀ c : A₀, ι c ≠ 0 → IsUnit (ι c) := by
      intro c hc0
      by_contra hcu
      have hcm : ι c ∈ maximalIdeal ↥A := (mem_maximalIdeal _).mpr hcu
      have h1 : gA c ∈ 𝔭₀.asIdeal := by rw [← hα𝔮, ← hsq, hβ𝔮]; exact hcm
      have h2 : βB (ι c) ∈ 𝔭 := by rw [hsq, hα𝔭]; exact h1
      exact hc0 (hβ𝔭 _ h2)

    let k : Subfield L := Subfield.closure (Set.range fun c : A₀ => ((ι c : ↥A) : L))
    have hclos : Subring.closure (Set.range fun c : A₀ => ((ι c : ↥A) : L)) =
        ((A.subtype).comp ι).range := by
      apply le_antisymm
      · exact Subring.closure_le.mpr (by rintro _ ⟨c, rfl⟩; exact ⟨c, rfl⟩)
      · rintro _ ⟨c, rfl⟩; exact Subring.subset_closure ⟨c, rfl⟩
    have hkA : ∀ z ∈ k, z ∈ A := by
      intro z hz
      rw [Subfield.mem_closure_iff] at hz
      obtain ⟨y, hy, w, hw, rfl⟩ := hz
      rw [hclos] at hy hw
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨d, rfl⟩ := hw
      by_cases hd : ι d = 0
      · simp [hd]
      · obtain ⟨u, hu⟩ := hιunit d hd
        have e : ((A.subtype.comp ι) d)⁻¹ = ((↑(u⁻¹) : ↥A) : L) := by
          rw [coe_unit_inv A u, hu]; rfl
        rw [div_eq_mul_inv, e]
        exact A.mul_mem _ _ (ι c).2 (↑(u⁻¹) : ↥A).2

    have hιk : ∀ c : A₀, ((ι c : ↥A) : L) ∈ k := fun c => Subfield.subset_closure ⟨c, rfl⟩
    letI algk : Algebra ↥k ↥A := (k.subtype.codRestrict A.toSubring (fun z => hkA z z.2)).toAlgebra
    letI alg₀k : Algebra A₀ ↥k := (((A.subtype).comp ι).codRestrict k (fun c => hιk c)).toAlgebra
    haveI : IsScalarTower A₀ ↥k ↥A := IsScalarTower.of_algebraMap_eq (fun c => Subtype.ext rfl)
    haveI : IsScalarTower ↥k ↥A L := IsScalarTower.of_algebraMap_eq (fun c => rfl)

    obtain ⟨P, hP0, hPt⟩ := halgF (algebraMap L F (t : L))
    have hjinj : Function.Injective j₀.rangeRestrict := fun a b h =>
      j₀.injective (congrArg Subtype.val h)
    let e₁ : X₀.functionField ≃+* ↥(j₀.range) :=
      RingEquiv.ofBijective j₀.rangeRestrict ⟨hjinj, j₀.rangeRestrict_surjective⟩
    let P₀ : Polynomial X₀.functionField := P.map e₁.symm.toRingHom
    have hP₀0 : P₀ ≠ 0 := (Polynomial.map_ne_zero_iff e₁.symm.injective).mpr hP0
    have hP₀t : Polynomial.eval₂ j₀ (algebraMap L F (t : L)) P₀ = 0 := by
      have hcomp : (algebraMap ↥(j₀.range) F).comp e₁.toRingHom = j₀ := by
        ext g; rfl
      have hPmap : P = P₀.map e₁.toRingHom := by
        rw [Polynomial.map_map]
        have : e₁.toRingHom.comp e₁.symm.toRingHom = RingHom.id _ := by ext; simp
        rw [this, Polynomial.map_id]
      rw [Polynomial.aeval_def, hPmap, Polynomial.eval₂_map, hcomp] at hPt
      exact hPt
    let P₁ : Polynomial Γ(X₀, U) := IsLocalization.integerNormalization (nonZeroDivisors Γ(X₀, U)) P₀
    have hP₁0 : P₁ ≠ 0 := fun h => hP₀0 (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
    have hP₁t : Polynomial.eval₂ (j₀.comp (algebraMap Γ(X₀, U) X₀.functionField)) (algebraMap L F (t : L)) P₁ = 0 :=
      IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors Γ(X₀, U)) j₀ P₀ hP₀t

    have hcompα : j₀.comp (algebraMap Γ(X₀, U) X₀.functionField) = bt.comp α := by
      ext r; exact (hbtα r).symm
    have hevalB : Polynomial.eval₂ α (βB t) P₁ = 0 := by
      apply hbtinj
      rw [Polynomial.hom_eval₂, ← hcompα, hbtβ, hP₁t, map_zero]

    have hrel : ∑ i : Fin (P₁.natDegree + 1), (t ^ (i : ℕ)) ⊗ₜ[A₀] P₁.coeff i =
        (0 : ↥A ⊗[A₀] Γ(X₀, U)) := by
      apply Λ.injective
      rw [map_sum, map_zero, ← hevalB, Polynomial.eval₂_eq_sum_range, Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΛ, map_pow, mul_comm]

    have hlin : LinearIndependent ↥k (fun i : Fin (P₁.natDegree + 1) => t ^ (i : ℕ)) :=
      linearIndependent_pow_of_mem_maximalIdeal A k hkA t htm ht0 (P₁.natDegree + 1)
    have hzero := one_tmul_eq_zero_of_sum_pow_tmul (A₀ := A₀) (k := ↥k) (S := ↥A) (R := Γ(X₀, U))
      t (P₁.natDegree + 1) hlin (fun i => P₁.coeff i) hrel

    have hlead : P₁.coeff P₁.natDegree = 0 := by
      apply hαinj
      rw [map_zero, ← hΛr]
      have := hzero ⟨P₁.natDegree, by omega⟩
      rw [this, map_zero]
    exact hP₁0 (Polynomial.leadingCoeff_eq_zero.mp hlead)

end S_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback (solution)
