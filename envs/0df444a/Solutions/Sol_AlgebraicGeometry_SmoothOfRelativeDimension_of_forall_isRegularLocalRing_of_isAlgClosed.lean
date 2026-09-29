-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.of_forall_isRegularLocalRing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/01f10d09-b04b-58b8-b14e-9dc71f91a05c

import Mathlib
import Theorems.Thm_IsRegularLocalRing_spanFinrank_ker_add_finrank_cotangentSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_forall_isRegularLocalRing_of_isAlgClosed

universe u v

open IsLocalRing TensorProduct

noncomputable section

namespace RationalPointCotangent

theorem ker_eq_maximalIdeal {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    RingHom.ker π = maximalIdeal A :=
  eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π fun c => ⟨_, hπ c⟩)

theorem sub_algebraMap_mem {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) (a : A) :
    a - algebraMap k A (π a) ∈ maximalIdeal A := by
  rw [← ker_eq_maximalIdeal π hπ, RingHom.mem_ker, map_sub, hπ, sub_self]

theorem apply_eq_zero_of_mem {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) {a : A}
    (ha : a ∈ maximalIdeal A) : π a = 0 := by
  rwa [← ker_eq_maximalIdeal π hπ, RingHom.mem_ker] at ha

theorem algebraMap_residueField_surjective {k : Type u} [Field k] {A : Type v} [CommRing A]
    [IsLocalRing A] [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    Function.Surjective (algebraMap k (ResidueField A)) := by
  intro z
  obtain ⟨a, rfl⟩ := residue_surjective z
  refine ⟨π a, ?_⟩
  rw [IsScalarTower.algebraMap_apply k A (ResidueField A), ResidueField.algebraMap_eq, eq_comm,
    ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact sub_algebraMap_mem π hπ a

def deriv {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    Derivation k A (CotangentSpace A) where
  toFun a := (maximalIdeal A).toCotangent ⟨a - algebraMap k A (π a), sub_algebraMap_mem π hπ a⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' c a := by
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    ext
    rw [Submodule.coe_smul_of_tower]
    simp only [Algebra.smul_def, map_mul, hπ]
    ring
  map_one_eq_zero' := by
    change (maximalIdeal A).toCotangent _ = 0
    rw [Ideal.toCotangent_eq_zero]
    simp
  leibniz' a b := by
    change (maximalIdeal A).toCotangent _ =
      a • (maximalIdeal A).toCotangent _ + b • (maximalIdeal A).toCotangent _
    rw [← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq]
    have h : ((⟨a * b - algebraMap k A (π (a * b)), sub_algebraMap_mem π hπ (a * b)⟩ :
        maximalIdeal A) : A) - ((a • (⟨b - algebraMap k A (π b), sub_algebraMap_mem π hπ b⟩ :
        maximalIdeal A) + b • (⟨a - algebraMap k A (π a), sub_algebraMap_mem π hπ a⟩ :
        maximalIdeal A) : maximalIdeal A) : A) =
        -((a - algebraMap k A (π a)) * (b - algebraMap k A (π b))) := by
      simp only [map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring
    rw [h, pow_two]
    exact neg_mem (Ideal.mul_mem_mul (sub_algebraMap_mem π hπ a) (sub_algebraMap_mem π hπ b))

theorem deriv_apply {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) (a : A) :
    deriv π hπ a =
      (maximalIdeal A).toCotangent ⟨a - algebraMap k A (π a), sub_algebraMap_mem π hπ a⟩ := rfl

theorem deriv_apply_of_mem {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) {a : A}
    (ha : a ∈ maximalIdeal A) : deriv π hπ a = (maximalIdeal A).toCotangent ⟨a, ha⟩ := by
  rw [deriv_apply]
  congr 1
  ext
  simp [apply_eq_zero_of_mem π hπ ha]

def toCotangentSpace {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    ResidueField A ⊗[A] Ω[A⁄k] →ₗ[ResidueField A] CotangentSpace A :=
  (deriv π hπ).liftKaehlerDifferential.liftBaseChange (ResidueField A)

theorem toCotangentSpace_tmul_D {k : Type u} [Field k] {A : Type v} [CommRing A]
    [IsLocalRing A] [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c)
    (c : ResidueField A) (a : A) :
    toCotangentSpace π hπ (c ⊗ₜ KaehlerDifferential.D k A a) = c • deriv π hπ a := by
  rw [toCotangentSpace, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]

theorem kerCotangentToTensor_surjective {k : Type u} [Field k] {A : Type v} [CommRing A]
    [IsLocalRing A] [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    Function.Surjective (KaehlerDifferential.kerCotangentToTensor k A (ResidueField A)) := by
  have hsub : Subsingleton Ω[ResidueField A⁄k] :=
    KaehlerDifferential.subsingleton_of_surjective k (ResidueField A)
      (algebraMap_residueField_surjective π hπ)
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_kerCotangentToTensor k A
    (ResidueField A) residue_surjective, Submodule.restrictScalars_eq_top_iff,
    LinearMap.ker_eq_top]
  exact Subsingleton.elim _ _

theorem toCotangentSpace_kerCotangentToTensor {k : Type u} [Field k] {A : Type v} [CommRing A]
    [IsLocalRing A] [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c)
    (y : RingHom.ker (algebraMap A (ResidueField A))) :
    toCotangentSpace π hπ (KaehlerDifferential.kerCotangentToTensor k A (ResidueField A)
      ((RingHom.ker (algebraMap A (ResidueField A))).toCotangent y)) =
      (maximalIdeal A).toCotangent ⟨y.1, by simpa [ker_residue] using y.2⟩ := by
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, toCotangentSpace_tmul_D, one_smul,
    deriv_apply_of_mem]

theorem toCotangentSpace_bijective {k : Type u} [Field k] {A : Type v} [CommRing A]
    [IsLocalRing A] [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    Function.Bijective (toCotangentSpace π hπ) := by
  constructor
  · intro w₁ w₂ h
    rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero]
    obtain ⟨v, hv⟩ := kerCotangentToTensor_surjective π hπ (w₁ - w₂)
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ v
    rw [← hv, toCotangentSpace_kerCotangentToTensor, Ideal.toCotangent_eq_zero] at h
    rw [← hv, (Ideal.toCotangent_eq_zero _ _).mpr, map_zero]
    simpa only [ResidueField.algebraMap_eq, ker_residue] using h
  · intro v
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
    refine ⟨KaehlerDifferential.kerCotangentToTensor k A (ResidueField A)
      ((RingHom.ker (algebraMap A (ResidueField A))).toCotangent ⟨x.1, ?_⟩), ?_⟩
    · simpa only [ResidueField.algebraMap_eq, ker_residue] using x.2
    · rw [toCotangentSpace_kerCotangentToTensor]

def cotangentEquiv {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    ResidueField A ⊗[A] Ω[A⁄k] ≃ₗ[ResidueField A] CotangentSpace A :=
  LinearEquiv.ofBijective (toCotangentSpace π hπ) (toCotangentSpace_bijective π hπ)

theorem finrank_tensor_kaehlerDifferential {k : Type u} [Field k] {A : Type v} [CommRing A]
    [IsLocalRing A] [Algebra k A] (π : A →+* k) (hπ : ∀ c, π (algebraMap k A c) = c) :
    Module.finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) =
      Module.finrank (ResidueField A) (CotangentSpace A) :=
  (cotangentEquiv π hπ).finrank_eq

end RationalPointCotangent

namespace JacobianCriterionAtClosedPoints

theorem finrank_tensor_le_spanFinrank {P : Type u} [CommRing P] {S : Type u} [CommRing S]
    [IsLocalRing S] [Algebra P S] {M : Type v} [AddCommGroup M] [Module P M] [Module S M]
    [IsScalarTower P S M] (I : Ideal P) (hI : I.FG) (mk : I →ₗ[P] M)
    (hmk : Function.Surjective mk) :
    Module.finrank (ResidueField S) (ResidueField S ⊗[S] M) ≤ I.spanFinrank := by
  classical
  obtain ⟨G, hGcard, hGspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hI
  have hGI : ∀ g ∈ G, g ∈ I := fun g hg => hGspan ▸ Submodule.subset_span hg
  let v : G → ResidueField S ⊗[S] M := fun g => (1 : ResidueField S) ⊗ₜ[S] mk ⟨g.1, hGI g.1 g.2⟩
  have hmem : ∀ (x : P) (hx : x ∈ I),
      (1 : ResidueField S) ⊗ₜ[S] mk ⟨x, hx⟩ ∈ Submodule.span (ResidueField S) (Set.range v) := by
    intro x hx
    have hx' : x ∈ Submodule.span P (G : Set P) := hGspan ▸ hx
    refine Submodule.span_induction (p := fun x _ => ∀ hxI : x ∈ I,
      (1 : ResidueField S) ⊗ₜ[S] mk ⟨x, hxI⟩ ∈ Submodule.span (ResidueField S) (Set.range v))
      ?_ ?_ ?_ ?_ hx' hx
    · intro g hg hgI
      exact Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩
    · intro h0
      rw [show (⟨0, h0⟩ : I) = 0 from rfl, map_zero, TensorProduct.tmul_zero]
      exact zero_mem _
    · intro x y hxs hys hx hy hxyI
      have hxI : x ∈ I := hGspan ▸ hxs
      have hyI : y ∈ I := hGspan ▸ hys
      rw [show (⟨x + y, hxyI⟩ : I) = ⟨x, hxI⟩ + ⟨y, hyI⟩ from rfl, map_add,
        TensorProduct.tmul_add]
      exact add_mem (hx hxI) (hy hyI)
    · intro a x hxs hx haxI
      have hxI : x ∈ I := hGspan ▸ hxs
      rw [show (⟨a • x, haxI⟩ : I) = a • ⟨x, hxI⟩ from rfl, map_smul, ← algebraMap_smul S a,
        ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul',
        ← algebraMap_smul (ResidueField S) (algebraMap P S a)]
      exact Submodule.smul_mem _ _ (hx hxI)
  have hspan : Submodule.span (ResidueField S) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    induction w using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul c m =>
      obtain ⟨⟨x, hxI⟩, rfl⟩ := hmk m
      have : c ⊗ₜ[S] mk ⟨x, hxI⟩ = c • ((1 : ResidueField S) ⊗ₜ[S] mk ⟨x, hxI⟩) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ c (hmem x hxI)
  have h := finrank_range_le_card (R := ResidueField S) v
  unfold Set.finrank at h
  rw [hspan, finrank_top, Fintype.card_coe, hGcard] at h
  exact h

theorem formallySmooth_of_isRegularLocalRing {k : Type u} [Field k] {P : Type u} [CommRing P]
    [IsLocalRing P] [IsNoetherianRing P] [Algebra k P] [Algebra.FormallySmooth k P]
    [Module.Free P Ω[P⁄k]] [Module.Finite P Ω[P⁄k]] {S : Type u} [CommRing S]
    [IsRegularLocalRing S] [Algebra k S] [Algebra P S] [IsScalarTower k P S]
    (hPS : Function.Surjective (algebraMap P S)) (π : S →+* k)
    (hπ : ∀ c, π (algebraMap k S c) = c) : Algebra.FormallySmooth k S := by
  classical
  let E : Algebra.Extension.{u} k S :=
    { Ring := P, σ := Function.surjInv hPS, algebraMap_σ := Function.surjInv_eq hPS }
  have hker : E.ker.FG := IsNoetherian.noetherian _
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField E hker]
  haveI : Module.Finite S E.Cotangent := Algebra.Extension.Cotangent.finite hker

  set κ := ResidueField S with hκ
  let f : κ ⊗[S] E.Cotangent →ₗ[κ] κ ⊗[S] E.CotangentSpace := E.cotangentComplex.baseChange κ
  let g : κ ⊗[S] E.CotangentSpace →ₗ[κ] κ ⊗[S] Ω[S⁄k] := E.toKaehler.baseChange κ
  have hfg : Function.Exact f g :=
    lTensor_exact κ E.exact_cotangentComplex_toKaehler E.toKaehler_surjective
  have hg : Function.Surjective g := LinearMap.lTensor_surjective κ E.toKaehler_surjective
  change Function.Injective f

  have h₁ : Module.finrank κ (κ ⊗[S] E.Cotangent) ≤ (RingHom.ker (algebraMap P S)).spanFinrank :=
    finrank_tensor_le_spanFinrank E.ker hker Algebra.Extension.Cotangent.mk
      Algebra.Extension.Cotangent.mk_surjective

  let πP : P →+* k := π.comp (algebraMap P S)
  have hπP : ∀ c, πP (algebraMap k P c) = c := fun c => by
    simp only [πP, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hπ]

  have h₂ : Module.finrank κ (κ ⊗[S] E.CotangentSpace) =
      Module.finrank (ResidueField P) (CotangentSpace P) := by
    have e₁ : Module.finrank κ (κ ⊗[S] E.CotangentSpace) = Module.finrank P Ω[P⁄k] := by
      change Module.finrank κ (κ ⊗[S] (S ⊗[P] Ω[P⁄k])) = _
      rw [(AlgebraTensorModule.cancelBaseChange P S κ κ Ω[P⁄k]).finrank_eq,
        Module.finrank_baseChange]
    have e₂ : Module.finrank (ResidueField P) (ResidueField P ⊗[P] Ω[P⁄k]) =
        Module.finrank P Ω[P⁄k] := Module.finrank_baseChange
    rw [e₁, ← e₂, RationalPointCotangent.finrank_tensor_kaehlerDifferential πP hπP]

  have h₃ : Module.finrank κ (κ ⊗[S] Ω[S⁄k]) = Module.finrank κ (CotangentSpace S) :=
    RationalPointCotangent.finrank_tensor_kaehlerDifferential π hπ

  have h₄ : (RingHom.ker (algebraMap P S)).spanFinrank + Module.finrank κ (CotangentSpace S) =
      Module.finrank (ResidueField P) (CotangentSpace P) :=
    IsRegularLocalRing.spanFinrank_ker_add_finrank_cotangentSpace (algebraMap P S) hPS

  have h₅ := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at h₅
  have h₆ := LinearMap.finrank_range_add_finrank_ker f
  rw [← LinearMap.exact_iff.mp hfg] at h₆
  have h₇ : Module.finrank κ (LinearMap.ker f) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp h₇

end JacobianCriterionAtClosedPoints

namespace JacobianCriterionAtClosedPoints

theorem exists_ringHom_localization_atPrime {k : Type u} [Field k] [IsAlgClosed k] {R : Type u}
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    ∃ π : Localization.AtPrime m →+* k, ∀ c, π (algebraMap k (Localization.AtPrime m) c) = c := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  have hbij : Function.Bijective (algebraMap k (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : (R ⧸ m) ≃+* k := (RingEquiv.ofBijective (algebraMap k (R ⧸ m)) hbij).symm
  let πR : R →+* k := e.toRingHom.comp (Ideal.Quotient.mk m)
  have hunit : ∀ y : m.primeCompl, IsUnit (πR y) := by
    intro y
    rw [isUnit_iff_ne_zero]
    change e (Ideal.Quotient.mk m y) ≠ 0
    rw [map_ne_zero_iff _ e.injective, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact y.2
  refine ⟨IsLocalization.lift (M := m.primeCompl) hunit, fun c => ?_⟩
  rw [IsScalarTower.algebraMap_apply k R (Localization.AtPrime m), IsLocalization.lift_eq]
  change e (Ideal.Quotient.mk m (algebraMap k R c)) = c
  rw [Ideal.Quotient.mk_algebraMap]
  exact (RingEquiv.ofBijective (algebraMap k (R ⧸ m)) hbij).symm_apply_apply c

theorem isSmoothAt_of_isRegularLocalRing {k : Type u} [Field k] [IsAlgClosed k] {R : Type u}
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal]
    [IsRegularLocalRing (Localization.AtPrime m)] : Algebra.IsSmoothAt k m := by
  classical
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k R›
  obtain ⟨π, hπ⟩ := exists_ringHom_localization_atPrime (k := k) m

  let A := MvPolynomial (Fin N) k
  let g : A →+* R := f.toRingHom
  have hg : Function.Surjective g := hf
  let S := Localization.AtPrime m
  let Q : Ideal A := m.comap g
  let P := Localization.AtPrime Q
  let toS : P →+* S := Localization.localRingHom Q m g rfl
  letI : Algebra P S := toS.toAlgebra
  have htoS : ∀ c, toS (algebraMap k P c) = algebraMap k S c := fun c => by
    rw [IsScalarTower.algebraMap_apply k A P, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply k R S]
    exact congrArg (algebraMap R S) (f.commutes c)
  haveI : IsScalarTower k P S := IsScalarTower.of_algebraMap_eq fun c => (htoS c).symm
  have hsurj : Function.Surjective (algebraMap P S) := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl z
    obtain ⟨a, rfl⟩ := hg r
    obtain ⟨b, hb⟩ := hg s
    have hbQ : b ∈ Q.primeCompl := by
      change g b ∉ m
      rw [hb]
      exact s.2
    refine ⟨IsLocalization.mk' P a ⟨b, hbQ⟩, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hb

  haveI : Algebra.FormallyEtale A P := Algebra.FormallyEtale.of_isLocalization (Rₘ := P) Q.primeCompl
  haveI : Module.Free A Ω[A⁄k] := Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis k (Fin N))
  haveI : Module.Finite A Ω[A⁄k] :=
    Module.Finite.of_basis (KaehlerDifferential.mvPolynomialBasis k (Fin N))
  let eΩ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A P
  haveI : Module.Free P Ω[P⁄k] := Module.Free.of_equiv eΩ
  haveI : Module.Finite P Ω[P⁄k] := Module.Finite.equiv eΩ
  exact JacobianCriterionAtClosedPoints.formallySmooth_of_isRegularLocalRing hsurj π hπ

theorem exists_isStandardSmoothOfRelativeDimension_away {k : Type u} [Field k] [IsAlgClosed k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (n : ℕ) (m : Ideal R)
    [m.IsMaximal] [IsRegularLocalRing (Localization.AtPrime m)]
    (hdim : ringKrullDim (Localization.AtPrime m) = (n : ℕ∞)) :
    ∃ t ∉ m, Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away t) := by
  classical
  haveI : Algebra.IsSmoothAt k m := isSmoothAt_of_isRegularLocalRing m
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨t, ht, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth k m
  refine ⟨t, ht, ?_⟩
  haveI : Algebra.IsStandardSmooth k (Localization.Away t) := hstd
  obtain ⟨ι, σ, _, hι, ⟨Pr⟩⟩ := hstd.out
  haveI := hι

  have hu : IsUnit (algebraMap R (ResidueField (Localization.AtPrime m)) t) := by
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime m)
      (ResidueField (Localization.AtPrime m))]
    exact (IsLocalization.map_units (Localization.AtPrime m) (⟨t, ht⟩ : m.primeCompl)).map _
  letI : Algebra (Localization.Away t) (ResidueField (Localization.AtPrime m)) :=
    (IsLocalization.Away.lift t hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away t) (ResidueField (Localization.AtPrime m)) :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq t hu r).symm
  haveI : Nontrivial (Localization.Away t) :=
    (algebraMap (Localization.Away t) (ResidueField (Localization.AtPrime m))).domain_nontrivial

  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension k (Localization.Away t) :=
    Pr.isStandardSmoothOfRelativeDimension rfl
  have hrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := k) (S := Localization.Away t) Pr.dimension
  haveI : Module.Finite (Localization.Away t) Ω[Localization.Away t⁄k] :=
    Module.finite_of_rank_eq_nat hrank
  have hfin : Module.finrank (Localization.Away t) Ω[Localization.Away t⁄k] = Pr.dimension :=
    Module.finrank_eq_of_rank_eq hrank

  obtain ⟨π, hπ⟩ := exists_ringHom_localization_atPrime (k := k) m
  have hΘ : Module.finrank (ResidueField (Localization.AtPrime m))
      (ResidueField (Localization.AtPrime m) ⊗[Localization.AtPrime m]
        Ω[Localization.AtPrime m⁄k]) = Module.finrank (ResidueField (Localization.AtPrime m))
      (CotangentSpace (Localization.AtPrime m)) :=
    RationalPointCotangent.finrank_tensor_kaehlerDifferential π hπ
  have hreg : Module.finrank (ResidueField (Localization.AtPrime m))
      (CotangentSpace (Localization.AtPrime m)) = n := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := Localization.AtPrime m)).mp ‹_›
    rw [hdim] at h
    exact_mod_cast h
  haveI : Algebra.FormallyEtale R (Localization.AtPrime m) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.AtPrime m) m.primeCompl
  haveI : Algebra.FormallyEtale R (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.Away t) (Submonoid.powers t)
  let eS := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R (Localization.AtPrime m)
  let eT := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R (Localization.Away t)
  have e₁ : Module.finrank (ResidueField (Localization.AtPrime m))
      (ResidueField (Localization.AtPrime m) ⊗[Localization.Away t] Ω[Localization.Away t⁄k]) =
      Module.finrank (ResidueField (Localization.AtPrime m))
        (ResidueField (Localization.AtPrime m) ⊗[R] Ω[R⁄k]) :=
    ((eT.symm.baseChange (Localization.Away t) (ResidueField (Localization.AtPrime m)) _ _).trans
      (AlgebraTensorModule.cancelBaseChange R (Localization.Away t)
        (ResidueField (Localization.AtPrime m)) (ResidueField (Localization.AtPrime m))
        Ω[R⁄k])).finrank_eq
  have e₂ : Module.finrank (ResidueField (Localization.AtPrime m))
      (ResidueField (Localization.AtPrime m) ⊗[Localization.AtPrime m]
        Ω[Localization.AtPrime m⁄k]) =
      Module.finrank (ResidueField (Localization.AtPrime m))
        (ResidueField (Localization.AtPrime m) ⊗[R] Ω[R⁄k]) :=
    ((eS.symm.baseChange (Localization.AtPrime m) (ResidueField (Localization.AtPrime m))
      _ _).trans (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime m)
        (ResidueField (Localization.AtPrime m)) (ResidueField (Localization.AtPrime m))
        Ω[R⁄k])).finrank_eq
  have e₃ : Module.finrank (ResidueField (Localization.AtPrime m))
      (ResidueField (Localization.AtPrime m) ⊗[Localization.Away t] Ω[Localization.Away t⁄k]) =
      Module.finrank (Localization.Away t) Ω[Localization.Away t⁄k] :=
    Module.finrank_baseChange
  exact Pr.isStandardSmoothOfRelativeDimension (by omega)

end JacobianCriterionAtClosedPoints

open AlgebraicGeometry JacobianCriterionAtClosedPoints in

theorem solution (k : Type u) [Field k] [IsAlgClosed k]
    (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (n : ℕ)
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p) ∧
        ringKrullDim (Localization.AtPrime p) = (n : ℕ∞)) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k R)) : Spec _ ⟶ Spec (CommRingCat.of k)) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n), CommRingCat.hom_ofHom]
  have key : ∀ (p : Ideal R) (_ : p.IsMaximal),
      ∃ t ∉ p, Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away t) := by
    intro p hp
    haveI := (hreg p hp).1
    exact exists_isStandardSmoothOfRelativeDimension_away n p (hreg p hp).2
  choose t ht hst using key
  refine ⟨Set.range fun p : MaximalSpectrum R => t p.asIdeal p.isMaximal, ?_, ?_⟩
  · by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    exact ht M hM (hle (Ideal.subset_span ⟨⟨M, hM⟩, rfl⟩))
  · rintro _ ⟨p, rfl⟩
    rw [← IsScalarTower.algebraMap_eq k R (Localization.Away _),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact hst p.asIdeal p.isMaximal

end

end S_AlgebraicGeometry_SmoothOfRelativeDimension_of_forall_isRegularLocalRing_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_forall_isRegularLocalRing_of_isAlgClosed (solution)
