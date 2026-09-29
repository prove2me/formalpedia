-- Prove2me | solution 1 for Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/59e93ac8-6abf-5f13-ae79-1748889a60dd

import Mathlib
import Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

namespace P2mJacobi

theorem finrank_tensor_kaehler_eq_finrank_range_add
    {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra P S] [Algebra R S] [IsScalarTower R P S]
    (hsurj : Function.Surjective (algebraMap P S)) [Module.Finite P Ω[P⁄R]]
    (k : Type u) [Field k] [Algebra S k] [Algebra P k] [IsScalarTower P S k] :
    Module.finrank k (k ⊗[P] Ω[P⁄R]) =
      Module.finrank k (LinearMap.range (cotangentComplexBaseChange R S P k)) +
        Module.finrank k (k ⊗[S] Ω[S⁄R]) := by
  let P' : Algebra.Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq hsurj }
  have hex : Function.Exact (P'.cotangentComplex.baseChange k) (P'.toKaehler.baseChange k) := by
    have h := lTensor_exact k P'.exact_cotangentComplex_toKaehler P'.toKaehler_surjective
    intro y
    have h1 : (P'.toKaehler.baseChange k) y = (P'.toKaehler.lTensor k) y :=
      congrFun (LinearMap.baseChange_eq_ltensor _) y
    rw [h1, h y, Set.mem_range, Set.mem_range]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, (congrFun (LinearMap.baseChange_eq_ltensor _) z).symm.trans hz⟩,
      fun ⟨z, hz⟩ => ⟨z, (congrFun (LinearMap.baseChange_eq_ltensor _) z).trans hz⟩⟩
  have hsurj' : Function.Surjective (P'.toKaehler.baseChange k) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective k P'.toKaehler_surjective
  have hrn := (P'.toKaehler.baseChange k).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj', finrank_top, LinearMap.exact_iff.mp hex] at hrn
  have e0 : k ⊗[S] P'.CotangentSpace ≃ₗ[k] k ⊗[P] Ω[P⁄R] :=
    AlgebraTensorModule.cancelBaseChange P S k k Ω[P⁄R]
  rw [← e0.finrank_eq, ← hrn, add_comm]
  congr 1
  rw [P'.cotangentComplexBaseChange_eq_lTensor_cotangentComplex k, LinearMap.range_comp,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

section LocSurj

variable {B A : Type u} [CommRing B] [CommRing A] (g : B →+* A) (hg : Function.Surjective g)
  (p : Ideal A) [p.IsPrime] (I : Ideal B) [I.IsPrime] (hI : I = Ideal.comap g p)

include hg in
theorem map_primeCompl_comap_eq :
    Submonoid.map g (Ideal.comap g p).primeCompl = p.primeCompl := by
  ext a
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact hb
  · intro ha; obtain ⟨b, rfl⟩ := hg a; exact ⟨b, ha, rfl⟩

include hg in

theorem localRingHom_surjective : Function.Surjective (Localization.localRingHom I p g hI) := by
  subst hI
  haveI : IsLocalization (Submonoid.map g (Ideal.comap g p).primeCompl) (Localization.AtPrime p) := by
    rw [map_primeCompl_comap_eq g hg p]; infer_instance
  exact IsLocalization.map_surjective_of_surjective (Ideal.comap g p).primeCompl
    (Localization.AtPrime (Ideal.comap g p)) (Localization.AtPrime p) hg

include hg in

theorem ker_localRingHom :
    RingHom.ker (Localization.localRingHom I p g hI) =
      (RingHom.ker g).map (algebraMap B (Localization.AtPrime I)) := by
  subst hI
  exact IsLocalization.ker_map (Localization.AtPrime p) g (map_primeCompl_comap_eq g hg p)

end LocSurj

section Tower

variable {R B A : Type u} [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
  (g : B →ₐ[R] A) (p : Ideal A) [p.IsPrime] (I : Ideal B) [I.IsPrime]
  (hI : I = Ideal.comap g.toRingHom p)

theorem localRingHom_algebraMap (r : R) :
    Localization.localRingHom I p g.toRingHom hI (algebraMap R _ r) =
      algebraMap R (Localization.AtPrime p) r := by
  rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime I),
    Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R A (Localization.AtPrime p)]
  simp

end Tower

theorem linearIndependent_one_tmul_of_map
    {P : Type u} [CommRing P] {k₁ k₂ : Type u} [Field k₁] [Field k₂] [Algebra P k₁] [Algebra P k₂]
    (σ : k₁ →+* k₂) (hσ : σ.comp (algebraMap P k₁) = algebraMap P k₂)
    {M : Type u} [AddCommGroup M] [Module P M] {ι : Type*} (m : ι → M)
    (h : LinearIndependent k₂ (fun i => (1 : k₂) ⊗ₜ[P] m i)) :
    LinearIndependent k₁ (fun i => (1 : k₁) ⊗ₜ[P] m i) := by
  classical
  let σₗ : k₁ →ₗ[P] k₂ :=
    { toFun := σ, map_add' := σ.map_add, map_smul' := fun p c => by
        simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
        rw [← hσ]; rfl }
  let θ : k₁ ⊗[P] M →ₗ[P] k₂ ⊗[P] M := TensorProduct.map σₗ LinearMap.id
  have hθ : ∀ (c : k₁) (x : M), θ (c • ((1 : k₁) ⊗ₜ[P] x)) = σ c • ((1 : k₂) ⊗ₜ[P] x) := by
    intro c x
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_eq_mul,
      mul_one]
    rfl
  rw [linearIndependent_iff'] at h ⊢
  intro s c hc i hi
  have := congrArg θ hc
  rw [map_sum, map_zero] at this
  simp only [hθ] at this
  have := h s (fun j => σ (c j)) this i hi
  exact (map_eq_zero σ).mp this

theorem injective_of_linearIndependent_of_span
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) {ι : Type*} [Fintype ι] (u : ι → V)
    (hu : ∀ v : V, ∃ c : ι → k, ∑ i, c i • u i = v)
    (hT : LinearIndependent k (fun i => T (u i))) : Function.Injective T := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨c, rfl⟩ := hu v
  rw [LinearMap.mem_ker, map_sum] at hv
  simp only [map_smul] at hv
  have hc := Fintype.linearIndependent_iff.mp hT c hv
  simp [hc]

theorem exists_sum_smul_one_tmul
    {P : Type u} [CommRing P] (k : Type u) [CommRing k] [Algebra P k]
    {ι : Type*} [Fintype ι] (w : ι → P) (K : Ideal P) (hK : K = Ideal.span (Set.range w))
    (v : k ⊗[P] K) :
    ∃ c : ι → k, ∑ i, c i • ((1 : k) ⊗ₜ[P] (⟨w i, hK ▸ Ideal.subset_span ⟨i, rfl⟩⟩ : K)) = v := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c z =>
    obtain ⟨z, hz⟩ := z
    have hz' : z ∈ Submodule.span P (Set.range w) := by rw [hK] at hz; exact hz
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun P).mp hz'
    refine ⟨fun i => c * algebraMap P k (d i), ?_⟩
    have : (⟨z, hz⟩ : K) = ∑ i, d i • (⟨w i, hK ▸ Ideal.subset_span ⟨i, rfl⟩⟩ : K) := by
      apply Subtype.ext
      simp [← hd]
    rw [this, tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_tmul', smul_eq_mul, mul_one, ← smul_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, by simp [add_smul, Finset.sum_add_distrib]⟩

theorem eq_bot_of_finrank_tensor_eq_zero
    {T : Type u} [CommRing T] [IsLocalRing T] (K : Ideal T) (hK : K.FG)
    (k : Type u) [Field k] [Algebra T k]
    [Algebra (IsLocalRing.ResidueField T) k] [IsScalarTower T (IsLocalRing.ResidueField T) k]
    (h : Module.finrank k (k ⊗[T] K) = 0) : K = ⊥ := by
  haveI : Module.Finite T K := Module.Finite.iff_fg.mpr hK
  have e : k ⊗[T] K ≃ₗ[k] k ⊗[IsLocalRing.ResidueField T] (IsLocalRing.ResidueField T ⊗[T] K) :=
    (AlgebraTensorModule.cancelBaseChange T (IsLocalRing.ResidueField T) k k K).symm
  have h0 : Module.finrank (IsLocalRing.ResidueField T) (IsLocalRing.ResidueField T ⊗[T] K) = 0 := by
    rw [← Module.finrank_baseChange (R := k), ← e.finrank_eq, h]
  have : Subsingleton (IsLocalRing.ResidueField T ⊗[T] K) := Module.finrank_zero_iff.mp h0
  rw [IsLocalRing.subsingleton_tensorProduct] at this
  exact Submodule.eq_bot_iff _ |>.mpr fun x hx =>
    congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : K) 0)

theorem finrank_residueField_tensor_kaehler_localization
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (p : Ideal A) [p.IsPrime] :
    Module.finrank p.ResidueField
        (p.ResidueField ⊗[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R]) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) := by
  haveI : Algebra.FormallyEtale A (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization (M := p.primeCompl)
  have eΩ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A (Localization.AtPrime p)
  exact ((eΩ.symm.baseChange (Localization.AtPrime p) p.ResidueField _ _) ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime p) p.ResidueField p.ResidueField
      Ω[A⁄R])).finrank_eq

theorem isDomain_localization_of_isSmoothAt
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (P : Ideal C) [P.IsPrime] [Algebra.IsSmoothAt R P] :
    IsDomain (Localization.AtPrime P) := by
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R P
  have hdisj : Disjoint (↑(Submonoid.powers f) : Set C) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hf (‹P.IsPrime›.mem_of_pow_mem n hn)
  haveI hP' : (P.map (algebraMap C (Localization.Away f))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ P ‹_› hdisj
  have hcomap : (P.map (algebraMap C (Localization.Away f))).comap
      (algebraMap C (Localization.Away f)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) _ ‹_› hdisj
  haveI : IsDomain (Localization.AtPrime (P.map (algebraMap C (Localization.Away f)))) :=
    (Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime R (Localization.Away f)
      (P.map (algebraMap C (Localization.Away f))) _).1
  have hloc : IsLocalization.AtPrime (Localization.AtPrime (P.map (algebraMap C (Localization.Away f))))
      ((P.map (algebraMap C (Localization.Away f))).comap (algebraMap C (Localization.Away f))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f) _ _
  have hS : ((P.map (algebraMap C (Localization.Away f))).comap
      (algebraMap C (Localization.Away f))).primeCompl = P.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  change IsLocalization _ _ at hloc
  rw [hS] at hloc
  exact (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (Localization.AtPrime (P.map (algebraMap C (Localization.Away f))))).toMulEquiv.isDomain

section Main

variable {R B A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing B] [Nontrivial B] [Algebra R B] [IsNoetherianRing B] [Algebra.FinitePresentation R B]
  [Algebra.FormallySmooth R B] [Module.Free B Ω[B⁄R]] [Module.Finite B Ω[B⁄R]]
  [CommRing A] [Algebra R A]

set_option maxHeartbeats 6400000 in

set_option backward.isDefEq.respectTransparency false in
theorem isSmoothAt_of_relations (g : B →ₐ[R] A) (hg : Function.Surjective g)
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    {ι : Type*} [Fintype ι] (z : ι → B) (hz : ∀ i, g (z i) = 0)
    (hli : letI := ((algebraMap (Localization.AtPrime p) p.ResidueField).comp
        (Localization.localRingHom (Ideal.comap g.toRingHom p) p g.toRingHom rfl)).toAlgebra
      LinearIndependent p.ResidueField (fun i => (1 : p.ResidueField)
        ⊗ₜ[Localization.AtPrime (Ideal.comap g.toRingHom p)]
          D R (Localization.AtPrime (Ideal.comap g.toRingHom p))
            (algebraMap B (Localization.AtPrime (Ideal.comap g.toRingHom p)) (z i))))
    (hcount : Module.finrank B Ω[B⁄R] =
      Fintype.card ι + Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by
  classical

  set J₀ : Ideal B := Ideal.span (Set.range z) with hJ₀
  have hJ₀le : ∀ b ∈ J₀, g b = 0 := by
    intro b hb
    rw [← RingHom.mem_ker]
    revert b hb
    change J₀ ≤ RingHom.ker g
    rw [hJ₀, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hz i
  haveI : Algebra.FinitePresentation R (B ⧸ J₀) :=
    Algebra.FinitePresentation.quotient ⟨(Set.finite_range z).toFinset, by simp [hJ₀]⟩
  set π : B ⧸ J₀ →ₐ[R] A := Ideal.Quotient.liftₐ J₀ g hJ₀le with hπdef
  have hπmk : ∀ b : B, π (Ideal.Quotient.mk J₀ b) = g b := fun b => rfl
  have hπsurj : Function.Surjective π :=
    Ideal.Quotient.lift_surjective_of_surjective J₀ hJ₀le hg
  have hπcomp : π.toRingHom.comp (Ideal.Quotient.mk J₀) = g.toRingHom := RingHom.ext fun b => rfl

  set 𝔓 : Ideal B := Ideal.comap g.toRingHom p with h𝔓
  set 𝔓C : Ideal (B ⧸ J₀) := Ideal.comap π.toRingHom p with h𝔓C
  set 𝔮C : Ideal (B ⧸ J₀) := Ideal.comap π.toRingHom q with h𝔮C
  have h𝔮𝔓 : 𝔮C ≤ 𝔓C := Ideal.comap_mono hqp
  have h𝔓' : 𝔓 = Ideal.comap (Ideal.Quotient.mk J₀) 𝔓C := by
    rw [h𝔓C, Ideal.comap_comap, hπcomp]

  set φ : Localization.AtPrime 𝔓 →+* Localization.AtPrime p :=
    Localization.localRingHom 𝔓 p g.toRingHom rfl with hφ
  set χ : Localization.AtPrime 𝔓 →+* Localization.AtPrime 𝔓C :=
    Localization.localRingHom 𝔓 𝔓C (Ideal.Quotient.mk J₀) h𝔓' with hχ
  set φ' : Localization.AtPrime 𝔓C →+* Localization.AtPrime p :=
    Localization.localRingHom 𝔓C p π.toRingHom rfl with hφ'
  set φq : Localization.AtPrime 𝔮C →+* Localization.AtPrime q :=
    Localization.localRingHom 𝔮C q π.toRingHom rfl with hφq
  have hφsurj : Function.Surjective φ := localRingHom_surjective g.toRingHom hg p 𝔓 rfl
  have hχsurj : Function.Surjective χ :=
    localRingHom_surjective (Ideal.Quotient.mk J₀) Ideal.Quotient.mk_surjective 𝔓C 𝔓 h𝔓'
  have hφ'surj : Function.Surjective φ' := localRingHom_surjective π.toRingHom hπsurj p 𝔓C rfl
  have hφqsurj : Function.Surjective φq := localRingHom_surjective π.toRingHom hπsurj q 𝔮C rfl
  have hχker : RingHom.ker χ = J₀.map (algebraMap B (Localization.AtPrime 𝔓)) := by
    rw [hχ, ker_localRingHom (Ideal.Quotient.mk J₀) Ideal.Quotient.mk_surjective 𝔓C 𝔓 h𝔓',
      Ideal.mk_ker]
  have hφ'ker : RingHom.ker φ' = (RingHom.ker π).map (algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C)) :=
    ker_localRingHom π.toRingHom hπsurj p 𝔓C rfl
  have hφqker : RingHom.ker φq = (RingHom.ker π).map (algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔮C)) :=
    ker_localRingHom π.toRingHom hπsurj q 𝔮C rfl
  have hφ'χ : φ'.comp χ = φ := by
    refine IsLocalization.ringHom_ext 𝔓.primeCompl (RingHom.ext fun b => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hχ, Localization.localRingHom_to_map, hφ', Localization.localRingHom_to_map, hφ,
      Localization.localRingHom_to_map]
    rfl

  letI iPS : Algebra (Localization.AtPrime 𝔓) (Localization.AtPrime p) := φ.toAlgebra
  letI iPS' : Algebra (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) := χ.toAlgebra
  letI iS'S : Algebra (Localization.AtPrime 𝔓C) (Localization.AtPrime p) := φ'.toAlgebra
  letI iTU : Algebra (Localization.AtPrime 𝔮C) (Localization.AtPrime q) := φq.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime 𝔓) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap g p 𝔓 rfl r).symm
  haveI : IsScalarTower R (Localization.AtPrime 𝔓C) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap π p 𝔓C rfl r).symm
  haveI : IsScalarTower R (Localization.AtPrime 𝔮C) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap π q 𝔮C rfl r).symm
  haveI : IsScalarTower R (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change _ = χ _
      rw [hχ, IsScalarTower.algebraMap_apply R B (Localization.AtPrime 𝔓),
        Localization.localRingHom_to_map,
        IsScalarTower.algebraMap_apply R (B ⧸ J₀) (Localization.AtPrime 𝔓C)]
      rfl
  haveI : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hφ'χ x).symm

  letI iPκ : Algebra (Localization.AtPrime 𝔓) p.ResidueField :=
    ((algebraMap (Localization.AtPrime p) p.ResidueField).comp φ).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime p) p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI iPκ' : Algebra (Localization.AtPrime 𝔓) 𝔓C.ResidueField :=
    ((algebraMap (Localization.AtPrime 𝔓C) 𝔓C.ResidueField).comp χ).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) 𝔓C.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI iTκU : Algebra (Localization.AtPrime 𝔮C) q.ResidueField :=
    ((algebraMap (Localization.AtPrime q) q.ResidueField).comp φq).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime 𝔮C) (Localization.AtPrime q) q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl

  haveI : Algebra.FormallyEtale B (Localization.AtPrime 𝔓) :=
    Algebra.FormallyEtale.of_isLocalization (M := 𝔓.primeCompl)
  haveI : Algebra.FormallySmooth R (Localization.AtPrime 𝔓) :=
    Algebra.FormallySmooth.comp R B (Localization.AtPrime 𝔓)
  have eΩP : Localization.AtPrime 𝔓 ⊗[B] Ω[B⁄R] ≃ₗ[Localization.AtPrime 𝔓]
      Ω[Localization.AtPrime 𝔓⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B (Localization.AtPrime 𝔓)
  haveI : Module.Free (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] := Module.Free.of_equiv eΩP
  haveI : Module.Finite (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] :=
    Module.Finite.equiv eΩP
  have hrankP : Module.finrank (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] =
      Module.finrank B Ω[B⁄R] := by
    rw [← eΩP.finrank_eq, Module.finrank_baseChange]

  have hzker : ∀ i, algebraMap B (Localization.AtPrime 𝔓) (z i) ∈ RingHom.ker χ := fun i => by
    rw [hχker]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
  have hkerspan : RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C)) =
      Ideal.span (Set.range (fun i => algebraMap B (Localization.AtPrime 𝔓) (z i))) := by
    change RingHom.ker χ = _
    rw [hχker, hJ₀, Ideal.map_span, ← Set.range_comp]
    rfl

  have hli' : LinearIndependent 𝔓C.ResidueField (fun i => (1 : 𝔓C.ResidueField)
      ⊗ₜ[Localization.AtPrime 𝔓] D R (Localization.AtPrime 𝔓)
        (algebraMap B (Localization.AtPrime 𝔓) (z i))) := by
    haveI : IsLocalHom φ' := Localization.isLocalHom_localRingHom 𝔓C p π.toRingHom rfl
    refine linearIndependent_one_tmul_of_map (IsLocalRing.ResidueField.map φ') ?_ _ hli
    refine RingHom.ext fun x => ?_
    change IsLocalRing.ResidueField.map φ' (IsLocalRing.residue _ (χ x)) =
      IsLocalRing.residue _ (φ x)
    rw [IsLocalRing.ResidueField.map_residue, ← hφ'χ]
    rfl
  have hinj' : Function.Injective (cotangentComplexBaseChange R (Localization.AtPrime 𝔓C)
      (Localization.AtPrime 𝔓) 𝔓C.ResidueField) := by
    refine injective_of_linearIndependent_of_span _
      (fun i => (1 : 𝔓C.ResidueField) ⊗ₜ[Localization.AtPrime 𝔓]
        (⟨algebraMap B (Localization.AtPrime 𝔓) (z i), hkerspan ▸ Ideal.subset_span ⟨i, rfl⟩⟩ :
          RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C))))
      (exists_sum_smul_one_tmul 𝔓C.ResidueField _ _ hkerspan) ?_
    convert hli' using 2 with i
    rw [cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply]
    rfl
  haveI hS'sm : Algebra.IsSmoothAt R 𝔓C :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField (R := R)
      (S := Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔓) hχsurj
        (IsNoetherian.noetherian _)).mpr hinj'

  haveI : Module.Finite (Localization.AtPrime 𝔓C) Ω[Localization.AtPrime 𝔓C⁄R] := inferInstance
  haveI : Module.Free (Localization.AtPrime 𝔓C) Ω[Localization.AtPrime 𝔓C⁄R] :=
    Module.free_of_flat_of_isLocalRing
  have hcountS' := finrank_tensor_kaehler_eq_finrank_range_add (R := R) hχsurj 𝔓C.ResidueField
  have hrange' : Module.finrank 𝔓C.ResidueField (LinearMap.range (cotangentComplexBaseChange R
      (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔓) 𝔓C.ResidueField)) = Fintype.card ι := by
    rw [LinearMap.finrank_range_of_inj hinj']
    apply le_antisymm
    ·
      have hspan : Submodule.span 𝔓C.ResidueField (Set.range (fun i => (1 : 𝔓C.ResidueField)
          ⊗ₜ[Localization.AtPrime 𝔓] (⟨algebraMap B (Localization.AtPrime 𝔓) (z i),
            hkerspan ▸ Ideal.subset_span ⟨i, rfl⟩⟩ :
          RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C))))) = ⊤ := by
        rw [eq_top_iff]
        rintro v -
        obtain ⟨c, rfl⟩ := exists_sum_smul_one_tmul 𝔓C.ResidueField _ _ hkerspan v
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      rw [← finrank_top, ← hspan]
      exact finrank_range_le_card _
    ·
      haveI : Module.Finite (Localization.AtPrime 𝔓)
          (RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C))) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      refine LinearIndependent.fintype_card_le_finrank (b := fun i => (1 : 𝔓C.ResidueField)
          ⊗ₜ[Localization.AtPrime 𝔓] (⟨algebraMap B (Localization.AtPrime 𝔓) (z i),
            hkerspan ▸ Ideal.subset_span ⟨i, rfl⟩⟩ :
          RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C)))) ?_
      refine LinearIndependent.of_comp (cotangentComplexBaseChange R (Localization.AtPrime 𝔓C)
        (Localization.AtPrime 𝔓) 𝔓C.ResidueField) ?_
      convert hli' using 2 with i
      simp only [Function.comp_apply]
      rw [cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply]
      rfl
  have hrankS' : Module.finrank (Localization.AtPrime 𝔓C) Ω[Localization.AtPrime 𝔓C⁄R] =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) := by
    rw [← Module.finrank_baseChange (R := 𝔓C.ResidueField)]
    rw [hrange', Module.finrank_baseChange, hrankP, hcount] at hcountS'
    omega

  haveI : IsDomain (Localization.AtPrime 𝔓C) := isDomain_localization_of_isSmoothAt (R := R) 𝔓C

  haveI hTsm : Algebra.IsSmoothAt R 𝔮C := by
    have hmem : (⟨𝔓C, inferInstance⟩ : PrimeSpectrum (B ⧸ J₀)) ∈ Algebra.smoothLocus R (B ⧸ J₀) :=
      hS'sm
    have hspec : (⟨𝔮C, inferInstance⟩ : PrimeSpectrum (B ⧸ J₀)) ⤳ ⟨𝔓C, inferInstance⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp h𝔮𝔓
    exact hspec.mem_open Algebra.isOpen_smoothLocus hmem

  letI iS'T : Algebra (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime 𝔓C)
      (Localization.AtPrime 𝔮C) 𝔓C.primeCompl 𝔮C.primeCompl
      (fun x hx h => hx (h𝔮𝔓 h))
  haveI : IsScalarTower (B ⧸ J₀) (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
  haveI : IsScalarTower R (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R (B ⧸ J₀) (Localization.AtPrime 𝔮C),
        IsScalarTower.algebraMap_apply R (B ⧸ J₀) (Localization.AtPrime 𝔓C),
        ← IsScalarTower.algebraMap_apply (B ⧸ J₀)]
  haveI : IsLocalization (𝔮C.primeCompl.map (algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C)))
      (Localization.AtPrime 𝔮C) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ 𝔓C.primeCompl 𝔮C.primeCompl
      (fun x hx h => hx (h𝔮𝔓 h))
  haveI : Algebra.FormallyEtale (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    Algebra.FormallyEtale.of_isLocalization
      (M := 𝔮C.primeCompl.map (algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C)))
  have eΩT : Localization.AtPrime 𝔮C ⊗[Localization.AtPrime 𝔓C] Ω[Localization.AtPrime 𝔓C⁄R]
      ≃ₗ[Localization.AtPrime 𝔮C] Ω[Localization.AtPrime 𝔮C⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R _ _
  haveI : Module.Free (Localization.AtPrime 𝔮C) Ω[Localization.AtPrime 𝔮C⁄R] :=
    Module.Free.of_equiv eΩT
  haveI : Module.Finite (Localization.AtPrime 𝔮C) Ω[Localization.AtPrime 𝔮C⁄R] :=
    Module.Finite.equiv eΩT
  have hrankT : Module.finrank (Localization.AtPrime 𝔮C) Ω[Localization.AtPrime 𝔮C⁄R] =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) := by
    rw [← eΩT.finrank_eq, Module.finrank_baseChange, hrankS']

  have hinjU : Function.Injective (cotangentComplexBaseChange R (Localization.AtPrime q)
      (Localization.AtPrime 𝔮C) q.ResidueField) :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField (R := R)
      (S := Localization.AtPrime q) (Localization.AtPrime 𝔮C) hφqsurj
        (IsNoetherian.noetherian _)).mp ‹Algebra.IsSmoothAt R q›
  have hcountU := finrank_tensor_kaehler_eq_finrank_range_add (R := R) hφqsurj q.ResidueField
  rw [Module.finrank_baseChange, hrankT, finrank_residueField_tensor_kaehler_localization,
    LinearMap.finrank_range_of_inj hinjU] at hcountU
  have hkerU : RingHom.ker φq = ⊥ := by
    haveI : IsLocalHom φq := Localization.isLocalHom_localRingHom 𝔮C q π.toRingHom rfl
    letI : Algebra (IsLocalRing.ResidueField (Localization.AtPrime 𝔮C)) q.ResidueField :=
      (IsLocalRing.ResidueField.map φq).toAlgebra
    haveI : IsScalarTower (Localization.AtPrime 𝔮C)
        (IsLocalRing.ResidueField (Localization.AtPrime 𝔮C)) q.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun x => by
        change IsLocalRing.residue _ (φq x) = IsLocalRing.ResidueField.map φq (IsLocalRing.residue _ x)
        rw [IsLocalRing.ResidueField.map_residue]
    have h0 : Module.finrank q.ResidueField (q.ResidueField ⊗[Localization.AtPrime 𝔮C]
        (RingHom.ker (algebraMap (Localization.AtPrime 𝔮C) (Localization.AtPrime q)))) = 0 := by
      omega
    exact eq_bot_of_finrank_tensor_eq_zero _ (IsNoetherian.noetherian _) q.ResidueField h0

  have hkerS' : RingHom.ker φ' = ⊥ := by
    rw [hφ'ker, Ideal.map_eq_bot_iff_le_ker]
    intro c hc
    rw [RingHom.mem_ker]

    have hcT : algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔮C) c = 0 := by
      have hmem : algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔮C) c ∈ RingHom.ker φq := by
        rw [hφqker]; exact Ideal.mem_map_of_mem _ hc
      rwa [hkerU, Ideal.mem_bot] at hmem
    obtain ⟨⟨t, ht⟩, htc⟩ := (IsLocalization.map_eq_zero_iff 𝔮C.primeCompl _ c).mp hcT
    have hmul : algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C) t *
        algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C) c = 0 := by
      rw [← map_mul, htc, map_zero]
    rcases mul_eq_zero.mp hmul with h0 | h0
    · exfalso
      obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalization.map_eq_zero_iff 𝔓C.primeCompl _ t).mp h0
      have : s * t ∈ 𝔮C := by rw [hst]; exact 𝔮C.zero_mem
      rcases (inferInstance : 𝔮C.IsPrime).mem_or_mem this with h1 | h1
      · exact hs (h𝔮𝔓 h1)
      · exact ht h1
    · exact h0

  have hφ'inj : Function.Injective φ' := (RingHom.injective_iff_ker_eq_bot φ').mpr hkerS'
  let φ'ₐ : Localization.AtPrime 𝔓C →ₐ[R] Localization.AtPrime p :=
    { φ' with commutes' := fun r => localRingHom_algebraMap π p 𝔓C rfl r }
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective φ'ₐ ⟨hφ'inj, hφ'surj⟩)

end Main

end P2mJacobi

open P2mJacobi

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    (h : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by
  classical

  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R A›

  set 𝔓 : Ideal (MvPolynomial (Fin n) R) := Ideal.comap g.toRingHom p with h𝔓
  set φ : Localization.AtPrime 𝔓 →+* Localization.AtPrime p :=
    Localization.localRingHom 𝔓 p g.toRingHom rfl with hφ
  have hφsurj : Function.Surjective φ := localRingHom_surjective g.toRingHom hg p 𝔓 rfl
  letI iPS : Algebra (Localization.AtPrime 𝔓) (Localization.AtPrime p) := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime 𝔓) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap g p 𝔓 rfl r).symm
  letI iPκ : Algebra (Localization.AtPrime 𝔓) p.ResidueField :=
    ((algebraMap (Localization.AtPrime p) p.ResidueField).comp
      (Localization.localRingHom (Ideal.comap g.toRingHom p) p g.toRingHom rfl)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime p) p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl

  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) :=
    Algebra.FormallyEtale.of_isLocalization (M := 𝔓.primeCompl)
  have eΩP : Localization.AtPrime 𝔓 ⊗[MvPolynomial (Fin n) R] Ω[MvPolynomial (Fin n) R⁄R]
      ≃ₗ[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) _
  haveI : Module.Free (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] := Module.Free.of_equiv eΩP
  haveI : Module.Finite (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] :=
    Module.Finite.equiv eΩP
  have hrankP : Module.finrank (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] =
      Module.finrank (MvPolynomial (Fin n) R) Ω[MvPolynomial (Fin n) R⁄R] := by
    rw [← eΩP.finrank_eq, Module.finrank_baseChange]

  have hcount := finrank_tensor_kaehler_eq_finrank_range_add (R := R) hφsurj p.ResidueField
  rw [Module.finrank_baseChange, hrankP, finrank_residueField_tensor_kaehler_localization, h]
    at hcount

  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker g.toRingHom) : (RingHom.ker g.toRingHom).FG)
  have hkerφ : RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime p)) =
      Ideal.span (Set.range (fun j : s =>
        algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (j : MvPolynomial (Fin n) R))) := by
    change RingHom.ker φ = _
    rw [hφ, ker_localRingHom g.toRingHom hg p 𝔓 rfl, ← hs, Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_range, Subtype.exists, exists_prop]

  set u : s → p.ResidueField ⊗[Localization.AtPrime 𝔓]
      RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime p)) :=
    fun j => (1 : p.ResidueField) ⊗ₜ[Localization.AtPrime 𝔓]
      (⟨algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (j : MvPolynomial (Fin n) R),
        hkerφ ▸ Ideal.subset_span ⟨j, rfl⟩⟩ :
        RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime p))) with hu
  set v : s → p.ResidueField ⊗[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R] :=
    fun j => cotangentComplexBaseChange R (Localization.AtPrime p) (Localization.AtPrime 𝔓)
      p.ResidueField (u j) with hv
  have hW : LinearMap.range (cotangentComplexBaseChange R (Localization.AtPrime p)
      (Localization.AtPrime 𝔓) p.ResidueField) = Submodule.span p.ResidueField (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨c, rfl⟩ := exists_sum_smul_one_tmul p.ResidueField _ _ hkerφ x
      rw [map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨u j, rfl⟩

  obtain ⟨ι, a, hainj, hspan, hli⟩ := exists_linearIndependent' (K := p.ResidueField) v
  haveI : Finite ι := Finite.of_injective a hainj
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank p.ResidueField (LinearMap.range
      (cotangentComplexBaseChange R (Localization.AtPrime p) (Localization.AtPrime 𝔓)
        p.ResidueField)) := by
    rw [← finrank_span_eq_card hli, hspan, hW]

  set z : ι → MvPolynomial (Fin n) R := fun i => (a i : MvPolynomial (Fin n) R) with hzdef
  have hz : ∀ i, g (z i) = 0 := fun i => by
    have : (a i : MvPolynomial (Fin n) R) ∈ RingHom.ker g.toRingHom := by
      rw [← hs]; exact Ideal.subset_span (a i).2
    exact this
  have hli' : LinearIndependent p.ResidueField (fun i => (1 : p.ResidueField)
      ⊗ₜ[Localization.AtPrime 𝔓] D R (Localization.AtPrime 𝔓)
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (z i))) := by
    convert hli using 2 with i
    simp only [Function.comp_apply, hv, hu, hzdef]
    rw [cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply]
    rfl
  refine isSmoothAt_of_relations g hg p q hqp z hz hli' ?_
  rw [hcard]
  exact hcount

end S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
end P2MW
export P2MW.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq (solution)
