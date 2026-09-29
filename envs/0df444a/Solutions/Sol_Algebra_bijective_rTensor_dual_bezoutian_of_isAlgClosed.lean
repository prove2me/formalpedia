-- Prove2me | solution 1 for Algebra.bijective_rTensor_dual_bezoutian_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5996955d-c7c2-53cd-b75c-c60d24a9fe37

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_bijective_compr2_mul_of_finite
import Theorems.Thm_MvPowerSeries_quotient_mk_det_mem_of_ne_bot
import Theorems.Thm_MvPolynomial_exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk
import Theorems.Thm_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime
import Theorems.Thm_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped TensorProduct

universe u

theorem Ws47.DLB.lid_rTensor_comp_mulLeft
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (Δ : A ⊗[R] A) (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (φ : Module.Dual R A) (s : A) :
    Algebra.TensorProduct.lid R A (LinearMap.rTensor A (φ.comp (LinearMap.mulLeft R s)) Δ) =
      s * Algebra.TensorProduct.lid R A (LinearMap.rTensor A φ Δ) := by
  have h2 : ∀ z : A ⊗[R] A, LinearMap.rTensor A (LinearMap.mulLeft R s) z = (s ⊗ₜ[R] (1 : A)) * z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h3 : ∀ z : A ⊗[R] A, ((1 : A) ⊗ₜ[R] s) * z = LinearMap.lTensor A (LinearMap.mulLeft R s) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h4 : ∀ w : R ⊗[R] A, Algebra.TensorProduct.lid R A (LinearMap.lTensor R (LinearMap.mulLeft R s) w) =
      s * Algebra.TensorProduct.lid R A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [Algebra.TensorProduct.lid_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]

  have h5 : LinearMap.rTensor A φ (LinearMap.lTensor A (LinearMap.mulLeft R s) Δ) =
      LinearMap.lTensor R (LinearMap.mulLeft R s) (LinearMap.rTensor A φ Δ) := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, h2, hbal, h3, h5, h4]

namespace Ws47
namespace CB3

variable {K : Type u} [Field K]

section Frame
variable {A : Type u} [CommRing A] [Algebra K A] (Δ : A ⊗[K] A)

noncomputable def thetaₗ : Module.Dual K A →ₗ[K] A where
  toFun φ := Algebra.TensorProduct.lid K A (LinearMap.rTensor A φ Δ)
  map_add' φ ψ := by simp [LinearMap.rTensor_add]
  map_smul' c φ := by simp [LinearMap.rTensor_smul]

theorem thetaₗ_apply (φ : Module.Dual K A) : thetaₗ (K := K) Δ φ = Algebra.TensorProduct.lid K A (LinearMap.rTensor A φ Δ) := rfl

theorem apply_thetaₗ (ε : A →ₗ[K] K) (φ : Module.Dual K A) :
    ε (thetaₗ (K := K) Δ φ) = φ (Algebra.TensorProduct.rid K K A (LinearMap.lTensor A ε Δ)) := by
  rw [thetaₗ_apply]
  induction Δ using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.rid_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem thetaₗ_comp_mulLeft (hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δ = ((1 : A) ⊗ₜ[K] s) * Δ)
    (φ : Module.Dual K A) (s : A) : thetaₗ (K := K) Δ (φ.comp (LinearMap.mulLeft K s)) = s * thetaₗ (K := K) Δ φ :=
  Ws47.DLB.lid_rTensor_comp_mulLeft K A Δ hbal φ s

theorem bijective_thetaₗ_of_injective [FiniteDimensional K A] (hinj : Function.Injective (thetaₗ (K := K) Δ)) :
    Function.Bijective (thetaₗ (K := K) Δ) := by
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  exact Subspace.dual_finrank_eq

theorem injective_thetaₗ_of_forall_factor
    (hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δ = ((1 : A) ⊗ₜ[K] s) * Δ)
    {ι : Type*} [Finite ι] (𝔫 : ι → Ideal A) (N : ℕ)
    (hcrt : Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (𝔫 i ^ N)))
    (hloc : ∀ (i : ι) (χ : Module.Dual K A), (∀ x ∈ 𝔫 i ^ N, χ x = 0) → thetaₗ (K := K) Δ χ = 0 → χ = 0) :
    Function.Injective (thetaₗ (K := K) Δ) := by
  classical
  haveI := Fintype.ofFinite ι
  set π : A →+* ((i : ι) → A ⧸ 𝔫 i ^ N) := RingHom.pi fun i => Ideal.Quotient.mk (𝔫 i ^ N) with hπ

  have hsurj := hcrt.2
  choose e he using fun i => hsurj (Pi.single i 1)
  have hπe : ∀ i j, Ideal.Quotient.mk (𝔫 j ^ N) (e i) = Pi.single (M := fun j => A ⧸ 𝔫 j ^ N) i 1 j := fun i j => by
    have := congrArg (fun v => v j) (he i); (simp [hπ] at this; exact this)

  have hsum : ∑ i, e i = 1 := by
    apply hcrt.1
    rw [map_sum, map_one]
    funext j
    simp only [Finset.sum_apply, Pi.one_apply, hπ, RingHom.pi_apply, hπe]
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
    simp

  have hekill : ∀ i, ∀ x ∈ 𝔫 i ^ N, e i * x = 0 := by
    intro i x hx
    apply hcrt.1
    rw [map_mul, map_zero, he]
    funext j
    simp only [Pi.mul_apply, Pi.zero_apply, hπ, RingHom.pi_apply]
    by_cases hij : j = i
    · subst hij; rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, mul_zero]
    · simp [hij]
  intro φ φ' hφφ'
  rw [← sub_eq_zero] at hφφ' ⊢
  rw [← map_sub] at hφφ'
  set χ := φ - φ' with hχ
  have hvan : ∀ i, ∀ x ∈ 𝔫 i ^ N, (χ.comp (LinearMap.mulLeft K (e i))) x = 0 := fun i x hx => by
    simp [hekill i x hx]

  have hψ0 : ∀ i, χ.comp (LinearMap.mulLeft K (e i)) = 0 := fun i =>
    hloc i _ (hvan i) (by rw [thetaₗ_comp_mulLeft Δ hbal, hφφ', mul_zero])

  have hdecomp : χ = ∑ i, χ.comp (LinearMap.mulLeft K (e i)) := by
    ext x
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [← map_sum, ← Finset.sum_mul, hsum, one_mul]
  rw [hdecomp]
  exact Finset.sum_eq_zero fun i _ => hψ0 i

end Frame

section Socle
variable {m : ℕ}

theorem apply_mk_det_ne_zero (q : Matrix (Fin m) (Fin m) (MvPowerSeries (Fin m) K))
    (f : Fin m → MvPowerSeries (Fin m) K) (hf : ∀ i, f i = ∑ j, q i j * MvPowerSeries.X j)
    [Module.Finite K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f))]
    (l : (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) →ₗ[K] K)
    (hl : Function.Bijective ((LinearMap.mul K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f))).compr₂ l)) :
    l (Ideal.Quotient.mk (Ideal.span (Set.range f)) q.det) ≠ 0 := by
  classical
  obtain ⟨hs0, hsJ⟩ := MvPowerSeries.quotient_mk_det_mem_of_ne_bot q f hf
  set s := Ideal.Quotient.mk (Ideal.span (Set.range f)) q.det with hs

  have hkill : ∀ φ : MvPowerSeries (Fin m) K, MvPowerSeries.constantCoeff φ = 0 →
      s * Ideal.Quotient.mk (Ideal.span (Set.range f)) φ = 0 := by
    intro φ hφ
    by_contra hne
    have hmem := hsJ (Ideal.span {s * Ideal.Quotient.mk (Ideal.span (Set.range f)) φ})
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨t, ht⟩ := hmem
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have hu : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range f)) (1 - t' * φ)) := by
      refine (MvPowerSeries.isUnit_iff_constantCoeff.mpr ?_).map _
      rw [map_sub, map_one, map_mul, hφ, mul_zero, sub_zero]
      exact isUnit_one
    apply hs0
    have h1 : s * Ideal.Quotient.mk (Ideal.span (Set.range f)) (1 - t' * φ) = 0 := by
      rw [map_sub, map_one, mul_sub, mul_one, map_mul, sub_eq_zero]
      calc s = Ideal.Quotient.mk _ t' * (s * Ideal.Quotient.mk _ φ) := ht.symm
        _ = s * (Ideal.Quotient.mk _ t' * Ideal.Quotient.mk _ φ) := by ring
    exact hu.mul_left_eq_zero.mp h1
  intro hl0
  apply hs0
  apply hl.1
  refine LinearMap.ext fun r => ?_
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.mul_apply', zero_mul, map_zero]

  have hC : ∀ c : K, s * Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPowerSeries.C c) = c • s := by
    intro c
    have h1 : (c • s : MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) =
        algebraMap K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) c * s := Algebra.smul_def c s
    rw [h1, mul_comm]
    show _ = Ideal.Quotient.mk _ (algebraMap K (MvPowerSeries (Fin m) K) c) * s
    congr 2
  have hsplit : s * Ideal.Quotient.mk (Ideal.span (Set.range f)) φ = MvPowerSeries.constantCoeff φ • s := by
    have hφ : φ = MvPowerSeries.C (MvPowerSeries.constantCoeff φ) +
        (φ - MvPowerSeries.C (MvPowerSeries.constantCoeff φ)) := by ring
    conv_lhs => rw [hφ]
    rw [map_add, mul_add, hC, hkill (φ - MvPowerSeries.C (MvPowerSeries.constantCoeff φ)) (by simp), add_zero]
  rw [hsplit, map_smul, hl0, smul_zero]

end Socle

section Local
variable {m : ℕ} (g : Fin m → MvPolynomial (Fin m) K)
  (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K)

local notation "P" => MvPolynomial (Fin m) K
local notation "A" => MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)

noncomputable def Δb : A ⊗[K] A :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
    (Matrix.det (Matrix.of b))

noncomputable def evR (ξ : Fin m → K) : MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  (Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) K) K).comp
    (Algebra.TensorProduct.map (AlgHom.id K (MvPolynomial (Fin m) K))
      (MvPolynomial.aeval fun j => MvPolynomial.C (ξ j)))

noncomputable def bAt (ξ : Fin m → K) (i j : Fin m) : MvPolynomial (Fin m) K := evR ξ (b i j)

noncomputable def transl (ξ : Fin m → K) : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval fun j => MvPolynomial.X j + MvPolynomial.C (ξ j)

omit g b in
theorem transl_comp_transl_neg (ξ : Fin m → K) : (transl (K := K) ξ).comp (transl (-ξ)) = AlgHom.id K P := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [transl]

noncomputable def translEquiv (ξ : Fin m → K) : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K :=
  AlgEquiv.ofAlgHom (transl ξ) (transl (-ξ)) (transl_comp_transl_neg ξ)
    (by simpa using transl_comp_transl_neg (K := K) (-ξ))

omit g b in
theorem aeval_C_comp (ξ : Fin m → K) (p : P) :
    MvPolynomial.aeval (fun j => (MvPolynomial.C (ξ j) : P)) p = (MvPolynomial.C (MvPolynomial.aeval ξ p) : P) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

omit g b in
theorem evR_tmul (ξ : Fin m → K) (p p' : P) :
    evR ξ (p ⊗ₜ[K] p') = p * MvPolynomial.C (MvPolynomial.aeval ξ p') := by
  show Algebra.TensorProduct.lmul' (S := P) K (Algebra.TensorProduct.map (AlgHom.id K P)
    (MvPolynomial.aeval fun j => (MvPolynomial.C (ξ j) : P)) (p ⊗ₜ[K] p')) = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply, aeval_C_comp]

theorem g_sub_C_eq_sum_bAt
    (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
      ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j))
    (ξ : Fin m → K) (i : Fin m) :
    g i - MvPolynomial.C (MvPolynomial.aeval ξ (g i)) =
      ∑ j, bAt b ξ i j * (MvPolynomial.X j - MvPolynomial.C (ξ j)) := by
  have := congrArg (evR ξ) (hb i)
  simpa [map_sub, map_sum, map_mul, evR_tmul, bAt] using this

theorem exists_point_of_isMaximal [IsAlgClosed K] (𝔫 : Ideal A) [𝔫.IsMaximal] :
    ∃ ξ : Fin m → K, ∀ p : P,
      Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0 := by
  have hmax : (𝔫.comap (Ideal.Quotient.mk (Ideal.span (Set.range g)))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨ξ, hξ⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hmax
  refine ⟨ξ, fun p => ?_⟩
  rw [← MvPolynomial.mem_vanishingIdeal_singleton_iff, ← hξ, Ideal.mem_comap]

set_option synthInstance.maxHeartbeats 800000 in

theorem eval_thetaₗ_Δb (ξ : Fin m → K) (hI : ∀ a ∈ Ideal.span (Set.range g), MvPolynomial.aeval ξ a = 0)
    (φ : Module.Dual K A) :
    Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) (MvPolynomial.aeval ξ) hI (thetaₗ (K := K) (Δb g b) φ) =
      φ (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ)))) := by
  classical
  set ε := Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) (MvPolynomial.aeval ξ) hI with hεdef
  have hε : ∀ p, ε (Ideal.Quotient.mk _ p) = MvPolynomial.aeval ξ p := fun _ => rfl
  have key : ∀ z : P ⊗[K] P, Algebra.TensorProduct.rid K K A (LinearMap.lTensor A ε.toLinearMap
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
        (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) z)) =
      Ideal.Quotient.mk (Ideal.span (Set.range g)) (evR ξ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul p p' =>
      rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, Algebra.TensorProduct.rid_tmul, evR_tmul, map_mul,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, hε, Algebra.smul_def, mul_comm]
      congr 1
    | add x y hx hy => simp only [map_add, hx, hy]
  have h := apply_thetaₗ (K := K) (Δb g b) ε.toLinearMap φ
  rw [AlgHom.toLinearMap_apply] at h
  rw [h]
  congr 1
  show _ = _
  rw [Δb, key, AlgHom.map_det]
  congr 2

variable [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
  (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
    ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j))

include hb

theorem exists_local_model (ξ : Fin m → K) (𝔫 : Ideal A) [𝔫.IsMaximal]
    (h𝔫 : ∀ p : P, Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0)
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    ∃ (q : Matrix (Fin m) (Fin m) (MvPowerSeries (Fin m) K)) (f : Fin m → MvPowerSeries (Fin m) K)
      (_ : ∀ i, f i = ∑ j, q i j * MvPowerSeries.X j)
      (_ : Module.Finite K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)))
      (Φ : (A ⧸ 𝔫 ^ N) ≃ₐ[K] (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f))),
      Φ (Ideal.Quotient.mk (𝔫 ^ N) (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ))))) =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det q) := by
  classical
  have hξ : ∀ i, MvPolynomial.aeval ξ (g i) = 0 := fun i =>
    (h𝔫 (g i)).mp (by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))]
      exact Ideal.zero_mem _)

  let σ : P ≃ₐ[K] P := translEquiv ξ
  have hσ : ∀ p, σ p = transl ξ p := fun _ => rfl
  have hσX : ∀ j, σ (MvPolynomial.X j - MvPolynomial.C (ξ j)) = MvPolynomial.X j := by
    intro j; simp [hσ, transl]
  let g' : Fin m → P := fun i => σ (g i)
  let f : Fin m → MvPowerSeries (Fin m) K := fun i => (g' i : MvPowerSeries (Fin m) K)
  let q : Matrix (Fin m) (Fin m) (MvPowerSeries (Fin m) K) := fun i j => ((σ (bAt b ξ i j) : P) : MvPowerSeries (Fin m) K)

  have hgb : ∀ i, g i = ∑ j, bAt b ξ i j * (MvPolynomial.X j - MvPolynomial.C (ξ j)) := by
    intro i
    have := g_sub_C_eq_sum_bAt g b hb ξ i
    rwa [hξ i, map_zero, sub_zero] at this
  have hg' : ∀ i, g' i = ∑ j, σ (bAt b ξ i j) * MvPolynomial.X j := by
    intro i
    show σ (g i) = _
    conv_lhs => rw [hgb i]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hσX]
  have hcoe : ∀ p : P, (p : MvPowerSeries (Fin m) K) = MvPolynomial.coeToMvPowerSeries.ringHom p := fun _ => rfl
  have hf : ∀ i, f i = ∑ j, q i j * MvPowerSeries.X j := by
    intro i
    show ((g' i : P) : MvPowerSeries (Fin m) K) = _
    rw [hg' i, hcoe, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hcoe, ← hcoe, MvPolynomial.coe_X]

  have hIJ : Ideal.span (Set.range g') = Ideal.map (σ : P →+* P) (Ideal.span (Set.range g)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  let τ : A ≃ₐ[K] (P ⧸ Ideal.span (Set.range g')) := Ideal.quotientEquivAlg _ _ σ hIJ
  have hτ : ∀ p, τ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (σ p) := fun _ => rfl

  let 𝔫' : Ideal (P ⧸ Ideal.span (Set.range g')) := Ideal.map (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) 𝔫
  haveI h𝔫'max : 𝔫'.IsMaximal := Ideal.IsMaximal.map_bijective _ (by exact τ.bijective) inferInstance
  have h𝔫'X : ∀ j, Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.X j) ∈ 𝔫' := by
    intro j
    have h1 : Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X j - MvPolynomial.C (ξ j)) ∈ 𝔫 :=
      (h𝔫 _).mpr (by simp)
    have h2 : τ (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X j - MvPolynomial.C (ξ j))) ∈ 𝔫' :=
      Ideal.mem_map_of_mem (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) h1
    rwa [hτ, hσX] at h2
  let τN : (A ⧸ 𝔫 ^ N) ≃ₐ[K] ((P ⧸ Ideal.span (Set.range g')) ⧸ 𝔫' ^ N) :=
    Ideal.quotientEquivAlg (𝔫 ^ N) (𝔫' ^ N) τ (by rw [Ideal.map_pow])
  have hτN : ∀ a, τN (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (τ a) := fun _ => rfl

  haveI : Module.Finite K (P ⧸ Ideal.span (Set.range g')) := Module.Finite.equiv τ.toLinearEquiv
  haveI : IsArtinianRing (P ⧸ Ideal.span (Set.range g')) := IsArtinianRing.of_finite K _
  have hN' : (Ideal.jacobson (⊥ : Ideal (P ⧸ Ideal.span (Set.range g')))) ^ N = ⊥ := by
    have hsurj : Function.Surjective (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) := τ.surjective
    have hker : RingHom.ker (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) ≤ ⊥ :=
      ((RingHom.injective_iff_ker_eq_bot _).mp τ.injective).le
    have hj := Ideal.map_jacobson_of_surjective hsurj hker
    rw [Ideal.map_bot] at hj
    rw [← hj, ← Ideal.map_pow, hN, Ideal.map_bot]
  obtain ⟨e₁⟩ := IsArtinianRing.nonempty_quotient_pow_algEquiv_localization_atPrime _ 𝔫' N hN'
  haveI : Module.Finite K (Localization.AtPrime 𝔫') := Module.Finite.equiv (e₁.restrictScalars K).toLinearEquiv
  obtain ⟨e₂, he₂⟩ :=
    MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk K g' 𝔫' h𝔫'X
  haveI hfin : Module.Finite K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) :=
    Module.Finite.equiv e₂.toLinearEquiv
  let Φ : (A ⧸ 𝔫 ^ N) ≃ₐ[K] (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) :=
    (τN.trans (e₁.restrictScalars K)).trans e₂
  have hdet : ((σ (Matrix.det (Matrix.of (bAt b ξ))) : P) : MvPowerSeries (Fin m) K) = Matrix.det q := by
    let ρ : P →+* MvPowerSeries (Fin m) K := MvPolynomial.coeToMvPowerSeries.ringHom.comp (σ : P →+* P)
    have hρ : ∀ p, ((σ p : P) : MvPowerSeries (Fin m) K) = ρ p := fun _ => rfl
    rw [hρ, RingHom.map_det]
    congr 1
  refine ⟨q, f, hf, hfin, Φ, ?_⟩
  have he₁ : ∀ x, e₁ (Ideal.Quotient.mk (𝔫' ^ N) x) = algebraMap _ (Localization.AtPrime 𝔫') x :=
    fun x => e₁.commutes x
  calc Φ (Ideal.Quotient.mk (𝔫 ^ N) (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ)))))
      = e₂ (e₁.restrictScalars K (τN (Ideal.Quotient.mk (𝔫 ^ N)
          (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ))))))) := rfl
    _ = e₂ (algebraMap _ (Localization.AtPrime 𝔫')
          (Ideal.Quotient.mk (Ideal.span (Set.range g')) (σ (Matrix.det (Matrix.of (bAt b ξ)))))) := by
        rw [AlgEquiv.restrictScalars_apply, hτN, hτ, he₁]
    _ = Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det q) := by
        rw [he₂, hdet]

theorem exists_frobenius_form_factor (ξ : Fin m → K) (𝔫 : Ideal A) [𝔫.IsMaximal]
    (h𝔫 : ∀ p : P, Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0)
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    ∃ lam : Module.Dual K (A ⧸ 𝔫 ^ N),
      (∀ ψ : Module.Dual K (A ⧸ 𝔫 ^ N), ∃ c : A ⧸ 𝔫 ^ N, ψ = lam.comp (LinearMap.mulLeft K c)) ∧
      (∀ c : A ⧸ 𝔫 ^ N, lam.comp (LinearMap.mulLeft K c) = 0 → c = 0) ∧
      lam (Ideal.Quotient.mk (𝔫 ^ N)
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ))))) ≠ 0 := by
  classical
  obtain ⟨q, f, hf, hfin, Φ, hΦ⟩ := exists_local_model g b hb ξ 𝔫 h𝔫 N hN
  haveI := hfin
  obtain ⟨l, hl⟩ := MvPowerSeries.exists_bijective_compr2_mul_of_finite q f hf
  have hls := apply_mk_det_ne_zero (K := K) q f hf l hl
  refine ⟨l.comp Φ.toLinearEquiv.toLinearMap, ?_, ?_, ?_⟩
  · intro ψ
    obtain ⟨x, hx⟩ := hl.2 (ψ.comp Φ.symm.toLinearEquiv.toLinearMap)
    refine ⟨Φ.symm x, LinearMap.ext fun y => ?_⟩
    have := LinearMap.congr_fun hx (Φ y)
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgEquiv.toLinearEquiv_apply, AlgEquiv.symm_apply_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
      map_mul, AlgEquiv.apply_symm_apply]
    exact this.symm
  · intro c hc
    have h0 : (LinearMap.mul K _).compr₂ l (Φ c) = (LinearMap.mul K _).compr₂ l 0 := by
      refine LinearMap.ext fun y => ?_
      have := LinearMap.congr_fun hc (Φ.symm y)
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
        map_mul, AlgEquiv.apply_symm_apply, LinearMap.zero_apply] at this
      simpa [LinearMap.compr₂_apply, LinearMap.mul_apply'] using this
    simpa using hl.1 h0
  · simpa [hΦ] using hls

theorem functional_eq_zero_of_forall_mem_pow (ξ : Fin m → K) (𝔫 : Ideal A) [𝔫.IsMaximal]
    (h𝔫 : ∀ p : P, Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0)
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥)
    (χ : Module.Dual K A) (hχ : ∀ x ∈ 𝔫 ^ N, χ x = 0) (hθ : thetaₗ (K := K) (Δb g b) χ = 0) : χ = 0 := by
  classical
  obtain ⟨lam, h1, h2, h3⟩ := exists_frobenius_form_factor g b hb ξ 𝔫 h𝔫 N hN
  have hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δb g b = ((1 : A) ⊗ₜ[K] s) * Δb g b :=
    fun s => Algebra.tmul_one_mul_bezoutian_eq_one_tmul_mul K g b hb s

  have hle : (𝔫 ^ N).restrictScalars K ≤ LinearMap.ker χ := fun x hx => LinearMap.mem_ker.mpr (hχ x hx)
  let ψ : Module.Dual K (A ⧸ 𝔫 ^ N) :=
    (((𝔫 ^ N).restrictScalars K).liftQ χ hle).comp (Submodule.Quotient.restrictScalarsEquiv K (𝔫 ^ N)).symm.toLinearMap
  have hψ : ∀ x, ψ (Ideal.Quotient.mk (𝔫 ^ N) x) = χ x := fun x => rfl
  obtain ⟨c, hc⟩ := h1 ψ
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  set y := thetaₗ (K := K) (Δb g b) (lam.comp (Ideal.Quotient.mkₐ K (𝔫 ^ N)).toLinearMap) with hy
  have hχ' : χ = (lam.comp (Ideal.Quotient.mkₐ K (𝔫 ^ N)).toLinearMap).comp (LinearMap.mulLeft K c') := by
    refine LinearMap.ext fun x => ?_
    rw [← hψ x, hc]
    simp [map_mul]
  have hθ' : c' * y = 0 := by rw [hy, ← thetaₗ_comp_mulLeft _ hbal, ← hχ', hθ]

  have hI : ∀ a ∈ Ideal.span (Set.range g), MvPolynomial.aeval ξ a = 0 := fun a ha =>
    (h𝔫 a).mp (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact Ideal.zero_mem _)
  have hεy := eval_thetaₗ_Δb g b ξ hI (lam.comp (Ideal.Quotient.mkₐ K (𝔫 ^ N)).toLinearMap)
  rw [← hy] at hεy
  have hy𝔫 : y ∉ 𝔫 := by
    intro hmem
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective y
    have hp0 : MvPolynomial.aeval ξ p = 0 := (h𝔫 p).mp (hp ▸ hmem)
    apply h3
    have : Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) (MvPolynomial.aeval ξ) hI y = 0 := by
      rw [← hp]; exact hp0
    rw [this] at hεy
    exact hεy.symm

  obtain ⟨z, w, hw, hzw⟩ := Ideal.IsMaximal.exists_inv ‹𝔫.IsMaximal› hy𝔫
  have hcw : ∀ k : ℕ, c' = c' * w ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc c' = c' * 1 * w ^ k := by rw [mul_one]; exact ih
        _ = c' * (z * y + w) * w ^ k := by rw [hzw]
        _ = (z * (c' * y) + c' * w) * w ^ k := by ring
        _ = c' * w ^ (k + 1) := by rw [hθ', mul_zero, zero_add, mul_assoc, ← pow_succ']
  have hc'mem : c' ∈ 𝔫 ^ N := by
    rw [hcw N]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hw N)

  rw [hχ']
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply]
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right x _ hc'mem), map_zero]

omit g b hb in
theorem iInf_le_prod_of_pairwise_isCoprime' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (I : ι → Ideal R) (h : Pairwise (Function.onFun IsCoprime I)) : ⨅ i, I i ≤ ∏ i, I i := by
  classical
  suffices hs : ∀ s : Finset ι, ⨅ i, I i ≤ ∏ i ∈ s, I i from hs Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have hcop : IsCoprime (I j) (∏ i ∈ s, I i) :=
      IsCoprime.prod_right fun i hi => h (fun heq => hj (heq ▸ hi))
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf (iInf_le _ j) ih

omit g b hb in
theorem crt_bijective {R : Type*} [CommRing R] {ι : Type*} [Finite ι] (I : ι → Ideal R)
    (hcop : Pairwise (Function.onFun IsCoprime I)) (hinf : ⨅ i, I i = ⊥) :
    Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (I i)) := by
  let e := Ideal.quotientInfRingEquivPiQuotient I hcop
  have hmk : Function.Bijective (Ideal.Quotient.mk (⨅ i, I i)) :=
    ⟨(injective_iff_map_eq_zero _).mpr fun a ha => by
        rwa [Ideal.Quotient.eq_zero_iff_mem, hinf, Ideal.mem_bot] at ha,
      Ideal.Quotient.mk_surjective⟩
  have hcomp : ⇑(RingHom.pi fun i => Ideal.Quotient.mk (I i)) = e ∘ Ideal.Quotient.mk _ := by
    funext x
    exact (Ideal.quotientInfToPiQuotient_mk I x).symm
  rw [hcomp]
  exact e.bijective.comp hmk

theorem bijective_thetaₗ_Δb [IsAlgClosed K] : Function.Bijective (thetaₗ (K := K) (Δb g b)) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K _
  obtain ⟨N, hN0⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥ := hN0.trans Submodule.zero_eq_bot
  haveI hfinι : Finite ↥{I : Ideal A | I.IsMaximal} := (IsArtinianRing.setOf_isMaximal_finite _).to_subtype
  haveI := Fintype.ofFinite ↥{I : Ideal A | I.IsMaximal}
  have hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δb g b = ((1 : A) ⊗ₜ[K] s) * Δb g b :=
    fun s => Algebra.tmul_one_mul_bezoutian_eq_one_tmul_mul K g b hb s

  have hcop : Pairwise (Function.onFun IsCoprime fun i : ↥{I : Ideal A | I.IsMaximal} => i.1 ^ N) := by
    intro i j hij
    haveI : (i.1).IsMaximal := i.2
    haveI : (j.1).IsMaximal := j.2
    exact (Ideal.isCoprime_of_isMaximal (fun h => hij (Subtype.ext h))).pow

  have hinf : (⨅ i : ↥{I : Ideal A | I.IsMaximal}, i.1 ^ N) = ⊥ := by
    refine le_bot_iff.mp ((iInf_le_prod_of_pairwise_isCoprime' _ hcop).trans ?_)
    rw [Finset.prod_pow, ← hN]
    refine Ideal.pow_right_mono ?_ N
    refine Ideal.prod_le_inf.trans ?_
    rw [Ideal.jacobson]
    exact le_sInf fun J hJ => Finset.inf_le (Finset.mem_univ (⟨J, hJ.2⟩ : ↥{I : Ideal A | I.IsMaximal}))
  have hcrt := crt_bijective (fun i : ↥{I : Ideal A | I.IsMaximal} => i.1 ^ N) hcop hinf

  refine bijective_thetaₗ_of_injective _ (injective_thetaₗ_of_forall_factor (K := K) (Δb g b) hbal
    (ι := ↥{I : Ideal A | I.IsMaximal}) (fun i => i.1) N hcrt ?_)
  rintro ⟨𝔫, h𝔫max⟩ χ hχ hθ
  haveI : 𝔫.IsMaximal := h𝔫max
  obtain ⟨ξ, hξ⟩ := exists_point_of_isMaximal g 𝔫
  exact functional_eq_zero_of_forall_mem_pow g b hb ξ 𝔫 hξ N hN χ hχ hθ

end Local

end Ws47.CB3

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {m : ℕ} (g : Fin m → MvPolynomial (Fin m) K)
    [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
    (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K)
    (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
      ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j)) :
    Function.Bijective (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) =>
      TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b))))) := by
  have key := Ws47.CB3.bijective_thetaₗ_Δb g b hb
  have hfun : (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) =>
      TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b))))) = ⇑(Ws47.CB3.thetaₗ (K := K) (Ws47.CB3.Δb g b)) := by
    funext φ
    rfl
  rw [hfun]
  exact key

end S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed
end P2MW
export P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed (solution)
