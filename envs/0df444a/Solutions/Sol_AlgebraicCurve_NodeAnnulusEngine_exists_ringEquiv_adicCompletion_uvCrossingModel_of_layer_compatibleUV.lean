-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/54f11189-4162-5566-9c89-31d763e1fbab

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Theorems.Thm_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
import Theorems.Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 400000

p2m_open "IsLocalRing ModularCurve ModularCurve.UVCrossingModel~U_mul_V"

namespace NodeLayerPresentationSol

section Model

variable {W : Type*} [CommRing W]

private theorem _root_.NodeLayerPresentationSol.mk_eq_mk (τ : W) (f : MvPowerSeries (Fin 2) W) :
    UVCrossingModel.mk τ f = Ideal.Quotient.mk (uvCrossingIdeal W τ) f := rfl

p2m_export "NodeLayerPresentationSol" "mk_eq_mk"
theorem U_mul_V (τ : W) : U τ * V τ = const τ τ := by
  rw [U, V, const, ← map_mul, mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

theorem exists_mul_eq_one_of_sub_mem (τ : W) (P Z : MvPowerSeries (Fin 2) W)
    (hP : MvPowerSeries.constantCoeff P = 0)
    (h : P * Z - 1 ∈ uvCrossingIdeal W τ) : ∃ w : W, τ * w = 1 := by
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨Q, hQ⟩ := h
  have := congrArg MvPowerSeries.constantCoeff hQ
  simp only [map_sub, map_mul, hP, zero_mul, map_one, MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_C, mul_zero, zero_sub] at this
  refine ⟨MvPowerSeries.constantCoeff Q, ?_⟩
  linear_combination this

theorem not_isUnit_pow [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) : ¬ IsUnit (π ^ E) := by
  intro h
  exact hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π (by omega)) h)

theorem not_isUnit_U [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) :
    ¬ IsUnit (U (π ^ E)) := by
  rintro ⟨z, hz⟩
  obtain ⟨Z, hZ⟩ := mk_surjective (π ^ E) (↑z⁻¹ : UVCrossingModel W (π ^ E))
  have h1 : U (π ^ E) * UVCrossingModel.mk (π ^ E) Z = 1 := by rw [hZ, ← hz, Units.mul_inv]
  rw [U, ← map_mul, ← map_one (UVCrossingModel.mk (π ^ E)), mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq] at h1
  obtain ⟨w, hw⟩ := exists_mul_eq_one_of_sub_mem (π ^ E) _ Z (MvPowerSeries.constantCoeff_X 0) h1
  exact not_isUnit_pow hπ hE (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)

theorem not_isUnit_V [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) :
    ¬ IsUnit (V (π ^ E)) := by
  rintro ⟨z, hz⟩
  obtain ⟨Z, hZ⟩ := mk_surjective (π ^ E) (↑z⁻¹ : UVCrossingModel W (π ^ E))
  have h1 : V (π ^ E) * UVCrossingModel.mk (π ^ E) Z = 1 := by rw [hZ, ← hz, Units.mul_inv]
  rw [V, ← map_mul, ← map_one (UVCrossingModel.mk (π ^ E)), mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq] at h1
  obtain ⟨w, hw⟩ := exists_mul_eq_one_of_sub_mem (π ^ E) _ Z (MvPowerSeries.constantCoeff_X 1) h1
  exact not_isUnit_pow hπ hE (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)

theorem not_isUnit_const [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) :
    ¬ IsUnit (const (π ^ E) π) := by
  rintro ⟨z, hz⟩
  obtain ⟨Z, hZ⟩ := mk_surjective (π ^ E) (↑z⁻¹ : UVCrossingModel W (π ^ E))
  have h1 : const (π ^ E) π * UVCrossingModel.mk (π ^ E) Z = 1 := by rw [hZ, ← hz, Units.mul_inv]
  rw [const, ← map_mul, ← map_one (UVCrossingModel.mk (π ^ E)), mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at h1
  obtain ⟨Q, hQ⟩ := h1
  have := congrArg MvPowerSeries.constantCoeff hQ
  simp only [map_sub, map_mul, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C,
    zero_mul, zero_sub] at this
  apply hπ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨MvPowerSeries.constantCoeff Z + π ^ (E - 1) * MvPowerSeries.constantCoeff Q, ?_⟩
  have hE' : π ^ E = π * π ^ (E - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hE'] at this
  linear_combination this

theorem eq_zero_of_const_eq_zero [IsNoetherianRing W] [IsLocalRing W] {τ : W} (hτ : ¬ IsUnit τ) (w : W)
    (h : const τ w = 0) : w = 0 := by
  rw [const, mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  obtain ⟨Q, hQ⟩ := h
  set d : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hd
  have hXX : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) = MvPowerSeries.monomial d 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul]

  have hcoeffXX : ∀ n : ℕ, MvPowerSeries.coeff ((n + 1) • d) (MvPowerSeries.X 0 * MvPowerSeries.X 1 * Q) =
      MvPowerSeries.coeff (n • d) Q := by
    intro n
    rw [hXX, MvPowerSeries.coeff_monomial_mul, if_pos (by rw [succ_nsmul]; exact le_add_self), one_mul,
      show (n + 1) • d - d = n • d by rw [succ_nsmul, add_tsub_cancel_right]]
  have hcoeffXX0 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (MvPowerSeries.X 0 * MvPowerSeries.X 1 * Q) = 0 := by
    rw [hXX, MvPowerSeries.coeff_monomial_mul, if_neg]
    intro hle; have := hle 0; simp [hd, Finsupp.add_apply] at this
  have hstep : ∀ n : ℕ, MvPowerSeries.coeff (n • d) Q = τ * MvPowerSeries.coeff ((n + 1) • d) Q := by
    intro n
    have := congrArg (MvPowerSeries.coeff ((n + 1) • d)) hQ
    rw [MvPowerSeries.coeff_C, if_neg (by
        intro h0
        have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h0
        simp [hd, Finsupp.add_apply] at this), sub_mul, map_sub, hcoeffXX,
      MvPowerSeries.coeff_C_mul] at this
    linear_combination -this
  have h0 : w = -(τ * MvPowerSeries.coeff (0 • d) Q) := by
    have := congrArg (MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ)) hQ
    rw [MvPowerSeries.coeff_C, if_pos rfl, sub_mul, map_sub, hcoeffXX0, MvPowerSeries.coeff_C_mul, zero_sub] at this
    rw [zero_nsmul]; exact this
  have hpow : ∀ n : ℕ, MvPowerSeries.coeff (0 • d) Q = τ ^ n * MvPowerSeries.coeff (n • d) Q := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_mul]
    | succ n ih => rw [ih, hstep n, pow_succ, mul_assoc]
  have hmem : w ∈ ⨅ n : ℕ, (Ideal.span {τ} : Ideal W) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [h0, hpow n, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨-(τ * MvPowerSeries.coeff (n • d) Q), by ring⟩
  have hne : (Ideal.span {τ} : Ideal W) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hτ
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne] at hmem
  simpa using hmem

noncomputable def freePart (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun m => if m 0 = 0 then MvPowerSeries.coeff m f else 0

noncomputable def quotPart (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun m => MvPowerSeries.coeff (m + Finsupp.single 0 1) f

theorem coeff_X_mul' (s : Fin 2) (g : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (MvPowerSeries.X s * g) =
      if m s = 0 then 0 else MvPowerSeries.coeff (m - Finsupp.single s 1) g := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases hm : m s = 0
  · rw [if_pos hm, if_neg]
    intro hle
    have := hle s
    rw [Finsupp.single_eq_same, hm] at this
    omega
  · rw [if_neg hm, if_pos, one_mul]
    intro t
    rw [Finsupp.single_apply]
    split_ifs with hts
    · subst hts; omega
    · exact Nat.zero_le _

theorem eq_X_mul_quotPart_add_freePart (f : MvPowerSeries (Fin 2) W) :
    f = MvPowerSeries.X 0 * quotPart f + freePart f := by
  ext m
  rw [map_add, coeff_X_mul']
  change _ = _ + (if m 0 = 0 then MvPowerSeries.coeff m f else 0)
  by_cases hm : m 0 = 0
  · rw [if_pos hm, if_pos hm, zero_add]
  · rw [if_neg hm, if_neg hm, add_zero]
    change _ = MvPowerSeries.coeff (m - Finsupp.single 0 1 + Finsupp.single 0 1) f
    have hm' : m - Finsupp.single 0 1 + Finsupp.single 0 1 = m := by
      ext t
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hts
      · subst hts; omega
      · omega
    rw [hm']

theorem exists_eq_X_mul_add_X_mul_of_constantCoeff_eq_zero (f : MvPowerSeries (Fin 2) W)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ∃ g₀ g₁ : MvPowerSeries (Fin 2) W, f = MvPowerSeries.X 0 * g₀ + MvPowerSeries.X 1 * g₁ := by
  have h0 := eq_X_mul_quotPart_add_freePart f
  have hdvd : MvPowerSeries.X (1 : Fin 2) ∣ freePart f := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm1
    change (if m 0 = 0 then MvPowerSeries.coeff m f else 0) = 0
    split_ifs with hm0
    · have hm : m = 0 := by
        ext t; fin_cases t
        · exact hm0
        · exact hm1
      rw [hm, MvPowerSeries.coeff_zero_eq_constantCoeff]
      exact hf
    · rfl
  obtain ⟨g₁, hg₁⟩ := hdvd
  exact ⟨quotPart f, g₁, by rw [← hg₁]; exact h0⟩

theorem mem_span_of_not_isUnit [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π)
    {E : ℕ} (hE : 1 ≤ E) [IsLocalRing (UVCrossingModel W (π ^ E))]
    (m : UVCrossingModel W (π ^ E)) (hm : ¬ IsUnit m) :
    m ∈ Ideal.span {const (π ^ E) π, U (π ^ E), V (π ^ E)} := by
  obtain ⟨f, rfl⟩ := mk_surjective (π ^ E) m
  set f₀ := MvPowerSeries.constantCoeff f with hf₀
  obtain ⟨g₀, g₁, hg⟩ := exists_eq_X_mul_add_X_mul_of_constantCoeff_eq_zero (f - MvPowerSeries.C f₀)
    (by rw [map_sub, MvPowerSeries.constantCoeff_C, hf₀, sub_self])
  have hf : UVCrossingModel.mk (π ^ E) f =
      const (π ^ E) f₀ + U (π ^ E) * UVCrossingModel.mk (π ^ E) g₀ + V (π ^ E) * UVCrossingModel.mk (π ^ E) g₁ := by
    have : f = MvPowerSeries.C f₀ + (MvPowerSeries.X 0 * g₀ + MvPowerSeries.X 1 * g₁) := by
      rw [← hg]; ring
    rw [this, map_add, map_add, map_mul, map_mul]
    simp only [const, U, V]
    ring
  by_cases hu : IsUnit f₀
  · exfalso
    apply hm
    rw [hf, add_assoc]
    have h1 : IsUnit (const (π ^ E) f₀) := hu.map (constHom (π ^ E))
    have h2 : U (π ^ E) * UVCrossingModel.mk (π ^ E) g₀ + V (π ^ E) * UVCrossingModel.mk (π ^ E) g₁ ∈
        maximalIdeal (UVCrossingModel W (π ^ E)) :=
      add_mem (Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr (not_isUnit_U hπ hE)))
        (Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr (not_isUnit_V hπ hE)))
    obtain ⟨c, hc⟩ := h1
    have : (c : UVCrossingModel W (π ^ E)) +
        (U (π ^ E) * UVCrossingModel.mk (π ^ E) g₀ + V (π ^ E) * UVCrossingModel.mk (π ^ E) g₁) =
        c * (1 + ↑c⁻¹ * (U (π ^ E) * UVCrossingModel.mk (π ^ E) g₀ + V (π ^ E) * UVCrossingModel.mk (π ^ E) g₁)) := by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    rw [← hc, this]
    refine (Units.isUnit c).mul ?_
    have hj := (maximalIdeal_le_jacobson (⊥ : Ideal (UVCrossingModel W (π ^ E))))
      (Ideal.mul_mem_left _ (↑c⁻¹) h2)
    rw [Ideal.mem_jacobson_bot] at hj
    simpa [mul_one, add_comm] using hj 1
  · have hmem : f₀ ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hu
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    rw [hf, hw]
    have : const (π ^ E) (π * w) = const (π ^ E) π * const (π ^ E) w := by
      rw [const, const, const, ← map_mul, ← map_mul]
    rw [this]
    refine add_mem (add_mem ?_ ?_) ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

end Model

section Dense

theorem exists_ringHom_extend {C W N : Type*} [CommRing C] [CommRing W] [CommRing N] [IsLocalRing N]
    (cst : C →+* N) (ϖ : C) (hϖ : cst ϖ ∈ maximalIdeal N) (π : W) (j : C →+* W)
    (hjinj : ∀ (n : ℕ) (c : C), j c ∈ Ideal.span {π ^ n} → c ∈ Ideal.span {ϖ ^ n})
    (hjsur : ∀ (n : ℕ) (w : W), ∃ c : C, w - j c ∈ Ideal.span {π ^ n}) :
    ∃ σ : W →+* AdicCompletion (maximalIdeal N) N,
      ∀ c : C, σ (j c) = algebraMap N (AdicCompletion (maximalIdeal N) N) (cst c) := by
  set 𝔪 : Ideal N := maximalIdeal N with h𝔪

  have key : ∀ (n : ℕ) (c c' : C), j c - j c' ∈ Ideal.span {π ^ n} →
      Ideal.Quotient.mk (𝔪 ^ n) (cst c) = Ideal.Quotient.mk (𝔪 ^ n) (cst c') := by
    intro n c c' h
    rw [Ideal.Quotient.eq, ← map_sub]
    have : c - c' ∈ Ideal.span {ϖ ^ n} := hjinj n _ (by rw [map_sub]; exact h)
    rw [Ideal.mem_span_singleton] at this
    obtain ⟨d, hd⟩ := this
    rw [hd, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖ n)
  choose apx hapx using hjsur

  have hwd : ∀ (n : ℕ) (w : W) (c : C), w - j c ∈ Ideal.span {π ^ n} →
      Ideal.Quotient.mk (𝔪 ^ n) (cst (apx n w)) = Ideal.Quotient.mk (𝔪 ^ n) (cst c) := by
    intro n w c hc
    apply key
    have : j (apx n w) - j c = (w - j c) - (w - j (apx n w)) := by ring
    rw [this]
    exact sub_mem hc (hapx n w)
  let σn : ∀ n : ℕ, W →+* N ⧸ 𝔪 ^ n := fun n =>
    { toFun := fun w => Ideal.Quotient.mk (𝔪 ^ n) (cst (apx n w))
      map_one' := by
        rw [hwd n 1 1 (by rw [_root_.map_one, sub_self]; exact zero_mem _), _root_.map_one, _root_.map_one]
      map_mul' := fun w₁ w₂ => by
        rw [← map_mul, ← map_mul]
        apply hwd
        have : w₁ * w₂ - j (apx n w₁ * apx n w₂) =
            w₁ * (w₂ - j (apx n w₂)) + (w₁ - j (apx n w₁)) * j (apx n w₂) := by rw [map_mul]; ring
        rw [this]
        exact add_mem (Ideal.mul_mem_left _ _ (hapx n w₂)) (Ideal.mul_mem_right _ _ (hapx n w₁))
      map_zero' := by
        rw [hwd n 0 0 (by rw [_root_.map_zero, sub_self]; exact zero_mem _), _root_.map_zero, _root_.map_zero]
      map_add' := fun w₁ w₂ => by
        rw [← map_add, ← map_add]
        apply hwd
        have : w₁ + w₂ - j (apx n w₁ + apx n w₂) = (w₁ - j (apx n w₁)) + (w₂ - j (apx n w₂)) := by
          rw [map_add]; ring
        rw [this]
        exact add_mem (hapx n w₁) (hapx n w₂) }
  have hσn : ∀ (n : ℕ) (w : W), σn n w = Ideal.Quotient.mk (𝔪 ^ n) (cst (apx n w)) := fun n w => rfl
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow 𝔪 hle).comp (σn n) = σn m := by
    intro m n hle
    apply RingHom.ext
    intro w
    change Ideal.Quotient.factorPow 𝔪 hle (Ideal.Quotient.mk (𝔪 ^ n) (cst (apx n w))) =
      Ideal.Quotient.mk (𝔪 ^ m) (cst (apx m w))
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    symm
    apply hwd
    have hle' : Ideal.span {π ^ n} ≤ Ideal.span {π ^ m} :=
      Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π hle)
    exact hle' (hapx n w)
  refine ⟨AdicCompletion.liftRingHom 𝔪 σn hcompat, fun c => ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [AdicCompletion.evalₐ_liftRingHom, hσn, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of]
  exact hwd n (j c) c (by rw [sub_self]; exact zero_mem _)

end Dense

section Lift

p2m_open "Ideal Quotient Ideal.Quotient AdicCompletion"

theorem factorPow_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨r, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk I hle r]

theorem exists_ringHom_adicCompletion_comp_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {S : Type*} [CommRing S] [IsLocalRing S] [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (f : R →+* S) (hf : ∀ x ∈ IsLocalRing.maximalIdeal R, f x ∈ IsLocalRing.maximalIdeal S) :
    ∃ g : AdicCompletion (IsLocalRing.maximalIdeal R) R →+* S,
      g.comp (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = f := by
  set mR : Ideal R := IsLocalRing.maximalIdeal R with hmR
  set mS : Ideal S := IsLocalRing.maximalIdeal S with hmS
  have hmap : Ideal.map f mR ≤ mS := Ideal.map_le_iff_le_comap.mpr fun x hx => hf x hx
  have hpow : ∀ n : ℕ, mR ^ n ≤ (mS ^ n).comap f := by
    intro n
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmap n
  let fam : (n : ℕ) → AdicCompletion mR R →+* S ⧸ mS ^ n := fun n =>
    (Ideal.quotientMap (mS ^ n) f (hpow n)).comp (evalₐ mR n : AdicCompletion mR R →+* R ⧸ mR ^ n)
  have hfam : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow mS hle).comp (fam n) = fam m := by
    intro m n hle
    apply RingHom.ext
    intro x
    change Ideal.Quotient.factorPow mS hle (Ideal.quotientMap (mS ^ n) f (hpow n) (evalₐ mR n x)) =
      Ideal.quotientMap (mS ^ m) f (hpow m) (evalₐ mR m x)
    rw [← factorPow_evalₐ mR hle x]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ mR n x)
    rw [← hr, Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]
  let g : AdicCompletion mR R →+* S := IsAdicComplete.liftRingHom mS fam hfam
  have hg : ∀ x : R, g (algebraMap R (AdicCompletion mR R) x) = f x := by
    intro x
    refine (IsHausdorff.eq_iff_smodEq (I := mS)).mpr fun n => ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
    change Ideal.Quotient.mk (mS ^ n) (IsAdicComplete.liftRingHom mS fam hfam _) = _
    rw [IsAdicComplete.mk_liftRingHom, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    change Ideal.quotientMap (mS ^ n) f (hpow n) (evalₐ mR n (of mR R x)) = _
    rw [evalₐ_of, Ideal.quotientMap_mk]
  exact ⟨g, RingHom.ext hg⟩

end Lift

end NodeLayerPresentationSol

open NodeLayerPresentationSol in

theorem solution
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (ϖ : L) (hϖ𝒩₀ : algebraMap L F ϖ ∈ 𝒩₀)

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F ϖ, hϖ𝒩₀⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)

    (x y : F) (hx : x ∈ 𝒩₀) (hy : y ∈ 𝒩₀)
    (hιx : ∃ β : UVCrossingModel W (π ^ E), IsUnit β ∧
      ι (algebraMap ↥𝒩₀ _ ⟨x, hx⟩) - U (π ^ E) * β ∈ Ideal.span {const (π ^ E) π})
    (hιy : ∃ β : UVCrossingModel W (π ^ E), IsUnit β ∧
      ι (algebraMap ↥𝒩₀ _ ⟨y, hy⟩) - V (π ^ E) * β ∈ Ideal.span {const (π ^ E) π})

    (C' : Subring L) (ϖ' : ↥C')
    (e : ℕ) (hϖe : ∃ v : L, v ∈ C' ∧ v⁻¹ ∈ C' ∧ ϖ = v * ((ϖ' : ↥C') : L) ^ e)

    (𝒩₀' : Subring F) [IsLocalRing ↥𝒩₀'] [IsNoetherianRing ↥𝒩₀'] (h01 : 𝒩₀ ≤ 𝒩₀')
    (hloc : ∀ f : ↥𝒩₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h01 f))
    (hC'mem : ∀ c : L, c ∈ C' → algebraMap L F c ∈ 𝒩₀')
    (hres' : ∀ g : ↥𝒩₀', ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ 𝒩₀'), ¬ IsUnit (g - ⟨_, h⟩))
    (hgen' : maximalIdeal ↥𝒩₀' ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) ⊔
      Ideal.span {⟨algebraMap L F (ϖ' : L), hC'mem _ ϖ'.2⟩})
    (hdim : 2 ≤ ringKrullDim ↥𝒩₀')

    {W' : Type*} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] [IsAdicComplete (maximalIdeal W') W']
    (π' : W') (hπ' : Irreducible π') (j : ↥C' →+* W') (hjϖ : j ϖ' = π')
    (hjinj : ∀ (n : ℕ) (c : ↥C'), j c ∈ Ideal.span {π' ^ n} → c ∈ Ideal.span {ϖ' ^ n})
    (hjsur : ∀ (n : ℕ) (w : W'), ∃ c : ↥C', w - j c ∈ Ideal.span {π' ^ n}) :
    ∃ (σ' : W' →+* AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')
      (ι' : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' ≃+* UVCrossingModel W' (π' ^ (e * E))),

      (∀ c : ↥C', σ' (j c) = algebraMap ↥𝒩₀' _ ⟨algebraMap L F (c : L), hC'mem _ c.2⟩) ∧
      (∀ o : W', ι' (σ' o) = const (π' ^ (e * E)) o) ∧

      maximalIdeal ↥𝒩₀' =
        Ideal.span {⟨algebraMap L F (ϖ' : L), hC'mem _ ϖ'.2⟩, ⟨x, h01 hx⟩, ⟨y, h01 hy⟩} ∧

      (∃ β : UVCrossingModel W' (π' ^ (e * E)), IsUnit β ∧
        ι' (algebraMap ↥𝒩₀' _ ⟨x, h01 hx⟩) - U (π' ^ (e * E)) * β ∈ Ideal.span {const (π' ^ (e * E)) π'}) ∧
      (∃ β : UVCrossingModel W' (π' ^ (e * E)), IsUnit β ∧
        ι' (algebraMap ↥𝒩₀' _ ⟨y, h01 hy⟩) - V (π' ^ (e * E)) * β ∈ Ideal.span {const (π' ^ (e * E)) π'}) ∧

      (∃ (θ : UVCrossingModel W (π ^ E) →+* UVCrossingModel W' (π' ^ (e * E))) (βU βV : UVCrossingModel W' (π' ^ (e * E))), IsUnit βU ∧ IsUnit βV ∧
        θ (U (π ^ E)) = βU * U (π' ^ (e * E)) ∧
        θ (V (π ^ E)) = βV * V (π' ^ (e * E)) ∧
        (∀ (f : F) (hf : f ∈ 𝒩₀), ι' (algebraMap ↥𝒩₀' _ ⟨f, h01 hf⟩) = θ (ι (algebraMap ↥𝒩₀ _ ⟨f, hf⟩)))) := by
  classical

  haveI hT0noe : IsNoetherianRing (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  haveI : Nontrivial (UVCrossingModel W (π ^ E)) := ι.symm.toEquiv.nontrivial
  haveI hMloc : IsLocalRing (UVCrossingModel W (π ^ E)) := IsLocalRing.of_surjective' ι.toRingHom ι.surjective
  have hpM : ¬ IsUnit (const (π ^ E) π) := not_isUnit_const hπ hE
  have huM : ¬ IsUnit (U (π ^ E)) := not_isUnit_U hπ hE
  have hvM : ¬ IsUnit (V (π ^ E)) := not_isUnit_V hπ hE
  obtain ⟨βx, hβx, hβxmem⟩ := hιx
  obtain ⟨βy, hβy, hβymem⟩ := hιy

  set ϖ0 : ↥𝒩₀ := ⟨algebraMap L F ϖ, hϖ𝒩₀⟩ with hϖ0def
  set x0 : ↥𝒩₀ := ⟨x, hx⟩ with hx0def
  set y0 : ↥𝒩₀ := ⟨y, hy⟩ with hy0def

  set ut : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ := ι.symm (U (π ^ E)) with hut
  set vt : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ := ι.symm (V (π ^ E)) with hvt
  have hιsymm_const : ∀ o : W, ι.symm (const (π ^ E) o) = σ o := by
    intro o; rw [← hconst, RingEquiv.symm_apply_apply]
  have hσπ' : σ π = algebraMap ↥𝒩₀ _ ϖ0 := hσπ
  have hconstpow : const (π ^ E) (π ^ E) = (const (π ^ E) π) ^ E := by
    simp only [const, map_pow]
  have huv : ut * vt = (algebraMap ↥𝒩₀ _ ϖ0) ^ E := by
    rw [hut, hvt, ← map_mul, U_mul_V, hconstpow, map_pow, hιsymm_const, hσπ']

  have hunit_reflect : ∀ a : ↥𝒩₀, ¬ IsUnit (ι (algebraMap ↥𝒩₀ _ a)) → ¬ IsUnit a := by
    intro a ha hu
    exact ha ((hu.map (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀))).map ι)
  have hmem_of_sub_mem : ∀ (z g : UVCrossingModel W (π ^ E)), ¬ IsUnit g →
      z - g ∈ Ideal.span {const (π ^ E) π} → ¬ IsUnit z := by
    intro z g hg hz hzunit
    have h1 : z - g ∈ maximalIdeal _ := by
      refine (Ideal.span_le.mpr ?_) hz
      rintro w rfl
      exact (mem_maximalIdeal _).mpr hpM
    have h2 : g ∈ maximalIdeal _ := (mem_maximalIdeal _).mpr hg
    have : z ∈ maximalIdeal _ := by
      have := add_mem h1 h2; simpa using this
    exact (mem_maximalIdeal _).mp this hzunit
  have hϖ0nu : ¬ IsUnit ϖ0 := by
    apply hunit_reflect
    rw [← hσπ', hconst]
    exact hpM
  have hx0nu : ¬ IsUnit x0 := by
    apply hunit_reflect
    exact hmem_of_sub_mem _ _ (fun h => huM (isUnit_of_mul_isUnit_left h)) hβxmem
  have hy0nu : ¬ IsUnit y0 := by
    apply hunit_reflect
    exact hmem_of_sub_mem _ _ (fun h => hvM (isUnit_of_mul_isUnit_left h)) hβymem

  have hϖne : algebraMap L F ϖ ≠ 0 := by
    intro h0
    have hϖ00 : ϖ0 = 0 := Subtype.ext h0
    have hc0 : const (π ^ E) π = 0 := by rw [← hconst, hσπ', hϖ00, map_zero, map_zero]
    exact hπ.ne_zero (eq_zero_of_const_eq_zero (not_isUnit_pow hπ hE) π hc0)

  set incl : ↥𝒩₀ →+* ↥𝒩₀' := Subring.inclusion h01 with hincl
  let cst : ↥C' →+* ↥𝒩₀' :=
    { toFun := fun c => ⟨algebraMap L F (c : L), hC'mem _ c.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hcst : ∀ c : ↥C', cst c = ⟨algebraMap L F (c : L), hC'mem _ c.2⟩ := fun c => rfl
  set ϖN : ↥𝒩₀' := ⟨algebraMap L F ((ϖ' : ↥C') : L), hC'mem _ ϖ'.2⟩ with hϖNdef
  have hcstϖ : cst ϖ' = ϖN := rfl
  set xN : ↥𝒩₀' := ⟨x, h01 hx⟩ with hxNdef
  set yN : ↥𝒩₀' := ⟨y, h01 hy⟩ with hyNdef
  have hinclx : incl x0 = xN := rfl
  have hincly : incl y0 = yN := rfl
  obtain ⟨v, hvC', hvinvC', hϖv⟩ := hϖe
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hϖne (by rw [hϖv, zero_mul, map_zero])
  set vN : ↥𝒩₀' := ⟨algebraMap L F v, hC'mem _ hvC'⟩ with hvNdef
  have hvNunit : IsUnit vN := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap L F v⁻¹, hC'mem _ hvinvC'⟩, ?_⟩
    ext
    change algebraMap L F v * algebraMap L F v⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hv0, map_one]
  have hinclϖ : incl ϖ0 = vN * ϖN ^ e := by
    ext
    change algebraMap L F ϖ = algebraMap L F v * (algebraMap L F ((ϖ' : ↥C') : L)) ^ e
    rw [hϖv, map_mul, map_pow]
  have hinclϖnu : ¬ IsUnit (incl ϖ0) := hloc ϖ0 hϖ0nu
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he0 | he0
    · exfalso
      apply hinclϖnu
      rw [hinclϖ, he0, pow_zero, mul_one]
      exact hvNunit
    · exact he0
  have hϖNnu : ¬ IsUnit ϖN := by
    intro h
    apply hinclϖnu
    rw [hinclϖ]
    exact hvNunit.mul (h.pow e)
  have hϖNmem : ϖN ∈ maximalIdeal ↥𝒩₀' := (mem_maximalIdeal _).mpr hϖNnu
  have hxNnu : ¬ IsUnit xN := hloc x0 hx0nu
  have hyNnu : ¬ IsUnit yN := hloc y0 hy0nu
  have heE : 1 ≤ e * E := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

  haveI hTnoe : IsNoetherianRing (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  haveI hTcomplete : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀'))
      (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal ↥𝒩₀') (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')).mpr
      (AdicCompletion.isAdicComplete AdicCompletion.maximalIdeal_fg)
  have h𝔪T : maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') =
      (maximalIdeal ↥𝒩₀').map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) :=
    AdicCompletion.maximalIdeal_eq_map
  have halg_mem : ∀ g : ↥𝒩₀', ¬ IsUnit g →
      algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') g ∈
        maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := by
    intro g hg
    rw [h𝔪T]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hg)

  obtain ⟨σ', hσ'j⟩ := exists_ringHom_extend cst ϖ' (by rw [hcstϖ]; exact hϖNmem) π' j hjinj hjsur
  have hσ'π' : σ' π' = algebraMap ↥𝒩₀' _ ϖN := by rw [← hjϖ, hσ'j, hcstϖ]
  letI : Algebra W' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := σ'.toAlgebra
  have halgW' : ∀ o : W', algebraMap W' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') o = σ' o := fun o => rfl

  set f : ↥𝒩₀ →+* AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' :=
    (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')).comp incl with hfdef
  have hf_apply : ∀ a : ↥𝒩₀, f a = algebraMap ↥𝒩₀' _ (incl a) := fun a => rfl
  have hf_loc : ∀ a ∈ maximalIdeal ↥𝒩₀, f a ∈ maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := by
    intro a ha
    rw [hf_apply]
    exact halg_mem _ (hloc a ((mem_maximalIdeal _).mp ha))
  obtain ⟨lam, hlam⟩ := exists_ringHom_adicCompletion_comp_eq f hf_loc
  have hlam_apply : ∀ a : ↥𝒩₀, lam (algebraMap ↥𝒩₀ _ a) = algebraMap ↥𝒩₀' _ (incl a) := by
    intro a
    have := congrArg (fun φ : ↥𝒩₀ →+* _ => φ a) hlam
    simpa [hf_apply] using this

  have h𝔪T0 : maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) =
      (maximalIdeal ↥𝒩₀).map (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)) :=
    AdicCompletion.maximalIdeal_eq_map
  have hlam_loc : ∀ t ∈ maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀),
      lam t ∈ maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := by
    intro t ht
    rw [h𝔪T0] at ht
    have : (maximalIdeal ↥𝒩₀).map (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)) ≤
        (maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')).comap lam := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap, hlam_apply]
      exact halg_mem _ (hloc a ((mem_maximalIdeal _).mp ha))
    exact this ht

  set uT : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' := lam ut with huT
  set vT : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' := lam vt with hvT
  have huTmem : uT ∈ maximalIdeal _ := by
    apply hlam_loc
    refine (mem_maximalIdeal _).mpr fun h => huM ?_
    have := h.map ι
    rwa [hut, RingEquiv.apply_symm_apply] at this
  have hvTmem : vT ∈ maximalIdeal _ := by
    apply hlam_loc
    refine (mem_maximalIdeal _).mpr fun h => hvM ?_
    have := h.map ι
    rwa [hvt, RingEquiv.apply_symm_apply] at this

  have hlamϖ : lam (algebraMap ↥𝒩₀ _ ϖ0) = algebraMap ↥𝒩₀' _ vN * (σ' π') ^ e := by
    rw [hlam_apply, hinclϖ, map_mul, map_pow, hσ'π']
  set v' : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' := (algebraMap ↥𝒩₀' _ vN) ^ E with hv'
  have hv'unit : IsUnit v' := (hvNunit.map _).pow E
  have hrelT : uT * vT = (σ' π') ^ (e * E) * v' := by
    rw [huT, hvT, ← map_mul, huv, map_pow, hlamϖ, mul_pow, ← pow_mul, hv', mul_comm]

  have h𝔪M : ∀ t : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀, t ∈ maximalIdeal _ →
      t ∈ Ideal.span {algebraMap ↥𝒩₀ _ ϖ0, ut, vt} := by
    intro t ht
    have hnu : ¬ IsUnit (ι t) := fun h => (mem_maximalIdeal _).mp ht (by
      have := h.map ι.symm; rwa [RingEquiv.symm_apply_apply] at this)
    have hmem := mem_span_of_not_isUnit hπ hE (ι t) hnu
    have : t = ι.symm (ι t) := (RingEquiv.symm_apply_apply ι t).symm
    rw [this]
    have hmap : (Ideal.span {const (π ^ E) π, U (π ^ E), V (π ^ E)}).map (ι.symm : _ →+* _) =
        Ideal.span {algebraMap ↥𝒩₀ _ ϖ0, ut, vt} := by
      rw [Ideal.map_span]
      congr 1
      ext w
      simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [RingHom.coe_coe, hιsymm_const, hσπ']
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hmem
  have hgenT : maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ≤
      Ideal.span {uT, vT} ⊔ Ideal.span {σ' π'} := by
    rw [h𝔪T, Ideal.map_le_iff_le_comap]
    intro g hg
    have hg' := hgen' hg
    rw [Ideal.mem_comap]

    rw [Submodule.mem_sup] at hg'
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hg'
    rw [map_add]
    refine add_mem ?_ ?_
    ·
      have hle : (maximalIdeal ↥𝒩₀).map incl ≤
          (Ideal.span {uT, vT} ⊔ Ideal.span {σ' π'}).comap
            (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, Ideal.mem_comap, ← hlam_apply]
        have hat : algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) a ∈ maximalIdeal _ := by
          rw [h𝔪T0]; exact Ideal.mem_map_of_mem _ ha
        have := h𝔪M _ hat
        rw [Ideal.mem_span_insert] at this
        obtain ⟨c₀, z, hz, hz'⟩ := this
        rw [Ideal.mem_span_pair] at hz
        obtain ⟨c₁, c₂, rfl⟩ := hz
        rw [hz', map_add, map_mul, map_add, map_mul, map_mul, hlamϖ]
        refine add_mem ?_ ?_
        · refine Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ?_))
          have : (σ' π') ^ e = σ' π' * (σ' π') ^ (e - 1) := by rw [← pow_succ']; congr 1; omega
          rw [this]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
        · refine Ideal.mem_sup_left (add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp [huT])))
            (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp [hvT]))))
      exact hle hg₁
    · rw [Ideal.mem_span_singleton] at hg₂
      obtain ⟨d, rfl⟩ := hg₂
      rw [map_mul, ← hσ'π']
      exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

  have hresT : Function.Surjective
      (⇑(IsLocalRing.residue (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) ∘
        ⇑(algebraMap W' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀'))) := by
    intro r
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨g, m, hm, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add (maximalIdeal ↥𝒩₀')
      AdicCompletion.maximalIdeal_fg 1 t
    obtain ⟨c, hc, hnu⟩ := hres' g
    refine ⟨j c, ?_⟩
    change IsLocalRing.residue _ (algebraMap W' _ (j c)) = IsLocalRing.residue _ (algebraMap ↥𝒩₀' _ g + m)
    rw [halgW', hσ'j, hcst, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have h1 : algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')
        (⟨algebraMap L F (c : L), hC'mem _ c.2⟩ - g) ∈ maximalIdeal _ := by
      apply halg_mem
      intro hu
      apply hnu
      have : g - ⟨algebraMap L F (c : L), hc⟩ = -(⟨algebraMap L F (c : L), hC'mem _ c.2⟩ - g) := by ring
      rw [this]
      exact hu.neg
    have h2 : m ∈ maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := by
      rw [h𝔪T]; rw [pow_one] at hm; exact hm
    have : algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ⟨algebraMap L F (c : L), hC'mem _ c.2⟩ -
        (algebraMap ↥𝒩₀' _ g + m) =
        algebraMap ↥𝒩₀' _ (⟨algebraMap L F (c : L), hC'mem _ c.2⟩ - g) - m := by
      rw [map_sub]; ring
    rw [this]
    exact sub_mem h1 h2
  let a : Fin 2 → AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' := ![uT, vT]
  have ha0 : a 0 = uT := rfl
  have ha1 : a 1 = vT := rfl
  have ha : ∀ i, a i ∈ maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := by
    intro i
    fin_cases i
    · exact huTmem
    · exact hvTmem
  have hspan_a : Ideal.span {uT, vT} ≤ Ideal.span (Set.range a) := by
    apply Ideal.span_mono
    rintro w (rfl | rfl)
    · exact ⟨0, ha0⟩
    · exact ⟨1, ha1⟩
  have hπ'mem : σ' π' ∈ (maximalIdeal W').map (algebraMap W' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := by
    rw [← halgW']
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hπ'.not_isUnit)
  have hgen : maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ≤
      Ideal.span (Set.range a) ⊔ maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ^ 2 ⊔
        (maximalIdeal W').map (algebraMap W' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := by
    refine hgenT.trans (sup_le ?_ ?_)
    · exact hspan_a.trans (le_sup_left.trans le_sup_left)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_sup_right hπ'mem
  obtain ⟨ψ, hψX, hψsurj⟩ :=
    IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span hresT a ha hgen
  set θ : MvPowerSeries (Fin 2) W' →+* AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀' := ψ.toRingHom with hθdef
  have hθapp : ∀ q, θ q = ψ q := fun q => rfl
  have hθC : ∀ o : W', θ (MvPowerSeries.C o) = σ' o := by
    intro o
    rw [hθapp, ← halgW', ← ψ.commutes o, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hθX0 : θ (MvPowerSeries.X 0) = uT := by rw [hθapp, hψX 0]; rfl
  have hθX1 : θ (MvPowerSeries.X 1) = vT := by rw [hθapp, hψX 1]; rfl
  have hθsurj : Function.Surjective θ := hψsurj

  have hrel : θ (MvPowerSeries.X 0) * θ (MvPowerSeries.X 1) =
      θ (MvPowerSeries.C π') ^ (e * E) * (hv'unit.unit : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') := by
    rw [hθX0, hθX1, hθC, hrelT, IsUnit.unit_spec]
  have hdimT : 2 ≤ ringKrullDim (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') :=
    IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le _ hdim
  obtain ⟨ι', hι'const, hι'X0, hι'X1⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit π' hπ' (e * E) heE θ
      hθsurj hv'unit.unit hrel hdimT
  rw [hθX0] at hι'X0
  rw [hθX1] at hι'X1
  have hconst' : ∀ o : W', ι' (σ' o) = const (π' ^ (e * E)) o := by
    intro o; rw [← hθC]; exact hι'const o

  have hlamϖmem : lam (algebraMap ↥𝒩₀ _ ϖ0) ∈
      Ideal.span {algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ϖN} := by
    rw [hlamϖ, hσ'π']
    have : (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ϖN) ^ e =
        (algebraMap ↥𝒩₀' _ ϖN) ^ (e - 1) * algebraMap ↥𝒩₀' _ ϖN := by
      rw [← pow_succ]; congr 1; omega
    rw [this, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hxT : ∃ b : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀', IsUnit b ∧
      algebraMap ↥𝒩₀' _ xN - uT * b ∈ Ideal.span {algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ϖN} := by
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hβxmem
    have h1 : ι.symm q * σ π = algebraMap ↥𝒩₀ _ x0 - ut * ι.symm βx := by
      have := congrArg ι.symm hq
      rw [map_mul, hιsymm_const, map_sub, map_mul, RingEquiv.symm_apply_apply] at this
      rw [this]
    have h2 := congrArg lam h1
    rw [map_mul, hσπ', map_sub, map_mul, hlam_apply x0] at h2
    refine ⟨lam (ι.symm βx), (hβx.map ι.symm).map lam, ?_⟩
    change algebraMap ↥𝒩₀' _ (incl x0) - lam ut * lam (ι.symm βx) ∈ _
    rw [← h2]
    exact Ideal.mul_mem_left _ _ hlamϖmem
  have hyT : ∃ b : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀', IsUnit b ∧
      algebraMap ↥𝒩₀' _ yN - vT * b ∈ Ideal.span {algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ϖN} := by
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hβymem
    have h1 : ι.symm q * σ π = algebraMap ↥𝒩₀ _ y0 - vt * ι.symm βy := by
      have := congrArg ι.symm hq
      rw [map_mul, hιsymm_const, map_sub, map_mul, RingEquiv.symm_apply_apply] at this
      rw [this]
    have h2 := congrArg lam h1
    rw [map_mul, hσπ', map_sub, map_mul, hlam_apply y0] at h2
    refine ⟨lam (ι.symm βy), (hβy.map ι.symm).map lam, ?_⟩
    change algebraMap ↥𝒩₀' _ (incl y0) - lam vt * lam (ι.symm βy) ∈ _
    rw [← h2]
    exact Ideal.mul_mem_left _ _ hlamϖmem

  set I : Ideal ↥𝒩₀' := Ideal.span {ϖN, xN, yN} with hIdef
  have hIle : I ≤ maximalIdeal ↥𝒩₀' := by
    rw [hIdef, Ideal.span_le]
    rintro w (rfl | rfl | rfl)
    · exact (mem_maximalIdeal _).mpr hϖNnu
    · exact (mem_maximalIdeal _).mpr hxNnu
    · exact (mem_maximalIdeal _).mpr hyNnu
  have hImapϖ : algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ϖN ∈
      I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) :=
    Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hImapx : algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') xN ∈
      I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) :=
    Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hImapy : algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') yN ∈
      I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) :=
    Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hspanϖ_le : Ideal.span {algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ϖN} ≤
      I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hImapϖ
  have huTI : uT ∈ I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := by
    obtain ⟨b, hb, hmem⟩ := hxT
    obtain ⟨bu, rfl⟩ := hb
    have : uT = (algebraMap ↥𝒩₀' _ xN - (algebraMap ↥𝒩₀' _ xN - uT * bu)) * ↑bu⁻¹ := by
      rw [sub_sub_cancel, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (sub_mem hImapx (hspanϖ_le hmem))
  have hvTI : vT ∈ I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := by
    obtain ⟨b, hb, hmem⟩ := hyT
    obtain ⟨bu, rfl⟩ := hb
    have : vT = (algebraMap ↥𝒩₀' _ yN - (algebraMap ↥𝒩₀' _ yN - vT * bu)) * ↑bu⁻¹ := by
      rw [sub_sub_cancel, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (sub_mem hImapy (hspanϖ_le hmem))
  have h𝔪T_le : maximalIdeal (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ≤
      I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := by
    refine hgenT.trans (sup_le ?_ ?_)
    · rw [Ideal.span_le]
      rintro w (rfl | rfl)
      · exact huTI
      · exact hvTI
    · rw [Ideal.span_le, Set.singleton_subset_iff, hσ'π']
      exact hImapϖ
  haveI hff := IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal ↥𝒩₀'
  have hW1 : maximalIdeal ↥𝒩₀' = I := by
    refine le_antisymm ?_ hIle
    intro g hg
    have h1 : algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') g ∈
        I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) :=
      h𝔪T_le (halg_mem g ((mem_maximalIdeal _).mp hg))
    have h2 : g ∈ (I.map (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀'))).comap
        (algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀')) := h1
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at h2

  have hι'ϖspan : ∀ s, s ∈ Ideal.span {algebraMap ↥𝒩₀' (AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') ϖN} →
      ι' s ∈ Ideal.span {const (π' ^ (e * E)) π'} := by
    intro s hs
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    rw [map_mul, ← hσ'π', hconst']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hadx : ∃ β : UVCrossingModel W' (π' ^ (e * E)), IsUnit β ∧
      ι' (algebraMap ↥𝒩₀' _ xN) - U (π' ^ (e * E)) * β ∈ Ideal.span {const (π' ^ (e * E)) π'} := by
    obtain ⟨b, hb, hmem⟩ := hxT
    refine ⟨ι' (hv'unit.unit : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀') * ι' b,
      ((Units.isUnit _).map ι').mul (hb.map ι'), ?_⟩
    have : ι' (algebraMap ↥𝒩₀' _ xN) - U (π' ^ (e * E)) * (ι' ↑hv'unit.unit * ι' b) =
        ι' (algebraMap ↥𝒩₀' _ xN - uT * b) := by
      rw [map_sub, map_mul, hι'X0]; ring
    rw [this]
    exact hι'ϖspan _ hmem
  have hady : ∃ β : UVCrossingModel W' (π' ^ (e * E)), IsUnit β ∧
      ι' (algebraMap ↥𝒩₀' _ yN) - V (π' ^ (e * E)) * β ∈ Ideal.span {const (π' ^ (e * E)) π'} := by
    obtain ⟨b, hb, hmem⟩ := hyT
    refine ⟨ι' b, hb.map ι', ?_⟩
    have : ι' (algebraMap ↥𝒩₀' _ yN) - V (π' ^ (e * E)) * ι' b = ι' (algebraMap ↥𝒩₀' _ yN - vT * b) := by
      rw [map_sub, map_mul, hι'X1]
    rw [this]
    exact hι'ϖspan _ hmem

  have htrans : ∃ (θ : UVCrossingModel W (π ^ E) →+* UVCrossingModel W' (π' ^ (e * E)))
      (βU βV : UVCrossingModel W' (π' ^ (e * E))), IsUnit βU ∧ IsUnit βV ∧
        θ (U (π ^ E)) = βU * U (π' ^ (e * E)) ∧
        θ (V (π ^ E)) = βV * V (π' ^ (e * E)) ∧
        (∀ (f : F) (hf : f ∈ 𝒩₀), ι' (algebraMap ↥𝒩₀' _ ⟨f, h01 hf⟩) = θ (ι (algebraMap ↥𝒩₀ _ ⟨f, hf⟩))) := by
    refine ⟨ι'.toRingHom.comp (lam.comp ι.symm.toRingHom),
      ι' (hv'unit.unit : AdicCompletion (maximalIdeal ↥𝒩₀') ↥𝒩₀'), 1,
      (Units.isUnit _).map ι', isUnit_one, ?_, ?_, ?_⟩
    · change ι' (lam (ι.symm (U (π ^ E)))) = _
      rw [← hut, ← huT, hι'X0]
      exact mul_comm _ _
    · change ι' (lam (ι.symm (V (π ^ E)))) = _
      rw [← hvt, ← hvT, hι'X1, one_mul]
    · intro f hf
      change ι' _ = ι' (lam (ι.symm (ι (algebraMap ↥𝒩₀ _ ⟨f, hf⟩))))
      rw [RingEquiv.symm_apply_apply, hlam_apply]
      rfl

  refine ⟨σ', ι', fun c => hσ'j c, hconst', ?_, hadx, hady, htrans⟩
  rw [hW1]

end S_AlgebraicCurve_NodeAnnulusEngine_exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV (solution)
