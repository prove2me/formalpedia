-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.exists_isUnit_sub_mul_U_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/91c1e85f-d714-57b7-9d9d-a313ba67428f

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_isUnit_sub_mul_U_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 320000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace NodeEndLawSecondSol

section Surgery

variable {W : Type*} [CommRing W]

open MvPowerSeries

noncomputable def freePart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun m => if m s = 0 then MvPowerSeries.coeff m f else 0

noncomputable def quotPart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun m => MvPowerSeries.coeff (m + Finsupp.single s 1) f

theorem coeff_freePart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (freePart s f) = if m s = 0 then MvPowerSeries.coeff m f else 0 := rfl

theorem coeff_quotPart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (quotPart s f) = MvPowerSeries.coeff (m + Finsupp.single s 1) f := rfl

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

theorem eq_X_mul_quotPart_add_freePart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) :
    f = MvPowerSeries.X s * quotPart s f + freePart s f := by
  ext m
  rw [map_add, coeff_X_mul', coeff_freePart, coeff_quotPart]
  by_cases hm : m s = 0
  · rw [if_pos hm, if_pos hm, zero_add]
  · rw [if_neg hm, if_neg hm, add_zero]
    have hm' : m - Finsupp.single s 1 + Finsupp.single s 1 = m := by
      ext t
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hts
      · subst hts; omega
      · omega
    rw [hm']

theorem freePart_free (s : Fin 2) (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) (hm : m s ≠ 0) :
    MvPowerSeries.coeff m (freePart s f) = 0 := by
  rw [coeff_freePart, if_neg hm]

theorem eq_zero_of_X_mul_free (s : Fin 2) (g : MvPowerSeries (Fin 2) W)
    (h : ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m (MvPowerSeries.X s * g) = 0) : g = 0 := by
  ext m
  have := h (m + Finsupp.single s 1) (by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]; omega)
  rw [coeff_X_mul', if_neg (by rw [Finsupp.add_apply, Finsupp.single_eq_same]; omega),
    add_tsub_cancel_right] at this
  simpa using this

theorem free_C_mul (s : Fin 2) (a : W) (r : MvPowerSeries (Fin 2) W)
    (hr : ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m r = 0) :
    ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m (MvPowerSeries.C a * r) = 0 := by
  intro m hm
  rw [MvPowerSeries.coeff_C_mul, hr m hm, mul_zero]

theorem free_X_mul (s t : Fin 2) (hst : t ≠ s) (r : MvPowerSeries (Fin 2) W)
    (hr : ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m r = 0) :
    ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m (MvPowerSeries.X t * r) = 0 := by
  intro m hm
  rw [coeff_X_mul']
  split_ifs with hmt
  · rfl
  · apply hr
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hst]
    omega

theorem free_add (s : Fin 2) (r r' : MvPowerSeries (Fin 2) W)
    (hr : ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m r = 0)
    (hr' : ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m r' = 0) :
    ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 → MvPowerSeries.coeff m (r + r') = 0 := by
  intro m hm
  rw [map_add, hr m hm, hr' m hm, add_zero]

theorem exists_eq_X_mul_add_X_mul_of_constantCoeff_eq_zero (f : MvPowerSeries (Fin 2) W)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ∃ g₀ g₁ : MvPowerSeries (Fin 2) W, f = MvPowerSeries.X 0 * g₀ + MvPowerSeries.X 1 * g₁ := by
  have h0 := eq_X_mul_quotPart_add_freePart 0 f
  have hdvd : MvPowerSeries.X (1 : Fin 2) ∣ freePart 0 f := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm1
    rw [coeff_freePart]
    split_ifs with hm0
    · have hm : m = 0 := by
        ext t; fin_cases t
        · exact hm0
        · exact hm1
      rw [hm, MvPowerSeries.coeff_zero_eq_constantCoeff]
      exact hf
    · rfl
  obtain ⟨g₁, hg₁⟩ := hdvd
  exact ⟨quotPart 0 f, g₁, by rw [← hg₁]; exact h0⟩

theorem eq_single_one_of_apply_zero_eq_zero (m : Fin 2 →₀ ℕ) (hm : m 0 = 0) :
    m = Finsupp.single 1 (m 1) := by
  ext t
  fin_cases t
  · simpa using hm
  · simp

theorem exists_isUnit_and_sub_X_pow_mul_mem [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π)
    (G : MvPowerSeries (Fin 2) W)
    (hG : G ∉ Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)}) :
    ∃ (m : ℕ) (H : MvPowerSeries (Fin 2) W), IsUnit H ∧
      G - MvPowerSeries.X 1 ^ m * H ∈ Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)} := by
  classical

  have hdiv : ∀ a : W, ¬ IsUnit a → ∃ c : W, a = π * c := fun a ha => by
    have hmem : a ∈ maximalIdeal W := (mem_maximalIdeal _).mpr ha
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    exact hmem

  have key : ∃ j : ℕ, IsUnit (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G) := by
    by_contra hall
    push Not at hall
    apply hG
    have hq : ∀ j : ℕ, ∃ c : W, MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G = π * c :=
      fun j => hdiv _ (hall j)
    choose c hc using hq
    set P : MvPowerSeries (Fin 2) W := fun n => if n 0 = 0 then c (n 1) else 0 with hP
    have hfree : freePart 0 G = MvPowerSeries.C π * P := by
      ext n
      rw [coeff_freePart, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply P, hP]
      dsimp only
      split_ifs with h0
      · rw [← hc (n 1), ← eq_single_one_of_apply_zero_eq_zero n h0]
      · rw [mul_zero]
    rw [eq_X_mul_quotPart_add_freePart 0 G, hfree]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  set m := Nat.find key with hmdef
  have hm : IsUnit (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) m) G) := Nat.find_spec key
  have hlt : ∀ j : ℕ, j < m → ¬ IsUnit (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G) :=
    fun j hj => Nat.find_min key hj
  have hq : ∀ j : ℕ, ∃ c : W, j < m → MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G = π * c := by
    intro j
    by_cases hj : j < m
    · obtain ⟨c, hc⟩ := hdiv _ (hlt j hj)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hq
  set Plow : MvPowerSeries (Fin 2) W := fun n => if n 0 = 0 ∧ n 1 < m then c (n 1) else 0 with hPlow
  set H : MvPowerSeries (Fin 2) W :=
    fun n => if n 0 = 0 then MvPowerSeries.coeff (n + Finsupp.single 1 m) G else 0 with hH
  have hs_le : ∀ n : Fin 2 →₀ ℕ, Finsupp.single (1 : Fin 2) m ≤ n ↔ m ≤ n 1 := fun n => Finsupp.single_le_iff
  have hfree : freePart 0 G = MvPowerSeries.C π * Plow + MvPowerSeries.X 1 ^ m * H := by
    ext n
    rw [coeff_freePart, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply Plow, hPlow,
      MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_apply H, hH]
    dsimp only
    by_cases h0 : n 0 = 0
    · rw [if_pos h0]
      by_cases h1 : n 1 < m
      · rw [if_pos ⟨h0, h1⟩, if_neg (by rw [hs_le]; omega), add_zero, ← hc (n 1) h1,
          ← eq_single_one_of_apply_zero_eq_zero n h0]
      · rw [if_neg (fun h => h1 h.2), mul_zero, zero_add, if_pos (by rw [hs_le]; omega), one_mul,
          if_pos (by rw [Finsupp.tsub_apply, h0]; simp),
          tsub_add_cancel_of_le ((hs_le n).mpr (by omega))]
    · rw [if_neg h0, if_neg (fun h => h0 h.1), mul_zero, zero_add]
      split_ifs with h2 h3
      · exfalso
        apply h0
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (by decide)] at h3
        simpa using h3
      · rw [one_mul]
      · rfl
  refine ⟨m, H, ?_, ?_⟩
  · rw [MvPowerSeries.isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_apply H, hH]
    dsimp only
    rw [if_pos (by simp), zero_add]
    exact hm
  · have : G - MvPowerSeries.X 1 ^ m * H = MvPowerSeries.X 0 * quotPart 0 G + MvPowerSeries.C π * Plow := by
      have h := eq_X_mul_quotPart_add_freePart 0 G
      rw [hfree] at h
      linear_combination h
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

end Surgery

section Model

variable {W : Type*} [CommRing W]

theorem mk_eq_mk (τ : W) (f : MvPowerSeries (Fin 2) W) :
    UVCrossingModel.mk τ f = Ideal.Quotient.mk (uvCrossingIdeal W τ) f := rfl

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

theorem not_isUnit_U [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) : ¬ IsUnit (U (π ^ E)) := by
  rintro ⟨z, hz⟩
  obtain ⟨Z, hZ⟩ := mk_surjective (π ^ E) (↑z⁻¹ : UVCrossingModel W (π ^ E))
  have h1 : U (π ^ E) * UVCrossingModel.mk (π ^ E) Z = 1 := by rw [hZ, ← hz, Units.mul_inv]
  rw [U, ← map_mul, ← map_one (UVCrossingModel.mk (π ^ E)), mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq] at h1
  obtain ⟨w, hw⟩ := exists_mul_eq_one_of_sub_mem (π ^ E) _ Z (MvPowerSeries.constantCoeff_X 0) h1
  exact not_isUnit_pow hπ hE (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)

theorem not_isUnit_V [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) : ¬ IsUnit (V (π ^ E)) := by
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

theorem isLocalRing_model [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) {E : ℕ}
    (hE : 1 ≤ E) : IsLocalRing (UVCrossingModel W (π ^ E)) := by
  haveI : Nontrivial (UVCrossingModel W (π ^ E)) := ⟨⟨0, 1, fun h => not_isUnit_U (W := W) hπ hE (by
    haveI := subsingleton_of_zero_eq_one h
    exact isUnit_of_subsingleton _)⟩⟩
  exact IsLocalRing.of_surjective' (UVCrossingModel.mk (π ^ E)) (mk_surjective _)

theorem span_pair_le_maximalIdeal [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E)
    [IsLocalRing (UVCrossingModel W (π ^ E))] :
    Ideal.span {const (π ^ E) π, U (π ^ E)} ≤ maximalIdeal (UVCrossingModel W (π ^ E)) := by
  rw [Ideal.span_le]
  rintro w (rfl | rfl)
  · exact (mem_maximalIdeal _).mpr (not_isUnit_const hπ hE)
  · exact (mem_maximalIdeal _).mpr (not_isUnit_U hπ hE)

theorem mem_span_of_not_isUnit [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) {E : ℕ}
    (hE : 1 ≤ E) [IsLocalRing (UVCrossingModel W (π ^ E))]
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

theorem mem_span_of_X_mul_mem {π : W} {E : ℕ} (hE : 1 ≤ E) (s t : Fin 2) (hst : t ≠ s)
    (z : UVCrossingModel W (π ^ E))
    (h : UVCrossingModel.mk (π ^ E) (MvPowerSeries.X s) * z ∈
      Ideal.span {const (π ^ E) π, UVCrossingModel.mk (π ^ E) (MvPowerSeries.X t)}) :
    z ∈ Ideal.span {const (π ^ E) π, UVCrossingModel.mk (π ^ E) (MvPowerSeries.X t)} := by
  obtain ⟨Z, rfl⟩ := mk_surjective (π ^ E) z
  rw [Ideal.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨A, rfl⟩ := mk_surjective (π ^ E) a
  obtain ⟨B, rfl⟩ := mk_surjective (π ^ E) b
  have hrel : MvPowerSeries.X s * Z - (A * MvPowerSeries.C π + B * MvPowerSeries.X t) ∈ uvCrossingIdeal W (π ^ E) := by
    rw [← Ideal.Quotient.eq]
    change UVCrossingModel.mk (π ^ E) (MvPowerSeries.X s * Z) =
      UVCrossingModel.mk (π ^ E) (A * MvPowerSeries.C π + B * MvPowerSeries.X t)
    rw [map_mul, ← hab, map_add, map_mul, map_mul]
    rfl
  rw [Ideal.mem_span_singleton] at hrel
  obtain ⟨Q, hQ⟩ := hrel
  have hXX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 =
      MvPowerSeries.X s * MvPowerSeries.X t := by
    fin_cases s <;> fin_cases t
    · exact absurd rfl hst
    · rfl
    · exact mul_comm _ _
    · exact absurd rfl hst
  have hE' : (π ^ E : W) = π * π ^ (E - 1) := by rw [← pow_succ']; congr 1; omega
  set A' := A - MvPowerSeries.C (π ^ (E - 1)) * Q with hA'
  set Z' := Z - MvPowerSeries.X t * Q with hZ'
  have key : MvPowerSeries.X s * Z' = MvPowerSeries.C π * A' + MvPowerSeries.X t * B := by
    have : MvPowerSeries.X s * Z = A * MvPowerSeries.C π + B * MvPowerSeries.X t +
        (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (π ^ E)) * Q := by
      rw [← hQ]; ring
    rw [hZ', hA', mul_sub, this, hXX, hE', map_mul]
    ring
  clear_value A' Z'
  have hAd := eq_X_mul_quotPart_add_freePart s A'
  have hBd := eq_X_mul_quotPart_add_freePart s B
  have hzero : MvPowerSeries.X s * (Z' - MvPowerSeries.C π * quotPart s A' - MvPowerSeries.X t * quotPart s B) =
      MvPowerSeries.C π * freePart s A' + MvPowerSeries.X t * freePart s B := by
    linear_combination key + (MvPowerSeries.C π) * hAd + (MvPowerSeries.X t) * hBd
  have hfree : ∀ m : Fin 2 →₀ ℕ, m s ≠ 0 →
      MvPowerSeries.coeff m (MvPowerSeries.C π * freePart s A' + MvPowerSeries.X t * freePart s B) = 0 :=
    free_add s _ _ (free_C_mul s π _ (freePart_free s A')) (free_X_mul s t hst _ (freePart_free s B))
  have hg0 := eq_zero_of_X_mul_free s
    (Z' - MvPowerSeries.C π * quotPart s A' - MvPowerSeries.X t * quotPart s B)
    (fun m hm => by rw [hzero]; exact hfree m hm)
  have hZ : Z = MvPowerSeries.C π * quotPart s A' + MvPowerSeries.X t * (Q + quotPart s B) := by
    have : Z' = MvPowerSeries.C π * quotPart s A' + MvPowerSeries.X t * quotPart s B := by
      rw [sub_sub, sub_eq_zero] at hg0; rw [hg0]
    rw [hZ'] at this
    rw [mul_add]
    linear_combination this
  rw [hZ, map_add, map_mul, map_mul]
  refine add_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp [const])))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

theorem exists_isUnit_and_sub_U_mul_mem [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π)
    {E : ℕ} (hE : 1 ≤ E) [IsLocalRing (UVCrossingModel W (π ^ E))]
    (z : UVCrossingModel W (π ^ E)) (h1 : z ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (γ : UVCrossingModel W (π ^ E)) (hγ : IsUnit γ)
    (h2 : z - γ * U (π ^ E) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}) :
    ∃ β : UVCrossingModel W (π ^ E), IsUnit β ∧ z - U (π ^ E) * β ∈ Ideal.span {const (π ^ E) π} := by
  rw [Ideal.mem_span_pair] at h1 h2
  obtain ⟨a, b, hab⟩ := h1
  obtain ⟨c, d, hcd⟩ := h2
  have hU : UVCrossingModel.mk (π ^ E) (MvPowerSeries.X 0) * (b - γ) ∈
      Ideal.span {const (π ^ E) π, UVCrossingModel.mk (π ^ E) (MvPowerSeries.X 1)} := by
    have : UVCrossingModel.mk (π ^ E) (MvPowerSeries.X 0) * (b - γ) = (c - a) * const (π ^ E) π + d * V (π ^ E) := by
      have e1 : U (π ^ E) * (b - γ) = z - γ * U (π ^ E) - a * const (π ^ E) π := by
        rw [← hab]; ring
      change U (π ^ E) * (b - γ) = _
      rw [e1, ← hcd]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp [V])))
  have hb := mem_span_of_X_mul_mem hE 0 1 (by decide) (b - γ) hU
  refine ⟨b, ?_, ?_⟩
  · have hm : b - γ ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
      refine (Ideal.span_le.mpr ?_) hb
      rintro w (rfl | rfl)
      · exact (mem_maximalIdeal _).mpr (not_isUnit_const hπ hE)
      · exact (mem_maximalIdeal _).mpr (not_isUnit_V hπ hE)
    obtain ⟨g, hg⟩ := hγ
    have : b = g * (1 + ↑g⁻¹ * (b - γ)) := by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hg]; ring
    rw [this]
    refine (Units.isUnit g).mul ?_
    have hj := (maximalIdeal_le_jacobson (⊥ : Ideal (UVCrossingModel W (π ^ E))))
      (Ideal.mul_mem_left _ (↑g⁻¹) hm)
    rw [Ideal.mem_jacobson_bot] at hj
    simpa [mul_one, add_comm] using hj 1
  · have : z - U (π ^ E) * b = a * const (π ^ E) π := by rw [← hab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

theorem map_mk_span_pair (π : W) (E : ℕ) :
    Ideal.map (UVCrossingModel.mk (π ^ E))
        (Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)}) =
      Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  rw [Ideal.map_span, Set.image_pair]
  rfl

theorem exists_isUnit_and_sub_mul_V_pow_mem [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π)
    (E : ℕ) (g : UVCrossingModel W (π ^ E)) (hg : g ∉ Ideal.span {const (π ^ E) π, U (π ^ E)}) :
    ∃ (m : ℕ) (γ : UVCrossingModel W (π ^ E)), IsUnit γ ∧
      g - γ * V (π ^ E) ^ m ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  obtain ⟨G, rfl⟩ := mk_surjective (π ^ E) g
  have hG : G ∉ Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)} := by
    intro h
    apply hg
    rw [← map_mk_span_pair]
    exact Ideal.mem_map_of_mem _ h
  obtain ⟨m, H, hH, hmem⟩ := exists_isUnit_and_sub_X_pow_mul_mem hπ G hG
  refine ⟨m, UVCrossingModel.mk (π ^ E) H, hH.map _, ?_⟩
  have := Ideal.mem_map_of_mem (UVCrossingModel.mk (π ^ E)) hmem
  rw [map_mk_span_pair, map_sub, map_mul, map_pow] at this
  have hV : UVCrossingModel.mk (π ^ E) (MvPowerSeries.X 1) = V (π ^ E) := rfl
  rw [hV] at this
  convert this using 2
  ring

end Model

section Ord

theorem ord_algebraMap_eq_zero {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    (v : Place K F') (a : K) (ha : a ≠ 0) :
    v.ord (algebraMap K F' a) = 0 := by
  have hu : IsUnit (⟨algebraMap K F' a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F' a⁻¹, v.algebraMap_mem' _⟩, ?_⟩
    ext
    change algebraMap K F' a * algebraMap K F' a⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem adicValuation_eq_exp_neg_ord {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    (v : Place K F') {f : F'} (hf : f ≠ 0) : v.adicValuation f = WithZero.exp (-v.ord f) := by
  rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem ord_add_of_lt {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    (v : Place K F') {a b : F'} (ha : a ≠ 0)
    (hb : b = 0 ∨ (b ≠ 0 ∧ v.ord a < v.ord b)) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  rcases hb with rfl | ⟨hb0, hb⟩
  · simp [ha]
  · have hva := adicValuation_eq_exp_neg_ord v ha
    have hvb := adicValuation_eq_exp_neg_ord v hb0
    have hlt : v.adicValuation b < v.adicValuation a := by
      rw [hva, hvb, WithZero.exp_lt_exp]; omega
    have hadd : v.adicValuation (a + b) = v.adicValuation a := Valuation.map_add_eq_of_lt_left _ hlt
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [h0, map_zero] at hadd
      exact v.adicValuation_ne_zero ha hadd.symm
    · simp only [Place.ord, hadd]

theorem ord_pow {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    (v : Place K F') (f : F') (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

end Ord

section Descent

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem mem_sup_pow_of_algebraMap_mem_map (J : Ideal R) (k : ℕ) (r : R)
    (h : algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈ J.map (algebraMap R _)) :
    r ∈ J ⊔ maximalIdeal R ^ k := by
  have key : ∀ w ∈ J.map (algebraMap R (AdicCompletion (maximalIdeal R) R)),
      ∃ s ∈ J, AdicCompletion.evalₐ (maximalIdeal R) k (w - algebraMap R _ s) = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∃ s ∈ J,
      AdicCompletion.evalₐ (maximalIdeal R) k (w - algebraMap R _ s) = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨s, hs, by rw [sub_self, map_zero]⟩
    · exact ⟨0, J.zero_mem, by rw [map_zero, sub_self, map_zero]⟩
    · rintro w₁ w₂ _ _ ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
      refine ⟨s₁ + s₂, J.add_mem hs₁ hs₂, ?_⟩
      have : w₁ + w₂ - algebraMap R _ (s₁ + s₂) = (w₁ - algebraMap R _ s₁) + (w₂ - algebraMap R _ s₂) := by
        rw [map_add]; ring
      rw [this, map_add, h₁, h₂, add_zero]
    · rintro z w _ ⟨s, hs, h⟩
      obtain ⟨a, y, hy, rfl⟩ :=
        AdicCompletion.exists_eq_algebraMap_add (maximalIdeal R) AdicCompletion.maximalIdeal_fg k z
      rw [← AdicCompletion.ker_evalₐ_eq_map_pow _ AdicCompletion.maximalIdeal_fg, RingHom.mem_ker] at hy
      refine ⟨a * s, J.mul_mem_left a hs, ?_⟩
      have : (algebraMap R _ a + y) • w - algebraMap R (AdicCompletion (maximalIdeal R) R) (a * s) =
          algebraMap R _ a * (w - algebraMap R _ s) + y * w := by
        rw [smul_eq_mul, map_mul]; ring
      rw [this, map_add, map_mul, h, mul_zero, zero_add, map_mul, hy, zero_mul]
  obtain ⟨s, hs, hks⟩ := key _ h
  rw [← map_sub, AdicCompletion.evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem] at hks
  have : r = s + (r - s) := by ring
  rw [this]
  exact add_mem (Ideal.mem_sup_left hs) (Ideal.mem_sup_right hks)

theorem mem_of_algebraMap_mem_map (J : Ideal R) (r : R)
    (h : algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈ J.map (algebraMap R _)) : r ∈ J := by
  by_cases hJ : J = ⊤
  · rw [hJ]; exact Submodule.mem_top
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hJle : J ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hJ
  have hne : (maximalIdeal R).map (Ideal.Quotient.mk J) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R ⧸ J) ∈ (maximalIdeal R).map (Ideal.Quotient.mk J) := htop ▸ Submodule.mem_top
    rw [← map_one (Ideal.Quotient.mk J), Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr hJle] at h1
    exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hkrull := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
  have hmem : Ideal.Quotient.mk J r ∈ ⨅ k : ℕ, ((maximalIdeal R).map (Ideal.Quotient.mk J)) ^ k := by
    rw [Ideal.mem_iInf]
    intro k
    have hk := mem_sup_pow_of_algebraMap_mem_map J k r h
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hk
    rwa [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow] at this
  rw [hkrull] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

end Descent

section EndLaw

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

noncomputable def resN (R : RegularProlongation A F Fbar) (N : Subring F)
    (hN : ∀ f : F, f ∈ N → f ∈ R.integers) : ↥N →+* Fbar where
  toFun g := R.residue ⟨g, hN g g.2⟩
  map_one' := by
    have : (⟨((1 : ↥N) : F), hN _ (1 : ↥N).2⟩ : R.integers) = 1 := Subtype.ext rfl
    rw [this, map_one]
  map_mul' a b := by
    have : (⟨((a * b : ↥N) : F), hN _ (a * b).2⟩ : R.integers) = ⟨a, hN a a.2⟩ * ⟨b, hN b b.2⟩ := Subtype.ext rfl
    rw [this, map_mul]
  map_zero' := by
    have : (⟨((0 : ↥N) : F), hN _ (0 : ↥N).2⟩ : R.integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  map_add' a b := by
    have : (⟨((a + b : ↥N) : F), hN _ (a + b).2⟩ : R.integers) = ⟨a, hN a a.2⟩ + ⟨b, hN b b.2⟩ := Subtype.ext rfl
    rw [this, map_add]

theorem resN_apply (R : RegularProlongation A F Fbar) (N : Subring F)
    (hN : ∀ f : F, f ∈ N → f ∈ R.integers) (g : ↥N) : resN R N hN g = R.residue ⟨g, hN g g.2⟩ := rfl

theorem resN_ne_zero_of_isUnit (R : RegularProlongation A F Fbar) (N : Subring F)
    (hN : ∀ f : F, f ∈ N → f ∈ R.integers) {g : ↥N} (hg : IsUnit g) : resN R N hN g ≠ 0 := by
  obtain ⟨g', hg'⟩ := hg.exists_right_inv
  intro h0
  have := congrArg (resN R N hN) hg'
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

end EndLaw

theorem endLawFirst
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    (R₁ : RegularProlongation A F Fbar₁) (x₁ : Place (ResidueField A) Fbar₁)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁.integers)
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (x y : ↥𝒩₀)
    (hxU : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι (algebraMap ↥𝒩₀ _ x) - γ * U (π ^ E) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (hyV : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι (algebraMap ↥𝒩₀ _ y) - γ * V (π ^ E) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hker : ∀ f : ↥𝒩₀, R₁.residue ⟨f, h𝒩₀ f f.2⟩ = 0 ↔
      ι (algebraMap ↥𝒩₀ _ f) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hcent : ∀ f : ↥𝒩₀, ¬ IsUnit f → R₁.residue ⟨f, h𝒩₀ f f.2⟩ ≠ 0 → 0 < x₁.ord (R₁.residue ⟨f, h𝒩₀ f f.2⟩))
    (hx₁ : R₁.residue ⟨x, h𝒩₀ x x.2⟩ = 0)
    (hunif : x₁.ord (R₁.residue ⟨y, h𝒩₀ y y.2⟩) = 1) :
    ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, h𝒩₀ f f.2⟩ ≠ 0 →
      (0 ≤ x₁.ord (R₁.residue ⟨f, h𝒩₀ f f.2⟩)) ∧
      (x₁.ord (R₁.residue ⟨f, h𝒩₀ f f.2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) := by
  classical

  haveI hlocM : IsLocalRing (UVCrossingModel W (π ^ E)) := isLocalRing_model hπ hE
  set Nh := AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ with hNh
  set rs : ↥𝒩₀ →+* Fbar₁ := resN R₁ 𝒩₀ h𝒩₀ with hrs
  have rs_apply : ∀ g : ↥𝒩₀, rs g = R₁.residue ⟨g, h𝒩₀ g g.2⟩ := fun g => rfl
  set φ : ↥𝒩₀ →+* UVCrossingModel W (π ^ E) := (ι : Nh →+* UVCrossingModel W (π ^ E)).comp (algebraMap ↥𝒩₀ Nh)
    with hφdef
  have hφ : ∀ g : ↥𝒩₀, φ g = ι (algebraMap ↥𝒩₀ Nh g) := fun g => rfl
  set Q : Ideal (UVCrossingModel W (π ^ E)) := Ideal.span {const (π ^ E) π, U (π ^ E)} with hQdef
  have hQle : Q ≤ maximalIdeal (UVCrossingModel W (π ^ E)) := span_pair_le_maximalIdeal hπ hE

  set oN : ↥C → ↥𝒩₀ := fun o => ⟨algebraMap L F (o : L), hCmem o o.2⟩ with hoN
  have rs_const : ∀ o : ↥C, rs (oN o) =
      algebraMap (ResidueField A) Fbar₁ (IsLocalRing.residue A ⟨(o : L), hC o o.2⟩) := fun o =>
    R₁.residue_algebraMap ⟨(o : L), hC o o.2⟩

  have hϖ0 : rs (oN ϖ) = 0 := by
    rw [rs_apply, hker, ← hσπ, hconst]
    exact Ideal.subset_span (by simp)

  have nonneg : ∀ g : ↥𝒩₀, 0 ≤ x₁.ord (rs g) := by
    intro g
    obtain ⟨o, ho⟩ := hres g
    have hsplit : g = oN o + (g - oN o) := by ring
    have hgo : rs g = rs (oN o) + rs (g - oN o) := by
      conv_lhs => rw [hsplit]
      rw [map_add]
    by_cases h1 : rs (g - oN o) = 0
    · rw [hgo, h1, add_zero, rs_const]
      by_cases h2 : IsLocalRing.residue A ⟨(o : L), hC o o.2⟩ = 0
      · rw [h2, map_zero, Place.ord_zero]
      · rw [ord_algebraMap_eq_zero x₁ _ h2]
    · have hpos : 0 < x₁.ord (rs (g - oN o)) := hcent _ ho h1
      by_cases h2 : rs (oN o) = 0
      · rw [hgo, h2, zero_add]; exact hpos.le
      · have hc0 : x₁.ord (rs (oN o)) = 0 := by
          rw [rs_const] at h2 ⊢
          exact ord_algebraMap_eq_zero x₁ _ (fun h => h2 (by rw [h, map_zero]))
        rw [hgo, (ord_add_of_lt x₁ h2 (Or.inr ⟨h1, by rw [hc0]; exact hpos⟩)).2, hc0]

  have unit_rs : ∀ g : ↥𝒩₀, IsUnit g → rs g ≠ 0 ∧ x₁.ord (rs g) = 0 := by
    intro g hg
    obtain ⟨g', hg'⟩ := hg.exists_right_inv
    have h1 : rs g * rs g' = 1 := by rw [← map_mul, hg', map_one]
    have hg0 : rs g ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hg'0 : rs g' ≠ 0 := right_ne_zero_of_mul_eq_one h1
    refine ⟨hg0, ?_⟩
    have := x₁.ord_mul hg0 hg'0
    rw [h1, Place.ord_one] at this
    have h2 := nonneg g
    have h3 := nonneg g'
    omega

  set t := rs y with htdef
  have ht1 : x₁.ord t = 1 := hunif
  have ht0 : t ≠ 0 := by intro h0; rw [h0, Place.ord_zero] at ht1; exact zero_ne_one ht1

  have hφx : φ x ∈ Q := (hker x).mp hx₁
  obtain ⟨γx, hγx, hγx'⟩ := hxU
  obtain ⟨β, hβ, hβx⟩ := exists_isUnit_and_sub_U_mul_mem hπ hE (φ x) hφx γx hγx hγx'
  obtain ⟨γy, hγy, hγy'⟩ := hyV
  set J : ℕ → Ideal ↥𝒩₀ := fun m => Ideal.span {oN ϖ, x, y ^ (m + 1)} with hJdef
  have hφϖ : φ (oN ϖ) = const (π ^ E) π := by rw [hφ, ← hconst, hσπ]
  have hUmem : ∀ m : ℕ, U (π ^ E) ∈ (J m).map φ := by
    intro m
    have hu : U (π ^ E) = ↑(hβ.unit⁻¹) * (φ x - (φ x - U (π ^ E) * β)) := by
      rw [sub_sub_cancel, mul_comm (U (π ^ E)) β, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [hu]
    refine Ideal.mul_mem_left _ _ (sub_mem (Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))) ?_)
    rw [Ideal.mem_span_singleton] at hβx
    obtain ⟨w, hw⟩ := hβx
    rw [hw, ← hφϖ]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp)))
  have hQJ : ∀ m : ℕ, Q ≤ (J m).map φ := by
    intro m
    rw [hQdef, Ideal.span_le]
    rintro w (rfl | rfl)
    · rw [← hφϖ]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
    · exact hUmem m
  have hVJ : ∀ m : ℕ, V (π ^ E) ^ (m + 1) ∈ (J m).map φ := by
    intro m
    set Q' := (J m).map φ with hQ'
    have hy' : Ideal.Quotient.mk Q' (V (π ^ E)) =
        Ideal.Quotient.mk Q' ↑(hγy.unit⁻¹) * Ideal.Quotient.mk Q' (φ y) := by
      rw [← map_mul, Ideal.Quotient.eq]
      have : V (π ^ E) - ↑(hγy.unit⁻¹) * φ y = -(↑(hγy.unit⁻¹) * (φ y - γy * V (π ^ E))) := by
        rw [mul_sub, ← mul_assoc, IsUnit.val_inv_mul, one_mul]; ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_left _ _ (hQJ m hγy'))
    have hzero : Ideal.Quotient.mk Q' (φ (y ^ (m + 1))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ (Ideal.subset_span (by simp)))
    have hgoal : Ideal.Quotient.mk Q' (V (π ^ E) ^ (m + 1)) = 0 := by
      have : Ideal.Quotient.mk Q' (V (π ^ E) ^ (m + 1)) =
          Ideal.Quotient.mk Q' ↑(hγy.unit⁻¹) ^ (m + 1) * Ideal.Quotient.mk Q' (φ (y ^ (m + 1))) := by
        rw [map_pow, hy']; simp only [map_pow]; ring
      rw [this, hzero]; ring
    exact Ideal.Quotient.eq_zero_iff_mem.mp hgoal

  have descent : ∀ (m : ℕ) (g : ↥𝒩₀), φ g ∈ (J m).map φ → g ∈ J m := by
    intro m g hg
    rw [hφdef, ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap] at hg
    change ι.symm (ι (algebraMap ↥𝒩₀ Nh g)) ∈ _ at hg
    rw [RingEquiv.symm_apply_apply] at hg
    exact mem_of_algebraMap_mem_map (J m) g hg

  intro f n hf0
  refine ⟨nonneg f, fun hn => ?_⟩
  have hφf : φ f ∉ Q := fun h => hf0 ((hker f).mpr h)
  obtain ⟨m, γ, hγ, hγf⟩ := exists_isUnit_and_sub_mul_V_pow_mem hπ E (φ f) hφf

  set δ : UVCrossingModel W (π ^ E) := γ * ↑(hγy.unit⁻¹) ^ m with hδdef
  have hδu : IsUnit δ := hγ.mul ((Units.isUnit _).pow m)
  have hδγ : δ * γy ^ m = γ := by
    rw [hδdef, mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
  set δN : Nh := ι.symm δ with hδN
  have hδNu : IsUnit δN := hδu.map ι.symm
  obtain ⟨u, z, hz, hδNeq⟩ :=
    AdicCompletion.exists_eq_algebraMap_add (maximalIdeal ↥𝒩₀) AdicCompletion.maximalIdeal_fg 1 δN
  rw [pow_one, ← AdicCompletion.maximalIdeal_eq_map] at hz
  have hu : IsUnit u := by
    by_contra hu
    have hmem : algebraMap ↥𝒩₀ Nh u ∈ maximalIdeal Nh := by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hu)
    have : δN ∈ maximalIdeal Nh := by rw [hδNeq]; exact add_mem hmem hz
    exact (mem_maximalIdeal _).mp this hδNu
  have hzM : ι z ∈ Ideal.span {const (π ^ E) π, U (π ^ E), V (π ^ E)} := by
    refine mem_span_of_not_isUnit hπ hE _ (fun hzu => (mem_maximalIdeal _).mp hz ?_)
    exact (MulEquiv.isUnit_map ι).mp hzu
  have hδφ : δ = φ u + ι z := by
    have := congrArg ι hδNeq
    rwa [hδN, RingEquiv.apply_symm_apply, map_add] at this
  obtain ⟨a, b, c, habc⟩ := Submodule.mem_span_triple.mp hzM
  simp only [smul_eq_mul] at habc

  have hkey : φ (f - u * y ^ m) ∈ (J m).map φ := by
    set Q' := (J m).map φ with hQ'
    have hQQ' : Q ≤ Q' := hQJ m
    set T := UVCrossingModel W (π ^ E) ⧸ Q' with hT
    set mk' := Ideal.Quotient.mk Q' with hmk'
    have e1 : mk' (φ f) = mk' γ * mk' (V (π ^ E)) ^ m := by
      rw [← map_pow, ← map_mul, Ideal.Quotient.eq]; exact hQQ' hγf
    have e2 : mk' (φ y) = mk' γy * mk' (V (π ^ E)) := by
      rw [← map_mul, Ideal.Quotient.eq]; exact hQQ' hγy'
    have e3 : mk' δ = mk' (φ u) + mk' (ι z) := by rw [hδφ, map_add]
    have e4 : mk' γ = mk' δ * mk' γy ^ m := by rw [← map_pow, ← map_mul, hδγ]
    have e5 : mk' (ι z) = mk' c * mk' (V (π ^ E)) := by
      rw [← map_mul, Ideal.Quotient.eq, ← habc]
      have : a * const (π ^ E) π + b * U (π ^ E) + c * V (π ^ E) - c * V (π ^ E) =
          a * const (π ^ E) π + b * U (π ^ E) := by ring
      rw [this]
      exact hQQ' (add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
    have hV1 : mk' (V (π ^ E)) ^ (m + 1) = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hVJ m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change mk' (φ (f - u * y ^ m)) = 0
    have : mk' (φ (f - u * y ^ m)) = mk' c * mk' γy ^ m * mk' (V (π ^ E)) ^ (m + 1) := by
      rw [map_sub, map_mul, map_pow, map_sub, map_mul, map_pow, e1, e2, e4, e3, e5]
      ring
    rw [this, hV1]; ring

  have hgJ : f - u * y ^ m ∈ J m := descent m _ hkey
  obtain ⟨a', b', c', habc'⟩ := Submodule.mem_span_triple.mp hgJ
  simp only [smul_eq_mul] at habc'
  have hresf : rs f = rs u * t ^ m + rs c' * t ^ (m + 1) := by
    have : f = u * y ^ m + (a' * oN ϖ + b' * x + c' * y ^ (m + 1)) := by rw [habc']; ring
    rw [this, map_add, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, hϖ0,
      show rs x = 0 from hx₁, mul_zero, mul_zero, zero_add, zero_add]

  obtain ⟨hu0, hordu⟩ := unit_rs u hu
  have hlead0 : rs u * t ^ m ≠ 0 := mul_ne_zero hu0 (pow_ne_zero m ht0)
  have hlead : x₁.ord (rs u * t ^ m) = (m : ℤ) := by
    rw [x₁.ord_mul hu0 (pow_ne_zero m ht0), hordu, ord_pow, ht1]; ring
  have hordf : x₁.ord (rs f) = (m : ℤ) := by
    rw [hresf]
    have htail : rs c' * t ^ (m + 1) = 0 ∨
        (rs c' * t ^ (m + 1) ≠ 0 ∧ x₁.ord (rs u * t ^ m) < x₁.ord (rs c' * t ^ (m + 1))) := by
      by_cases hc' : rs c' = 0
      · left; rw [hc', zero_mul]
      · right
        refine ⟨mul_ne_zero hc' (pow_ne_zero _ ht0), ?_⟩
        rw [hlead, x₁.ord_mul hc' (pow_ne_zero _ ht0), ord_pow, ht1]
        have := nonneg c'
        push_cast
        omega
    rw [(ord_add_of_lt x₁ hlead0 htail).2, hlead]
  have hnm : n = m := by
    have : (n : ℤ) = (m : ℤ) := by rw [← hn, ← rs_apply, hordf]
    exact_mod_cast this
  subst hnm
  exact ⟨γ, hγ, hγf⟩

section Swap

variable {W : Type*} [CommRing W] (τ : W)

theorem crossingSwap_U : crossingSwap τ (U τ) = V τ := by
  show crossingSwap τ (UVCrossingModel.mk τ (MvPowerSeries.X 0)) = UVCrossingModel.mk τ (MvPowerSeries.X 1)
  rw [crossingSwap_mk, uvSwapEquiv_X_zero]

theorem crossingSwap_V : crossingSwap τ (V τ) = U τ := by
  show crossingSwap τ (UVCrossingModel.mk τ (MvPowerSeries.X 1)) = UVCrossingModel.mk τ (MvPowerSeries.X 0)
  rw [crossingSwap_mk, uvSwapEquiv_X_one]

theorem crossingSwap_const (w : W) : crossingSwap τ (const τ w) = const τ w := by
  show crossingSwap τ (UVCrossingModel.mk τ (MvPowerSeries.C w)) = UVCrossingModel.mk τ (MvPowerSeries.C w)
  rw [crossingSwap_mk, uvSwapEquiv_C]

theorem crossingSwap_symm_U : (crossingSwap τ).symm (U τ) = V τ := by
  rw [RingEquiv.symm_apply_eq, crossingSwap_V]

theorem crossingSwap_symm_V : (crossingSwap τ).symm (V τ) = U τ := by
  rw [RingEquiv.symm_apply_eq, crossingSwap_U]

theorem crossingSwap_symm_const (w : W) : (crossingSwap τ).symm (const τ w) = const τ w := by
  rw [RingEquiv.symm_apply_eq, crossingSwap_const]

theorem map_span_pair_equiv (e : UVCrossingModel W τ ≃+* UVCrossingModel W τ) (a b : UVCrossingModel W τ) :
    (Ideal.span {a, b}).map e = Ideal.span {e a, e b} := by
  rw [Ideal.map_span, Set.image_pair]

theorem sub_mul_mem_span_of_equiv (e : UVCrossingModel W τ ≃+* UVCrossingModel W τ)
    (p a b : UVCrossingModel W τ) (hp : e p = p) (z γ : UVCrossingModel W τ)
    (h : z - γ * a ∈ Ideal.span {p, b}) : e z - e γ * e a ∈ Ideal.span {p, e b} := by
  have := Ideal.mem_map_of_mem e h
  rwa [map_span_pair_equiv, hp, map_sub, map_mul] at this

end Swap

end NodeEndLawSecondSol

open NodeEndLawSecondSol in
theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₂ : RegularProlongation A F Fbar₂) (x₂ : Place (ResidueField A) Fbar₂)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀ : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₂.integers)

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)

    (x y : ↥𝒩₀)
    (hxU : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι (algebraMap ↥𝒩₀ _ x) - γ * U (π ^ E) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (hyV : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι (algebraMap ↥𝒩₀ _ y) - γ * V (π ^ E) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})

    (hker : ∀ f : ↥𝒩₀, R₂.residue ⟨f, h𝒩₀ f f.2⟩ = 0 ↔
      ι (algebraMap ↥𝒩₀ _ f) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (hcent : ∀ f : ↥𝒩₀, ¬ IsUnit f → R₂.residue ⟨f, h𝒩₀ f f.2⟩ ≠ 0 → 0 < x₂.ord (R₂.residue ⟨f, h𝒩₀ f f.2⟩))
    (hy₂ : R₂.residue ⟨y, h𝒩₀ y y.2⟩ = 0)
    (hunif : x₂.ord (R₂.residue ⟨x, h𝒩₀ x x.2⟩) = 1) :
    ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, h𝒩₀ f f.2⟩ ≠ 0 →
      (0 ≤ x₂.ord (R₂.residue ⟨f, h𝒩₀ f f.2⟩)) ∧
      (x₂.ord (R₂.residue ⟨f, h𝒩₀ f f.2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}) := by

  set s : UVCrossingModel W (π ^ E) ≃+* UVCrossingModel W (π ^ E) := crossingSwap (π ^ E) with hs
  set ι' : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E) := ι.trans s with hι'
  have hι' : ∀ z, ι' z = s (ι z) := fun z => rfl
  have hsπ : s (const (π ^ E) π) = const (π ^ E) π := crossingSwap_const _ _
  have hsπ' : s.symm (const (π ^ E) π) = const (π ^ E) π := crossingSwap_symm_const _ _
  have hconst' : ∀ o : W, ι' (σ o) = const (π ^ E) o := fun o => by
    rw [hι', hconst, hs, crossingSwap_const]

  have hxU' : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι' (algebraMap ↥𝒩₀ _ y) - γ * U (π ^ E) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
    obtain ⟨γ, hγ, h⟩ := hyV
    refine ⟨s γ, hγ.map s, ?_⟩
    have := sub_mul_mem_span_of_equiv (π ^ E) s (const (π ^ E) π) (V (π ^ E)) (U (π ^ E)) hsπ _ γ h
    rwa [hs, crossingSwap_V, crossingSwap_U] at this
  have hyV' : ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      ι' (algebraMap ↥𝒩₀ _ x) - γ * V (π ^ E) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
    obtain ⟨γ, hγ, h⟩ := hxU
    refine ⟨s γ, hγ.map s, ?_⟩
    have := sub_mul_mem_span_of_equiv (π ^ E) s (const (π ^ E) π) (U (π ^ E)) (V (π ^ E)) hsπ _ γ h
    rwa [hs, crossingSwap_U, crossingSwap_V] at this

  have hker' : ∀ f : ↥𝒩₀, R₂.residue ⟨f, h𝒩₀ f f.2⟩ = 0 ↔
      ι' (algebraMap ↥𝒩₀ _ f) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
    intro f
    rw [hker f, hι']
    constructor
    · intro h
      have := Ideal.mem_map_of_mem s h
      rwa [map_span_pair_equiv, hsπ, hs, crossingSwap_V] at this
    · intro h
      have := Ideal.mem_map_of_mem s.symm h
      rwa [map_span_pair_equiv, RingEquiv.symm_apply_apply, hsπ', hs, crossingSwap_symm_U] at this

  intro f n hf0
  obtain ⟨hnonneg, hlaw⟩ := endLawFirst A R₂ x₂ 𝒩₀ h𝒩₀ C hC hCmem ϖ hres π hπ σ hσπ E hE ι' hconst' y x
    hxU' hyV' hker' hcent hy₂ hunif f n hf0
  refine ⟨hnonneg, fun hn => ?_⟩
  obtain ⟨γ, hγ, hmem⟩ := hlaw hn
  refine ⟨s.symm γ, hγ.map s.symm, ?_⟩
  have := Ideal.mem_map_of_mem s.symm hmem
  rwa [map_span_pair_equiv, hsπ', map_sub, map_mul, map_pow, hι', RingEquiv.symm_apply_apply, hs,
    crossingSwap_symm_U, crossingSwap_symm_V] at this

end S_AlgebraicCurve_NodeAnnulusEngine_exists_isUnit_sub_mul_U_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_isUnit_sub_mul_U_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel (solution)
