-- Prove2me | solution 1 for AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a8b134af-3010-5ebd-9888-729c59066573

import Mathlib
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace SlotPlaceAux

open LaurentPolynomial AutomorphicForm

abbrev LP := LaurentPolynomial ℂ

theorem satakePow_sum_prod {R : Type*} [CommRing R] (α β : R) :
    ∀ n : ℕ, satakePow n (α + β) (α * β) = α ^ n + β ^ n
  | 0 => by rw [satakePow_zero, pow_zero, pow_zero]; norm_num
  | 1 => by rw [satakePow_one, pow_one, pow_one]
  | (n + 2) => by
      rw [satakePow_add_two, satakePow_sum_prod α β (n + 1), satakePow_sum_prod α β n]
      ring

theorem map_satakePow {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s e : R) :
    ∀ n : ℕ, φ (satakePow n s e) = satakePow n (φ s) (φ e)
  | 0 => by rw [satakePow_zero, satakePow_zero, map_ofNat]
  | 1 => by rw [satakePow_one, satakePow_one]
  | (n + 2) => by
      rw [satakePow_add_two, satakePow_add_two, map_sub, map_mul, map_mul,
        map_satakePow φ s e (n + 1), map_satakePow φ s e n]

theorem C_mul_apply (c : ℂ) (p : LP) (n : ℤ) : (C c * p).coeff n = c * p.coeff n := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_single_zero_mul p c n

theorem T_apply (a n : ℤ) : (T a : LP).coeff n = if a = n then 1 else 0 :=
  Finsupp.single_apply

theorem natCast_eq_C (m : ℕ) : ((m : ℕ) : LP) = C (m : ℂ) := (map_natCast C m).symm

noncomputable def coeff0 : LP →ₗ[ℂ] ℂ where
  toFun p := p.coeff 0
  map_add' p q := Finsupp.add_apply p.coeff q.coeff 0
  map_smul' c p := by
    rw [smul_eq_C_mul, C_mul_apply, RingHom.id_apply, smul_eq_mul]

theorem coeff0_apply (p : LP) : coeff0 p = p.coeff 0 := rfl

theorem T_add_T_neg_pow (f : ℤ) (k : ℕ) :
    ((T f + T (-f)) ^ k : LP) =
      ∑ m ∈ Finset.range (k + 1), C ((k.choose m : ℕ) : ℂ) * T (f * (2 * (m : ℤ) - k)) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [T_pow, T_pow, ← T_add, natCast_eq_C, mul_comm]
  congr 2
  push_cast [Nat.cast_sub hmk]
  ring

theorem T_add_T_neg_pow_apply_zero (f : ℤ) (hf : f ≠ 0) (k : ℕ) :
    ((T f + T (-f)) ^ k : LP).coeff 0 = if Even k then ((k.choose (k / 2) : ℕ) : ℂ) else 0 := by
  rw [T_add_T_neg_pow, ← coeff0_apply, map_sum]
  have key : ∀ m ∈ Finset.range (k + 1),
      coeff0 (C ((k.choose m : ℕ) : ℂ) * T (f * (2 * (m : ℤ) - k)) : LP) =
        if 2 * m = k then ((k.choose m : ℕ) : ℂ) else 0 := by
    intro m _
    rw [coeff0_apply, C_mul_apply, T_apply]
    by_cases h : 2 * m = k
    · have h0 : f * (2 * (m : ℤ) - k) = 0 := by
        rw [← h]; push_cast; ring
      rw [if_pos h0, if_pos h, mul_one]
    · have h0 : f * (2 * (m : ℤ) - k) ≠ 0 := by
        refine mul_ne_zero hf fun h' => h ?_
        have : (2 * (m : ℤ)) = (k : ℤ) := sub_eq_zero.mp h'
        exact_mod_cast this
      rw [if_neg h0, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl key]
  split_ifs with hk
  · rw [Finset.sum_eq_single_of_mem (k / 2) (Finset.mem_range.mpr (by omega))]
    · obtain ⟨m₀, hm₀⟩ := hk
      rw [if_pos (by omega)]
    · intro m _ hne
      obtain ⟨m₀, hm₀⟩ := hk
      rw [if_neg (by omega)]
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]
    intro h
    exact hk ⟨m, by omega⟩

theorem four_pow_mul_wallis (m : ℕ) :
    (4 : ℝ) ^ m * ∏ n ∈ Finset.range m, (2 * (n : ℝ) + 1) / (2 * n + 2) = ((2 * m).choose m : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, pow_succ,
        show (4 : ℝ) ^ m * 4 * ((∏ n ∈ Finset.range m, (2 * (n : ℝ) + 1) / (2 * n + 2)) *
            ((2 * (m : ℝ) + 1) / (2 * m + 2))) =
          4 * ((2 * (m : ℝ) + 1) / (2 * m + 2)) *
            ((4 : ℝ) ^ m * ∏ n ∈ Finset.range m, (2 * (n : ℝ) + 1) / (2 * n + 2)) by ring, ih]
      have h := Nat.succ_mul_centralBinom_succ m
      rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
      have h' : ((m : ℝ) + 1) * (((2 * (m + 1)).choose (m + 1) : ℕ) : ℝ) =
          2 * (2 * (m : ℝ) + 1) * (((2 * m).choose m : ℕ) : ℝ) := by
        exact_mod_cast h
      have hm : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
      calc 4 * ((2 * (m : ℝ) + 1) / (2 * m + 2)) * (((2 * m).choose m : ℕ) : ℝ)
          = (4 * (2 * (m : ℝ) + 1) * (((2 * m).choose m : ℕ) : ℝ)) / (2 * m + 2) := by ring
        _ = (((2 * (m + 1)).choose (m + 1) : ℕ) : ℝ) := by
          rw [div_eq_iff hm]
          linear_combination (-2 : ℝ) * h'

theorem momentA_eq (N ξ σ : ℂ) (hσ : σ ^ 2 = N * ξ) (a : ℕ) :
    (1 + (-1 : ℂ) ^ a) / 2 * (4 * (N * ξ)) ^ (a / 2) *
        ((∏ n ∈ Finset.range (a / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) =
      (if Even a then ((a.choose (a / 2) : ℕ) : ℂ) else 0) * σ ^ a := by
  rcases Nat.even_or_odd a with ha | ha
  · obtain ⟨m, rfl⟩ := ha
    have h2 : (m + m) / 2 = m := by omega
    rw [if_pos ⟨m, rfl⟩, h2, Even.neg_one_pow ⟨m, rfl⟩, ← hσ, show m + m = 2 * m by ring, pow_mul,
      mul_pow]
    have hw := four_pow_mul_wallis m
    have hw' : (4 : ℂ) ^ m * ((∏ n ∈ Finset.range m, (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) =
        (((2 * m).choose m : ℕ) : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hw
      push_cast at this ⊢
      exact this
    linear_combination (σ ^ 2) ^ m * hw'
  · rw [Odd.neg_one_pow ha, if_neg (Nat.not_even_iff_odd.mpr ha)]
    ring

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))

theorem one_le_slotDeg : 1 ≤ SatakeCombination.slotDeg K L ws v := by
  unfold SatakeCombination.slotDeg
  have h' : ((ws v).1.asIdeal).under (𝓞 K) = v.asIdeal := by
    have := congrArg HeightOneSpectrum.asIdeal (ws v).2
    simpa using this
  haveI : (ws v).1.asIdeal.LiesOver v.asIdeal := ⟨h'.symm⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  exact Ideal.inertiaDeg'_pos v.asIdeal (ws v).1.asIdeal

theorem sum_slotCoeff_mul_functional (Φ : LP →ₗ[ℂ] ℂ) (ξ σr : ℂ)
    (hσ : σr ^ 2 = HeckeEigensystem.cNorm v * ξ)
    (hNws : Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (k j : ℕ) :
    ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      SatakeCombination.slotCoeff K L ws v k j r *
        (Φ ((T 1 + T (-1)) ^ r 0) * σr ^ r 0 * ξ ^ r 1) =
      Φ ((T (SatakeCombination.slotDeg K L ws v) + T (-(SatakeCombination.slotDeg K L ws v : ℤ))) ^ k) *
        σr ^ (SatakeCombination.slotDeg K L ws v * k) * ξ ^ (SatakeCombination.slotDeg K L ws v * j) := by
  have hΦC : ∀ (a : ℂ) (p : LP), Φ (C a * p) = a * Φ p := fun a p => by
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  set f : ℕ := SatakeCombination.slotDeg K L ws v with hf
  have hf1 : 1 ≤ f := one_le_slotDeg K L ws v
  set N : ℂ := HeckeEigensystem.cNorm v with hN
  have hN0 : N ≠ 0 := HeckeEigensystem.cNorm_ne_zero v
  have hNw : (Ideal.absNorm (ws v).1.asIdeal : ℂ) = N ^ f := by
    rw [hN, HeckeEigensystem.cNorm, hNws]; push_cast; rfl

  set α : LP := C σr * T 1 with hα
  set β : LP := C σr * T (-1) with hβ
  set X : LP := C σr * (T 1 + T (-1)) with hX
  set Y : LP := C (σr ^ 2) with hY
  have hXab : X = α + β := by rw [hX, hα, hβ, mul_add]
  have hYab : Y = α * β := by
    rw [hY, hα, hβ, mul_mul_mul_comm, ← T_add, add_neg_cancel, T_zero, mul_one, ← map_mul, sq]
  let g : Fin 2 → LP := ![X, Y]

  have hterm : ∀ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      SatakeCombination.slotCoeff K L ws v k j r * (Φ ((T 1 + T (-1)) ^ r 0) * σr ^ r 0 * ξ ^ r 1) =
        ((N ^ f) ^ j)⁻¹ * Φ (C ((SatakeCombination.slotWord K L ws v k j).coeff r) * ∏ i, g i ^ r i) := by
    intro r _
    have hXY : ∏ i, g i ^ r i = C (σr ^ r 0 * (σr ^ 2) ^ r 1) * (T 1 + T (-1)) ^ r 0 := by
      rw [Fin.prod_univ_two]
      simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hX, hY, mul_pow, ← map_pow, ← map_pow, map_mul]
      ring
    have hR : Φ (C ((SatakeCombination.slotWord K L ws v k j).coeff r) * ∏ i, g i ^ r i) =
        (SatakeCombination.slotWord K L ws v k j).coeff r * ((σr ^ r 0 * (σr ^ 2) ^ r 1) *
          Φ ((T 1 + T (-1)) ^ r 0)) := by
      rw [hXY]
      conv_lhs => rw [← mul_assoc, ← map_mul]
      rw [hΦC, mul_assoc]
    have hNv : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = N := by rw [hN]; rfl
    rw [hR, SatakeCombination.slotCoeff, hNw, hNv, show (σr ^ 2) ^ r 1 = N ^ r 1 * ξ ^ r 1 by rw [hσ, mul_pow]]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum]

  have heval : ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      C ((SatakeCombination.slotWord K L ws v k j).coeff r) * ∏ i, g i ^ r i =
        MvPolynomial.eval₂ C g (SatakeCombination.slotWord K L ws v k j) :=
    (MvPolynomial.eval₂_eq' C g _).symm
  rw [heval]

  have hsw : SatakeCombination.slotWord K L ws v k j =
      satakePow f (MvPolynomial.X 0) (MvPolynomial.X 1) ^ k * ((MvPolynomial.X 1) ^ f) ^ j := by
    rw [SatakeCombination.slotWord, SatakeCombination.univWord, Nat.sub_add_cancel hf1]
  have h1 : MvPolynomial.eval₂ C g (SatakeCombination.slotWord K L ws v k j) =
      satakePow f X Y ^ k * (Y ^ f) ^ j := by
    rw [hsw, ← MvPolynomial.coe_eval₂Hom, map_mul, map_pow, map_pow, map_pow, map_satakePow]
    simp [g]
  have h2 : satakePow f X Y = C (σr ^ f) * (T f + T (-(f : ℤ))) := by
    rw [hXab, hYab, satakePow_sum_prod, hα, hβ, mul_pow, mul_pow, ← map_pow, T_pow, T_pow, mul_one,
      mul_neg_one, mul_add]
  have h3 : Φ (MvPolynomial.eval₂ C g (SatakeCombination.slotWord K L ws v k j)) =
      (σr ^ f) ^ k * ((σr ^ 2) ^ f) ^ j * Φ ((T f + T (-(f : ℤ))) ^ k) := by
    rw [h1, h2, hY, mul_pow, ← map_pow, ← map_pow, ← map_pow, mul_right_comm, ← map_mul, hΦC]
  rw [h3, show ((σr ^ 2) ^ f) ^ j = (N ^ f) ^ j * (ξ ^ f) ^ j by rw [hσ, mul_pow, mul_pow]]
  field_simp
  ring

end SlotPlaceAux

open SlotPlaceAux LaurentPolynomial AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (w' : HeightOneSpectrum (𝓞 L))
    (ξ ζ σr s : ℂ)
    (hσ : σr ^ 2 = HeckeEigensystem.cNorm v * ξ)
    (hs : ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) = σr ^ SatakeCombination.slotDeg K L ws v)
    (hζ : ξ ^ SatakeCombination.slotDeg K L ws v = ζ)
    (hNws : Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (k j : ℕ) :
    ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      SatakeCombination.slotCoeff K L ws v k j r *
        ((1 + (-1 : ℂ) ^ r 0) / 2 * (4 * (HeckeEigensystem.cNorm v * ξ)) ^ (r 0 / 2) *
          ((∏ n ∈ Finset.range (r 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ξ ^ r 1) =
      ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) ^ k * ζ ^ j *
        ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff 0 := by
  have hf1 := one_le_slotDeg K L ws v
  have hf0 : (SatakeCombination.slotDeg K L ws v : ℤ) ≠ 0 := by
    exact_mod_cast (show SatakeCombination.slotDeg K L ws v ≠ 0 by omega)

  have hsum : ∀ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      SatakeCombination.slotCoeff K L ws v k j r *
        ((1 + (-1 : ℂ) ^ r 0) / 2 * (4 * (HeckeEigensystem.cNorm v * ξ)) ^ (r 0 / 2) *
          ((∏ n ∈ Finset.range (r 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ξ ^ r 1) =
      SatakeCombination.slotCoeff K L ws v k j r *
        (coeff0 ((T 1 + T (-1)) ^ r 0) * σr ^ r 0 * ξ ^ r 1) := by
    intro r _
    rw [momentA_eq _ _ _ hσ, coeff0_apply, T_add_T_neg_pow_apply_zero 1 one_ne_zero]
  rw [Finset.sum_congr rfl hsum, sum_slotCoeff_mul_functional K L ws v coeff0 ξ σr hσ hNws k j, coeff0_apply,
    T_add_T_neg_pow_apply_zero _ hf0, T_add_T_neg_pow_apply_zero 1 one_ne_zero, ← hζ, hs, ← pow_mul,
    ← pow_mul]
  ring

end S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero
end P2MW
export P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero (solution)
