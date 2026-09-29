-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/aa25d7fd-495a-59f1-a61a-0e706b69a054

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Theorems.Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm
open scoped nonZeroDivisors

noncomputable section

section Helpers

variable (F : Type) [Field F] [NumberField F]

private def piIdele (v : HeightOneSpectrum (𝓞 F)) : (FiniteAdeleRing (𝓞 F) F)ˣ :=
  localUnit (𝓞 F) F v (uniformizerUnit F v)

private theorem exponentAt_inv (w : HeightOneSpectrum (𝓞 F)) (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finIdeleExponentAt F w δ⁻¹ = -finIdeleExponentAt F w δ := by
  have h := finIdeleExponentAt_mul F w δ δ⁻¹
  rw [mul_inv_cancel, finIdeleExponentAt_one] at h
  linarith

private theorem exponentAt_zpow (w : HeightOneSpectrum (𝓞 F)) (δ : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (n : ℤ) : finIdeleExponentAt F w (δ ^ n) = n * finIdeleExponentAt F w δ := by
  refine Int.induction_on n ?_ (fun i ih => ?_) (fun i ih => ?_)
  · rw [zpow_zero, finIdeleExponentAt_one, zero_mul]
  · rw [zpow_add_one, finIdeleExponentAt_mul, ih]
    ring
  · rw [zpow_sub_one, finIdeleExponentAt_mul, ih, exponentAt_inv]
    ring

private theorem exponentAt_prod (w : HeightOneSpectrum (𝓞 F)) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (f : HeightOneSpectrum (𝓞 F) → (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finIdeleExponentAt F w (∏ v ∈ s, f v) = ∑ v ∈ s, finIdeleExponentAt F w (f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, finIdeleExponentAt_one]
  | insert v t hvt ih => rw [Finset.prod_insert hvt, finIdeleExponentAt_mul, ih, Finset.sum_insert hvt]

private theorem exponentAt_box_of_mem (s : Finset (HeightOneSpectrum (𝓞 F)))
    (k : HeightOneSpectrum (𝓞 F) → ℤ) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ s) :
    finIdeleExponentAt F w (∏ v ∈ s, piIdele F v ^ k v) = k w := by
  classical
  rw [exponentAt_prod]
  simp_rw [exponentAt_zpow, piIdele, finIdeleExponentAt_localUnit_uniformizer, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq s w, if_pos hw]

private theorem exponentAt_box_of_notMem (s : Finset (HeightOneSpectrum (𝓞 F)))
    (k : HeightOneSpectrum (𝓞 F) → ℤ) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ s) :
    finIdeleExponentAt F w (∏ v ∈ s, piIdele F v ^ k v) = 0 := by
  classical
  rw [exponentAt_prod]
  simp_rw [exponentAt_zpow, piIdele, finIdeleExponentAt_localUnit_uniformizer, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq s w, if_neg hw]

private theorem valued_coe_ne_zero (w : HeightOneSpectrum (𝓞 F)) (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  intro h
  have : ((δ * δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = 1 := by
    rw [mul_inv_cancel, Units.val_one, coe_one_apply]
  rw [Units.val_mul, coe_mul_apply, h, zero_mul] at this
  exact zero_ne_one this

private theorem valued_coe_eq_exp (w : HeightOneSpectrum (𝓞 F)) (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) w) = WithZero.exp (-finIdeleExponentAt F w δ) := by
  rw [finIdeleExponentAt, neg_neg, WithZero.exp_log (valued_coe_ne_zero F w δ)]

private theorem max_valued_ne_zero (x y p q : FiniteAdeleRing (𝓞 F) F) (h : x * p + y * q = 1)
    (v : HeightOneSpectrum (𝓞 F)) : max (Valued.v (x v)) (Valued.v (y v)) ≠ 0 := by
  intro hmax
  have hx : Valued.v (x v) = 0 := le_antisymm ((le_max_left _ _).trans hmax.le) zero_le'
  have hy : Valued.v (y v) = 0 := le_antisymm ((le_max_right _ _).trans hmax.le) zero_le'
  rw [map_eq_zero] at hx hy
  have h1 : x v * p v + y v * q v = 1 := by
    have h2 := congrArg (fun z : FiniteAdeleRing (𝓞 F) F => z v) h
    simpa only [coe_add_apply, coe_mul_apply, coe_one_apply] using h2
  rw [hx, hy, zero_mul, zero_mul, add_zero] at h1
  exact zero_ne_one h1

private theorem eventually_max_valued_eq_one (x y p q : FiniteAdeleRing (𝓞 F) F)
    (h : x * p + y * q = 1) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      max (Valued.v (x v)) (Valued.v (y v)) = 1 := by
  filter_upwards [x.2, y.2, p.2, q.2] with v hx hy hp hq
  have hx' : Valued.v (x v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx
  have hy' : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hy
  have hp' : Valued.v (p v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hp
  have hq' : Valued.v (q v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hq
  have h1 : x v * p v + y v * q v = 1 := by
    have h2 := congrArg (fun z : FiniteAdeleRing (𝓞 F) F => z v) h
    simpa only [coe_add_apply, coe_mul_apply, coe_one_apply] using h2
  have h3 : Valued.v (x v * p v + y v * q v) ≤ max (Valued.v (x v * p v)) (Valued.v (y v * q v)) :=
    Valuation.map_add _ _ _
  rw [h1, map_one, map_mul, map_mul] at h3
  exact le_antisymm (max_le hx' hy')
    (h3.trans (max_le_max (mul_le_of_le_one_right' hp') (mul_le_of_le_one_right' hq')))

private theorem exists_row_combination
    (g : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ p q : FiniteAdeleRing (𝓞 F) F,
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 * p +
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 * q = 1 := by
  refine ⟨((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1,
    ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1, ?_⟩
  have h := congrFun (congrFun (Units.mul_inv g) 1) 1
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using h

private theorem max_mul_exp_ne_zero {α β : WithZero (Multiplicative ℤ)} (hαβ : max α β ≠ 0) (m : ℤ) :
    max (α * WithZero.exp m) β ≠ 0 := by
  intro hm
  apply hαβ
  have hα : α * WithZero.exp m = 0 := le_antisymm ((le_max_left _ _).trans hm.le) zero_le'
  have hβ : β = 0 := le_antisymm ((le_max_right _ _).trans hm.le) zero_le'
  rcases mul_eq_zero.mp hα with hα0 | hα0
  · rw [hα0, hβ, max_self]
  · exact absurd hα0 WithZero.exp_ne_zero

private theorem exists_residue (h : ℕ) (hh : 0 < h) (c : ℤ) :
    ∃ t : ℤ, 0 ≤ t ∧ t < h ∧ Int.ModEq (h : ℤ) t c :=
  ⟨c % h, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), Int.mod_modEq _ _⟩

private theorem exists_exponent_modEq (h : ℕ) (hh : 0 < h) (α β : WithZero (Multiplicative ℤ))
    (r : ℤ) :
    ∃ n : ℕ, n ≤ 2 * h ∧
      Int.ModEq (h : ℤ) ((n : ℤ) + 2 * (-WithZero.log (max (α * WithZero.exp (n : ℤ)) β))) r := by
  have hmono : Monotone (WithZero.exp : ℤ → WithZero (Multiplicative ℤ)) :=
    fun a b hab => WithZero.exp_le_exp.mpr hab
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    obtain ⟨t, ht0, hth, htmod⟩ := exists_residue h hh (r + 2 * WithZero.log β)
    refine ⟨t.toNat, ?_, ?_⟩
    · have h1 := Int.toNat_of_nonneg ht0
      omega
    · have hm : max (0 : WithZero (Multiplicative ℤ)) β = β := max_eq_right zero_le'
      rw [Int.toNat_of_nonneg ht0, zero_mul, hm]
      have h' := htmod.add_right (2 * -WithZero.log β)
      rwa [show r + 2 * WithZero.log β + 2 * -WithZero.log β = r by ring] at h'
  · obtain ⟨A, rfl⟩ : ∃ A : ℤ, α = WithZero.exp A := ⟨_, (WithZero.exp_log hα).symm⟩
    rcases eq_or_ne β 0 with hβ | hβ
    · subst hβ
      obtain ⟨t, ht0, hth, htmod⟩ := exists_residue h hh (-r - 2 * A)
      refine ⟨t.toNat, ?_, ?_⟩
      · have h1 := Int.toNat_of_nonneg ht0
        omega
      · have hm : max (WithZero.exp A * WithZero.exp t) (0 : WithZero (Multiplicative ℤ)) =
            WithZero.exp A * WithZero.exp t := max_eq_left zero_le'
        rw [Int.toNat_of_nonneg ht0, hm, ← WithZero.exp_add, WithZero.log_exp]
        have h' := htmod.neg.sub_right (2 * A)
        rw [show -(-r - 2 * A) - 2 * A = r by ring] at h'
        rw [show t + 2 * -(A + t) = -t - 2 * A by ring]
        exact h'
    · obtain ⟨B, rfl⟩ : ∃ B : ℤ, β = WithZero.exp B := ⟨_, (WithZero.exp_log hβ).symm⟩
      rcases le_or_gt ((h : ℤ) - 1) (B - A) with hk | hk
      · obtain ⟨t, ht0, hth, htmod⟩ := exists_residue h hh (r + 2 * B)
        refine ⟨t.toNat, ?_, ?_⟩
        · have h1 := Int.toNat_of_nonneg ht0
          omega
        · rw [Int.toNat_of_nonneg ht0, ← WithZero.exp_add, ← hmono.map_max, WithZero.log_exp,
            max_eq_right (show A + t ≤ B by omega)]
          have h' := htmod.add_right (2 * -B)
          rwa [show r + 2 * B + 2 * -B = r by ring] at h'
      · have hk0 : 0 ≤ max (B - A) 0 := le_max_right _ _
        have hk1 : B - A ≤ max (B - A) 0 := le_max_left _ _
        have hk2 : max (B - A) 0 ≤ (h : ℤ) - 1 := max_le (by omega) (by omega)
        obtain ⟨t, ht0, hth, htmod⟩ := exists_residue h hh (-r - 2 * A - max (B - A) 0)
        have hkt : 0 ≤ max (B - A) 0 + t := add_nonneg hk0 ht0
        refine ⟨(max (B - A) 0 + t).toNat, ?_, ?_⟩
        · have h1 := Int.toNat_of_nonneg hkt
          omega
        · rw [Int.toNat_of_nonneg hkt, ← WithZero.exp_add, ← hmono.map_max, WithZero.log_exp,
            max_eq_left (show B ≤ A + (max (B - A) 0 + t) by omega)]
          have h' := (htmod.add_left (max (B - A) 0)).neg.sub_right (2 * A)
          rw [show -(max (B - A) 0 + (-r - 2 * A - max (B - A) 0)) - 2 * A = r by ring] at h'
          rw [show max (B - A) 0 + t + 2 * -(A + (max (B - A) 0 + t)) =
            -(max (B - A) 0 + t) - 2 * A by ring]
          exact h'

private def twistExp (x y : FiniteAdeleRing (𝓞 F) F) (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  -WithZero.log (max (Valued.v (x v) * WithZero.exp (m : ℤ)) (Valued.v (y v)))

private theorem exists_twist (h : ℕ) (hh : 0 < h) (x y : FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) (r : ℤ) :
    ∃ n : ℕ, n ≤ 2 * h ∧ Int.ModEq (h : ℤ) ((n : ℤ) + 2 * twistExp F x y n v) r := by
  simpa only [twistExp] using exists_exponent_modEq h hh (Valued.v (x v)) (Valued.v (y v)) r

private theorem mk0_eq_prod_content (S : Finset (HeightOneSpectrum (𝓞 F))) (I : (Ideal (𝓞 F))⁰)
    (hI : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ (I : Ideal (𝓞 F)) → v ∈ S) :
    ClassGroup.mk0 I = ∏ v ∈ S, contentHomFin F (piIdele F v) ^
      FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
  classical
  have hI0 : (I : Ideal (𝓞 F)) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  have hI0' : ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hI0
  have hδ : contentHomFin F (∏ v ∈ S, piIdele F v ^
      FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) =
      ∏ v ∈ S, contentHomFin F (piIdele F v) ^
        FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun v _ => map_zpow _ _ _)
  rw [← hδ, contentHomFin_apply, ← ClassGroup.mk_mk0 F]
  refine congrArg (ClassGroup.mk F) (Units.ext ?_)
  rw [FractionalIdeal.coe_mk0, Units.val_mk0]
  conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 F) (K := F) hI0']
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 F) (K := F)
    (finAssocFracIdeal_ne_zero F _)]
  refine finprod_congr fun w => congrArg _ ?_
  rw [count_finAssocFracIdeal]
  by_cases hw : w ∈ S
  · rw [exponentAt_box_of_mem F S _ hw]
  · rw [exponentAt_box_of_notMem F S _ hw, FractionalIdeal.count_coe F w hI0, Nat.cast_eq_zero]
    by_contra hne
    exact hw (hI w ((Associates.count_ne_zero_iff_dvd hI0 w.irreducible).mp hne))

end Helpers

theorem solution
    (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ),
      ∀ g : Matrix.GeneralLinearGroup (Fin 2)
        (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F),
        ∃ a ∈ R, ∃ d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
              max
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
                    ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v))) ∧
          AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
            AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g) := by
  classical
  obtain ⟨S, hS⟩ := ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd (𝓞 F)
  have hh : 0 < Nat.card (ClassGroup (𝓞 F)) := Nat.card_pos
  have hPh : ∀ v : HeightOneSpectrum (𝓞 F),
      contentHomFin F (piIdele F v) ^ Nat.card (ClassGroup (𝓞 F)) = 1 := fun _ => pow_card_eq_one'
  refine ⟨(Fintype.piFinset fun _ : S => Finset.range (2 * Nat.card (ClassGroup (𝓞 F)) + 1)).image
    (fun m : S → ℕ => ∏ v ∈ S.attach, piIdele F (v : HeightOneSpectrum (𝓞 F)) ^ ((m v : ℕ) : ℤ)), ?_⟩
  intro g
  obtain ⟨p, q, hpq⟩ := exists_row_combination F g
  obtain ⟨x, hx⟩ : ∃ x, x = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 := ⟨_, rfl⟩
  rw [← hx, ← hy] at hpq
  rw [← hx, ← hy]
  have hne : ∀ v, max (Valued.v (x v)) (Valued.v (y v)) ≠ 0 := max_valued_ne_zero F x y p q hpq
  have hfin := Filter.eventually_cofinite.mp (eventually_max_valued_eq_one F x y p q hpq)

  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), T = hfin.toFinset := ⟨_, rfl⟩
  have hT_notMem : ∀ {v}, v ∉ T → max (Valued.v (x v)) (Valued.v (y v)) = 1 := by
    intro v hv
    by_contra hne1
    exact hv (hT ▸ hfin.mem_toFinset.mpr hne1)

  obtain ⟨dOff, hdOff⟩ : ∃ dOff : (FiniteAdeleRing (𝓞 F) F)ˣ,
      dOff = ∏ v ∈ T \ S, piIdele F v ^ twistExp F x y 0 v := ⟨_, rfl⟩
  have hEdOff_S : ∀ w ∈ S, finIdeleExponentAt F w dOff = 0 := by
    intro w hw
    rw [hdOff]
    exact exponentAt_box_of_notMem F (T \ S) _ (fun h' => (Finset.mem_sdiff.mp h').2 hw)
  have hEdOff : ∀ w, w ∉ S → finIdeleExponentAt F w dOff = twistExp F x y 0 w := by
    intro w hw
    rw [hdOff]
    by_cases hwT : w ∈ T
    · exact exponentAt_box_of_mem F (T \ S) _ (Finset.mem_sdiff.mpr ⟨hwT, hw⟩)
    · rw [exponentAt_box_of_notMem F (T \ S) _ (fun h' => hwT (Finset.mem_sdiff.mp h').1), twistExp,
        Nat.cast_zero, WithZero.exp_zero, mul_one, hT_notMem hwT, WithZero.log_one, neg_zero]

  obtain ⟨I, hI, hIS⟩ := hS ((contentHomFin F dOff ^ 2)⁻¹ *
    contentHomFin F (Matrix.GeneralLinearGroup.det g))
  have hgen := mk0_eq_prod_content F S I hIS

  choose nn hnn using fun v : HeightOneSpectrum (𝓞 F) => exists_twist F (Nat.card (ClassGroup (𝓞 F)))
    hh x y v (FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))
  obtain ⟨a, ha⟩ : ∃ a : (FiniteAdeleRing (𝓞 F) F)ˣ,
      a = ∏ v ∈ S, piIdele F v ^ ((nn v : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨dS, hdS⟩ : ∃ dS : (FiniteAdeleRing (𝓞 F) F)ˣ,
      dS = ∏ v ∈ S, piIdele F v ^ twistExp F x y (nn v) v := ⟨_, rfl⟩
  have hEa_mem : ∀ w ∈ S, finIdeleExponentAt F w a = ((nn w : ℕ) : ℤ) := by
    intro w hw
    rw [ha]
    exact exponentAt_box_of_mem F S _ hw
  have hEa_notMem : ∀ w, w ∉ S → finIdeleExponentAt F w a = 0 := by
    intro w hw
    rw [ha]
    exact exponentAt_box_of_notMem F S _ hw
  have hEdS_mem : ∀ w ∈ S, finIdeleExponentAt F w dS = twistExp F x y (nn w) w := by
    intro w hw
    rw [hdS]
    exact exponentAt_box_of_mem F S _ hw
  have hEdS_notMem : ∀ w, w ∉ S → finIdeleExponentAt F w dS = 0 := by
    intro w hw
    rw [hdS]
    exact exponentAt_box_of_notMem F S _ hw
  refine ⟨a, ?_, dS * dOff, fun w => ?_, ?_⟩
  ·
    rw [Finset.mem_image]
    refine ⟨fun v => nn v, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro v
      rw [Finset.mem_range]
      have h1 := (hnn v).1
      omega
    · rw [ha]
      exact Finset.prod_attach S (fun v => piIdele F v ^ ((nn v : ℕ) : ℤ))
  ·
    rw [valued_coe_eq_exp, finIdeleExponentAt_mul, coe_mul_apply, map_mul, valued_coe_eq_exp F w a⁻¹,
      exponentAt_inv, neg_neg]
    by_cases hw : w ∈ S
    · rw [hEdS_mem w hw, hEdOff_S w hw, add_zero, hEa_mem w hw, twistExp, neg_neg,
        WithZero.exp_log (max_mul_exp_ne_zero (hne w) _)]
    · rw [hEdS_notMem w hw, hEdOff w hw, zero_add, hEa_notMem w hw, twistExp, neg_neg,
        WithZero.exp_log (max_mul_exp_ne_zero (hne w) _), Nat.cast_zero]
  ·
    have hkey : contentHomFin F a * contentHomFin F dS ^ 2 = ClassGroup.mk0 I := by
      rw [hgen, ha, hdS, map_prod, map_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      have hmod : (((nn v : ℕ) : ℤ) + 2 * twistExp F x y (nn v) v) % (Nat.card (ClassGroup (𝓞 F)) : ℤ) =
          FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) %
            (Nat.card (ClassGroup (𝓞 F)) : ℤ) := (hnn v).2
      rw [map_zpow, map_zpow, sq, ← zpow_add, ← zpow_add,
        show ((nn v : ℕ) : ℤ) + (twistExp F x y (nn v) v + twistExp F x y (nn v) v) =
          ((nn v : ℕ) : ℤ) + 2 * twistExp F x y (nn v) v by ring,
        zpow_eq_zpow_emod' _ (hPh v), hmod, ← zpow_eq_zpow_emod' _ (hPh v)]
    rw [map_mul, mul_pow, ← mul_assoc, hkey, hI, mul_comm, mul_inv_cancel_left]

end

end S_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq (solution)
