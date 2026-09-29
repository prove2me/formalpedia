-- Prove2me | solution 1 for AlgebraicCurve.Place.eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/00b36953-182d-5283-8fce-03fb62fb4188

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_evalEval
import Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_mul
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

namespace JetBridge

theorem coeff_evalEval_C_add_X_congr {K : Type*} [CommRing K] (G : Polynomial (Polynomial K)) (a : K)
    (m : ℕ) (Y Y' : PowerSeries K)
    (h : ∀ r, r < m → PowerSeries.coeff r Y = PowerSeries.coeff r Y') :
    ∀ r, r < m →
      PowerSeries.coeff r ((G.map (mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.C a + PowerSeries.X) Y)
        = PowerSeries.coeff r ((G.map (mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.C a + PowerSeries.X) Y') := by
  set Gf := G.map (mapRingHom (algebraMap K (PowerSeries K))) with hGf

  have hdvd : (PowerSeries.X : PowerSeries K) ^ m ∣ Y - Y' := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro r hr
    rw [map_sub, h r hr, sub_self]

  have hdvd2 : Y - Y' ∣ Gf.evalEval (PowerSeries.C a + PowerSeries.X) Y
      - Gf.evalEval (PowerSeries.C a + PowerSeries.X) Y' := by
    have h1 : (C Y - C Y' : Polynomial (PowerSeries K)) ∣ Gf.eval (C Y) - Gf.eval (C Y') :=
      sub_dvd_eval_sub (C Y) (C Y') Gf
    have h2 := map_dvd (evalRingHom (PowerSeries.C a + PowerSeries.X)) h1
    simpa [evalEval] using h2
  intro r hr
  have h3 : (PowerSeries.X : PowerSeries K) ^ m ∣ Gf.evalEval (PowerSeries.C a + PowerSeries.X) Y
      - Gf.evalEval (PowerSeries.C a + PowerSeries.X) Y' := dvd_trans hdvd hdvd2
  rw [PowerSeries.X_pow_dvd_iff] at h3
  have h4 := h3 r hr
  rw [map_sub, sub_eq_zero] at h4
  exact h4

theorem taylorCoeff_evalEval_eq_coeff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (p : Polynomial (Polynomial K)) (r : ℕ) :
    taylorCoeff v (z - algebraMap K F (v.evalAt z)) r
        ((p.map (mapRingHom (algebraMap K F))).evalEval z y)
      = PowerSeries.coeff r ((p.map (mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.C (v.evalAt z) + PowerSeries.X)
          (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y)) := by
  have h := mk_taylorCoeff_evalEval v hv ht hz hy p
  rw [mk_taylorCoeff_eq_C_add_X v hv hz ht] at h
  have h2 := congrArg (PowerSeries.coeff r) h
  rwa [PowerSeries.coeff_mk] at h2

theorem inv_mem_of_evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {s : F} (hs : s ∈ v.toValuationSubring)
    (hs0 : v.evalAt s ≠ 0) : s⁻¹ ∈ v.toValuationSubring := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨s, hs⟩ ≠ 0 := by
    rw [← v.algebraMap_evalAt hv hs]
    exact (_root_.map_ne_zero _).mpr hs0
  have hu : IsUnit (⟨s, hs⟩ : v.toValuationSubring) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : v.toValuationSubring) : F) = s := by rw [hu]
  have hinv : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = s⁻¹ := by
    have h1 : s * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [← hinv]
  exact ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).2

theorem eq_taylorCoeff_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {s : F} (hs : s ∈ v.toValuationSubring) (hs0 : v.evalAt s ≠ 0)
    (m : ℕ) (σ : ℕ → K)
    (hσ : ∀ r, r < m →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ x.1 * taylorCoeff v t x.2 s = if r = 0 then 1 else 0) :
    ∀ r, r < m → σ r = taylorCoeff v t r s⁻¹ := by
  have hsinv : s⁻¹ ∈ v.toValuationSubring := inv_mem_of_evalAt_ne_zero v hv hs hs0
  have hs' : s ≠ 0 := by
    intro h0; apply hs0; rw [h0]
    have := taylorCoeff_algebraMap v t (0 : K) 0
    rw [map_zero] at this
    simpa using this

  have hτ : ∀ r, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, taylorCoeff v t x.1 s⁻¹ * taylorCoeff v t x.2 s
      = if r = 0 then 1 else 0 := by
    intro r
    rw [← taylorCoeff_mul v hv ht hsinv hs r, inv_mul_cancel₀ hs',
      show (1 : F) = algebraMap K F 1 from (map_one _).symm, taylorCoeff_algebraMap]
  have ha0 : taylorCoeff v t 0 s ≠ 0 := by rwa [taylorCoeff_zero]

  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    have e1 := hσ r hr
    have e2 := hτ r
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Nat.sub_self] at e1 e2
    have hsum : ∑ k ∈ Finset.range r, σ k * taylorCoeff v t (r - k) s
        = ∑ k ∈ Finset.range r, taylorCoeff v t k s⁻¹ * taylorCoeff v t (r - k) s :=
      Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hk; omega)]
    rw [hsum] at e1
    have e3 : σ r * taylorCoeff v t 0 s = taylorCoeff v t r s⁻¹ * taylorCoeff v t 0 s := by
      have := e1.trans e2.symm
      exact add_left_cancel this
    exact mul_right_cancel₀ ha0 e3

theorem eq_taylorCoeff_of_forall_coeff_evalEval_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0)
    (m : ℕ) (w : ℕ → K) (hw0 : w 0 = v.evalAt y)
    (hw : ∀ r, r < m → PowerSeries.coeff r
        ((G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.C (v.evalAt z) + PowerSeries.X) (PowerSeries.mk w)) = 0) :
    ∀ r, r < m → w r = taylorCoeff v (z - algebraMap K F (v.evalAt z)) r y := by
  set a : PowerSeries K := PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y
    with ha
  set x : PowerSeries K := PowerSeries.C (v.evalAt z) + PowerSeries.X with hx
  set p : Polynomial (Polynomial (PowerSeries K)) :=
    G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K))) with hp
  set f : Polynomial (PowerSeries K) := p.map (Polynomial.evalRingHom x) with hf
  set Y : PowerSeries K := PowerSeries.mk w with hYdef
  have hfeval : ∀ b, f.eval b = p.evalEval x b := fun b => Polynomial.map_evalRingHom_eval x b p

  have ha_root : f.eval a = 0 := by
    rw [hfeval]
    exact evalEval_C_add_X_mk_taylorCoeff_eq_zero v hv hz hy ht G hG

  have hYroot : (PowerSeries.X : PowerSeries K) ^ m ∣ f.eval Y := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro r hr
    rw [hfeval]
    exact hw r hr

  have ha0 : PowerSeries.constantCoeff a = v.evalAt y := by
    rw [ha, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, taylorCoeff_zero]
  have hY0 : PowerSeries.constantCoeff Y = v.evalAt y := by
    rw [hYdef, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hw0]
  have hD : PowerSeries.constantCoeff (Y - a) = 0 := by rw [map_sub, hY0, ha0, sub_self]

  have hunit : IsUnit (f.derivative.eval a) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    rw [hf, Polynomial.derivative_map, Polynomial.map_evalRingHom_eval, hp, Polynomial.derivative_map,
      ← Polynomial.map_mapRingHom_evalEval PowerSeries.constantCoeff, Polynomial.map_map,
      Polynomial.mapRingHom_comp]
    have hcc : (PowerSeries.constantCoeff (R := K)).comp (algebraMap K (PowerSeries K)) = RingHom.id K := by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, ← PowerSeries.C_eq_algebraMap, PowerSeries.constantCoeff_C, RingHom.id_apply]
    rw [hcc, Polynomial.mapRingHom_id, Polynomial.map_id, hx, map_add, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, add_zero, ha0]
    exact hsep

  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f a (Y - a)
  rw [show a + (Y - a) = Y by ring, ha_root, zero_add] at hk
  have hfac : f.eval Y = (Y - a) * (f.derivative.eval a + k * (Y - a)) := by rw [hk]; ring
  have hunit2 : IsUnit (f.derivative.eval a + k * (Y - a)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_mul, hD, mul_zero, add_zero,
      ← PowerSeries.isUnit_iff_constantCoeff]
    exact hunit
  obtain ⟨u, hu⟩ := hunit2
  have hdvdD : (PowerSeries.X : PowerSeries K) ^ m ∣ Y - a := by
    have e : Y - a = f.eval Y * ↑u⁻¹ := by
      rw [hfac, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact Dvd.dvd.mul_right hYroot _
  rw [PowerSeries.X_pow_dvd_iff] at hdvdD
  intro r hr
  have e := hdvdD r hr
  rw [map_sub, sub_eq_zero, hYdef, ha, PowerSeries.coeff_mk, PowerSeries.coeff_mk] at e
  exact e

theorem coeff_eq_of_forall_coeff_eval_eq_zero {K : Type*} [CommRing K] (f : Polynomial (PowerSeries K))
    (a Y : PowerSeries K) (ha : f.eval a = 0)
    (hunit : IsUnit (PowerSeries.constantCoeff (f.derivative.eval a)))
    (h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff a) (m : ℕ)
    (hY : ∀ r, r < m → PowerSeries.coeff r (f.eval Y) = 0) :
    ∀ r, r < m → PowerSeries.coeff r Y = PowerSeries.coeff r a := by
  have hYroot : (PowerSeries.X : PowerSeries K) ^ m ∣ f.eval Y := by
    rw [PowerSeries.X_pow_dvd_iff]; exact hY
  have hD : PowerSeries.constantCoeff (Y - a) = 0 := by rw [map_sub, h0, sub_self]
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f a (Y - a)
  rw [show a + (Y - a) = Y by ring, ha, zero_add] at hk
  have hfac : f.eval Y = (Y - a) * (f.derivative.eval a + k * (Y - a)) := by rw [hk]; ring
  have hunit2 : IsUnit (f.derivative.eval a + k * (Y - a)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_mul, hD, mul_zero, add_zero]
    exact hunit
  obtain ⟨u, hu⟩ := hunit2
  have hdvdD : (PowerSeries.X : PowerSeries K) ^ m ∣ Y - a := by
    have e : Y - a = f.eval Y * ↑u⁻¹ := by
      rw [hfac, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact Dvd.dvd.mul_right hYroot _
  rw [PowerSeries.X_pow_dvd_iff] at hdvdD
  intro r hr
  have e := hdvdD r hr
  rwa [map_sub, sub_eq_zero] at e

section TaylorHom

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mk_taylorCoeff_add (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    (PowerSeries.mk fun n => taylorCoeff v t n (f + g))
      = (PowerSeries.mk fun n => taylorCoeff v t n f) + (PowerSeries.mk fun n => taylorCoeff v t n g) := by
  ext n
  rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    taylorCoeff_add v hv ht hf hg]

theorem mk_taylorCoeff_mul (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    (PowerSeries.mk fun n => taylorCoeff v t n (f * g))
      = (PowerSeries.mk fun n => taylorCoeff v t n f) * (PowerSeries.mk fun n => taylorCoeff v t n g) := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, taylorCoeff_mul v hv ht hf hg n]
  exact Finset.sum_congr rfl fun x _ => by rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem mk_taylorCoeff_algebraMap (v : Place K F) (t : F) (c : K) :
    (PowerSeries.mk fun n => taylorCoeff v t n (algebraMap K F c)) = PowerSeries.C c := by
  ext n
  rw [PowerSeries.coeff_mk, taylorCoeff_algebraMap, PowerSeries.coeff_C]

theorem aeval_mem_toValuationSubring (v : Place K F) {σ : Type*} (f : σ → F)
    (hf : ∀ s, f s ∈ v.toValuationSubring) (H : MvPolynomial σ K) :
    MvPolynomial.aeval f H ∈ v.toValuationSubring := by
  induction H using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact v.algebraMap_mem' c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p s hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hf s)

theorem mk_taylorCoeff_aeval (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {σ : Type*} (f : σ → F) (hf : ∀ s, f s ∈ v.toValuationSubring) (H : MvPolynomial σ K) :
    (PowerSeries.mk fun n => taylorCoeff v t n (MvPolynomial.aeval f H))
      = MvPolynomial.aeval (fun s => PowerSeries.mk fun n => taylorCoeff v t n (f s)) H := by
  induction H using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, mk_taylorCoeff_algebraMap]
    exact PowerSeries.C_eq_algebraMap (R := K) ▸ rfl
  | add p q hp hq =>
    rw [map_add, map_add, mk_taylorCoeff_add v hv ht (aeval_mem_toValuationSubring v f hf p)
      (aeval_mem_toValuationSubring v f hf q), hp, hq]
  | mul_X p s hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      mk_taylorCoeff_mul v hv ht (aeval_mem_toValuationSubring v f hf p) (hf s), hp]

end TaylorHom

theorem coeff_evalEval_sum_monomial_eq {K : Type*} [Field K] (G : Polynomial (Polynomial K)) (a : K)
    {m : ℕ} (w : Fin m → K) (Y : PowerSeries K) (hY : ∀ i : Fin m, PowerSeries.coeff (i : ℕ) Y = w i)
    (i : Fin m) :
    ((G.map (mapRingHom (C : K →+* Polynomial K))).evalEval (C a + X)
        (∑ j : Fin m, monomial (j : ℕ) (w j))).coeff i
      = PowerSeries.coeff (i : ℕ) ((G.map (mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.C a + PowerSeries.X) Y) := by
  set W : Polynomial K := ∑ j : Fin m, monomial (j : ℕ) (w j) with hW

  have hWc : ∀ r, r < m → PowerSeries.coeff r (W : PowerSeries K) = PowerSeries.coeff r Y := by
    intro r hr
    rw [Polynomial.coeff_coe, hW, finset_sum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_eq_single (⟨r, hr⟩ : Fin m)]
    · simp [hY ⟨r, hr⟩]
    · intro j _ hj
      rw [if_neg]
      intro e
      exact hj (Fin.ext e)
    · intro h; exact absurd (Finset.mem_univ _) h

  have hC : (Polynomial.coeToPowerSeries.ringHom (R := K)).comp (C : K →+* Polynomial K)
      = algebraMap K (PowerSeries K) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
      PowerSeries.C_eq_algebraMap]
  have hcoe : Polynomial.coeToPowerSeries.ringHom (R := K)
        ((G.map (mapRingHom (C : K →+* Polynomial K))).evalEval (C a + X) W)
      = (G.map (mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.C a + PowerSeries.X) (W : PowerSeries K) := by
    rw [← Polynomial.map_mapRingHom_evalEval, Polynomial.map_map, Polynomial.mapRingHom_comp, hC,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X]
  rw [← Polynomial.coeff_coe, ← Polynomial.coeToPowerSeries.ringHom_apply, hcoe]
  exact coeff_evalEval_C_add_X_congr G a m _ _ hWc i i.2

end JetBridge

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {s : F} (hs : s ∈ v.toValuationSubring) (hs0 : v.evalAt s ≠ 0)
    (m : ℕ) (σ : ℕ → K)
    (hσ : ∀ r, r < m →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ x.1 * taylorCoeff v t x.2 s = if r = 0 then 1 else 0) :
    ∀ r, r < m → σ r = taylorCoeff v t r s⁻¹ :=
  JetBridge.eq_taylorCoeff_inv v hv ht hs hs0 m σ hσ

end S_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
end P2MW
export P2MW.S_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq (solution)
