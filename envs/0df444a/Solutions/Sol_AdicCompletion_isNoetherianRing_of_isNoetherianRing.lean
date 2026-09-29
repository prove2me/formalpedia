-- Prove2me | solution 1 for AdicCompletion.isNoetherianRing_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/20d3c716-d894-5fc8-b40e-2ca9519e78f6

import Mathlib
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace AdicCompletionNoetherian

open MvPolynomial MvPowerSeries

variable {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (f : Fin n → R)

noncomputable abbrev XI : Ideal (MvPolynomial (Fin n) R) := MvPolynomial.idealOfVars (Fin n) R

noncomputable abbrev ev : MvPolynomial (Fin n) R →+* R := (MvPolynomial.aeval f).toRingHom

lemma ev_C (r : R) : ev f (C r) = r := by simp [ev]

lemma ev_surjective : Function.Surjective (ev f) := fun r => ⟨C r, ev_C f r⟩

lemma map_XI_eq : Ideal.map (ev f) (XI) = Ideal.span (Set.range f) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp [ev]

variable (hf : Ideal.span (Set.range f) = I)
include hf

lemma XI_le_comap : (XI : Ideal (MvPolynomial (Fin n) R)) ≤ I.comap (ev f) := by
  rw [← Ideal.map_le_iff_le_comap, map_XI_eq, hf]

lemma XI_pow_le_comap (k : ℕ) :
    (XI : Ideal (MvPolynomial (Fin n) R)) ^ k ≤ (I ^ k).comap (ev f) :=
  (Ideal.pow_right_mono (XI_le_comap I f hf) k).trans (Ideal.le_comap_pow _ k)

lemma map_XI_pow_eq (k : ℕ) : Ideal.map (ev f) (XI ^ k) = I ^ k := by
  rw [Ideal.map_pow, map_XI_eq, hf]

noncomputable def phi (k : ℕ) : MvPowerSeries (Fin n) R →+* R ⧸ I ^ k :=
  (Ideal.quotientMap (I ^ k) (ev f) (XI_pow_le_comap I f hf k)).comp
    (MvPowerSeries.truncTotalAlgHom (Fin n) R k).toRingHom

lemma phi_apply (k : ℕ) (p : MvPowerSeries (Fin n) R) :
    phi I f hf k p = Ideal.Quotient.mk (I ^ k) (ev f (truncTotal k p)) := by
  simp [phi, Ideal.quotientMap_mk]

lemma phi_eq_of_sub_mem (k : ℕ) (p : MvPowerSeries (Fin n) R) (P : MvPolynomial (Fin n) R)
    (h : truncTotal k p - P ∈ (XI : Ideal (MvPolynomial (Fin n) R)) ^ k) :
    phi I f hf k p = Ideal.Quotient.mk (I ^ k) (ev f P) := by
  rw [phi_apply, Ideal.Quotient.eq, ← map_sub]
  exact XI_pow_le_comap I f hf k h

lemma phi_compat {k l : ℕ} (hkl : k ≤ l) :
    (Ideal.Quotient.factorPow I hkl).comp (phi I f hf l) = phi I f hf k := by
  ext p
  simp only [RingHom.coe_comp, Function.comp_apply, phi_apply, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact XI_pow_le_comap I f hf k
    (truncTotal_sub_truncTotal_mem_pow_idealOfVars hkl le_rfl _)

noncomputable def Phi : MvPowerSeries (Fin n) R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (fun k => phi I f hf k) (fun hkl => phi_compat I f hf hkl)

lemma evalₐ_Phi (k : ℕ) (p : MvPowerSeries (Fin n) R) :
    AdicCompletion.evalₐ I k (Phi I f hf p) = phi I f hf k p :=
  AdicCompletion.evalₐ_liftRingHom I _ _ k p

lemma Phi_surjective : Function.Surjective (Phi I f hf) := by
  intro y
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R y

  have hd : ∀ j : ℕ, a.val (j + 1) - a.val j ∈ I ^ j := by
    intro j
    have h := a.property (Nat.le_succ j)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [← neg_sub]; exact neg_mem h
  have hP : ∀ j : ℕ, ∃ P : MvPolynomial (Fin n) R,
      P ∈ (XI : Ideal (MvPolynomial (Fin n) R)) ^ j ∧ ev f P = a.val (j + 1) - a.val j := by
    intro j
    have hmem : a.val (j + 1) - a.val j ∈ Ideal.map (ev f) (XI ^ j) := by
      rw [map_XI_pow_eq I f hf]; exact hd j
    exact (Ideal.mem_map_iff_of_surjective _ (ev_surjective f)).mp hmem
  choose P hPmem hPev using hP

  let g : MvPowerSeries (Fin n) R :=
    fun x => ∑ j ∈ Finset.range (Finsupp.degree x + 1), MvPolynomial.coeff x (P j)
  refine ⟨g + MvPowerSeries.C (a.val 0), ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro k
  rw [map_add, map_add, evalₐ_Phi, evalₐ_Phi, AdicCompletion.evalₐ_mk]

  have hg : truncTotal k g - ∑ j ∈ Finset.range k, P j ∈
      (XI : Ideal (MvPolynomial (Fin n) R)) ^ k := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hx, MvPolynomial.coeff_sum, sub_eq_zero]
    change (∑ j ∈ Finset.range (Finsupp.degree x + 1), MvPolynomial.coeff x (P j)) = _
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro j hj hj'
    simp only [Finset.mem_range, not_lt] at hj hj'
    exact (MvPolynomial.mem_pow_idealOfVars_iff' j (P j)).mp (hPmem j) x (by omega)
  rw [phi_eq_of_sub_mem I f hf k g _ hg, map_sum]
  simp_rw [hPev]
  rw [Finset.sum_range_sub (fun j => a.val j) k]

  have hC : phi I f hf k (MvPowerSeries.C (a.val 0)) = Ideal.Quotient.mk (I ^ k) (a.val 0) := by
    rw [phi_eq_of_sub_mem I f hf k _ (MvPolynomial.C (a.val 0)) ?_, ev_C]
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hx, MvPowerSeries.coeff_C,
      MvPolynomial.coeff_C, sub_eq_zero]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  rw [hC, ← map_add, sub_add_cancel]

end AdicCompletionNoetherian

theorem solution {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  haveI : IsNoetherianRing (MvPowerSeries (Fin n) R) := MvPowerSeries.isNoetherianRing_of_finite
  exact isNoetherianRing_of_surjective _ _ (AdicCompletionNoetherian.Phi I f hf)
    (AdicCompletionNoetherian.Phi_surjective I f hf)

end S_AdicCompletion_isNoetherianRing_of_isNoetherianRing
end P2MW
export P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing (solution)
