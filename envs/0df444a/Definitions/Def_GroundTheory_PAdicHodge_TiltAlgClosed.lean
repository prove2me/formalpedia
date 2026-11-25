-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
-- name    : GroundTheory_PAdicHodge_TiltAlgClosed
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:17.912996+00:00
-- url     : https://prove2.me/theorems/0f440614-0342-5b48-95c3-bd2c186aaea5
-- title:
--   Tilt Alg Closed
-- statement:
--   Definitions and structural lemmas for Tilt Alg Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgClosed.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq
import Theorems.Thm_GroundTheory_PAdicHodge_exists_tilt_norm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open Filter Topology NNReal Polynomial
section Approximation
variable {F : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
theorem norm_coeff_rpow_le_norm_coeff_zero_rpow {L : Type*} [Field L] [Algebra F L]
    [Algebra.IsAlgebraic F L] (β : L) {i : ℕ} (hi : i < (minpoly F β).natDegree) :
    ‖(minpoly F β).coeff i‖ ^ (1 / ((minpoly F β).natDegree - i : ℝ)) ≤
      ‖(minpoly F β).coeff 0‖ ^ (1 / (minpoly F β).natDegree : ℝ) := by
  rw [← spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, ← spectralValueTerms_of_lt_natDegree _ hi]
  exact le_ciSup (spectralValueTerms_bddAbove _) i
theorem norm_coeff_comp_rpow_le {P : F[X]} (hmon : P.Monic) (hirr : Irreducible P) (x : F) {i : ℕ}
    (hi : i < P.natDegree) :
    ‖(P.comp (X + C x)).coeff i‖ ^ (1 / (P.natDegree - i : ℝ)) ≤
      ‖P.eval x‖ ^ (1 / P.natDegree : ℝ) := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) P
    (degree_pos_of_irreducible hirr).ne'
  have hmin : minpoly F (α - algebraMap F (AlgebraicClosure F) x) = P.comp (X + C x) := by
    rw [minpoly.sub_algebraMap, ← minpoly.eq_of_irreducible_of_monic hirr hα hmon]
  have hdeg : (P.comp (X + C x)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have h := norm_coeff_rpow_le_norm_coeff_zero_rpow (F := F) (L := AlgebraicClosure F)
    (α - algebraMap F (AlgebraicClosure F) x) (i := i) (by rw [hmin, hdeg]; exact hi)
  rwa [hmin, hdeg, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add] at h
theorem isAlgClosed_of_exists_approx_root
    (hdiv : ∀ z : F, z ≠ 0 → ∀ n : ℕ, 0 < n → ∃ c : F, ‖c‖ ^ n = ‖z‖)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (happrox : ∀ R : F[X], R.Monic → 0 < R.natDegree → (∀ i, ‖R.coeff i‖ ≤ 1) →
      ∃ y : F, ‖y‖ ≤ 1 ∧ ‖R.eval y‖ ≤ δ) :
    IsAlgClosed F := by
  refine IsAlgClosed.of_exists_root _ fun P hmon hirr => ?_
  set d := P.natDegree with hd
  have hd0 : 0 < d := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)

  have step : ∀ x : F, ∃ x' : F, ‖P.eval x'‖ ≤ δ * ‖P.eval x‖ ∧ ‖x' - x‖ ^ d ≤ ‖P.eval x‖ := by
    intro x
    by_cases hx : P.eval x = 0
    · exact ⟨x, by simp [hx], by rw [sub_self, norm_zero, zero_pow hd0.ne', hx, norm_zero]⟩
    obtain ⟨c, hc⟩ := hdiv _ hx d hd0
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero, zero_pow hd0.ne', eq_comm, norm_eq_zero] at hc
      exact hx hc
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    set Q := P.comp (X + C x) with hQ
    have hQmon : Q.Monic := hmon.comp_X_add_C x
    have hQdeg : Q.natDegree = d := by rw [hQ, natDegree_comp, natDegree_X_add_C, mul_one]
    have hQc : ∀ i, i < d → ‖Q.coeff i‖ ≤ ‖c‖ ^ (d - i) := by
      intro i hi
      have h := norm_coeff_comp_rpow_le hmon hirr x hi
      have hroot : ‖P.eval x‖ ^ (1 / d : ℝ) = ‖c‖ := by
        rw [← hc, one_div, Real.pow_rpow_inv_natCast (norm_nonneg _) hd0.ne']
      rw [hroot] at h
      have hdi : (d : ℝ) - i = ((d - i : ℕ) : ℝ) := by rw [Nat.cast_sub hi.le]
      rw [hdi, one_div] at h
      have hne : d - i ≠ 0 := by omega
      calc ‖Q.coeff i‖ = (‖Q.coeff i‖ ^ (((d - i : ℕ) : ℝ)⁻¹)) ^ (d - i) :=
            (Real.rpow_inv_natCast_pow (norm_nonneg _) hne).symm
        _ ≤ ‖c‖ ^ (d - i) := pow_le_pow_left₀ (by positivity) h _
    set R := Q.scaleRoots c⁻¹ with hR
    have hRmon : R.Monic := (monic_scaleRoots_iff _).2 hQmon
    have hRdeg : R.natDegree = d := by rw [hR, natDegree_scaleRoots, hQdeg]
    have hRc : ∀ i, ‖R.coeff i‖ ≤ 1 := by
      intro i
      rw [hR, coeff_scaleRoots, hQdeg, norm_mul, norm_pow, norm_inv]
      rcases lt_or_ge i d with hi | hi
      · rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hcpos _)]
        exact hQc i hi
      · rw [Nat.sub_eq_zero_of_le hi, pow_zero, mul_one]
        rcases hi.lt_or_eq with hi | hi
        · rw [coeff_eq_zero_of_natDegree_lt (hQdeg ▸ hi), norm_zero]; exact zero_le_one
        · rw [← hi, ← hQdeg, hQmon.coeff_natDegree, norm_one]
    obtain ⟨y, hy1, hy⟩ := happrox R hRmon (hRdeg ▸ hd0) hRc
    refine ⟨x + c * y, ?_, ?_⟩
    · have heval : R.eval y = c⁻¹ ^ d * P.eval (x + c * y) := by
        have := scaleRoots_eval_mul Q (c * y) c⁻¹
        rw [inv_mul_cancel_left₀ hc0, hQdeg] at this
        rw [← hR] at this
        rw [this, hQ, eval_comp, eval_add, eval_X, eval_C, add_comm]
      have hPx' : P.eval (x + c * y) = c ^ d * R.eval y := by
        rw [heval, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc0, one_pow, one_mul]
      rw [hPx', norm_mul, norm_pow, hc, mul_comm δ]
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    · rw [add_sub_cancel_left, norm_mul, ← hc]
      exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (norm_nonneg _) hy1) _
  choose f hf1 hf2 using step
  set s : ℕ → F := fun n => f^[n] 0 with hs
  have hsucc : ∀ n, s (n + 1) = f (s n) := fun n => Function.iterate_succ_apply' f n 0
  set M := ‖P.eval 0‖ with hM
  have hval : ∀ n, ‖P.eval (s n)‖ ≤ δ ^ n * M := by
    intro n
    induction n with
    | zero => simp [hs, hM]
    | succ n ih =>
      rw [hsucc, pow_succ, mul_comm (δ ^ n) δ, mul_assoc]
      exact (hf1 _).trans (mul_le_mul_of_nonneg_left ih hδ0)
  set r : ℝ := δ ^ (1 / d : ℝ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hδ0 _
  have hr1 : r < 1 := Real.rpow_lt_one hδ0 hδ1 (by positivity)
  have hdist : ∀ n, dist (s n) (s (n + 1)) ≤ M ^ (1 / d : ℝ) * r ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hsucc]
    have h1 : ‖f (s n) - s n‖ ^ d ≤ δ ^ n * M := (hf2 _).trans (hval n)
    have h2 : ‖f (s n) - s n‖ = (‖f (s n) - s n‖ ^ d) ^ (1 / d : ℝ) := by
      rw [one_div, Real.pow_rpow_inv_natCast (norm_nonneg _) hd0.ne']
    rw [h2]
    calc (‖f (s n) - s n‖ ^ d) ^ (1 / d : ℝ) ≤ (δ ^ n * M) ^ (1 / d : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = M ^ (1 / d : ℝ) * r ^ n := by
          rw [Real.mul_rpow (pow_nonneg hδ0 _) (norm_nonneg _), mul_comm ((δ ^ n) ^ (1 / d : ℝ))]
          congr 1
          rw [hr, ← Real.rpow_natCast δ n, ← Real.rpow_mul hδ0,
            ← Real.rpow_natCast (δ ^ (1 / d : ℝ)) n, ← Real.rpow_mul hδ0]
          congr 1
          ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r _ hr1 hdist)
  refine ⟨L, ?_⟩
  have hlim : Tendsto (fun n => P.eval (s n)) atTop (𝓝 (P.eval L)) :=
    (P.continuous.tendsto L).comp hL
  have hzero : Tendsto (fun n => P.eval (s n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hval ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const M
  exact tendsto_nhds_unique hlim hzero
end Approximation
section Tilt
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "♮" x:max => ((PreTilt.untilt x : normInteger K) : K)
theorem exists_tilt_norm_pow_eq [IsAlgClosed K] (z : K♭) (hz : z ≠ 0) (n : ℕ) (hn : 0 < n) :
    ∃ c : K♭, ‖c‖ ^ n = ‖z‖ := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (tiltSharp K p z) hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, tiltSharp_eq_zero_iff] at hw
    exact hz hw
  obtain ⟨c, hc⟩ := exists_tilt_norm_eq (p := p) hw0
  exact ⟨c, by rw [hc, ← norm_pow, hw, norm_tiltSharp]⟩
theorem exists_approx_root_tilt [IsAlgClosed K] (a : 𝒪♭) (hp : ‖(p : K)‖ ≤ ‖♮a‖) (ha1 : ‖♮a‖ < 1)
    (R : K♭[X]) (hmon : R.Monic) (hdeg : 0 < R.natDegree) (hR : ∀ i, ‖R.coeff i‖ ≤ 1) :
    ∃ y : K♭, ‖y‖ ≤ 1 ∧ ‖R.eval y‖ ≤ ‖a‖ := by
  have hinj : Function.Injective (algebraMap 𝒪♭ K♭) := IsFractionRing.injective 𝒪♭ K♭

  obtain ⟨R', hR'⟩ : R ∈ lifts (algebraMap 𝒪♭ K♭) :=
    (lifts_iff_coeff_lifts R).2 fun i => norm_le_one_iff_exists_algebraMap.1 (hR i)
  replace hR' : R'.map (algebraMap 𝒪♭ K♭) = R := hR'
  have hR'mon : R'.Monic := monic_of_injective hinj (hR' ▸ hmon)
  have hR'deg : R'.natDegree = R.natDegree := by rw [← hR', natDegree_map_eq_of_injective hinj]

  set ϖ : normInteger K := a.untilt with hϖ
  set φ := untiltModHom (p := p) ϖ hp with hφ
  have hnt : Nontrivial (normInteger K ⧸ Ideal.span {ϖ}) := by
    refine Ideal.Quotient.nontrivial_iff.2 fun htop => ?_
    have h1 : (1 : normInteger K) ∈ Ideal.span {ϖ} := htop ▸ Submodule.mem_top
    rw [mem_span_singleton_iff_norm_le] at h1
    simp only [OneMemClass.coe_one, norm_one] at h1
    exact absurd (h1.trans_lt ha1) (lt_irrefl _)
  set Qbar := R'.map φ with hQbar
  have hQbarmon : Qbar.Monic := hR'mon.map φ
  have hQbardeg : Qbar.natDegree = R.natDegree := by
    rw [hQbar, hR'mon.natDegree_map, hR'deg]
  obtain ⟨Q, hQmap, hQdeg, hQmon⟩ := lifts_and_natDegree_eq_and_monic
    (f := Ideal.Quotient.mk (Ideal.span {ϖ}))
    (map_surjective _ Ideal.Quotient.mk_surjective Qbar) hQbarmon

  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Q.map (normInteger K).subtype) (by
    rw [degree_eq_natDegree (hQmon.map _).ne_zero, natDegree_map_eq_of_injective
      Subtype.val_injective, hQdeg, hQbardeg]
    exact_mod_cast hdeg.ne')
  have hzint : IsIntegral (normInteger K) z := ⟨Q, hQmon, by
    rw [IsRoot.def, eval_map] at hz
    exact hz⟩
  have hzmem : z ∈ normInteger K := Valuation.Integers.mem_of_integral normInteger_integers hzint
  set z' : normInteger K := ⟨z, hzmem⟩
  have hQz : Q.eval z' = 0 := by
    apply Subtype.val_injective
    rw [IsRoot.def, eval_map] at hz
    have : (normInteger K).subtype (Q.eval z') = Q.eval₂ (normInteger K).subtype z := by
      rw [← eval₂_at_apply]; rfl
    rw [ZeroMemClass.coe_zero]
    exact this.trans hz

  obtain ⟨y, hy⟩ := untiltModHom_surjective (p := p) ϖ hp (Ideal.Quotient.mk _ z')
  have hker : R'.eval y ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, ← eval₂_at_apply, ← eval_map, ← hQbar, hφ, hy, ← hQmap, eval_map,
      eval₂_at_apply, hQz, map_zero]
  rw [ker_untiltModHom a ϖ rfl hp, Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le] at hker
  refine ⟨algebraMap 𝒪♭ K♭ y, ?_, ?_⟩
  · rw [norm_algebraMap_preTilt]
    exact preTilt_norm_le_one y
  · rw [← hR', eval_map, eval₂_at_apply, norm_algebraMap_preTilt]
    exact hker
instance isAlgClosed_tilt [IsAlgClosed K] : IsAlgClosed K♭ := by
  obtain ⟨ϖ, h1, h2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) ‖(p : K)‖
    IsPerfectoidField.norm_natCast_lt_one
  obtain ⟨a, ha⟩ := exists_norm_untilt_eq (p := p) ⟨ϖ, mem_normInteger.2 h2.le⟩ h1
  have hp : ‖(p : K)‖ ≤ ‖♮a‖ := by rw [ha]; exact h1.le
  have ha1 : ‖♮a‖ < 1 := by rw [ha]; exact h2
  exact isAlgClosed_of_exists_approx_root (exists_tilt_norm_pow_eq (K := K) (p := p))
    (norm_nonneg a) (by rw [preTilt_norm_def]; exact ha1) (exists_approx_root_tilt a hp ha1)
end Tilt
end GroundTheory.PAdicHodge
end


