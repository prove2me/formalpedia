-- Prove2me | Definitions.Def_RPLib_S3_EllW2K
-- name    : RPLib_S3_EllW2K
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:25:06.557005+00:00
-- url     : https://prove2.me/theorems/c02bdc6c-af5b-466c-8301-c640cb6f58c4
-- title:
--   The Eichler-Selberg trace formula in weight two: the split/parabolic part at `s = 0` gives `hypG1 M 2 n δ`
-- statement:
--   The split/parabolic part at `s = 0` gives `hypG1 M 2 n δ`.
--
--   * `isSP_ut`, `wtS_ut`: upper-triangular matrices are split/parabolic, so `wtS = wt` there.
--   * `tendsto_cpartS`: the `c ≠ 0` top edges tend to `0` (bound `32 / (Y (c² + e²))`, `summable_SPc_E`).
--   * `tendsto_SP_lim`: `∫_{𝒟_Y} SPS_0 → -Σ_{e ∣ n} Σ_{σ = ±1} pairL 1 (σe) (σ n/e)`.
--   * `pair_conv1`, **`tendsto_SP_hyp`**: `n C_2⁻¹ ∫_{𝒟_Y} SPS_0 → hypG1 M 2 n δ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2I
import Definitions.Def_RPLib_S3_EllW2J
import Definitions.Def_RPLib_S3_HypPar

/-!
# S3-ES-Wt2 (O6, part K): the split/parabolic part at `s = 0` gives `hypG1 M 2 n δ`

* `isSP_ut`, `wtS_ut`: upper-triangular matrices are split/parabolic, so `wtS = wt` there.
* `tendsto_cpartS`: the `c ≠ 0` top edges tend to `0` (bound `32 / (Y (c² + e²))`, `summable_SPc_E`).
* `tendsto_SP_lim`: `∫_{𝒟_Y} SPS_0 → -Σ_{e ∣ n} Σ_{σ = ±1} pairL 1 (σe) (σ n/e)`.
* `pair_conv1`, **`tendsto_SP_hyp`**: `n C_2⁻¹ ∫_{𝒟_Y} SPS_0 → hypG1 M 2 n δ`.
-/

open MeasureTheory Set Filter Complex
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma isSP_ut (a b d : ℤ) : IsSP (HypPar.ut a b d) :=
  ⟨a - d, by simp [HypPar.ut, Matrix.det_fin_two_of]; ring⟩

lemma wtS_ut (n : ℤ) (δ' : ZMod M) (a b d : ℤ) :
    wtS M n δ' (HypPar.ut a b d) = HypPar.wt M n δ' (HypPar.ut a b d) := by
  unfold wtS; rw [if_pos (isSP_ut a b d)]

/-- The `c ≠ 0` part of the top edge at `m = 1` tends to `0`. -/
theorem tendsto_cpartS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) :
    Tendsto (fun Y : ℝ => ∑' g : S3.Conj.Mat,
      Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} (fun g => wtS M n δ' g * HypPar.topI g 1 Y) g)
      atTop (𝓝 0) := by
  set W0 : ℝ := (Fintype.card (Fin 2 → ZMod M) : ℝ) with hW0
  have hW0nn : 0 ≤ W0 := Nat.cast_nonneg _
  set F : S3.Conj.Mat → ℝ := {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0}.indicator
      (fun g => ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)⁻¹) with hF
  have hS : HasSum F (∑' g, F g) := (summable_SPc_E hn).hasSum
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine squeeze_zero_norm' (a := fun Y : ℝ => W0 * (32 / Y) * ∑' g, F g) ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 * (n : ℝ))] with Y hY
    have hY1 : 1 ≤ Y := by linarith
    have hY0 : 0 < Y := by linarith
    have hYn : 8 * (n : ℝ) ^ 2 ≤ Y ^ 2 := by nlinarith
    refine tsum_of_norm_bounded (hS.mul_left (W0 * (32 / Y))) fun g => ?_
    have hCnn : 0 ≤ W0 * (32 / Y) := mul_nonneg hW0nn (div_nonneg (by norm_num) hY0.le)
    have hind : 0 ≤ F g := Set.indicator_nonneg (fun g _ => by positivity) g
    by_cases hc : g 1 0 = 0
    · rw [Set.indicator_of_notMem (show g ∉ {g : S3.Conj.Mat | g 1 0 ≠ 0} by simpa using hc), norm_zero]
      exact mul_nonneg hCnn hind
    · rw [Set.indicator_of_mem (show g ∈ {g : S3.Conj.Mat | g 1 0 ≠ 0} from hc)]
      by_cases hd : g.det = n ∧ IsSP g
      · have hFg : F g = ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)⁻¹ :=
          Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0}
            from ⟨hd.1, hd.2, hc⟩) _
        rw [hFg, norm_mul]
        have h1 := norm_wtS_le n δ' g
        have h2 := norm_topI_one_le hn hd.1 hd.2 hc hY1 hYn
        calc ‖wtS M n δ' g‖ * ‖HypPar.topI g 1 Y‖
            ≤ W0 * (32 / (Y * ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2))) :=
              mul_le_mul h1 h2 (norm_nonneg _) hW0nn
          _ = W0 * (32 / Y) * ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)⁻¹ := by
              rw [mul_assoc, ← div_eq_mul_inv, div_div]
      · rw [wtS_of_not (fun h => hd ⟨h.1, h.2.2⟩), zero_mul, norm_zero]
        exact mul_nonneg hCnn hind
  · have h := ((tendsto_const_nhds (x := (32 : ℝ))).div_atTop tendsto_id).const_mul W0
    simpa using h.mul_const (∑' g, F g)

/-- The truncated split/parabolic integral at `s = 0` converges to the sum of the pair limits. -/
theorem tendsto_SP_lim {n : ℕ} (hn : 0 < n) (δ' : ZMod M) :
    Tendsto (fun Y : ℝ => ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SPS M (n : ℤ) δ' 0 z) atTop
      (𝓝 (-(∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
        HypPar.pairL M n δ' 1 (σ * e) (σ * ((n / e : ℕ) : ℤ))))) := by
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hlim : Tendsto (fun Y : ℝ =>
      -(∑' g : S3.Conj.Mat,
          Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} (fun g => wtS M n δ' g * HypPar.topI g 1 Y) g +
        ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
          ∑' b : ℤ, HypPar.wt M n δ' (HypPar.ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) *
            HypPar.topI (HypPar.ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) 1 Y)) atTop
      (𝓝 (-(0 + ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
        HypPar.pairL M n δ' 1 (σ * e) (σ * ((n / e : ℕ) : ℤ))))) := by
    refine ((tendsto_cpartS hnz δ').add (tendsto_finsetSum _ fun e he =>
      tendsto_finsetSum _ fun σ hσ => ?_)).neg
    obtain ⟨hprod, -, -⟩ := HypPar.pair_facts he hσ
    exact HypPar.tendsto_pair n δ' (by rw [hprod]; exact hnz) le_rfl
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  rw [integral_truncS hnz δ' hY, HypPar.tsum_split hn (fun g => wtS M n δ' g * HypPar.topI g 1 Y)
    (summable_topS hnz δ' hY) (fun g hg => by rw [wtS_of_not (fun h => hg h.1), zero_mul])]
  simp only [wtS_ut]

/-- The pair value at weight `2` (`m = 1`). -/
theorem pair_conv1 (n : ℤ) (hn : 0 < n) (δ' : ZMod M) {a d : ℤ} (had : a * d = n) :
    (n : ℂ) * (Bergman.bergmanConst 2)⁻¹ * (-(HypPar.pairL M n δ' 1 a d)) =
      ((HypPar.pairQ M δ' 2 a d : ℚ) : ℂ) := by
  unfold HypPar.pairL
  split_ifs with h
  · subst h
    have := HypPar.pair_par (k := 2) le_rfl n δ' had hn
    simpa only [show (2 : ℕ) - 1 = 1 from rfl, pow_one] using this
  · have := HypPar.pair_hyp (k := 2) le_rfl n δ' had hn h
    simpa only [show (2 : ℕ) - 1 = 1 from rfl, pow_one] using this

/-- **The split/parabolic part at `s = 0`, weight `2`**: `n C_2⁻¹ ∫_{𝒟_Y} SPS_0 → hypG1 M 2 n δ`
(with `δ'' = unitOf M n * δ`, as in `EichlerSelberg.trace_heckeTn_diamond`). -/
theorem tendsto_SP_hyp {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    Tendsto (fun Y : ℝ => (n : ℂ) * (Bergman.bergmanConst 2)⁻¹ *
      ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SPS M (n : ℤ) ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) 0 z) atTop
      (𝓝 ((S3.hypG1 M 2 n (δ : ZMod M) : ℚ) : ℂ)) := by
  set δ'' : ZMod M := ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) with hδ''
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hDδ : (((δ''.val : ℕ) : ℤ) : ZMod M) = δ'' := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hU : (M : ℤ) ∣ (((δ : ZMod M)).val : ℤ) * ((((δ⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℕ) : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one, ZMod.natCast_zmod_val]
    rw [Units.mul_inv, sub_self]
  have hD : (M : ℤ) ∣ ((δ''.val : ℕ) : ℤ) - (n : ℤ) * (((δ : ZMod M)).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hδ'', Units.val_mul, coe_unitOf hnM, sub_self]
  have hP := HypPar.sum_pairQ_eq (M := M) (k := 2) (by norm_num) hn hnM (δ : ZMod M) _ hU _ hD
  rw [hDδ] at hP
  have hL := (tendsto_SP_lim hn δ'').const_mul ((n : ℂ) * (Bergman.bergmanConst 2)⁻¹)
  convert hL using 2
  rw [← hP, show ((n : ℕ) : ℂ) = (((n : ℕ) : ℤ) : ℂ) from (Int.cast_natCast n).symm,
    ← Finset.sum_neg_distrib, Finset.mul_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  exact (pair_conv1 n hnz δ'' (HypPar.pair_facts he hσ).1).symm

end RamanujanPetersson.EllW2


