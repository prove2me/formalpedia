-- Prove2me | Definitions.Def_RPLib_S3_EllW2ZD1
-- name    : RPLib_S3_EllW2ZD1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:32:11.720903+00:00
-- url     : https://prove2.me/theorems/9e762637-02c8-4a94-aa72-36d3f42c6812
-- title:
--   The Eichler-Selberg trace formula in weight two: the `R^(-s-1)` zero mode of one modulus `c`
-- statement:
--   The `R^(-s-1)` zero mode of one modulus `c`.
--
--   * `Wc_eq_WN`: `Wc = (WN : ℂ)`; `muc_eq_norm`: `μ_c = (‖μ_c‖ : ℂ)` (both weights are nonnegative reals).
--   * `continuous_VS_ut`, `continuous_VS_u`, `aesm_intVS`, `integrable_intVS` (`u ↦ ∫_t VS` is integrable).
--   * `summable_WN_VS`, `abs_tsum_WN_VS_sub_le`: for one `u`, AS Abel summation with the K4b discrepancy:
--     `|Σ'_t WN(c,t) VS(c,t,u) − ‖μ_c‖ ∫_t VS| ≤ (‖μ_c‖ + Bd)(1+s)/(|c|y) (c²y²)^(-s) 2πy/(|c|(u²+y²)) + Σ_{excF} ‖WcF‖ VS`.
--   * `HZD` (that majorant), `integrable_HZD`, `integral_HZD`; `summable_WN_IU`.
--   * **`abs_tsum_WN_IU_sub_le`**: for `c ≠ 0`, `0 < n`, `0 ≤ s`, `0 < y`,
--     `|Σ'_t WN(c,t) ∫_u VS − ‖μ_c‖ ∫_u ∫_t VS| ≤ (‖μ_c‖ + Bd)(1+s)/(|c|y) (c²y²)^(-s) 2π²/|c| + Σ_{excF} ‖WcF‖ ∫_u VS`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2ZT1

/-!
# S3-ES-Wt2 (O6, file ZD1): the `R^(-s-1)` zero mode of one modulus `c`

* `Wc_eq_WN`: `Wc = (WN : ℂ)`; `muc_eq_norm`: `μ_c = (‖μ_c‖ : ℂ)` (both weights are nonnegative reals).
* `continuous_VS_ut`, `continuous_VS_u`, `aesm_intVS`, `integrable_intVS` (`u ↦ ∫_t VS` is integrable).
* `summable_WN_VS`, `abs_tsum_WN_VS_sub_le`: for one `u`, AS Abel summation with the K4b discrepancy:
  `|Σ'_t WN(c,t) VS(c,t,u) − ‖μ_c‖ ∫_t VS| ≤ (‖μ_c‖ + Bd)(1+s)/(|c|y) (c²y²)^(-s) 2πy/(|c|(u²+y²)) + Σ_{excF} ‖WcF‖ VS`.
* `HZD` (that majorant), `integrable_HZD`, `integral_HZD`; `summable_WN_IU`.
* **`abs_tsum_WN_IU_sub_le`**: for `c ≠ 0`, `0 < n`, `0 ≤ s`, `0 < y`,
  `|Σ'_t WN(c,t) ∫_u VS − ‖μ_c‖ ∫_u ∫_t VS| ≤ (‖μ_c‖ + Bd)(1+s)/(|c|y) (c²y²)^(-s) 2π²/|c| + Σ_{excF} ‖WcF‖ ∫_u VS`.
-/

open MeasureTheory Set Filter
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma Wc_eq_WN (n : ℤ) (δ' : ZMod M) (c t : ℤ) : Wc M n δ' c t = ((WN M n δ' c t : ℝ) : ℂ) := by
  unfold Wc WN
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun a _ => wtN_eq_norm n δ' _

lemma muc_eq_norm (n : ℤ) (δ' : ZMod M) (c : ℤ) : muc M n δ' c = ((‖muc M n δ' c‖ : ℝ) : ℂ) := by
  have e1 : ∑ u ∈ Finset.range (c.natAbs * M), WcF M n δ' c u =
      ((∑ u ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c u‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun u _ => WcF_eq_norm n δ' c u
  have e2 : muc M n δ' c = (((∑ u ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c u‖) /
      ((c.natAbs * M : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold muc; rw [e1, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [e2, Complex.norm_real, Real.norm_of_nonneg
    (div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Nat.cast_nonneg _))]

lemma continuous_VS_ut (s : ℝ) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Continuous fun p : ℝ × ℝ => VS s c n p.1 y p.2 := by
  unfold VS
  refine Continuous.rpow_const ?_ fun p => Or.inl (Rp_pos hc hy.ne' hn p.2).ne'
  unfold Rp RcN; fun_prop

lemma continuous_VS_u (s : ℝ) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    Continuous fun u => VS s c n u y t := by
  have h1 := continuous_VS_ut s hc hy hn
  have h2 : Continuous fun u : ℝ => (u, t) := continuous_id.prodMk continuous_const
  have h3 := h1.comp h2
  exact h3

lemma aesm_intVS (s : ℝ) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    AEStronglyMeasurable (fun u : ℝ => ∫ t, VS s c n u y t) volume :=
  ((continuous_VS_ut s hc hy hn).stronglyMeasurable.integral_prod_right'
    (ν := volume)).aestronglyMeasurable

lemma integrable_intVS {s : ℝ} (hs : 0 ≤ s) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable fun u : ℝ => ∫ t, VS s c n u y t := by
  refine (integrable_ubnd (y := y) s c hy).mono' (aesm_intVS s hc hy hn)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun t => VS_nonneg s hc hy.ne' hn t)]
  exact integral_VS_le hs hc hy hn

lemma summable_WN_VS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {y : ℝ} (hy : 0 < y) (u : ℝ) :
    Summable fun t : ℤ => WN M n δ' c t * VS s c n u y t :=
  (tsum_WcF_VS_le hn δ' hc hs hy u).1.of_nonneg_of_le
    (fun t => mul_nonneg (WN_nonneg n δ' c t) (VS_nonneg' _ _ _ _ _ _))
    (fun t => mul_le_mul_of_nonneg_right (WN_le n δ' c t) (VS_nonneg' _ _ _ _ _ _))

/-- **One `u`.** Abel summation of the absolute weights against `VS`. -/
theorem abs_tsum_WN_VS_sub_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    |∑' t : ℤ, WN M n δ' c t * VS s c n u y t - ‖muc M n δ' c‖ * ∫ t, VS s c n u y t| ≤
      (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
        (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2))))) +
      ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * VS s c n u y t := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hq : 0 < c.natAbs * M := Nat.mul_pos (Int.natAbs_pos.2 hc) (NeZero.pos M)
  have hsF : Summable fun t : ℤ => WcF M n δ' c t * ΦS s c n u y t :=
    Summable.of_norm_bounded ((summable_ΦS (u := u) hs hc' hy hn').norm.mul_left
      (c.natAbs * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2)) (fun t => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (norm_WcF_le n δ' c t) (norm_nonneg _))
  have hmain := norm_tsum_periodic_sub_le (f := fun t : ℤ => WcF M n δ' c t) (μ := muc M n δ' c) hq
    (fun t => WcF_periodic n δ' c t) (sum_WcF_eq n δ' hc) (Bd_nonneg n c)
    (fun m _ => norm_sum_WcF_sub_le_fW hn δ' hc m) (norm_WcF_le n δ' c)
    (hasDerivAt_ΦS (u := u) s hc' hy.ne' hn') (integrable_ΦS' (u := u) hs hc' hy hn')
    (integrable_ΦS (u := u) hs hc' hy hn') (summable_ΦS (u := u) hs hc' hy hn')
  rw [integral_ΦS, integral_norm_ΦS'] at hmain
  have hW : ∑' t : ℤ, Wc M n δ' c t * ΦS s c n u y t =
      ∑' t : ℤ, WcF M n δ' c t * ΦS s c n u y t - ∑ t ∈ excF n, WcF M n δ' c t * ΦS s c n u y t :=
    tsum_Wc_mul hn δ' c (fun t : ℤ => ΦS s c n u y t) hsF
  have hT : ((∑' t : ℤ, WN M n δ' c t * VS s c n u y t : ℝ) : ℂ) =
      ∑' t : ℤ, Wc M n δ' c t * ΦS s c n u y t := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun t => by rw [Complex.ofReal_mul, Wc_eq_WN]; rfl
  have eL : ((∑' t : ℤ, WN M n δ' c t * VS s c n u y t - ‖muc M n δ' c‖ * ∫ t, VS s c n u y t : ℝ) : ℂ) =
      (∑' t : ℤ, WcF M n δ' c t * ΦS s c n u y t - muc M n δ' c * ((∫ t, VS s c n u y t : ℝ) : ℂ)) -
        ∑ t ∈ excF n, WcF M n δ' c t * ΦS s c n u y t := by
    rw [Complex.ofReal_sub, hT, hW, Complex.ofReal_mul, ← muc_eq_norm]; ring
  have hex : ‖∑ t ∈ excF n, WcF M n δ' c t * ΦS s c n u y t‖ ≤
      ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * VS s c n u y t := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul, ΦS, Complex.norm_real, Real.norm_of_nonneg (VS_nonneg' _ _ _ _ _ _)]
  have hd : ∫ t, |dVS s c n u y t| ≤ (1 + s) / (|(c : ℝ)| * y) *
      (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))) :=
    (integral_abs_dVS_le hs hc' hy hn').trans (mul_le_mul_of_nonneg_left (integral_VS_le hs hc' hy hn')
      (div_nonneg (by linarith) (by positivity)))
  have key : ‖((∑' t : ℤ, WN M n δ' c t * VS s c n u y t - ‖muc M n δ' c‖ * ∫ t, VS s c n u y t : ℝ) : ℂ)‖ ≤
      (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
        (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2))))) +
      ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * VS s c n u y t := by
    rw [eL]
    refine (norm_sub_le _ _).trans (add_le_add (hmain.trans ?_) hex)
    exact mul_le_mul_of_nonneg_left hd (add_nonneg (norm_nonneg _) (Bd_nonneg n c))
  rwa [Complex.norm_real, Real.norm_eq_abs] at key

/-- The `u`-majorant of `abs_tsum_WN_VS_sub_le`. -/
def HZD (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s y : ℝ) (c : ℤ) (u : ℝ) : ℝ :=
  (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
    (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2))))) +
  ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * VS s c n u y t

lemma integrable_HZD {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    Integrable fun u => HZD M n δ' s y c u := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  unfold HZD
  exact (((integrable_ubnd s (c : ℝ) hy).const_mul _).const_mul _).add
    (integrable_finsetSum _ fun t _ => (integrable_VS_u hs hc' hy hn' t).const_mul _)

lemma integral_HZD {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    ∫ u, HZD M n δ' s y c u =
      (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
        (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|))) +
      ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hA : Integrable fun u : ℝ => (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
      (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2))))) :=
    ((integrable_ubnd s (c : ℝ) hy).const_mul _).const_mul _
  have hCi : ∀ t ∈ excF n, Integrable fun u : ℝ => ‖WcF M n δ' c t‖ * VS s c n u y t :=
    fun t _ => (integrable_VS_u hs hc' hy hn' t).const_mul _
  unfold HZD
  rw [integral_add hA (integrable_finsetSum _ hCi), integral_const_mul, integral_const_mul,
    integral_ubnd s hc' hy, integral_finsetSum _ hCi]
  congr 1
  exact Finset.sum_congr rfl fun t _ => integral_const_mul _ _

lemma summable_WN_IU {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {y : ℝ} (hy : 0 < y) :
    Summable fun t : ℤ => WN M n δ' c t * ∫ u, VS s c n u y t :=
  (tsum_WcF_IU_le hn δ' hc hs hy).1.of_nonneg_of_le
    (fun t => mul_nonneg (WN_nonneg n δ' c t) (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _))
    (fun t => mul_le_mul_of_nonneg_right (WN_le n δ' c t)
      (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _))

/-- **ZD1.** The zero mode of one modulus `c ≠ 0`: main term `‖μ_c‖ ∫∫ VS` plus an explicit remainder. -/
theorem abs_tsum_WN_IU_sub_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    |∑' t : ℤ, WN M n δ' c t * (∫ u, VS s c n u y t) - ‖muc M n δ' c‖ * ∫ u, ∫ t, VS s c n u y t| ≤
      (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
        (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|))) +
      ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hI : ∀ t : ℤ, Integrable fun u => WN M n δ' c t * VS s c n u y t :=
    fun t => (integrable_VS_u hs hc' hy hn' t).const_mul _
  have hsumN : Summable fun t : ℤ => ∫ u, ‖WN M n δ' c t * VS s c n u y t‖ := by
    have e : ∀ t : ℤ, ∫ u, ‖WN M n δ' c t * VS s c n u y t‖ = WN M n δ' c t * ∫ u, VS s c n u y t := by
      intro t
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      exact Real.norm_of_nonneg (mul_nonneg (WN_nonneg n δ' c t) (VS_nonneg' _ _ _ _ _ _))
    simp_rw [e]
    exact summable_WN_IU hn δ' hc hs hy
  have hswap : ∑' t : ℤ, WN M n δ' c t * ∫ u, VS s c n u y t =
      ∫ u, ∑' t : ℤ, WN M n δ' c t * VS s c n u y t := by
    rw [← integral_tsum_of_summable_integral_norm hI hsumN]
    exact tsum_congr fun t => (integral_const_mul _ _).symm
  have hBi : Integrable fun u : ℝ => ‖muc M n δ' c‖ * ∫ t, VS s c n u y t :=
    (integrable_intVS hs hc' hy hn').const_mul _
  have hpt := fun u => abs_tsum_WN_VS_sub_le hn δ' hc hs hy u
  have hAm : Measurable fun u : ℝ => ∑' t : ℤ, WN M n δ' c t * VS s c n u y t := by
    have e : (fun u : ℝ => ∑' t : ℤ, WN M n δ' c t * VS s c n u y t) =
        fun u => (∑' t : ℤ, ENNReal.ofReal (WN M n δ' c t * VS s c n u y t)).toReal := by
      funext u
      rw [ENNReal.tsum_toReal_eq (fun t => ENNReal.ofReal_ne_top)]
      exact tsum_congr fun t =>
        (ENNReal.toReal_ofReal (mul_nonneg (WN_nonneg n δ' c t) (VS_nonneg' _ _ _ _ _ _))).symm
    rw [e]
    have h1 : ∀ t : ℤ, Measurable fun u : ℝ => ENNReal.ofReal (WN M n δ' c t * VS s c n u y t) :=
      fun t => ENNReal.measurable_ofReal.comp
        ((continuous_VS_u s hc' hy hn' t).measurable.const_mul _)
    have h2 := (Measurable.ennreal_tsum h1).ennreal_toReal
    exact h2
  have hAi : Integrable fun u : ℝ => ∑' t : ℤ, WN M n δ' c t * VS s c n u y t := by
    refine (hBi.add (integrable_HZD hn δ' hc hs hy)).mono' hAm.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    have h0 : 0 ≤ ∑' t : ℤ, WN M n δ' c t * VS s c n u y t :=
      tsum_nonneg fun t => mul_nonneg (WN_nonneg n δ' c t) (VS_nonneg' _ _ _ _ _ _)
    have h1 := (abs_le.1 (hpt u)).2
    have h2 : ‖∑' t : ℤ, WN M n δ' c t * VS s c n u y t‖ ≤
        ‖muc M n δ' c‖ * (∫ t, VS s c n u y t) + HZD M n δ' s y c u := by
      rw [Real.norm_of_nonneg h0]; unfold HZD; linarith
    exact h2
  have e2 : ‖muc M n δ' c‖ * ∫ u, ∫ t, VS s c n u y t =
      ∫ u, ‖muc M n δ' c‖ * ∫ t, VS s c n u y t := (integral_const_mul _ _).symm
  rw [hswap, e2, ← integral_sub hAi hBi, ← integral_HZD hn δ' hc hs hy]
  exact abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => abs_nonneg _) (integrable_HZD hn δ' hc hs hy)
    (Eventually.of_forall fun u => hpt u))

end RamanujanPetersson.EllW2


