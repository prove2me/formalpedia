-- Prove2me | Definitions.Def_RPLib_S3_EllW2ZD2
-- name    : RPLib_S3_EllW2ZD2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:34:04.223629+00:00
-- url     : https://prove2.me/theorems/1868a934-5c54-47f6-825e-9e22b8e5eaaa
-- title:
--   The Eichler-Selberg trace formula in weight two: `ZS = Σ_c ‖μ_c‖ ∫∫ VS + O(KY y)`, uniformly in `0 < s ≤ 1`
-- statement:
--   `ZS = Σ_c ‖μ_c‖ ∫∫ VS + O(KY y)`, uniformly in `0 < s ≤ 1`.
--
--   * `WN_zero_left`, `muc_zero_left`; `Zc` (one modulus), `Jm` (its main term `‖μ_c‖ ∫_u ∫_t VS`).
--   * `summable_ZSct`, `ZS_eq_tsum_Zc` (`ZS = Σ'_c Zc`), `summable_Zc`.
--   * `rpow_neg_le_max`; `KY y = max 1 (y²)⁻¹ / y`; `BZD`, `abs_Zc_sub_Jm_le` (ZD1 made uniform), `hasSum_BZD`, `tsum_BZD_le`.
--   * **`abs_ZS_sub_le`**: for `0 < n`, `0 < s ≤ 1`, `0 < y`: `Jm` is summable and
--     `|ZS − Σ'_c Jm c| ≤ KY y · CZD M n`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2ZD1

/-!
# S3-ES-Wt2 (O6, file ZD2): `ZS = Σ_c ‖μ_c‖ ∫∫ VS + O(KY y)`, uniformly in `0 < s ≤ 1`

* `WN_zero_left`, `muc_zero_left`; `Zc` (one modulus), `Jm` (its main term `‖μ_c‖ ∫_u ∫_t VS`).
* `summable_ZSct`, `ZS_eq_tsum_Zc` (`ZS = Σ'_c Zc`), `summable_Zc`.
* `rpow_neg_le_max`; `KY y = max 1 (y²)⁻¹ / y`; `BZD`, `abs_Zc_sub_Jm_le` (ZD1 made uniform), `hasSum_BZD`, `tsum_BZD_le`.
* **`abs_ZS_sub_le`**: for `0 < n`, `0 < s ≤ 1`, `0 < y`: `Jm` is summable and
  `|ZS − Σ'_c Jm c| ≤ KY y · CZD M n`.
-/

open MeasureTheory Set Filter
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma WN_zero_left (n : ℤ) (δ' : ZMod M) (t : ℤ) : WN M n δ' 0 t = 0 := by simp [WN, fib]

lemma muc_zero_left (n : ℤ) (δ' : ZMod M) : muc M n δ' 0 = 0 := by simp [muc]

/-- The zero mode of one modulus `c`. -/
def Zc (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s y : ℝ) (c : ℤ) : ℝ :=
  ∑' t : ℤ, WN M n δ' c t * ∫ u, VS s c n u y t

/-- Its main term. -/
def Jm (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s y : ℝ) (c : ℤ) : ℝ :=
  ‖muc M n δ' c‖ * ∫ u, ∫ t, VS s c n u y t

lemma ZSct_nonneg (n : ℤ) (δ' : ZMod M) (s y : ℝ) :
    0 ≤ fun ct : ℤ × ℤ => WN M n δ' ct.1 ct.2 * ∫ u, VS s ct.1 n u y ct.2 := fun ct =>
  mul_nonneg (WN_nonneg _ _ _ _) (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _)

theorem summable_ZSct {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    Summable fun ct : ℤ × ℤ => WN M n δ' ct.1 ct.2 * ∫ u, VS s ct.1 n u y ct.2 := by
  have h0 := ZSct_nonneg (M := M) n δ' s y
  set K := KZ M n s y * (2 * π ^ 2 * (y ^ 2) ^ (-s)) with hK
  have hK0 : 0 ≤ K := mul_nonneg (KZ_nonneg n hs.le hy) (by positivity)
  have hfib : ∀ c : ℤ, Summable (fun t : ℤ => WN M n δ' c t * ∫ u, VS s c n u y t) ∧
      ∑' t : ℤ, WN M n δ' c t * ∫ u, VS s c n u y t ≤ K * |(c : ℝ)| ^ (-(1 + 2 * s)) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp only [WN_zero_left, zero_mul, tsum_zero]
      exact ⟨summable_zero, mul_nonneg hK0 (Real.rpow_nonneg (abs_nonneg _) _)⟩
    · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      obtain ⟨hsu, hle⟩ := tsum_WcF_IU_le hn δ' hc hs.le hy
      refine ⟨summable_WN_IU hn δ' hc hs.le hy, ?_⟩
      calc ∑' t : ℤ, WN M n δ' c t * ∫ u, VS s c n u y t
          ≤ ∑' t : ℤ, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t :=
            Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_right (WN_le n δ' c t)
              (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _)) (summable_WN_IU hn δ' hc hs.le hy) hsu
        _ ≤ _ := hle
        _ = K * |(c : ℝ)| ^ (-(1 + 2 * s)) := by rw [rpow_c_identity hc' s y, hK]; ring
  have hsZ := Real.summable_abs_int_rpow (show 1 < 1 + 2 * s by linarith)
  exact (summable_prod_of_nonneg h0).2 ⟨fun c => (hfib c).1,
    Summable.of_nonneg_of_le (fun c => tsum_nonneg fun t => h0 (c, t)) (fun c => (hfib c).2)
      (hsZ.mul_left K)⟩

lemma summable_Zc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    Summable (Zc M n δ' s y) :=
  ((summable_prod_of_nonneg (ZSct_nonneg (M := M) n δ' s y)).1 (summable_ZSct hn δ' hs hy)).2

theorem ZS_eq_tsum_Zc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    ZS M n δ' s y = ∑' c : ℤ, Zc M n δ' s y c := by
  have h := summable_ZSct (M := M) hn δ' hs hy
  have hf := ((summable_prod_of_nonneg (ZSct_nonneg (M := M) n δ' s y)).1 h).1
  unfold ZS Zc
  exact h.tsum_prod' hf

lemma rpow_neg_le_max {x s : ℝ} (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : x ^ (-s) ≤ max 1 x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)

/-- The `y`-factor of the uniform bound. -/
def KY (y : ℝ) : ℝ := max 1 (y ^ 2)⁻¹ / y

lemma KY_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ KY y :=
  div_nonneg ((zero_le_one).trans (le_max_left _ _)) hy.le

def CZ1 (M : ℕ) [NeZero M] (n : ℤ) : ℝ := 4 * π ^ 2 * mNA M n
def CZ2 (M : ℕ) [NeZero M] : ℝ :=
  4 * π ^ 2 * (33 * (Fintype.card (Fin 2 → ZMod M) : ℝ) * (M : ℝ) ^ ((33 : ℝ) / 32))
def CZ3 (M : ℕ) [NeZero M] (n : ℤ) : ℝ := ((excF n).card : ℝ) * ((Fintype.card (Fin 2 → ZMod M) : ℝ) * π)

/-- The uniform remainder bound of the modulus `c`. -/
def BZD (M : ℕ) [NeZero M] (n : ℤ) (y : ℝ) (c : ℤ) : ℝ :=
  KY y * (CZ1 M n * |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) + CZ2 M * KL.fp (fW (N0f M n)) c.natAbs +
    CZ3 M n * |(c : ℝ)| ^ (-(5 / 4 : ℝ)))

lemma BZD_nonneg (n : ℤ) {y : ℝ} (hy : 0 < y) (c : ℤ) : 0 ≤ BZD M n y c := by
  unfold BZD CZ1 CZ2 CZ3
  have := mNA_nonneg (M := M) n
  have := fp_fW_nonneg (N0f M n) c.natAbs
  have := KY_nonneg hy
  positivity

theorem abs_Zc_sub_Jm_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) :
    |Zc M n δ' s y c - Jm M n δ' s y c| ≤ BZD M n y c := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hca : 0 < |(c : ℝ)| := abs_pos.2 hc'
  have hc1 : 1 ≤ |(c : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
  have hy2 : 0 < y ^ 2 := by positivity
  set m := max 1 (y ^ 2)⁻¹ with hm
  have hm0 : 0 ≤ m := (zero_le_one).trans (le_max_left _ _)
  have hX : ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) ≤ m := by
    refine le_trans ?_ (rpow_neg_le_max hy2 hs.le hs1)
    refine Real.rpow_le_rpow_of_nonpos hy2 ?_ (by linarith)
    have : 1 ≤ (c : ℝ) ^ 2 := by rw [← sq_abs]; nlinarith
    nlinarith
  have hX0 : 0 ≤ ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) := Real.rpow_nonneg (by positivity) _
  have hmuc : ‖muc M n δ' c‖ ≤ mNA M n := norm_muc_le hn δ' hc
  have hP : 0 ≤ 2 * π ^ 2 / |(c : ℝ)| := by positivity
  have hq : (1 + s) / (|(c : ℝ)| * y) ≤ 2 / (|(c : ℝ)| * y) :=
    div_le_div_of_nonneg_right (by linarith) (mul_pos hca hy).le
  have h1 : (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
      (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|))) ≤
      KY y * (CZ1 M n * |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) + CZ2 M * KL.fp (fW (N0f M n)) c.natAbs) := by
    have hz : |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) = (|(c : ℝ)| ^ 2)⁻¹ := by
      rw [show (-(1 + 2 * (1 / 2 : ℝ))) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hca.le,
        Real.rpow_natCast]
    have hN : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    calc (‖muc M n δ' c‖ + Bd M n c) * ((1 + s) / (|(c : ℝ)| * y) *
          (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)))
        ≤ (mNA M n + Bd M n c) * (2 / (|(c : ℝ)| * y) * (m * (2 * π ^ 2 / |(c : ℝ)|))) :=
          mul_le_mul (add_le_add hmuc le_rfl) (mul_le_mul hq (mul_le_mul_of_nonneg_right hX hP)
            (mul_nonneg hX0 hP) (by positivity))
            (mul_nonneg (div_nonneg (by linarith) (mul_pos hca hy).le) (mul_nonneg hX0 hP))
            (add_nonneg (mNA_nonneg n) (Bd_nonneg n c))
      _ = KY y * (CZ1 M n * |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) +
            CZ2 M * KL.fp (fW (N0f M n)) c.natAbs) := by
          unfold KY CZ1 CZ2 Bd
          rw [hz, hN, ← hm]
          field_simp
          ring
  have h2 : ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t ≤
      KY y * (CZ3 M n * |(c : ℝ)| ^ (-(5 / 4 : ℝ))) := by
    have hL : (0 : ℝ) ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := by positivity
    have hy' : (y ^ 2) ^ (-s) ≤ m := rpow_neg_le_max hy2 hs.le hs1
    calc ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t
        ≤ (excF n).card * ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) * (y ^ 2) ^ (-s)) *
            |(c : ℝ)| ^ (-(5/4 : ℝ)) := exc_sum_le hn.le δ' hc hs.le hy
      _ ≤ (excF n).card * ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) * m) *
            |(c : ℝ)| ^ (-(5/4 : ℝ)) := by gcongr
      _ = KY y * (CZ3 M n * |(c : ℝ)| ^ (-(5 / 4 : ℝ))) := by unfold KY CZ3; rw [← hm]; ring
  calc |Zc M n δ' s y c - Jm M n δ' s y c| ≤ _ := abs_tsum_WN_IU_sub_le hn δ' hc hs.le hy
    _ ≤ KY y * (CZ1 M n * |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) + CZ2 M * KL.fp (fW (N0f M n)) c.natAbs) +
          KY y * (CZ3 M n * |(c : ℝ)| ^ (-(5 / 4 : ℝ))) := add_le_add h1 h2
    _ = BZD M n y c := by unfold BZD; ring

/-- The constant of the uniform bound. -/
def CZD (M : ℕ) [NeZero M] (n : ℤ) : ℝ := CZ1 M n * 4 + CZ2 M * (2 * CW (N0f M n)) + CZ3 M n * 10

lemma hasSum_BZD (n : ℤ) (y : ℝ) :
    HasSum (BZD M n y) (KY y * (CZ1 M n * (∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ)))) +
      CZ2 M * (∑' c : ℤ, KL.fp (fW (N0f M n)) c.natAbs) +
      CZ3 M n * (∑' c : ℤ, |(c : ℝ)| ^ (-(5 / 4 : ℝ))))) := by
  have h2 := ((Real.summable_abs_int_rpow (show (1 : ℝ) < 1 + 2 * (1 / 2) by norm_num)).hasSum).mul_left
    (CZ1 M n)
  have h3 := ((summable_fW_int (sixteen_le_N0f M n)).hasSum).mul_left (CZ2 M)
  have h4 := (summable_abs_int_rpow54.hasSum).mul_left (CZ3 M n)
  exact ((h2.add h3).add h4).mul_left (KY y)

lemma tsum_BZD_le {n : ℤ} (hn : 0 ≤ n) {y : ℝ} (hy : 0 < y) :
    ∑' c : ℤ, BZD M n y c ≤ KY y * CZD M n := by
  rw [(hasSum_BZD n y).tsum_eq]
  have hS2 : ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) ≤ 4 := by
    have h := tsum_abs_int_rpow_le (s := 1 / 2) (by norm_num)
    have e : (2 : ℝ) + 1 / (1 / 2) = 4 := by norm_num
    rw [e] at h
    exact h
  have hS3 := tsum_fW_int_le (sixteen_le_N0f M n)
  have hS4 := tsum_abs_int_rpow54_le
  have h1 : 0 ≤ CZ1 M n := by unfold CZ1; have := mNA_nonneg (M := M) n; positivity
  have h2 : 0 ≤ CZ2 M := by unfold CZ2; positivity
  have h3 : 0 ≤ CZ3 M n := by unfold CZ3; positivity
  unfold CZD
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hS2 h1) (mul_le_mul_of_nonneg_left hS3 h2))
    (mul_le_mul_of_nonneg_left hS4 h3)) (KY_nonneg hy)

/-- **ZD2.** `ZS(s, y) = Σ'_c ‖μ_c‖ ∫∫ VS + O(KY y)`, uniformly in `0 < s ≤ 1`. -/
theorem abs_ZS_sub_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {y : ℝ} (hy : 0 < y) :
    Summable (Jm M n δ' s y) ∧ |ZS M n δ' s y - ∑' c : ℤ, Jm M n δ' s y c| ≤ KY y * CZD M n := by
  have hZ := summable_Zc (M := M) hn δ' hs hy
  have hd : ∀ c : ℤ, |Zc M n δ' s y c - Jm M n δ' s y c| ≤ BZD M n y c := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have e1 : Zc M n δ' s y 0 = 0 := by simp only [Zc, WN_zero_left, zero_mul, tsum_zero]
      have e2 : Jm M n δ' s y 0 = 0 := by simp only [Jm, muc_zero_left, norm_zero, zero_mul]
      rw [e1, e2, sub_zero, abs_zero]
      exact BZD_nonneg n hy 0
    · exact abs_Zc_sub_Jm_le hn δ' hc hs hs1 hy
  have hB := (hasSum_BZD (M := M) n y).summable
  have hsd : Summable fun c : ℤ => Zc M n δ' s y c - Jm M n δ' s y c :=
    Summable.of_norm_bounded hB (fun c => by rw [Real.norm_eq_abs]; exact hd c)
  have hJ : Summable (Jm M n δ' s y) := by
    have h := hZ.sub hsd
    have e : (fun c : ℤ => Zc M n δ' s y c - (Zc M n δ' s y c - Jm M n δ' s y c)) = Jm M n δ' s y := by
      funext c; ring
    rw [e] at h
    exact h
  refine ⟨hJ, ?_⟩
  rw [ZS_eq_tsum_Zc hn δ' hs hy, ← hZ.tsum_sub hJ]
  have hup : ∑' c : ℤ, (Zc M n δ' s y c - Jm M n δ' s y c) ≤ ∑' c : ℤ, BZD M n y c :=
    Summable.tsum_le_tsum (fun c => (abs_le.1 (hd c)).2) hsd hB
  have hlo : ∑' c : ℤ, -BZD M n y c ≤ ∑' c : ℤ, (Zc M n δ' s y c - Jm M n δ' s y c) :=
    Summable.tsum_le_tsum (fun c => (abs_le.1 (hd c)).1) hB.neg hsd
  rw [tsum_neg] at hlo
  have hT := tsum_BZD_le (M := M) hn.le hy
  exact abs_le.2 ⟨by linarith, by linarith⟩

end RamanujanPetersson.EllW2


