-- Prove2me | Definitions.Def_RPLib_S3_EllW2Z
-- name    : RPLib_S3_EllW2Z
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:42:17.808524+00:00
-- url     : https://prove2.me/theorems/d60c5f57-35f1-4a64-98a1-717e5ce2a23e
-- title:
--   The Eichler-Selberg trace formula in weight two: the trivial zero-mode bound for one `c`
-- statement:
--   The trivial zero-mode bound for one `c`.
--
--   * `norm_WcF_eq`/`WcF_eq_norm`: `WcF` is a nonnegative real; `norm_muc_le`: `‖μ_c‖ ≤ n L / 2`.
--   * `tsum_WcF_VS_le`: for fixed `(c, u)`, Abel summation (file AS) with the trivial discrepancy gives
--     `Σ'_t ‖WcF c t‖ VS(c,t,u) ≤ KZ (c²y²)^(-s) 2πy/(|c|(u²+y²))`, `KZ = n L (1/2 + (1+s)(1/2+M)/y)`.
--   * `integrable_VS_u`; `tsum_WcF_IU_le`: `Σ'_t ‖WcF c t‖ ∫_u VS ≤ KZ (c²y²)^(-s) 2π²/|c|` (summable).
--   * `WN`: the absolute zero-mode weight `Σ_{a ∈ fib} ‖wtN (mkT n (c,t) a)‖ ≤ ‖WcF‖` (`WN_le`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2P

/-!
# S3-ES-Wt2 (O6, file Z): the trivial zero-mode bound for one `c`

* `norm_WcF_eq`/`WcF_eq_norm`: `WcF` is a nonnegative real; `norm_muc_le`: `‖μ_c‖ ≤ n L / 2`.
* `tsum_WcF_VS_le`: for fixed `(c, u)`, Abel summation (file AS) with the trivial discrepancy gives
  `Σ'_t ‖WcF c t‖ VS(c,t,u) ≤ KZ (c²y²)^(-s) 2πy/(|c|(u²+y²))`, `KZ = n L (1/2 + (1+s)(1/2+M)/y)`.
* `integrable_VS_u`; `tsum_WcF_IU_le`: `Σ'_t ‖WcF c t‖ ∫_u VS ≤ KZ (c²y²)^(-s) 2π²/|c|` (summable).
* `WN`: the absolute zero-mode weight `Σ_{a ∈ fib} ‖wtN (mkT n (c,t) a)‖ ≤ ‖WcF‖` (`WN_le`).
-/

open MeasureTheory Set Filter Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

variable {M : ℕ} [NeZero M]

lemma WcF_eq_ofReal (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    WcF M n δ' c t =
      ((∑ a ∈ fib n c t, (S3.levelCount M δ' (mkT n (c, t) a) : ℝ) / 2 : ℝ) : ℂ) := by
  unfold WcF; push_cast; rfl

lemma norm_WcF_eq (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    ‖WcF M n δ' c t‖ = ∑ a ∈ fib n c t, (S3.levelCount M δ' (mkT n (c, t) a) : ℝ) / 2 := by
  rw [WcF_eq_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => by positivity)]

lemma WcF_eq_norm (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    WcF M n δ' c t = ((‖WcF M n δ' c t‖ : ℝ) : ℂ) := by
  rw [norm_WcF_eq]; exact WcF_eq_ofReal n δ' c t

lemma norm_muc_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) :
    ‖muc M n δ' c‖ ≤ (n.toNat : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 := by
  have hq : 0 < c.natAbs * M := Nat.mul_pos (Int.natAbs_pos.2 hc) (NeZero.pos M)
  have hq' : (0 : ℝ) < ((c.natAbs * M : ℕ) : ℝ) := by exact_mod_cast hq
  unfold muc
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hq']
  refine (norm_sum_le _ _).trans ((sum_norm_WcF_le hn δ' hc).trans_eq ?_)
  push_cast; ring

/-- `KZ = n L (1/2 + (1+s)(1/2+M)/y)`, `L = #(Fin 2 → ZMod M)`. -/
def KZ (M : ℕ) [NeZero M] (n : ℤ) (s y : ℝ) : ℝ :=
  (n.toNat : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) * (1 / 2 + (1 + s) * (1 / 2 + M) / y)

lemma KZ_nonneg (n : ℤ) {s y : ℝ} (hs : 0 ≤ s) (hy : 0 < y) : 0 ≤ KZ M n s y := by
  unfold KZ; positivity

/-- **Trivial bound for one `(c, u)`** (Abel summation with the trivial discrepancy). -/
lemma tsum_WcF_VS_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {y : ℝ} (hy : 0 < y) (u : ℝ) :
    Summable (fun t : ℤ => ‖WcF M n δ' c t‖ * VS s c n u y t) ∧
      ∑' t : ℤ, ‖WcF M n δ' c t‖ * VS s c n u y t ≤
        KZ M n s y * ((c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hq : 0 < c.natAbs * M := Nat.mul_pos (Int.natAbs_pos.2 hc) (NeZero.pos M)
  have hL0 : (0 : ℝ) ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := by positivity
  have hAS := norm_tsum_periodic_sub_le (f := WcF M n δ' c) (μ := muc M n δ' c) hq
    (fun t => WcF_periodic n δ' c t) (sum_WcF_eq n δ' hc)
    (B := 2 * ∑ v ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c v‖) (by positivity)
    (fun m hm => trivial_disc (sum_WcF_eq n δ' hc) m hm) (fun t => norm_WcF_le n δ' c t)
    (hasDerivAt_ΦS (u := u) s hc' hy.ne' hn') (integrable_ΦS' (u := u) hs hc' hy hn')
    (integrable_ΦS (u := u) hs hc' hy hn') (summable_ΦS (u := u) hs hc' hy hn')
  have hsV : Summable fun t : ℤ => VS s c n u y t :=
    (Complex.summable_ofReal (f := fun t : ℤ => VS s c n u y t)).1 (summable_ΦS (u := u) hs hc' hy hn')
  have hF0 : ∀ t : ℤ, 0 ≤ ‖WcF M n δ' c t‖ * VS s c n u y t := fun t =>
    mul_nonneg (norm_nonneg _) (VS_nonneg s hc' hy.ne' hn' t)
  have hsum : Summable fun t : ℤ => ‖WcF M n δ' c t‖ * VS s c n u y t :=
    Summable.of_nonneg_of_le hF0 (fun t => mul_le_mul_of_nonneg_right (norm_WcF_le n δ' c t)
      (VS_nonneg s hc' hy.ne' hn' t)) (hsV.mul_left _)
  have hid : ∑' t : ℤ, WcF M n δ' c t * ΦS s c n u y t =
      ((∑' t : ℤ, ‖WcF M n δ' c t‖ * VS s c n u y t : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun t => ?_
    rw [Complex.ofReal_mul, ← WcF_eq_norm, ΦS]
  have hIV0 : 0 ≤ ∫ t, VS s c n u y t := integral_nonneg fun t => VS_nonneg s hc' hy.ne' hn' t
  have hI1 : ‖∫ x, ΦS s c n u y x‖ = ∫ t, VS s c n u y t := by
    rw [integral_ΦS, Complex.norm_real, Real.norm_of_nonneg hIV0]
  have hI2 : ∫ x, ‖ΦS' s c n u y x‖ ≤ (1 + s) / (|(c : ℝ)| * y) * ∫ t, VS s c n u y t := by
    rw [integral_norm_ΦS']; exact integral_abs_dVS_le hs hc' hy hn'
  rw [hid] at hAS
  have hX : ‖((∑' t : ℤ, ‖WcF M n δ' c t‖ * VS s c n u y t : ℝ) : ℂ)‖ =
      ∑' t : ℤ, ‖WcF M n δ' c t‖ * VS s c n u y t := by
    rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg hF0)]
  have hm : ‖muc M n δ' c * ∫ x, ΦS s c n u y x‖ = ‖muc M n δ' c‖ * ∫ t, VS s c n u y t := by
    rw [norm_mul, hI1]
  have h1 : ‖((∑' t : ℤ, ‖WcF M n δ' c t‖ * VS s c n u y t : ℝ) : ℂ)‖ ≤
      ‖muc M n δ' c * ∫ x, ΦS s c n u y x‖ + (‖muc M n δ' c‖ +
        2 * ∑ v ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c v‖) * ∫ x, ‖ΦS' s c n u y x‖ :=
    sub_le_iff_le_add'.1 ((norm_sub_norm_le _ _).trans hAS)
  rw [hX, hm] at h1
  have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
  have hcpos : (0 : ℝ) < |(c : ℝ)| := by linarith
  have hcabs : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hμle := norm_muc_le hn δ' hc
  have hBle : 2 * ∑ v ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c v‖ ≤
      |(c : ℝ)| * ((M : ℝ) * ((n.toNat : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ))) := by
    have h := sum_norm_WcF_le hn δ' hc
    have e : ((c.natAbs * (M * n.toNat) : ℕ) : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 =
        |(c : ℝ)| * ((M : ℝ) * ((n.toNat : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ))) / 2 := by
      simp only [Nat.cast_mul]; rw [hcabs]; ring
    linarith
  set B := 2 * ∑ v ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c v‖ with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set nL := (n.toNat : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) with hnL
  have hnL0 : 0 ≤ nL := by rw [hnL]; positivity
  have hab : (‖muc M n δ' c‖ + B) / |(c : ℝ)| ≤ nL * (1 / 2 + M) := by
    rw [div_le_iff₀ hcpos]
    have : nL / 2 ≤ |(c : ℝ)| * (nL / 2) := le_mul_of_one_le_left (by linarith) hc1
    linarith
  have hcoef : ‖muc M n δ' c‖ + (‖muc M n δ' c‖ + B) * ((1 + s) / (|(c : ℝ)| * y)) ≤ KZ M n s y := by
    have e : (‖muc M n δ' c‖ + B) * ((1 + s) / (|(c : ℝ)| * y)) =
        (‖muc M n δ' c‖ + B) / |(c : ℝ)| * ((1 + s) / y) := by
      rw [div_mul_div_comm, mul_div_assoc]
    have h2 : (‖muc M n δ' c‖ + B) / |(c : ℝ)| * ((1 + s) / y) ≤ nL * (1 / 2 + M) * ((1 + s) / y) :=
      mul_le_mul_of_nonneg_right hab (by positivity)
    have h3 : KZ M n s y = nL / 2 + nL * (1 / 2 + M) * ((1 + s) / y) := by
      unfold KZ; rw [← hnL]; ring
    rw [e, h3]; linarith
  have hIV := integral_VS_le (u := u) hs hc' hy hn'
  refine ⟨hsum, ?_⟩
  calc ∑' t : ℤ, ‖WcF M n δ' c t‖ * VS s c n u y t
      ≤ ‖muc M n δ' c‖ * (∫ t, VS s c n u y t) + (‖muc M n δ' c‖ + B) * ∫ x, ‖ΦS' s c n u y x‖ := by
        linarith
    _ ≤ ‖muc M n δ' c‖ * (∫ t, VS s c n u y t) +
          (‖muc M n δ' c‖ + B) * ((1 + s) / (|(c : ℝ)| * y) * ∫ t, VS s c n u y t) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hI2 (add_nonneg (norm_nonneg _) hB0))
    _ = (‖muc M n δ' c‖ + (‖muc M n δ' c‖ + B) * ((1 + s) / (|(c : ℝ)| * y))) *
          ∫ t, VS s c n u y t := by ring
    _ ≤ KZ M n s y * ∫ t, VS s c n u y t := mul_le_mul_of_nonneg_right hcoef hIV0
    _ ≤ _ := mul_le_mul_of_nonneg_left hIV (KZ_nonneg n hs hy)

/-- `u ↦ VS` is integrable. -/
lemma integrable_VS_u {s : ℝ} (hs : 0 ≤ s) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    Integrable fun u => VS s c n u y t := by
  have hcont : Continuous fun u => VS s c n u y t := by
    unfold VS
    refine Continuous.rpow_const ?_ fun u => Or.inl (Rp_pos hc hy.ne' hn t).ne'
    unfold Rp RcN; fun_prop
  have hb : Integrable fun u : ℝ => (c ^ 2) ^ (-s - 1) * (y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹ :=
    (integrable_inv_sq_add_sq hy).const_mul _
  refine hb.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (VS_nonneg s hc hy.ne' hn t)]
  have hu : 0 < u ^ 2 + y ^ 2 := by positivity
  calc VS s c n u y t ≤ (c ^ 2 * (u ^ 2 + y ^ 2)) ^ (-s - 1) := VS_le_pt hs hc hy.ne' hn t
    _ = (c ^ 2) ^ (-s - 1) * ((u ^ 2 + y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹) := by
        rw [Real.mul_rpow (by positivity) hu.le, Real.rpow_sub_one hu.ne', div_eq_mul_inv]
    _ ≤ (c ^ 2) ^ (-s - 1) * ((y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos (by positivity) (le_add_of_nonneg_left (sq_nonneg u))
            (by linarith)) (by positivity)) (by positivity)
    _ = _ := by ring

/-- **Trivial bound for one `c`**, integrated in `u`. -/
lemma tsum_WcF_IU_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun t : ℤ => ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t) ∧
      ∑' t : ℤ, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t ≤
        KZ M n s y * ((c ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hf0 : 0 ≤ fun t : ℤ => ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t := fun t =>
    mul_nonneg (norm_nonneg _) (integral_nonneg fun u => VS_nonneg s hc' hy.ne' hn' t)
  have hS : ∀ S : Finset ℤ, ∑ t ∈ S, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t ≤
      KZ M n s y * ((c ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)) := by
    intro S
    have hint : ∀ t ∈ S, Integrable fun u => ‖WcF M n δ' c t‖ * VS s c n u y t :=
      fun t _ => (integrable_VS_u hs hc' hy hn' t).const_mul _
    calc ∑ t ∈ S, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t
        = ∫ u, ∑ t ∈ S, ‖WcF M n δ' c t‖ * VS s c n u y t := by
          rw [integral_finsetSum S hint]
          exact Finset.sum_congr rfl fun t _ => (integral_const_mul _ _).symm
      _ ≤ ∫ u, KZ M n s y * ((c ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))) := by
          refine integral_mono (integrable_finsetSum S hint) ((integrable_ubnd s c hy).const_mul _)
            fun u => ?_
          obtain ⟨hsu, hle⟩ := tsum_WcF_VS_le hn δ' hc hs hy u
          exact (hsu.sum_le_tsum S fun t _ => mul_nonneg (norm_nonneg _)
            (VS_nonneg s hc' hy.ne' hn' t)).trans hle
      _ = KZ M n s y * ((c ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)) := by
          rw [integral_const_mul, integral_ubnd s hc' hy]
  exact ⟨summable_of_sum_le hf0 hS, Real.tsum_le_of_sum_le hf0 hS⟩

/-- The absolute zero-mode weight `Σ_{a ∈ fib} ‖wtN (mkT n (c,t) a)‖`. -/
def WN (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (c t : ℤ) : ℝ :=
  ∑ a ∈ fib n c t, ‖wtN M n δ' (mkT n (c, t) a)‖

lemma WN_nonneg (n : ℤ) (δ' : ZMod M) (c t : ℤ) : 0 ≤ WN M n δ' c t :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma WN_le (n : ℤ) (δ' : ZMod M) (c t : ℤ) : WN M n δ' c t ≤ ‖WcF M n δ' c t‖ := by
  by_cases hc : c = 0
  · subst hc; simp [WN, fib]
  rw [norm_WcF_eq]; unfold WN
  refine Finset.sum_le_sum fun a ha => ?_
  rw [wtN_mkT n δ' hc (Finset.mem_filter.1 ha).2]
  split_ifs
  · rw [norm_zero]; positivity
  · exact le_of_eq (by rw [norm_div, Complex.norm_natCast, Complex.norm_two])

end RamanujanPetersson.EllW2


