-- Prove2me | Definitions.Def_RPLib_S3_EllW2AB1
-- name    : RPLib_S3_EllW2AB1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:51:40.384902+00:00
-- url     : https://prove2.me/theorems/0d49b9a6-92c0-4fcd-b7d0-fd8afa7b6691
-- title:
--   The Eichler-Selberg trace formula in weight two: the Abelian step with a kernel
-- statement:
--   The Abelian step with a kernel.
--
--   * `Fab f s n = f n · n^(-(1+2s))`; `term_ofReal`, `LSeries_ofReal`, `summable_Fab`.
--   * `tendsto_abel`: Cesàro mean `l` of `f ≥ 0` gives `s · Σ' Fab f s n → l/2` as `s → 0+`
--     (Mathlib `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg` at `σ = 1 + 2s`).
--   * `tendsto_abel_kernel`: a bounded kernel `κ s n → K0` (along `𝓝[>] 0 ×ˢ atTop`) gives
--     `s · Σ' Fab f s n · κ s n → K0 · l/2`.
--   * `kerY nr y s m = 2 (y²)^(-s) KS(s, nr/(m y)²)`: `abs_kerY_le`, `tendsto_kerY` (limit `π²`),
--     **`tendsto_abel_kerY`**.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2KS3

/-!
# S3-ES-Wt2 (O6, file AB1): the Abelian step with a kernel

* `Fab f s n = f n · n^(-(1+2s))`; `term_ofReal`, `LSeries_ofReal`, `summable_Fab`.
* `tendsto_abel`: Cesàro mean `l` of `f ≥ 0` gives `s · Σ' Fab f s n → l/2` as `s → 0+`
  (Mathlib `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg` at `σ = 1 + 2s`).
* `tendsto_abel_kernel`: a bounded kernel `κ s n → K0` (along `𝓝[>] 0 ×ˢ atTop`) gives
  `s · Σ' Fab f s n · κ s n → K0 · l/2`.
* `kerY nr y s m = 2 (y²)^(-s) KS(s, nr/(m y)²)`: `abs_kerY_le`, `tendsto_kerY` (limit `π²`),
  **`tendsto_abel_kerY`**.
-/

open Filter Topology Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- The Dirichlet-series term at `σ = 1 + 2s`. -/
def Fab (f : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ := f n * (n : ℝ) ^ (-(1 + 2 * s))

lemma natCast_rpow_neg_le_one (n : ℕ) {σ : ℝ} (hσ : 0 < σ) : (n : ℝ) ^ (-σ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h; rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ < 0).ne]; exact zero_le_one
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

lemma term_ofReal (f : ℕ → ℝ) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    LSeries.term (fun k => (f k : ℂ)) (σ : ℂ) n = ((f n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    rw [LSeries.term_zero, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.2 hσ), mul_zero,
      Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
      div_eq_mul_inv]

lemma LSeries_ofReal (f : ℕ → ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    LSeries (fun k => (f k : ℂ)) (σ : ℂ) = ((∑' n : ℕ, f n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  exact tsum_congr fun n => term_ofReal f hσ n

lemma Fab_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (s : ℝ) (n : ℕ) : 0 ≤ Fab f s n :=
  mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma summable_Fab {f : ℕ → ℝ} {l : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hlim : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, f k) / (N : ℝ)) atTop (𝓝 l))
    {s : ℝ} (hs : 0 < s) : Summable (Fab f s) := by
  have hσ : (1 : ℝ) < 1 + 2 * s := by linarith
  have hS : LSeriesSummable (fun k => (f k : ℂ)) ((1 + 2 * s : ℝ) : ℂ) := by
    refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ hf zero_le_one (by simpa using hσ)
    exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim)
  have h2 : Summable fun n => ((f n * (n : ℝ) ^ (-(1 + 2 * s)) : ℝ) : ℂ) :=
    (show Summable _ from hS).congr fun n => term_ofReal f (show (0 : ℝ) < 1 + 2 * s by linarith).ne' n
  exact Complex.summable_ofReal.1 h2

theorem tendsto_abel {f : ℕ → ℝ} {l : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hlim : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, f k) / (N : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun s : ℝ => s * ∑' n : ℕ, Fab f s n) (𝓝[>] 0) (𝓝 (l / 2)) := by
  have h := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg f hlim hf
  have hmap : Tendsto (fun s : ℝ => 1 + 2 * s) (𝓝[>] 0) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun s : ℝ => 1 + 2 * s) (𝓝 0) (𝓝 (1 + 2 * 0)) :=
        (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
      rw [mul_zero, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith
  have h2 := (Complex.continuous_re.tendsto _).comp (h.comp hmap)
  rw [Complex.ofReal_re] at h2
  have h3 : Tendsto (fun s : ℝ => 2 * (s * ∑' n : ℕ, Fab f s n)) (𝓝[>] 0) (𝓝 l) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    have hσ : (1 + 2 * s : ℝ) ≠ 0 := (show (0 : ℝ) < 1 + 2 * s by linarith).ne'
    simp only [Function.comp_apply]
    rw [LSeries_ofReal f hσ, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    unfold Fab
    ring
  exact (h3.div_const 2).congr fun s => by ring

theorem tendsto_abel_kernel {f : ℕ → ℝ} {l : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hlim : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, f k) / (N : ℝ)) atTop (𝓝 l))
    {κ : ℝ → ℕ → ℝ} {K0 B : ℝ} (hB : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ n, |κ s n| ≤ B)
    (hκ : Tendsto (fun p : ℝ × ℕ => κ p.1 p.2) (𝓝[>] 0 ×ˢ atTop) (𝓝 K0)) :
    Tendsto (fun s : ℝ => s * ∑' n : ℕ, Fab f s n * κ s n) (𝓝[>] 0) (𝓝 (K0 * (l / 2))) := by
  have hA := tendsto_abel hf hlim
  have hl : 0 ≤ l := ge_of_tendsto' hlim fun N =>
    div_nonneg (Finset.sum_nonneg fun k _ => hf k) (Nat.cast_nonneg N)
  have hK : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ n, |κ s n - K0| ≤ B + |K0| := fun s hs hs1 n => by
    have h1 := abs_le.1 (hB s hs hs1 n)
    exact abs_le.2 ⟨by linarith [le_abs_self K0], by linarith [neg_abs_le K0]⟩
  have hG : ∀ s : ℝ, 0 < s → s ≤ 1 → Summable fun n => |Fab f s n * (κ s n - K0)| :=
    fun s hs hs1 => Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => by
        rw [abs_mul, abs_of_nonneg (Fab_nonneg hf s n), mul_comm (B + |K0|)]
        exact mul_le_mul_of_nonneg_left (hK s hs hs1 n) (Fab_nonneg hf s n))
      ((summable_Fab hf hlim hs).mul_left (B + |K0|))
  have hD : Tendsto (fun s : ℝ => s * ∑' n : ℕ, Fab f s n * (κ s n - K0)) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hL1p : 0 < l / 2 + 1 := by linarith
    set ε1 := ε / (2 * (l / 2 + 1)) with hε1
    have hε1p : 0 < ε1 := by positivity
    obtain ⟨pa, hpa, pb, hpb, hP⟩ := Filter.eventually_prod_iff.1 (Metric.tendsto_nhds.1 hκ ε1 hε1p)
    obtain ⟨C, hC⟩ := Filter.eventually_atTop.1 hpb
    set SC := ∑ i ∈ Finset.range C, f i with hSC
    have h1 : Tendsto (fun s : ℝ => s * ((B + |K0|) * SC)) (𝓝[>] 0) (𝓝 (0 * ((B + |K0|) * SC))) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
    rw [zero_mul] at h1
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hpa, hA.eventually (gt_mem_nhds (show l / 2 < l / 2 + 1 by linarith)),
      h1.eventually (gt_mem_nhds (half_pos hε))] with s hs hs1 hpas hAs h1s
    have hs0 : 0 < s := hs
    have hs1' : s ≤ 1 := (Set.mem_Iio.1 hs1).le
    have hFs := summable_Fab hf hlim hs0
    have hGs := hG s hs0 hs1'
    have hfin : ∑ i ∈ Finset.range C, |Fab f s i * (κ s i - K0)| ≤ (B + |K0|) * SC := by
      rw [hSC, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (Fab_nonneg hf s i), mul_comm (B + |K0|)]
      have hFi : Fab f s i ≤ f i :=
        mul_le_of_le_one_right (hf i) (natCast_rpow_neg_le_one i (by linarith))
      exact mul_le_mul hFi (hK s hs0 hs1' i) (abs_nonneg _) (hf i)
    have htail : ∑' i, |Fab f s (i + C) * (κ s (i + C) - K0)| ≤ ε1 * ∑' n, Fab f s n := by
      have hFt : Summable fun i => Fab f s (i + C) := hFs.comp_injective (add_left_injective C)
      have hle : ∑' i, Fab f s (i + C) ≤ ∑' n, Fab f s n := by
        rw [← hFs.sum_add_tsum_nat_add C]
        linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range C) => Fab_nonneg hf s i]
      calc ∑' i, |Fab f s (i + C) * (κ s (i + C) - K0)| ≤ ∑' i, ε1 * Fab f s (i + C) := by
            refine Summable.tsum_le_tsum (fun i => ?_) (hGs.comp_injective (add_left_injective C))
              (hFt.mul_left ε1)
            rw [abs_mul, abs_of_nonneg (Fab_nonneg hf s _), mul_comm ε1]
            have hd := hP hpas (hC (i + C) (Nat.le_add_left C i))
            rw [Real.dist_eq] at hd
            exact mul_le_mul_of_nonneg_left hd.le (Fab_nonneg hf s _)
        _ = ε1 * ∑' i, Fab f s (i + C) := tsum_mul_left
        _ ≤ ε1 * ∑' n, Fab f s n := mul_le_mul_of_nonneg_left hle hε1p.le
    have hsplit := hGs.sum_add_tsum_nat_add C
    have hnorm : |∑' n, Fab f s n * (κ s n - K0)| ≤ ∑' n, |Fab f s n * (κ s n - K0)| := by
      have := norm_tsum_le_tsum_norm (f := fun n => Fab f s n * (κ s n - K0))
        (by simpa only [Real.norm_eq_abs] using hGs)
      simpa only [Real.norm_eq_abs] using this
    have hA0 : 0 ≤ s * ∑' n, Fab f s n := mul_nonneg hs0.le (tsum_nonneg (Fab_nonneg hf s))
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hs0]
    have hbound : ∑' n, |Fab f s n * (κ s n - K0)| ≤ (B + |K0|) * SC + ε1 * ∑' n, Fab f s n := by
      rw [← hsplit]
      exact add_le_add hfin htail
    have hmain : s * |∑' n, Fab f s n * (κ s n - K0)| ≤
        s * ((B + |K0|) * SC) + ε1 * (s * ∑' n, Fab f s n) :=
      calc s * |∑' n, Fab f s n * (κ s n - K0)|
          ≤ s * ((B + |K0|) * SC + ε1 * ∑' n, Fab f s n) :=
            mul_le_mul_of_nonneg_left (hnorm.trans hbound) hs0.le
        _ = s * ((B + |K0|) * SC) + ε1 * (s * ∑' n, Fab f s n) := by ring
    have hε1L : ε1 * (l / 2 + 1) = ε / 2 := by
      rw [hε1, div_mul_eq_mul_div, mul_div_mul_right ε 2 hL1p.ne']
    have h3 : ε1 * (s * ∑' n, Fab f s n) ≤ ε1 * (l / 2 + 1) :=
      mul_le_mul_of_nonneg_left hAs.le hε1p.le
    linarith
  have hsum := (hA.const_mul K0).add hD
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with s hs hs1
  have hs0 : 0 < s := hs
  have hFs := summable_Fab hf hlim hs0
  have hGs : Summable fun n => Fab f s n * (κ s n - K0) :=
    Summable.of_abs (hG s hs0 (Set.mem_Iio.1 hs1).le)
  have e : ∑' n, Fab f s n * κ s n = K0 * ∑' n, Fab f s n + ∑' n, Fab f s n * (κ s n - K0) := by
    rw [← tsum_mul_left, ← (hFs.mul_left K0).tsum_add hGs]
    exact tsum_congr fun n => by ring
  rw [e]
  ring

/-! ## The kernel of the main term -/

lemma rpow_neg_le_max1 {x s : ℝ} (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : x ^ (-s) ≤ max 1 x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)

/-- `2 (y²)^(-s) KS(s, nr/(m y)²)`. -/
def kerY (nr y s : ℝ) (m : ℕ) : ℝ := 2 * (y ^ 2) ^ (-s) * KS s (nr / ((m : ℝ) * y) ^ 2)

lemma abs_kerY_le {nr y : ℝ} (hn : 0 ≤ nr) (hy : 0 < y) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (m : ℕ) :
    |kerY nr y s m| ≤ 2 * max 1 (y ^ 2)⁻¹ * (2 * π ^ 2) := by
  have hε : 0 ≤ nr / ((m : ℝ) * y) ^ 2 := div_nonneg hn (sq_nonneg _)
  have h0 := KS_nonneg s hε
  have h1 := KS_le hs.le hε
  have h2 := rpow_neg_le_max1 (pow_pos hy 2) hs.le hs1
  have h3 : 0 ≤ (y ^ 2) ^ (-s) := Real.rpow_nonneg (sq_nonneg y) _
  have h4 : (y ^ 2) ^ (-s) * KS s (nr / ((m : ℝ) * y) ^ 2) ≤ max 1 (y ^ 2)⁻¹ * (2 * π ^ 2) :=
    mul_le_mul h2 h1 h0 ((zero_le_one).trans (le_max_left _ _))
  unfold kerY
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg zero_le_two h3) h0)]
  calc 2 * (y ^ 2) ^ (-s) * KS s (nr / ((m : ℝ) * y) ^ 2)
      = 2 * ((y ^ 2) ^ (-s) * KS s (nr / ((m : ℝ) * y) ^ 2)) := by ring
    _ ≤ 2 * (max 1 (y ^ 2)⁻¹ * (2 * π ^ 2)) := by linarith
    _ = 2 * max 1 (y ^ 2)⁻¹ * (2 * π ^ 2) := by ring

theorem tendsto_kerY {nr y : ℝ} (hn : 0 ≤ nr) (hy : 0 < y) :
    Tendsto (fun p : ℝ × ℕ => kerY nr y p.1 p.2) (𝓝[>] 0 ×ˢ atTop) (𝓝 (π ^ 2)) := by
  have hfst : Tendsto (fun p : ℝ × ℕ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have hg : Tendsto (fun m : ℕ => ((m : ℝ) * y) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_natCast_atTop_atTop.atTop_mul_const hy)
  have hε : Tendsto (fun m : ℕ => nr / ((m : ℝ) * y) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hg
  have hsnd : Tendsto (fun p : ℝ × ℕ => nr / ((p.2 : ℝ) * y) ^ 2) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) :=
    hε.comp tendsto_snd
  have hmap : Tendsto (fun p : ℝ × ℕ => (p.1, nr / ((p.2 : ℝ) * y) ^ 2)) (𝓝[>] 0 ×ˢ atTop) lKS := by
    refine tendsto_nhdsWithin_iff.2 ⟨hfst.prodMk_nhds hsnd, ?_⟩
    have h1 : ∀ᶠ p : ℝ × ℕ in 𝓝[>] 0 ×ˢ atTop, p.1 ∈ Set.Ioi (0 : ℝ) :=
      tendsto_fst.eventually eventually_mem_nhdsWithin
    have h2 : ∀ᶠ p : ℝ × ℕ in 𝓝[>] 0 ×ˢ atTop, nr / ((p.2 : ℝ) * y) ^ 2 < 1 :=
      hsnd.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨Set.mem_Ici.2 (Set.mem_Ioi.1 hp1).le, Set.mem_Icc.2 ⟨div_nonneg hn (sq_nonneg _), hp2.le⟩⟩
  have hK := tendsto_KS.comp hmap
  have hcont : Continuous fun s : ℝ => (y ^ 2) ^ (-s) :=
    continuous_const.rpow continuous_neg fun _ => Or.inl (pow_pos hy 2).ne'
  have hA : Tendsto (fun p : ℝ × ℕ => (y ^ 2) ^ (-p.1)) (𝓝[>] 0 ×ˢ atTop) (𝓝 1) := by
    have h0 := (hcont.tendsto 0).comp hfst
    rw [neg_zero, Real.rpow_zero] at h0
    exact h0
  have h5 := (hA.const_mul 2).mul hK
  rw [show (2 : ℝ) * 1 * (π ^ 2 / 2) = π ^ 2 by ring] at h5
  exact h5.congr fun p => rfl

/-- **AB1.** The main term of one sign: `s · Σ' f(m) m^(-1-2s) kerY → π² l / 2`. -/
theorem tendsto_abel_kerY {f : ℕ → ℝ} {l : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hlim : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, f k) / (N : ℝ)) atTop (𝓝 l))
    {nr y : ℝ} (hn : 0 ≤ nr) (hy : 0 < y) :
    Tendsto (fun s : ℝ => s * ∑' m : ℕ, Fab f s m * kerY nr y s m) (𝓝[>] 0)
      (𝓝 (π ^ 2 * (l / 2))) :=
  tendsto_abel_kernel hf hlim (fun s hs hs1 m => abs_kerY_le hn hy hs hs1 m) (tendsto_kerY hn hy)

end RamanujanPetersson.EllW2


