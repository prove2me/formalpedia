-- Prove2me | Definitions.Def_RPLib_S3_KernelSDE2
-- name    : RPLib_S3_KernelSDE2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:41:03.621257+00:00
-- url     : https://prove2.me/theorems/bde12228-94d4-497a-96a5-54d7546ba3fa
-- title:
--   The Eichler-Selberg trace formula in weight two: the limit `s → 0+` of the MAIN sum
-- statement:
--   The limit `s → 0+` of the MAIN sum.
--
--   * `tendsto_WtR`, `tendsto_MFm`, `tendsto_Fm` (pointwise).
--   * `tendsto_tsum_Fm` (dominated convergence with the majorant `majS`).
--   * `tendsto_zero_part`: the `(0,0)` modes tend to `0` (squeeze with `T Bnd Bnd (8 s² + 4 s)`).
--   * `tendsto_tsum_MF`: `Summable (MF M 0 z w)` and `Σ_{c'} MF s → Σ_{c'} MF 0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDE

/-!
# S3-ES-Wt2, part KS_D (E2): the limit `s → 0+` of the MAIN sum

* `tendsto_WtR`, `tendsto_MFm`, `tendsto_Fm` (pointwise).
* `tendsto_tsum_Fm` (dominated convergence with the majorant `majS`).
* `tendsto_zero_part`: the `(0,0)` modes tend to `0` (squeeze with `T Bnd Bnd (8 s² + 4 s)`).
* `tendsto_tsum_MF`: `Summable (MF M 0 z w)` and `Σ_{c'} MF s → Σ_{c'} MF 0`.
-/

open Complex Filter Topology
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

lemma tendsto_WtR (M : ℕ) [NeZero M] {t : ℝ} (ht : 0 < t) (c' : ℕ) :
    Tendsto (fun s => ((WtR M s t c' : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((WtR M 0 t c' : ℝ) : ℂ)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hX : 0 < ((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4 := by positivity
  have hb : t / (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4) ≠ 0 := (div_pos ht hX).ne'
  have k1 := (((Real.continuousAt_const_rpow (b := 0) hb).tendsto).div_const
    (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4)).ofReal
  unfold WtR
  exact k1.mono_left nhdsWithin_le_nhds

lemma tendsto_MFm {M : ℕ} [NeZero M] {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) (c' : ℕ) (mr : ℤ × ℤ) :
    Tendsto (fun s => MFm M s z w c' mr) (𝓝[>] 0) (𝓝 (MFm M 0 z w c' mr)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have k1 := tendsto_WtR M (mul_pos hy hv) c'
  have k2 := tendsto_gS (div_pos hy hMr) (mr.1 : ℝ)
  have k3 := tendsto_gS (div_pos hv hMr) (mr.2 : ℝ)
  unfold MFm
  exact k1.mul (((k2.mul k3).mul_const _).mul_const _)

lemma tendsto_Fm {M : ℕ} [NeZero M] {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) (p : ℕ × (ℤ × ℤ)) :
    Tendsto (fun s => Fm M s z w p) (𝓝[>] 0) (𝓝 (Fm M 0 z w p)) := by
  unfold Fm
  split_ifs with h
  · exact tendsto_const_nhds
  · exact tendsto_MFm hy hv p.1 p.2

theorem tendsto_tsum_Fm {M : ℕ} [NeZero M] {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Tendsto (fun s => ∑' p, Fm M s z w p) (𝓝[>] 0) (𝓝 (∑' p, Fm M 0 z w p)) := by
  refine tendsto_tsum_of_dominated_convergence ((summable_majS M).mul_left
    (max 1 (z.im * w.im) * (Bnd (z.im / M) * Bnd (w.im / M)))) (fun p => tendsto_Fm hy hv p) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs p
  exact norm_Fm_le hs.1.le hs.2.le hy hv (KernelSD.rpow_le_max_one (mul_pos hy hv) hs.1.le hs.2.le) p

theorem tendsto_zero_part {M : ℕ} [NeZero M] {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Tendsto (fun s => ∑' c' : ℕ, MFm M s z w c' 0) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun s : ℝ =>
      max 1 (z.im * w.im) * (Bnd (z.im / M) * Bnd (w.im / M)) * (8 * s ^ 2 + 4 * s)) := by fun_prop
  have h := hc.tendsto 0
  have e : max 1 (z.im * w.im) * (Bnd (z.im / M) * Bnd (w.im / M)) * (8 * (0 : ℝ) ^ 2 + 4 * 0) = 0 := by
    ring
  rw [e] at h
  refine squeeze_zero_norm' ?_ (h.mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
  obtain ⟨hz, hzb⟩ := zero_part_le (M := M) hs.1.le hs.2.le hy hv
    (KernelSD.rpow_le_max_one (mul_pos hy hv) hs.1.le hs.2.le)
  exact (norm_tsum_le_tsum_norm hz).trans hzb

/-- **MAIN limit** `s → 0+`. -/
theorem tendsto_tsum_MF {M : ℕ} [NeZero M] {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Summable (MF M 0 z w) ∧
      Tendsto (fun s => ∑' c' : ℕ, MF M s z w c') (𝓝[>] 0) (𝓝 (∑' c' : ℕ, MF M 0 z w c')) := by
  have h0 := hasSum_MF_split (M := M) le_rfl zero_le_one hy hv
  have hz0 : ∑' c' : ℕ, MFm M 0 z w c' 0 = 0 := by simp [MFm_zero_s_zero hy]
  rw [hz0, zero_add] at h0
  refine ⟨h0.summable, ?_⟩
  rw [h0.tsum_eq]
  have hlim := (tendsto_zero_part (M := M) hy hv).add (tendsto_tsum_Fm (M := M) hy hv)
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
  exact ((hasSum_MF_split (M := M) hs.1.le hs.2.le hy hv).tsum_eq).symm

end RamanujanPetersson.KernelSD


