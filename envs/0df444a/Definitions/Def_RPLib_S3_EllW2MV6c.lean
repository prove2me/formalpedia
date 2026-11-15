-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV6c
-- name    : RPLib_S3_EllW2MV6c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:24:00.080417+00:00
-- url     : https://prove2.me/theorems/852b85d9-321c-46be-8e00-23cebccd6da0
-- title:
--   The Eichler-Selberg trace formula in weight two: the residue densities sum to the full density
-- statement:
--   The residue densities sum to the full density.
--
--   * `tsum_moebius_div_sq`: `Σ' j, μ(j)/j² = 6/π²` (from `L(ζ,2)·L(μ,2) = 1` and `ζ(2) = π²/6`).
--   * `Cm_one`: `C_1 = 6/π²`.
--   * **`sum_Dm`** (`n ≠ 0`, `|n| ⊥ m`): `Σ_{r : ZMod m} D_m(r) = (Σ_{h ∣ |n|} 1/h) · 6/π²`
--     (uniqueness of limits: the residue-class sums add up to the full sum, which is the `m = 1` case).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV6b

/-!
# S3-ES-Wt2 (O6, file MV6c): the residue densities sum to the full density

* `tsum_moebius_div_sq`: `Σ' j, μ(j)/j² = 6/π²` (from `L(ζ,2)·L(μ,2) = 1` and `ζ(2) = π²/6`).
* `Cm_one`: `C_1 = 6/π²`.
* **`sum_Dm`** (`n ≠ 0`, `|n| ⊥ m`): `Σ_{r : ZMod m} D_m(r) = (Σ_{h ∣ |n|} 1/h) · 6/π²`
  (uniqueness of limits: the residue-class sums add up to the full sum, which is the `m = 1` case).
-/

open Finset Filter Topology

open scoped ArithmeticFunction.Moebius

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

theorem tsum_moebius_div_sq :
    ∑' j : ℕ, (μ j : ℝ) / j / j = 6 / Real.pi ^ 2 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h1 := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h1
  have h2 : LSeries (fun n : ℕ => ((μ n : ℤ) : ℂ)) 2 =
      ((∑' j : ℕ, (μ j : ℝ) / j / j : ℝ) : ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun j => ?_
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · rw [LSeries.term_of_ne_zero hj, Complex.cpow_two]
      push_cast
      ring
  have h1' : (Real.pi : ℂ) ^ 2 / 6 * ((∑' j : ℕ, (μ j : ℝ) / j / j : ℝ) : ℂ) = 1 := by
    rw [← h2]
    exact h1
  have h4 : Real.pi ^ 2 / 6 * ∑' j : ℕ, (μ j : ℝ) / j / j = 1 := by
    exact_mod_cast h1'
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  rw [eq_div_iff hpi]
  linarith

theorem Cm_one : Cm 1 = 6 / Real.pi ^ 2 := by
  rw [← tsum_moebius_div_sq, Cm]
  refine tsum_congr fun j => ?_
  simp [gm]

lemma Dm_one (n : ℤ) : Dm 1 n 0 = (∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h) * Cm 1 := by
  simp [Dm, Am]

variable {m : ℕ} [NeZero m]

theorem sum_Dm {n : ℤ} (hn : n ≠ 0) (hnm : Nat.Coprime n.natAbs m) :
    ∑ r : ZMod m, Dm m n r = (∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h) * (6 / Real.pi ^ 2) := by
  have h1 : Tendsto (fun N : ℕ => (∑ k ∈ Icc 1 N, (Nk n k : ℝ) / k) / N) atTop
      (𝓝 (∑ r : ZMod m, Dm m n r)) := by
    have := tendsto_finsetSum (univ : Finset (ZMod m)) fun r _ => tendsto_res hn hnm r
    refine this.congr fun N => ?_
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have h2 : Tendsto (fun N : ℕ => (∑ k ∈ Icc 1 N, (Nk n k : ℝ) / k) / N) atTop
      (𝓝 (Dm 1 n 0)) := by
    have := tendsto_res (m := 1) hn (Nat.coprime_one_right _) 0
    refine this.congr fun N => ?_
    congr 1
    exact Finset.sum_congr rfl fun k _ => if_pos (Subsingleton.elim _ _)
  rw [tendsto_nhds_unique h1 h2, Dm_one, Cm_one]

end RamanujanPetersson.EllW2


