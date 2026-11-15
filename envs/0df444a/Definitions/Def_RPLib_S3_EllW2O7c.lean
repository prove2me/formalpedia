-- Prove2me | Definitions.Def_RPLib_S3_EllW2O7c
-- name    : RPLib_S3_EllW2O7c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:29:01.57504+00:00
-- url     : https://prove2.me/theorems/61dd20ba-7527-4df7-b5e8-e56b44872c65
-- title:
--   The Eichler-Selberg trace formula in weight two: the weight-two trace formula from the residue statement P6
-- statement:
--   The weight-two trace formula from the residue statement P6.
--
--   * `P6Stmt`: `s · LS(s) → π σ₁(n)/n` as `s → 0+` (`M ≥ 4`, `n > 0` prime to `M`).
--   * `bergmanConst_two`: `C₂ = -π`; `eisG1_two`: `eisG1 M 2 n = Σ_{e ∣ n} e` for `n` prime to `M`.
--   * **`trace_heckeTn_diamond_wt2_of_P6`**: `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = traceFormulaG1 M 2 n δ`, given P6.
--   * **`eichlerSelbergG1_of_P6`**: `S3.EichlerSelbergG1` from P6.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2P7b
import Definitions.Def_RPLib_S3_EichlerSelberg

/-!
# S3-ES-Wt2 (O7c): the weight-two trace formula from the residue statement P6

* `P6Stmt`: `s · LS(s) → π σ₁(n)/n` as `s → 0+` (`M ≥ 4`, `n > 0` prime to `M`).
* `bergmanConst_two`: `C₂ = -π`; `eisG1_two`: `eisG1 M 2 n = Σ_{e ∣ n} e` for `n` prime to `M`.
* **`trace_heckeTn_diamond_wt2_of_P6`**: `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = traceFormulaG1 M 2 n δ`, given P6.
* **`eichlerSelbergG1_of_P6`**: `S3.EichlerSelbergG1` from P6.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate Topology MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm RamanujanPetersson.KernelSD RamanujanPetersson.HypPar
open RamanujanPetersson.HeckeAlgebra (heckeTn)
open RamanujanPetersson.Diamond (diamond)

/-- **P6**: the residue of the regularised hyperbolic-parabolic zero mode at `s = 0`. -/
def P6Stmt : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ n : ℕ, 0 < n → n.Coprime M → ∀ δ : (ZMod M)ˣ,
    Tendsto (fun s : ℝ => (s : ℂ) * LS M (n : ℤ) ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s) (𝓝[>] 0)
      (𝓝 (((π * (ArithmeticFunction.sigma 1 n : ℝ) / n : ℝ)) : ℂ))

lemma bergmanConst_two : Bergman.bergmanConst 2 = -(π : ℂ) := by
  rw [Bergman.bergmanConst, I_sq]
  norm_num
  ring

lemma eisG1_two {M n : ℕ} (hnM : n.Coprime M) : S3.eisG1 M 2 n = ∑ e ∈ n.divisors, (e : ℚ) := by
  rw [S3.eisG1, if_pos rfl, Finset.filter_true_of_mem]
  intro e he
  exact (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)) hnM).symm

/-- **Eichler-Selberg / Cohen-Oesterle in weight two, from P6.** -/
theorem trace_heckeTn_diamond_wt2_of_P6 (hP6 : P6Stmt) {M : ℕ} [NeZero M] (hM : 4 ≤ M) {n : ℕ}
    (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))
        (heckeTn ((2 : ℕ) : ℤ) n * diamond ((2 : ℕ) : ℤ) δ) =
      ((S3.traceFormulaG1 M 2 n (δ : ZMod M) : ℚ) : ℂ) := by
  have : (pmSL (Gamma1 M)).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSL _)
  let _ : Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M)) := Fintype.ofFinite _
  rw [trace_wt2_split (by omega) hn hnM δ, index_mul_scalTrace (by omega)]
  have h1 : (n : ℂ) ^ (2 - 1) = (n : ℂ) := by norm_num
  rw [h1, restPart0_eq_of_P6 (by omega) hn hnM δ (hP6 M hM n hn hnM δ), S3.traceFormulaG1,
    eisG1_two hnM, bergmanConst_two]
  simp only [ArithmeticFunction.sigma_one_apply]
  push_cast
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- **`S3.EichlerSelbergG1` from P6.** -/
theorem eichlerSelbergG1_of_P6 (h : P6Stmt) : S3.EichlerSelbergG1 := by
  refine ES.eichlerSelbergG1_of_wt2 ?_
  intro M _ hM p hp hpM m δ
  rw [Tpow_eq_heckeTn]
  exact trace_heckeTn_diamond_wt2_of_P6 h hM (pow_pos hp.out.pos m)
    (Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpM)) δ

end RamanujanPetersson.EllW2


