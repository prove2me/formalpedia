-- Prove2me | Definitions.Def_RPLib_S3_EllW2P7b
-- name    : RPLib_S3_EllW2P7b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:26:04.212211+00:00
-- url     : https://prove2.me/theorems/0a0f6188-8901-45b5-b900-481ca8bfb8bd
-- title:
--   The Eichler-Selberg trace formula in weight two: the O6 value from the residue statement P6
-- statement:
--   The O6 value from the residue statement P6.
--
--   * `norm_L_add_le`: if `∫_{𝒟_Y} NHS_s → L` and `s·LS(s) → ρ` as `s → 0+`, then `‖L + ρ‖ ≤ CNA/Y`.
--   * **`restPart0_eq_of_P6`**: given P6 (`s·LS(s) → ρ`),
--     `n C_2⁻¹ ∫_{Γ₁(M)\ℍ} restPart0 = hypG1 M 2 n δ + n C_2⁻¹ (-ρ)`.
--     With `C_2 = bergmanConst 2 = -π`, the value `ρ = π σ₁(n)/n` gives `eisG1 M 2 n = σ₁(n)` (file O7c).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2P7
import Definitions.Def_RPLib_S3_EllW2K

/-!
# S3-ES-Wt2 (O6, file P7b): the O6 value from the residue statement P6

* `norm_L_add_le`: if `∫_{𝒟_Y} NHS_s → L` and `s·LS(s) → ρ` as `s → 0+`, then `‖L + ρ‖ ≤ CNA/Y`.
* **`restPart0_eq_of_P6`**: given P6 (`s·LS(s) → ρ`),
  `n C_2⁻¹ ∫_{Γ₁(M)\ℍ} restPart0 = hypG1 M 2 n δ + n C_2⁻¹ (-ρ)`.
  With `C_2 = bergmanConst 2 = -π`, the value `ρ = π σ₁(n)/n` gives `eisG1 M 2 n = σ₁(n)` (file O7c).
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups Topology Modular Pointwise
  RamanujanPetersson.S3.Conj

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm RamanujanPetersson.KernelSD

variable {M : ℕ} [NeZero M]

theorem norm_L_add_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) {L ρ : ℂ}
    (hL : Tendsto (fun s => ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z) (𝓝[>] 0) (𝓝 L))
    (hP6 : Tendsto (fun s : ℝ => (s : ℂ) * LS M n δ' s) (𝓝[>] 0) (𝓝 ρ)) :
    ‖L + ρ‖ ≤ CNA M n / Y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : Tendsto (fun s : ℝ => ((((n : ℝ) ^ s / (1 + s)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : ContinuousAt (fun s : ℝ => (n : ℝ) ^ s / (1 + s)) 0 :=
      (Real.continuousAt_const_rpow hn0.ne').div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    have h2 := (Complex.continuous_ofReal.continuousAt.comp h1).tendsto
    rw [Function.comp_def] at h2
    convert h2.mono_left nhdsWithin_le_nhds using 2
    simp
  have hf : Tendsto (fun s : ℝ => (∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z) +
      (((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) * LS M n δ' s) (𝓝[>] 0) (𝓝 (L + ρ)) := by
    have h := hL.add (hK.mul hP6)
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s _
    simp only [Complex.ofReal_div]
    ring
  refine le_of_tendsto hf.norm ?_
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
  exact norm_INS_add_le hn δ' hs.1 hs.2 hY

/-- **O6 from P6.** -/
theorem restPart0_eq_of_P6 (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) [Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M))] {ρ : ℂ}
    (hP6 : Tendsto (fun s : ℝ => (s : ℂ) *
      LS M (n : ℤ) ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s) (𝓝[>] 0) (𝓝 ρ)) :
    (n : ℂ) * (Bergman.bergmanConst 2)⁻¹ * ∫ z in fdom (Gamma1 M), restPart0 M n δ z =
      ((S3.hypG1 M 2 n (δ : ZMod M) : ℚ) : ℂ) + (n : ℂ) * (Bergman.bergmanConst 2)⁻¹ * (-ρ) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hAB : Tendsto (fun Y : ℝ => (∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, restPart0 M n δ (c.out⁻¹ • τ)) -
          ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SPS M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) 0 τ)
      atTop (𝓝 (-ρ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      ((tendsto_const_nhds (x := CNA M (n : ℤ))).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    rw [sub_neg_eq_add]
    exact norm_L_add_le hn' _ hY (tendsto_trunc_NHS hM hn hnM δ hY) hP6
  have h1 := (tendsto_trunc_restPart0 hM hn hnM δ).const_mul ((n : ℂ) * (Bergman.bergmanConst 2)⁻¹)
  have h2 := (hAB.const_mul ((n : ℂ) * (Bergman.bergmanConst 2)⁻¹)).add (tendsto_SP_hyp hn hnM δ)
  have h3 : Tendsto (fun Y : ℝ => (n : ℂ) * (Bergman.bergmanConst 2)⁻¹ *
      ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M), ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, restPart0 M n δ (c.out⁻¹ • τ))
      atTop (𝓝 ((n : ℂ) * (Bergman.bergmanConst 2)⁻¹ * (-ρ) +
        ((S3.hypG1 M 2 n (δ : ZMod M) : ℚ) : ℂ))) :=
    h2.congr fun Y => by simp only [mul_sub]; ring
  rw [tendsto_nhds_unique h1 h3]
  ring

end RamanujanPetersson.EllW2


