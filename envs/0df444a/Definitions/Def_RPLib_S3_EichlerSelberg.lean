-- Prove2me | Definitions.Def_RPLib_S3_EichlerSelberg
-- name    : RPLib_S3_EichlerSelberg
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:46:01.153688+00:00
-- url     : https://prove2.me/theorems/df64929c-8868-4b43-a81d-367bf51e4268
-- title:
--   The Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$, $k \ge 3$
-- statement:
--   For $M \ge 3$, $k \ge 3$, $n \ge 1$ coprime to $M$ and $\delta \in (\mathbb{Z}/M)^\times$:
--   $$\operatorname{Tr}\big(T_n \langle \delta \rangle \mid S_k(\Gamma_1(M))\big) = A_1 + A_2 + A_3 + A_4,$$
--   the scalar, elliptic (Hurwitz class number), hyperbolic and Eisenstein terms of Cohen and Oesterlé, with $A_4 = 0$ for $k \ge 3$. Assembled from the kernel method: the trace as an integral of the kernel diagonal, the scalar and elliptic contributions, and the hyperbolic-parabolic total via Stokes' theorem.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Theorem 12.4.11

import Mathlib
import Definitions.Def_RPLib_S3_Kernel
import Definitions.Def_RPLib_S3_HypParI
import Definitions.Def_RPLib_S3_HypPar

/-!
# S3-HypParTerms (O9): the Eichler-Selberg / Cohen-Oesterle trace formula on `S_k(Γ₁(M))`, `k ≥ 3`

Assembly of
* `EllTerm.trace_eq_central_add_rest`: `Tr(T_n ⟨δ⟩) = index · scalTrace + A2 + n^{k-1} B_k⁻¹ ∫_{Γ₁(M)\ℍ} restPart`;
* `HypPar.index_mul_scalTrace`: `index · scalTrace = A1`;
* `HypPar.traceDown`: `∫_{Γ₁(M)\ℍ} restPart = ∫_𝒟 Ktil`;
* `HypPar.hypPar_main` + `HypPar.sum_pairQ_eq`: `n^{k-1} B_k⁻¹ ∫_𝒟 Ktil = A3`;
* `A4 = 0` for `k ≥ 3`;
* `Kernel.Tpow_eq_heckeTn`: the `Tpow` recursion of `S3.Statements` is `T_{p^m}`.

Main results: `trace_heckeTn_diamond` (any `n` prime to `M`), `trace_Tpow_diamond` (the `EichlerSelbergG1` shape),
`eichlerSelbergG1_three_le` (the `S3.EichlerSelbergG1` statement restricted to `k ≥ 3`) and
`eichlerSelbergG1_of_wt2` (`S3.EichlerSelbergG1` from its weight-two case).
-/

open Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.ES

open RP.FundDomain RP.Petersson RamanujanPetersson.Bergman RamanujanPetersson.Diamond
  RamanujanPetersson.Hecke RamanujanPetersson.Kernel RamanujanPetersson.EllTerm RamanujanPetersson.HypPar
open RamanujanPetersson.HeckeAlgebra (heckeTn)

/-- The Eisenstein term vanishes off weight two. -/
lemma eisG1_of_ne {M k n : ℕ} (hk : k ≠ 2) : S3.eisG1 M k n = 0 := by
  rw [S3.eisG1, if_neg hk]

/-- **Eichler-Selberg / Cohen-Oesterle for `S_k(Γ₁(M))`, `k ≥ 3`.** For `M ≥ 3`, `n > 0` prime to `M` and
`δ ∈ (ℤ/M)ˣ`: `Tr(T_n ⟨δ⟩ | S_k(Γ₁(M))) = A1 + A2 + A3 + A4`. -/
theorem trace_heckeTn_diamond {M : ℕ} [NeZero M] (hM : 3 ≤ M) {k : ℕ} (hk : 3 ≤ k) {n : ℕ} (hn : 0 < n)
    (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (S1 M (k : ℤ)) (heckeTn (k : ℤ) n * diamond (k : ℤ) δ) =
      ((S3.traceFormulaG1 M k n (δ : ZMod M) : ℚ) : ℂ) := by
  obtain ⟨hRi, htr⟩ := trace_eq_central_add_rest hM hk hn hnM δ
  set δ'' : ZMod M := ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) with hδ''
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  obtain ⟨hKi, hKeq⟩ := traceDown hM hk hnz δ'' hRi
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hH := hypPar_main hn δ'' hm hKi
  -- level data for `sum_pairQ_eq`: `D = δ''` lifted, `U = δ⁻¹` lifted
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
  have hP := sum_pairQ_eq (M := M) (k := m + 1) (by omega) hn hnM (δ : ZMod M) _ hU _ hD
  rw [hDδ] at hP
  simp only [Nat.add_sub_cancel] at htr
  rw [htr, index_mul_scalTrace hM, hKeq, hH, hP]
  simp only [S3.traceFormulaG1, eisG1_of_ne (show m + 1 ≠ 2 by omega), add_zero, Rat.cast_add]

/-- **The `EichlerSelbergG1` shape, `k ≥ 3`**: `Tr(T_{p^m} ⟨δ⟩ | S_k(Γ₁(M))) = A1 + A2 + A3 + A4` with the
`Tpow` recursion of `S3.Statements` (`p ∤ M`, `M ≥ 3`). -/
theorem trace_Tpow_diamond {M : ℕ} [NeZero M] (hM : 3 ≤ M) {k : ℕ} (hk : 3 ≤ k) (p : ℕ) [hp : Fact p.Prime]
    (hpM : ¬ p ∣ M) (m : ℕ) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (S1 M (k : ℤ)) (S3.Tpow p hpM (k : ℤ) m * diamond (k : ℤ) δ) =
      ((S3.traceFormulaG1 M k (p ^ m) (δ : ZMod M) : ℚ) : ℂ) := by
  rw [Tpow_eq_heckeTn]
  exact trace_heckeTn_diamond hM hk (pow_pos hp.out.pos m)
    (Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpM)) δ

/-- `S3.EichlerSelbergG1` restricted to `k ≥ 3`. -/
theorem eichlerSelbergG1_three_le :
    ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ k : ℕ, 3 ≤ k → ∀ (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ)
      (δ : (ZMod M)ˣ),
      LinearMap.trace ℂ (S1 M (k : ℤ)) (S3.Tpow p hpM (k : ℤ) m * diamond (k : ℤ) δ) =
        ((S3.traceFormulaG1 M k (p ^ m) (δ : ZMod M) : ℚ) : ℂ) := by
  intro M hMz hM k hk p hp hpM m δ
  exact trace_Tpow_diamond (by omega) hk p hpM m δ

/-- `S3.EichlerSelbergG1` follows from its weight-two case (S3-ES-Wt2). -/
theorem eichlerSelbergG1_of_wt2
    (h2 : ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ)
      (δ : (ZMod M)ˣ),
      LinearMap.trace ℂ (S1 M ((2 : ℕ) : ℤ)) (S3.Tpow p hpM ((2 : ℕ) : ℤ) m * diamond ((2 : ℕ) : ℤ) δ) =
        ((S3.traceFormulaG1 M 2 (p ^ m) (δ : ZMod M) : ℚ) : ℂ)) :
    S3.EichlerSelbergG1 := by
  intro M hMz hM k hk p hp hpM m δ
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    exact h2 M hM p hpM m δ
  · exact eichlerSelbergG1_three_le M hM k h p hpM m δ

end RamanujanPetersson.ES


