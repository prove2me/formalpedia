-- Prove2me | Definitions.Def_RPLib_S3_EichlerSelbergWt2
-- name    : RPLib_S3_EichlerSelbergWt2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:07:08.277776+00:00
-- url     : https://prove2.me/theorems/60d26b28-adeb-4aec-a04e-de7b0f849231
-- title:
--   The Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, $M \ge 4$
-- statement:
--   The Eichler-Selberg / Cohen-Oesterle trace formula in weight two.
--
--   The weight-two kernel series diverges; the route is Hecke's trick (the regularised kernel with
--   `|cz + d|^{-2s}`, `s → 0+`), whose only analytic input is the residue statement `P6Stmt`
--   (`lib/S3/EllW2_O7c.lean`), proved as `p6` in `lib/S3/EllW2_AS4.lean`.
--
--   * **`trace_heckeTn_diamond_wt2`**: `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = traceFormulaG1 M 2 n δ` for `M ≥ 4`,
--     `n > 0` prime to `M` (the Cohen-Oesterle formula at `k = 2`, including the `σ₁` Eisenstein term).
--   * **`eichlerSelbergWt2_h2`**: the weight-two hypothesis `h2` of `ES.eichlerSelbergG1_of_wt2`.
--   * **`eichlerSelbergG1`**: `S3.EichlerSelbergG1` (every weight `k ≥ 2`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2O7c
import Definitions.Def_RPLib_S3_EllW2AS4

/-!
# S3-ES-Wt2: the Eichler-Selberg / Cohen-Oesterle trace formula in weight two

The weight-two kernel series diverges; the route is Hecke's trick (the regularised kernel with
`|cz + d|^{-2s}`, `s → 0+`), whose only analytic input is the residue statement `P6Stmt`
(`lib/S3/EllW2_O7c.lean`), proved as `p6` in `lib/S3/EllW2_AS4.lean`.

* **`trace_heckeTn_diamond_wt2`**: `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = traceFormulaG1 M 2 n δ` for `M ≥ 4`,
  `n > 0` prime to `M` (the Cohen-Oesterle formula at `k = 2`, including the `σ₁` Eisenstein term).
* **`eichlerSelbergWt2_h2`**: the weight-two hypothesis `h2` of `ES.eichlerSelbergG1_of_wt2`.
* **`eichlerSelbergG1`**: `S3.EichlerSelbergG1` (every weight `k ≥ 2`).
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

/-- **Eichler-Selberg / Cohen-Oesterle in weight two**:
`Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = traceFormulaG1 M 2 n δ` (`M ≥ 4`, `n > 0` prime to `M`). -/
theorem trace_heckeTn_diamond_wt2 {M : ℕ} [NeZero M] (hM : 4 ≤ M) {n : ℕ}
    (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))
        (heckeTn ((2 : ℕ) : ℤ) n * diamond ((2 : ℕ) : ℤ) δ) =
      ((S3.traceFormulaG1 M 2 n (δ : ZMod M) : ℚ) : ℂ) :=
  trace_heckeTn_diamond_wt2_of_P6 p6 hM hn hnM δ

/-- The weight-two hypothesis of `ES.eichlerSelbergG1_of_wt2`. -/
theorem eichlerSelbergWt2_h2 :
    ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ)
      (δ : (ZMod M)ˣ),
      LinearMap.trace ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))
          (S3.Tpow p hpM ((2 : ℕ) : ℤ) m * diamond ((2 : ℕ) : ℤ) δ) =
        ((S3.traceFormulaG1 M 2 (p ^ m) (δ : ZMod M) : ℚ) : ℂ) := by
  intro M _ hM p hp hpM m δ
  rw [Tpow_eq_heckeTn]
  exact trace_heckeTn_diamond_wt2 hM (pow_pos hp.out.pos m)
    (Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpM)) δ

/-- **`S3.EichlerSelbergG1`**: the Eichler-Selberg trace formula on `S_k(Γ₁(M))` for every `k ≥ 2`. -/
theorem eichlerSelbergG1 : S3.EichlerSelbergG1 :=
  ES.eichlerSelbergG1_of_wt2 eichlerSelbergWt2_h2

end RamanujanPetersson.EllW2


