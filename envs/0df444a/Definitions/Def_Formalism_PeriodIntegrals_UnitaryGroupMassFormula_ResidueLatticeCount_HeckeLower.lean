-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:20.003945+00:00
-- url     : https://prove2.me/theorems/2d1abd89-5b37-4955-97d8-128dc667388a
-- title:
--   Hecke Lower
-- statement:
--   Definitions and structural lemmas for Hecke Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/HeckeLower.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.Residue
def idealZeta (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' I : {I : Ideal (𝓞 E) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ) ^ (-s)
def zetaR (s : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s)
def ZetaLePow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
    Summable (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-s)) ∧
      idealZeta E s ≤ zetaR s ^ Module.finrank ℚ E
def ZetaRLe : Prop := ∀ s : ℝ, 1 < s → zetaR s ≤ 1 + 1 / (s - 1)
def HeckeLower : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
    Summable (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-s)) →
    dedekindZeta_residue E ≤
      (4 : ℝ) ^ s * (2 * Real.pi) ^ Module.finrank ℚ E * ((|discr E| : ℤ) : ℝ) ^ ((s - 1) / 2) * idealZeta E s
def Optimise : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (m : ℕ) (D : ℝ), 2 ≤ m → 4 / 9 * (3 * Real.pi / 4) ^ m ≤ D →
    ∃ s : ℝ, 1 < s ∧
      (4 : ℝ) ^ s * (2 * Real.pi) ^ m * D ^ ((s - 1) / 2) * (1 + 1 / (s - 1)) ^ m ≤
        (C * Real.log (D ^ ((1 : ℝ) / m))) ^ m
end PI.Residue


