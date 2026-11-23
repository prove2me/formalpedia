-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
-- name    : Formalism_PeriodIntegrals_DatumBlockEigen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:07.648378+00:00
-- url     : https://prove2.me/theorems/e05bef87-b2cc-4781-a1d9-645f0166fdc7
-- title:
--   Datum Block Eigen
-- statement:
--   Definitions and structural lemmas for Datum Block Eigen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DatumBlockEigen.lean

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Finset
namespace PI.DatumBlockEigen
def blockCond {F : Type} [Field F] (O : Subring F) (ϖ : F) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (A : GL (Fin (a + t)) F) : Prop :=
  let M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A : Matrix (Fin (a + t)) (Fin (a + t)) F)
  (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = M.toBlocks₁₁) ∧
  (∀ i j, M.toBlocks₁₂ i j ∈ O) ∧
  M.toBlocks₂₁ ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ∧
  (∃ D ∈ Formalism.DoubleCosetMeasures.GLint O t, (D : Matrix (Fin t) (Fin t) F) = M.toBlocks₂₂)
end PI.DatumBlockEigen
namespace PI
open PI.DatumBlockEigen in

def DatumBlockEigen : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a →
    ∀ (ρ : J' →* ℂˣ), (∀ k : J', (k : GL (Fin a) F) ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a → ρ k = 1) →
    ∀ h : GL (Fin (a + t)) F, blockCond O ϖ J' h →
      let Mi : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
        Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
          ((h⁻¹ : GL (Fin (a + t)) F) : Matrix (Fin (a + t)) (Fin (a + t)) F)
      ∃ k' : J', ((k' : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = Mi.toBlocks₁₁ ∧
        ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
          Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ (Mi * x) = ((ρ k' : ℂˣ) : ℂ) * Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x
end PI


