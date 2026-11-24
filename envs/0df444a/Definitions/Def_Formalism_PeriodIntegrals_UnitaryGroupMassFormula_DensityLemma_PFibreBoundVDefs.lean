-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundVDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundVDefs
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:09.572337+00:00
-- url     : https://prove2.me/theorems/20895fe9-989b-4fb0-84c0-5d70756f3843
-- title:
--   PFibre Bound VDefs
-- statement:
--   Definitions and structural lemmas for PFibre Bound VDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFibreBoundVDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
def hW (k : ℕ) (j : Fin (k + 1)) : ℂ := if j.val = k then -1 else 1
def zW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => z (wI k r j)
def cmOf (k r : ℕ) (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  S - (1 / 2 : ℂ) • (Bm * Matrix.diagonal (hW k) * Bmᴴ)
def unipotentBlockMatrix (k r : ℕ) (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : B.Mat k r :=
  Matrix.of fun i j =>
    (if i = j then 1 else 0) +
    (if h : i.val < r ∧ r ≤ j.val ∧ j.val ≤ r + k then
      Bm ⟨i.val, h.1⟩ ⟨j.val - r, by omega⟩ else 0) +
    (if h : i.val < r ∧ r + k < j.val then
      cmOf k r Bm S ⟨i.val, h.1⟩ ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ else 0) +
    (if h : r ≤ i.val ∧ i.val ≤ r + k ∧ r + k < j.val then
      -(hW k ⟨i.val - r, by omega⟩) * star (Bm ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ ⟨i.val - r, by omega⟩)
      else 0)
def UnipotentBlockCoordinates : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z →
    (∀ n ∈ C2.N0set k r z, ∃ (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ),
      Bm *ᵥ zW k r z = 0 ∧ Sᴴ = -S ∧ n = unipotentBlockMatrix k r Bm S) ∧
    (∀ (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ),
      Bm *ᵥ zW k r z = 0 → Sᴴ = -S → unipotentBlockMatrix k r Bm S ∈ C2.N0set k r z)
end PI.UnitaryGroupMassFormula.DLm


