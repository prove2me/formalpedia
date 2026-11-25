-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BigCellMemUnitary
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_BigCellMemUnitary
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:08:46.901649+00:00
-- url     : https://prove2.me/theorems/ba11e7a0-eaa2-49b5-8d9a-e075d47b11d7
-- title:
--   Big Cell Mem Unitary
-- statement:
--   Definitions and structural lemmas for Big Cell Mem Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BigCellMemUnitary.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
namespace GlobalTheory
namespace BigCellUnitary
def pos (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) → Fin (2 * r + k + 1) :=
  Sum.elim (Sum.elim (eI k r) (esI k r)) (wI k r)
theorem pos_bijective (k r : ℕ) : Function.Bijective (pos k r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp; omega⟩
  rintro ((a | a) | a) ((b | b) | b) h <;>
    simp only [pos, eI, esI, wI, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    first
      | (exfalso; omega)
      | (have : a = b := Fin.ext (by omega); rw [this])
def posEquiv (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) ≃ Fin (2 * r + k + 1) :=
  Equiv.ofBijective _ (pos_bijective k r)
end BigCellUnitary
end GlobalTheory


