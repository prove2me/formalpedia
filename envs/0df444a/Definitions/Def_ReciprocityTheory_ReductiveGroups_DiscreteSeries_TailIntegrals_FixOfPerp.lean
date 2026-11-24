-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:18:15.340918+00:00
-- url     : https://prove2.me/theorems/2ae25089-5296-4d91-84a4-0d529aa0b9ea
-- title:
--   Fix Of Perp
-- statement:
--   Definitions and structural lemmas for Fix Of Perp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixOfPerp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
def sigI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩
def sgnI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
theorem sigI_val (i : Fin (2 * r + k + 1)) :
    (sigI k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl
theorem sig_sig (i : Fin (2 * r + k + 1)) : sigI k r (sigI k r i) = i := by
  apply Fin.ext; rw [sigI_val, sigI_val]; split_ifs <;> omega
abbrev EE (k r : ℕ) := EuclideanSpace ℂ (Fin (2 * r + k + 1))
def HE (k r : ℕ) : EE k r →ₗ[ℂ] EE k r := Matrix.toEuclideanLin (Hpk k r)
def sigE (k r : ℕ) : Fin (2 * r + k + 1) ≃ Fin (2 * r + k + 1) := ⟨sigI k r, sigI k r, sig_sig, sig_sig⟩
end ReciprocityTheory.ChartRestriction.DS.Xi.GS


