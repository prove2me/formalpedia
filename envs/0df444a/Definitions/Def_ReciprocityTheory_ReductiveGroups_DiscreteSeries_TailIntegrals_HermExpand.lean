-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:24.571791+00:00
-- url     : https://prove2.me/theorems/814ebe76-a6e7-4434-ab40-369a085f219b
-- title:
--   Herm Expand
-- statement:
--   Definitions and structural lemmas for Herm Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace BL
section ex
variable (k n : ℕ)
def wp (i : Fin (k - 1)) : Fin (2 * n + k + 1) := wI k n ⟨i.val + 1, by omega⟩
def wv (i : Fin (k - 1)) : Fin (2 * n + k + 1) → ℂ := bvec (wp k n i)
def Phv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV' k n) (Sum.elim (phiV k n) (wv k n))
def Psv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV k n) (Sum.elim (phiV' k n) (wv k n))
end ex
end BL
end ReciprocityTheory.ChartRestriction.DS.Xi


