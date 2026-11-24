-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:58.878667+00:00
-- url     : https://prove2.me/theorems/d9b8a9e4-ffcb-45bd-a9b5-10f1c19debf7
-- title:
--   Hpk Mul Vec Mul Vec
-- statement:
--   Definitions and structural lemmas for Hpk Mul Vec Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
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
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
end herm
section hpk
variable (k r : ℕ)
variable {k r}
end hpk
section tri
end tri
section dl
variable {k r : ℕ}
def Pm (k r : ℕ) (g : Mat k r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => herm (Hpk k r) (g *ᵥ phiV' k r b) (phiV' k r a)
def cl (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : Fin (r + 1)) : ℝ≥0 :=
  ∏ j : Fin (l.val + 1), ‖τ (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)
    (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)‖₊
end dl
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities


