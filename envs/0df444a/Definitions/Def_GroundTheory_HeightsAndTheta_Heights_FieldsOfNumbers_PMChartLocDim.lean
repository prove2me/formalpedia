-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartLocDim
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartLocDim
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:30:50.80017+00:00
-- url     : https://prove2.me/theorems/564182da-8c6b-47f2-8f8b-f24215c0b1ee
-- title:
--   PMChart Loc Dim
-- statement:
--   Definitions and structural lemmas for PMChart Loc Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace MChartLocDim
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [Fintype K] in

theorem chartMap_mem (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (p : MRing ι F) : chartMap P u p ∈ degZeroLoc P {W} := by
  have hr : (chartMap P u).range ≤ degZeroLoc P {W} := by
    rw [chartMap, aeval_range, Algebra.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) v)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (fun h => hu v.1 (hPW h)) (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hu v.1)
  exact hr ⟨p, rfl⟩
def toLoc (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) : (MRing ι F ⧸ chartIdeal P u) →+* degZeroLoc P {W} :=
  Ideal.Quotient.lift (chartIdeal P u)
    ((chartMap P u).toRingHom.codRestrict (degZeroLoc P {W}) (chartMap_mem P W hPW u hu))
    (fun _ ha => Subtype.ext (RingHom.mem_ker.mp ha))
end MChartLocDim
end
end GroundTheory.Heights₂.Heights.FieldNumbers


