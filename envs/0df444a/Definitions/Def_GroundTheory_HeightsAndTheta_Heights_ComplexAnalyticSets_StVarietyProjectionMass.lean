-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyProjectionMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyProjectionMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:08.401668+00:00
-- url     : https://prove2.me/theorems/44b37ef5-c699-4056-b257-46d532c321e2
-- title:
--   St Variety Projection Mass
-- statement:
--   Definitions and structural lemmas for St Variety Projection Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarietyProjectionMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section
def rowsProj {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 ((U.submatrix s id).mulVec fun j => z j)
open Classical in

def VarietyProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B))
end
end GroundTheory.Heights₂.Heights


