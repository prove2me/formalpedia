-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsHilbEmptyZero
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsHilbEmptyZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:41.562622+00:00
-- url     : https://prove2.me/theorems/a4dc1d8e-76dd-400d-8e98-a06acf974579
-- title:
--   Statements Hilb Empty Zero
-- statement:
--   Definitions and structural lemmas for Statements Hilb Empty Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsHilbEmptyZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
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
universe u
def HilbEmptyZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), (∀ W ∈ I.minimalPrimes, ¬ IsRelevant W) →
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0
noncomputable def HilbEmptyZero.blockIdeal (k : Fin 2) : Ideal (MRing (fun _ : Fin 2 => Fin 2) ℚ) :=
  Ideal.span (Set.range fun i : Fin 2 => (X ⟨k, i⟩ : MRing (fun _ : Fin 2 => Fin 2) ℚ))
end GroundTheory.Heights₂.Heights.FieldNumbers


