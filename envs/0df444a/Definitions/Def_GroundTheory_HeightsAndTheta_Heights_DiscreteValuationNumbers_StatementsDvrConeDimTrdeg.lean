-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:18.277117+00:00
-- url     : https://prove2.me/theorems/2e690eeb-f993-471c-a64e-9f13982c3a6b
-- title:
--   Statements Dvr Cone Dim Trdeg
-- statement:
--   Definitions and structural lemmas for Statements Dvr Cone Dim Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsDvrConeDimTrdeg.lean

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
def DvrConeDimTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
      ringKrullDim (MRing ι O ⧸ P) =
        (((Algebra.trdeg O (MRing ι O ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞)
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


