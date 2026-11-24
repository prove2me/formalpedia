-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFibreVar
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFibreVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:54.218524+00:00
-- url     : https://prove2.me/theorems/e79aa026-85d1-42ee-b03e-1ae301365b95
-- title:
--   Statements Fibre Var
-- statement:
--   Definitions and structural lemmas for Statements Fibre Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsFibreVar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
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
universe u
def FibreVarieties.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      (IsMultiProjPrime (genFib P) ∧
        ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) ∧
      ∀ W : Ideal (MRing ι O), divCycle P (C ϖ) W ≠ 0 →
        IsMultiProjPrime (specialIdeal W) ∧
          ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
            ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
end
end GroundTheory.Heights₂.Heights.NumbersDVR


