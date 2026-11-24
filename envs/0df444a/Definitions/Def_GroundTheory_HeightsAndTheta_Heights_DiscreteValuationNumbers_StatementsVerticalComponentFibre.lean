-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalComponentFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalComponentFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:27.087375+00:00
-- url     : https://prove2.me/theorems/5cf6ee0c-9968-4f76-8d75-b1547ba1b495
-- title:
--   Statements Vertical Component Fibre
-- statement:
--   Definitions and structural lemmas for Statements Vertical Component Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsVerticalComponentFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFibreVar
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
def VerticalComponentFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (f : MRing ι O) (b : K → ℕ), IsMultiHomog f b → f ∉ P →
    ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → (C ϖ : MRing ι O) ∈ W →
      IsMultiProjPrime (specialIdeal W) ∧
        ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
end
end GroundTheory.Heights₂.Heights.NumbersDVR


