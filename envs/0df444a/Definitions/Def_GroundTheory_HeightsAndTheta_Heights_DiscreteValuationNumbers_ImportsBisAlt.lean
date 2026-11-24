-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:40.180147+00:00
-- url     : https://prove2.me/theorems/518b4f04-8f73-4e1e-a45e-3c2971183973
-- title:
--   Imports Bis Alt
-- statement:
--   Definitions and structural lemmas for Imports Bis Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsBisAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
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
def BlowUpStrictTransform.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ s : MRing ι O, s ∉ P → ∀ (e : K → ℕ) (m : MRing ι O),
    ∀ H : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ H →
      (divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) H ≠ 0 ∨
        divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) H ≠ 0) →
      divCycle P s (H.comap (liftForm (J := BlowUpIdx ι))) ≠ 0
end
end GroundTheory.Heights₂.Heights.NumbersDVR


