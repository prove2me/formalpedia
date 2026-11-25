-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:12:00.175825+00:00
-- url     : https://prove2.me/theorems/5bcb19be-c37c-4b62-9fc9-a20e8657154d
-- title:
--   Second Split Smul
-- statement:
--   Definitions and structural lemmas for Second Split Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitSmul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)
def KerBack : Prop :=
  ∀ c : K, ∀ g : GL n T, g ∈ Formalism.UG.UJ s J → (∀ x, x ∈ Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) →
    (∀ i j, ∃ w ∈ O, (conjPrime₂ θ P g - 1) i j = c * w) →
    ∀ y ∈ Lat O θ J P, ∃ z ∈ Lat O θ J P, ((g : Matrix n n T) - 1) *ᵥ y = c • z
def SurjCore : Prop :=
  ∀ A : GL n O, ∃ g : GL n T, g ∈ Formalism.UG.UJ s J ∧ (∀ x, x ∈ Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) ∧
    conjPrime₂ θ P g = (A : Matrix n n O).map (algebraMap O K)
end MassDataIdxCore


