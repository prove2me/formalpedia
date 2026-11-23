-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_IndSetFinite
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_IndSetFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:33.175792+00:00
-- url     : https://prove2.me/theorems/de6916bf-df43-4afb-b410-4a617484fc47
-- title:
--   Ind Set Finite
-- statement:
--   Definitions and structural lemmas for Ind Set Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/IndSetFinite.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_FiniteOfIntegralBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions NumberField
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
def indSet (X P : Submodule E S.V) (z : S.V) (Λ : Submodule (𝓞 E) S.V) :
    Set ((P ⧸ X.comap P.subtype) → (P ⧸ X.comap P.subtype)) :=
  {φ | ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ γ z = z ∧ (∀ x ∈ Λ, γ x ∈ Λ) ∧
    (∀ x ∈ P, γ x ∈ P) ∧
    ∀ (x : P) (hx : γ x.1 ∈ P), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, hx⟩}
end PI.AutLzFinite.SlopeTestRemainingChoices


