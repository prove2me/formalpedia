-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:32.046153+00:00
-- url     : https://prove2.me/theorems/508347c0-e4f7-4b0c-be11-23485c609bcb
-- title:
--   Statements Norm Of Divided Form
-- statement:
--   Definitions and structural lemmas for Statements Norm Of Divided Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsNormOfDividedForm.lean

import Mathlib
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
open MvPolynomial
noncomputable section
def NormOfDividedForm.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing B] [IsDomain B] [Algebra O B]
    [Module.Free O B] [Module.Finite O B] (n : ℕ) (η : Fin n → B) (t : Fin n → O)
    (P : MvPolynomial (Fin n) O),
    Algebra.adjoin O (Set.range η) = ⊤ → ∑ m, t m • η m = 1 → Prime P →
      (∑ m, X m * C (η m)) ∣ map (algebraMap O B) P →
        ∀ u : Fin n → O,
          eval u P = eval t P * LinearMap.det (LinearMap.mulLeft O (∑ m, u m • η m))
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


