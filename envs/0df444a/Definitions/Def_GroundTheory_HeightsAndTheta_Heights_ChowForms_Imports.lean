-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:20.956557+00:00
-- url     : https://prove2.me/theorems/9cbfc85a-e3c4-4c31-9a64-b4de667601b2
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Imports.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
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
def GenericLinearTrdeg.Statement : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (N k d : ℕ) (η : Fin N → E),
    Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = d →
      Algebra.trdeg F (Algebra.adjoin F
        (Set.range (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E)) ∪
          Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m)))) = ((k * N + min k d : ℕ) : Cardinal)
def IncIdealDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k d : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal P k) =
        ((k * n - k + min k d : ℕ) : WithBot ℕ∞)
def ChowFormBirational.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (g : MvPolynomial (Fin (k + 1) × Fin n) F) (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)),
    IsProjPrime P → IsChowForm P (k + 1) g → ∑ j, c j * genPt P j = 1 →
      ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
        ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
              C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
            aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


