-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:49:02.574221+00:00
-- url     : https://prove2.me/theorems/9d69b440-731c-53a6-ae59-8cea18c62044
-- title:
--   St Line Normal Form
-- statement:
--   Definitions and structural lemmas for St Line Normal Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StLineNormalForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
section NormalForm
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def LineNormalForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n : ℕ, 0 < n ∧
    ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
      ∃ v w : W, v ∈ l ∧ IsHyperbolicPair h v w ∧
        (lineCoeffs (E := E) La v, lineCoeffs (E := E) La w) ∈ KK ∧
        ∀ x ∈ La, (n : E) * h.toSesq w x ∈ lineCoeffs (E := E) La v ∧
          (n : E) * h.toSesq v x ∈ lineCoeffs (E := E) La w
end NormalForm
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


