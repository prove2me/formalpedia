-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Signature
-- name    : GroundTheory_HeightsAndTheta_Theta_Signature
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:38.416573+00:00
-- url     : https://prove2.me/theorems/7db4fcfb-00cb-485c-a3aa-d48a33c5e28e
-- title:
--   Signature
-- statement:
--   Definitions and structural lemmas for Signature, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Signature.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Inertia
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_embedding_over_b3860a0a3dd0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open Module Matrix NumberField GroundTheory.Automorphic
section General
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
noncomputable def completedGram (h : HermitianForm F E V) (b : Basis ι E V) (φ : E →+* ℂ) :
    Matrix ι ι ℂ :=
  (gram h.toSesq b).map φ
variable {φ : E →+* ℂ}
variable [FiniteDimensional E V]
noncomputable def signatureAt (h : HermitianForm F E V) (φ : E →+* ℂ) : ℕ × ℕ :=
  matrixSignature (completedGram h (Module.finBasis E V) φ)
end General
section CM
variable {F E : Type*} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
noncomputable def signature (h : HermitianForm F E V) (v : InfinitePlace F) : ℕ × ℕ :=
  signatureAt h (exists_embedding_over F E v).choose
end CM
end GroundTheory.Heights₂.Theta


