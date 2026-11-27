-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGroupCommutantScalars
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGroupCommutantScalars
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:27:14.207588+00:00
-- url     : https://prove2.me/theorems/324d9ca0-da63-5ff8-9356-80b1391bcfe9
-- title:
--   Unitary Group Commutant Scalars
-- statement:
--   Definitions and structural lemmas for Unitary Group Commutant Scalars, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryGroupCommutantScalars.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
namespace GlobalTheory.RegSS.UComm
variable {A : Type} [Field A] {n : Type} [Fintype n] [DecidableEq n]
def rowv (σ : A →+* A) (J : Matrix n n A) (v : n → A) : n → A := (fun i => σ (v i)) ᵥ* J
def proj (σ : A →+* A) (J : Matrix n n A) (v : n → A) : Matrix n n A := vecMulVec v (rowv σ J v)
def refl (σ : A →+* A) (J : Matrix n n A) (v : n → A) : Matrix n n A :=
  1 + (-(2 / hform σ J v v)) • proj σ J v
end GlobalTheory.RegSS.UComm
namespace GlobalTheory.RegSS
end GlobalTheory.RegSS


