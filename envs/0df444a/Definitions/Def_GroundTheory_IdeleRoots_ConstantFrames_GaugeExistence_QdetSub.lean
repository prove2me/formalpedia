-- Prove2me | Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
-- name    : GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:11.44922+00:00
-- url     : https://prove2.me/theorems/6a157207-3225-5f6a-85c9-a14b9b0f78f6
-- title:
--   Qdet Sub
-- statement:
--   Definitions and structural lemmas for Qdet Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial Formalism.REAL
namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists
noncomputable section
section Capelli
variable {A : Type} [Ring A] [Algebra ℂ A]
def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A (k : ℂ)) else 0) + C (E a b)
def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), C ((Equiv.Perm.sign σ : ℤ) : A) *
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod
def evU (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) (fun a => (Algebra.commutes u a).symm)
end Capelli
end
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists


