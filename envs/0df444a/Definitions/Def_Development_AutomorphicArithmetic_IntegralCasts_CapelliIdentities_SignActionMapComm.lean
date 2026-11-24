-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SignActionMapComm
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SignActionMapComm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:23:42.131801+00:00
-- url     : https://prove2.me/theorems/613e27c9-7e6f-4129-b4ee-e01bbd7c3b89
-- title:
--   Sign Action Map Comm
-- statement:
--   Definitions and structural lemmas for Sign Action Map Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SignActionMapComm.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.VA :
    Formalism.MainNotions.S.AutInst → Type :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ Fin I.n → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.sigA :
    (I : Formalism.MainNotions.S.AutInst) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) →+* TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)
noncomputable def UpperTheory.Reformulated.B.Qk24.colM :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} → (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) → Matrix (Fin I.n) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) ↦
      (Matrix.of :
          (Fin I.n → Fin k → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
            Matrix (Fin I.n) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)))
        fun (l : Fin I.n) (i : Fin k) ↦ b i l
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk24.Jf :
    (I : Formalism.MainNotions.S.AutInst) → Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) ↦ I.J.map (⇑(Formalism.UG.inclE (Formalism.MainNotions.S.Af I.F)) : I.E → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
noncomputable def UpperTheory.Reformulated.B.Qk24.rowM :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} → (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) → Matrix (Fin k) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) ↦
      Formalism.UG.cT (UpperTheory.Reformulated.B.Qk24.sigA I) (UpperTheory.Reformulated.B.Qk24.colM I b) * UpperTheory.Reformulated.B.Qk24.Jf I
noncomputable def UpperTheory.Reformulated.B.Qk24.Mk :
    (I : Formalism.MainNotions.S.AutInst) →
      {k : ℕ} →
        (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) →
          (Fin k → UpperTheory.Reformulated.B.Qk24.VA I) →
            Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
              Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) →
                Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) :=
    fun (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b d : Fin k → UpperTheory.Reformulated.B.Qk24.VA I)
        (X Y : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) ↦
      (1 : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) +
          UpperTheory.Reformulated.B.Qk24.colM I b * X * UpperTheory.Reformulated.B.Qk24.rowM I d +
        UpperTheory.Reformulated.B.Qk24.colM I d * Y * UpperTheory.Reformulated.B.Qk24.rowM I b


