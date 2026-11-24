-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_AdelClassFin
-- name    : Formalism_PeriodIntegrals_AdelClassFin
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:23:38.182256+00:00
-- url     : https://prove2.me/theorems/0b61d936-98cc-4608-9690-379ace93cf27
-- title:
--   Adel Class Fin
-- statement:
--   Definitions and structural lemmas for Adel Class Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/AdelClassFin.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AdelClassFin
open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix
def GFf (I : Formalism.MainNotions.S.AutInst) : Set I.Gf :=
  {x | ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    I.fmat x = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))}
def AdelClassFin : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) →
    ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ u ∈ U, x = γ * s * u
end PI.AdelClassFin


