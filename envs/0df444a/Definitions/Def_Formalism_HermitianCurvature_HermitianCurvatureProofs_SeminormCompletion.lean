-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:31:39.455615+00:00
-- url     : https://prove2.me/theorems/e4b65357-571b-41f6-b648-58ae5c6a15f5
-- title:
--   Seminorm Completion
-- statement:
--   Definitions and structural lemmas for Seminorm Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux8
def SW {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (_p : Seminorm ℂ V) : Type := V
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (p : Seminorm ℂ V)
instance : AddCommGroup (SW p) := inferInstanceAs (AddCommGroup V)
instance : Module ℂ (SW p) := inferInstanceAs (Module ℂ V)
noncomputable instance : SeminormedAddCommGroup (SW p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := SW p) p.toAddGroupSeminorm
noncomputable instance : NormedSpace ℂ (SW p) where
  norm_smul_le c v := le_of_eq (map_smul_eq_mul p c v)
end
section supp
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pi
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
end pi
end supp
end Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


