-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftOfLocal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftOfLocal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T17:54:20.4547+00:00
-- url     : https://prove2.me/theorems/a5889a32-1f93-4d64-a489-2ee2fc927f5c
-- title:
--   Lift Of Local
-- statement:
--   Definitions and structural lemmas for Lift Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftOfLocal.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
namespace Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
def lpt (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (s : ℕ) (t : E) (h : TB.Pt E) : C.LPt :=
  C.loc (S.σ v) h ++ [(s, S.σ v t)]
end
end Formalism.FourierDecayAlt.P.PBA


