-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:02.959252+00:00
-- url     : https://prove2.me/theorems/bdef4845-3b5f-48ad-9016-ea048eaddce8
-- title:
--   Standard Character Exists
-- statement:
--   Definitions and structural lemmas for Standard Character Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StandardCharacterExists.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
def ex {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a b : ℕ) : ℂ :=
  if h : a < d ∧ b < d then N ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
instance (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance
end Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.StandardCharacterExists
end Formalism.FourierDecayAlt.P


