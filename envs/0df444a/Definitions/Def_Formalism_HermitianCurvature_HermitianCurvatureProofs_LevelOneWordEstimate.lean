-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelOneWordEstimate
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelOneWordEstimate
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:05.672343+00:00
-- url     : https://prove2.me/theorems/2161f618-b026-4eef-821e-e05b9c6c9f99
-- title:
--   Level One Word Estimate
-- statement:
--   Definitions and structural lemmas for Level One Word Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelOneWordEstimate.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
def LevelOneWordEstimate : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (q : ℝ → ℝ) (w : List (Letter ℝ S)) (N : ℕ) (dl Y : ℝ),
    8 ≤ N → w.length ≤ N → (N : ℝ) ^ 2 / 8 ≤ dl →
    (∀ l ∈ w, if l.plus then dl ≤ |Y - l.pt| else dl ≤ |Y - l.pt| ∧ dl ≤ |Y - (l.pt - 1)|) →
    q Y ≠ 0 →
    Real.exp (-2) ≤ qw q w Y / q Y ∧ qw q w Y / q Y ≤ Real.exp 2
end Formalism.FourierDecayAlt.P.PBD


