-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
-- name    : Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:08.168383+00:00
-- url     : https://prove2.me/theorems/c5f3037f-3880-4839-816b-1e72f2b255b9
-- title:
--   Step Tie
-- statement:
--   Definitions and structural lemmas for Step Tie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
section steptie
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
noncomputable def stQ (k : ℕ) (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus
variable {D}
end steptie
end Formalism.InvariantFactorPaths.KP.LL


