-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
-- name    : Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:39.384368+00:00
-- url     : https://prove2.me/theorems/f3585234-47eb-4be5-b10b-706770b94297
-- title:
--   Letter At Succ Val
-- statement:
--   Definitions and structural lemmas for Letter At Succ Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LetterAtSuccVal.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
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
section block
variable {N r : ℕ} (D : BlockData N)
def wv (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i), c)
def ev (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i + 1), c)
def zi (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalZ N r D.T.t (Fin.castSucc i)
def si (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalS N r D.T.t (Fin.castSucc i)
def wU (c : Fin r) : BVar N r D.T.t := Sum.inl (Fin.castSucc D.uPos, c)
def zP (r : ℕ) : BVar N r D.T.t := scalZ N r D.T.t (Fin.last D.T.t)
def sP (r : ℕ) : BVar N r D.T.t := scalS N r D.T.t (Fin.last D.T.t)
variable {D}
end block
end Formalism.InvariantFactorPaths.KP.LL


