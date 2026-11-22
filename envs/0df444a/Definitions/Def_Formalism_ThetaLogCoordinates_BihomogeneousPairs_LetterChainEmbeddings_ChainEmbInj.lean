-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
-- name    : Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:09.041888+00:00
-- url     : https://prove2.me/theorems/20db0877-5934-48fd-bc0a-bfbf698bc7be
-- title:
--   Chain Emb Inj
-- statement:
--   Definitions and structural lemmas for Chain Emb Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
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
open scoped Pointwise
section lat
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
noncomputable def Lat (j : Fin D.T.t → ℕ) (jp : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}
noncomputable def Pt (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
    (scalZ N r D.T.t (Fin.castSucc i)) (scalS N r D.T.t (Fin.castSucc i))
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
    (D.T.z i) y
noncomputable def PL (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  L.foldr (fun i acc => Pt p D j jp i acc) y
noncomputable def Pplus (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
    (scalZ N r D.T.t (Fin.last D.T.t)) (scalS N r D.T.t (Fin.last D.T.t))
    (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y
variable {p D}
end lat
end Formalism.InvariantFactorPaths.KP.LL


