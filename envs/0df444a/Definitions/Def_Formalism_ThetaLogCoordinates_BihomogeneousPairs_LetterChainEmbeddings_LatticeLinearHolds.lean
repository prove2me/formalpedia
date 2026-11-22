-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
-- name    : Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:18.660967+00:00
-- url     : https://prove2.me/theorems/43335e2c-a1e0-45b5-8cb5-911bdfd578f8
-- title:
--   Lattice Linear Holds
-- statement:
--   Definitions and structural lemmas for Lattice Linear Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean

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
section abs
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}
noncomputable def cmTiePL (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) :
    Module.End ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  ∑ l ∈ range (o + 1),
    (((-1 : ℚ_[p]) ^ l) / (((l.factorial : ℚ_[p]) ^ 2) * ((o + n + r + z - 1).choose l : ℚ_[p]))) •
      ((tieEh w e zv sv) ^ l * ((tieF w e) ^ l * LinearMap.mulLeft ℚ_[p] (X zv ^ z)))
end abs
section block
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
noncomputable def cmPLL (p : ℕ) [Fact p.Prime] {N r : ℕ} (D : BlockData N) (L : List (Fin D.T.t))
    (j : Fin D.T.t → ℕ) (jp : ℕ) : Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  L.foldr (fun i acc => cmTiePL (wv D i) (ev D i) (zi D r i) (si D r i)
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
    (D.T.z i) * acc) 1
noncomputable def cmPplusL (p : ℕ) [Fact p.Prime] {N r : ℕ} (D : BlockData N) (jp : ℕ) :
    Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  cmTiePL (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus
end block
end Formalism.InvariantFactorPaths.KP.LL


