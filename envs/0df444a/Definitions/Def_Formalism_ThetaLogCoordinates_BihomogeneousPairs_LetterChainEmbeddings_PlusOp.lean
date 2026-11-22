-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
-- name    : Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:45.895413+00:00
-- url     : https://prove2.me/theorems/a630bfde-9fdb-4c6f-bdd2-dd205d337435
-- title:
--   Plus Op
-- statement:
--   Definitions and structural lemmas for Plus Op, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
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
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
section plusop
variable {p : ℕ} [Fact p.Prime]
noncomputable abbrev po_d {σ : Type} (v : σ) : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] :=
  (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
variable {N r : ℕ} [NeZero r] {D : BlockData N}
noncomputable abbrev po_R (p : ℕ) [Fact p.Prime] (N r t b : ℕ) : Submodule ℚ_[p] (MvPolynomial (BVar N r t) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p]
    {m | (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b}
end plusop
end Formalism.InvariantFactorPaths.KP.LL


