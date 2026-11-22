-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:54.064448+00:00
-- url     : https://prove2.me/theorems/39f127a5-f58f-428f-a42c-403009ac71d2
-- title:
--   First Weight Le Of Support
-- statement:
--   Definitions and structural lemmas for First Weight Le Of Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
section Lib
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Lib
section YC
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def YCondC (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (M : WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sSup {S | S ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} ∧
    GlStableC p LL j Cs S}
end YC
section Split
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def glRest (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j j' : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  glAct p LL j' c d - glAct p LL j c d
end Split
end Formalism.InvariantFactorPaths.L4


