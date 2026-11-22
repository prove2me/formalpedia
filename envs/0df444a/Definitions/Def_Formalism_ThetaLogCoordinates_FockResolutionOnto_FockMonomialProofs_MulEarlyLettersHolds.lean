-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:55.778802+00:00
-- url     : https://prove2.me/theorems/61382d87-84ab-44aa-94fa-229dce9f47db
-- title:
--   Mul Early Letters Holds
-- statement:
--   Definitions and structural lemmas for Mul Early Letters Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
section Gen
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
noncomputable abbrev SuppLE [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M}
noncomputable abbrev wd [NeZero r] (LL : Letters N) (j : ℕ) (l : List (Fin r)) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (l.map fun c => glAct p LL j 0 c).prod
end Gen
section Tools
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Tools
section Last
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
end Last
end Formalism.InvariantFactorPaths.L4


