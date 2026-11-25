-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:06.838002+00:00
-- url     : https://prove2.me/theorems/7c2ea686-6eb3-49b5-bc90-52c002cd4ef1
-- title:
--   Wt Add Single
-- statement:
--   Definitions and structural lemmas for Wt Add Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
namespace GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
def wt (C : Type) [CommRing C] (A : σ →₀ ℕ) : C := A.prod fun _ e => (e.factorial : C)
def pair : MvPolynomial σ C →ₗ[C] MvPolynomial σ C →ₗ[C] C :=
  (basisMonomials σ C).constr C fun A => wt C A • lcoeff C A
end GlobalTheory.DetPowPairing


