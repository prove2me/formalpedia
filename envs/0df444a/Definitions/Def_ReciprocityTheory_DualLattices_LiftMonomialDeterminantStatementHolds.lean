-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
-- name    : ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:08.2778+00:00
-- url     : https://prove2.me/theorems/2e02f15d-ab21-4020-9a8a-2186efc64175
-- title:
--   Lift Monomial Determinant Statement Holds
-- statement:
--   Definitions and structural lemmas for Lift Monomial Determinant Statement Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatementHolds.lean

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
def uR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R :=
  (hv.exists_of_le_one (D.u_int j y)).choose
def MuR (hv : v.Integers R) (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) R :=
  Matrix.of fun y α => ∏ j, uR hv D j y ^ (α j).val
end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
namespace ReciprocityTheory.PGsh.Up
end ReciprocityTheory.PGsh.Up


