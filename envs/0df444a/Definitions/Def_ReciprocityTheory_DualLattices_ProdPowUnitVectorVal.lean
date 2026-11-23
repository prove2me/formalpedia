-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
-- name    : ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:36.415637+00:00
-- url     : https://prove2.me/theorems/65545dea-5ef9-4422-bb2f-4cdb649b9c47
-- title:
--   Prod Pow Unit Vector Val
-- statement:
--   Definitions and structural lemmas for Prod Pow Unit Vector Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdPowUnitVectorVal.lean

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
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
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
def e1 (l : Ix g) : Nb p g := Pi.single l 1
def hvec (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R := uR hv D j y ^ p
def bR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) : Nb p g → R :=
  (MuR hv D)⁻¹ *ᵥ hvec hv D j
def epow (D : Lifts H U X) (α : Nb p g) : R := ∏ j, D.ε j ^ (α j).val
def psi (a : O) (y : Nb p g) : Nb p g := ((H.ρ a).map PadicInt.toZMod) *ᵥ y
end ReciprocityTheory.PGsh.Up.UnitVectorPowers


