-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:54:21.605169+00:00
-- url     : https://prove2.me/theorems/0a7125ee-1f30-4209-94b0-474caa80ef78
-- title:
--   LPSOriginal Special Fibre Frobenius
-- statement:
--   Definitions and structural lemmas for LPSOriginal Special Fibre Frobenius, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)
def lpsOriginalPrimeSpecToInteger : Spec (.of (ZMod p)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p)))
abbrev lpsOriginalSpecialFibre : Scheme :=
  pullback (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p)
def lpsOriginalSpecialFibreToPrimeField : lpsOriginalSpecialFibre p N hN ⟶ Spec (.of (ZMod p)) :=
  pullback.snd (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p)
def lpsOriginalSpecialFibreFrobenius : lpsOriginalSpecialFibre p N hN ⟶ lpsOriginalSpecialFibre p N hN :=
  absoluteFrobenius p _ (lpsOriginalSpecialFibreToPrimeField p N hN)
abbrev lpsOriginalProjectiveJSpecialFibre : Scheme :=
  pullback lpsOriginalIntegerProjectiveJLineToSpecZ (lpsOriginalPrimeSpecToInteger p)
def lpsOriginalProjectiveJSpecialFibreToPrimeField :
    lpsOriginalProjectiveJSpecialFibre p ⟶ Spec (.of (ZMod p)) :=
  pullback.snd lpsOriginalIntegerProjectiveJLineToSpecZ (lpsOriginalPrimeSpecToInteger p)
def lpsOriginalSpecialFibreToProjectiveJ :
    lpsOriginalSpecialFibre p N hN ⟶ lpsOriginalProjectiveJSpecialFibre p :=
  pullback.lift
    (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p) ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
    (lpsOriginalSpecialFibreToPrimeField p N hN)
    (by
      change (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p) ≫
        lpsOriginalIntegerNormalGluedToProjectiveJ N hN) ≫ lpsOriginalIntegerProjectiveJLineToSpecZ =
        pullback.snd (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p) ≫ lpsOriginalPrimeSpecToInteger p
      rw [Category.assoc]
      exact pullback.condition)
end
end QEC.Coding.TannerLiftedProduct


