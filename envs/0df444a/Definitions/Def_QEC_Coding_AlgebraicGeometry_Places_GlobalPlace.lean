-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
-- name    : QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:08:41.229322+00:00
-- url     : https://prove2.me/theorems/a7285449-51dc-479a-9b4c-80a642274a3a
-- title:
--   Global Place
-- statement:
--   Definitions and structural lemmas for Global Place, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped WithZero
structure GlobalPlace (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F] where
  valuation : Valuation F ℤᵐ⁰
  normalized : Function.Surjective valuation
namespace GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
noncomputable def uniformizer (P : GlobalPlace k F) : F :=
  Classical.choose (P.normalized (WithZero.exp (-1 : ℤ)))
def order (P : GlobalPlace k F) (f : F) : ℤ :=
  -WithZero.log (P.valuation f)
abbrev valuationRing (P : GlobalPlace k F) : ValuationSubring F :=
  P.valuation.valuationSubring
abbrev residueField (P : GlobalPlace k F) : Type _ :=
  IsLocalRing.ResidueField (valuationRing P)
def residue (P : GlobalPlace k F) : valuationRing P →+* residueField P :=
  IsLocalRing.residue _
theorem mem_valuationRing_iff (P : GlobalPlace k F) (f : F) :
    f ∈ valuationRing P ↔ P.valuation f ≤ 1 :=
  P.valuation.mem_valuationSubring_iff f
def RegularAt (P : GlobalPlace k F) (f : F) : Prop := P.valuation f ≤ 1
def evaluate (P : GlobalPlace k F) : valuationRing P →+* residueField P :=
  residue P
noncomputable def evaluateRegular (P : GlobalPlace k F) (f : F) (hf : RegularAt P f) :
    residueField P :=
  evaluate P ⟨f, (mem_valuationRing_iff P f).mpr hf⟩
theorem rationalInfinity_surjective (k : Type*) [Field k] [DecidableEq (RatFunc k)] :
    Function.Surjective (RatFunc.inftyValuation k) := by
  classical
  intro x
  rcases GroupWithZero.eq_zero_or_unit x with (rfl | ⟨x, rfl⟩)
  · exact ⟨0, by simp⟩
  · refine ⟨RatFunc.X ^ WithZero.log x.val, ?_⟩
    rw [RatFunc.inftyValuation.X_zpow]
    exact WithZero.exp_log (Units.ne_zero x)
noncomputable def rationalInfinity (k : Type*) [Field k] [Finite k] : GlobalPlace k (RatFunc k) := by
  letI : DecidableEq (RatFunc k) := Classical.decEq _
  exact
    { valuation := RatFunc.inftyValuation k
      normalized := rationalInfinity_surjective k }
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


