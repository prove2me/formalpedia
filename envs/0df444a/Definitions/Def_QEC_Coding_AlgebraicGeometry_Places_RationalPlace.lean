-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
-- name    : QEC_Coding_AlgebraicGeometry_Places_RationalPlace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:43:13.606419+00:00
-- url     : https://prove2.me/theorems/ac67623d-a364-4284-8052-d7c543a19eac
-- title:
--   Rational Place
-- statement:
--   Definitions and structural lemmas for Rational Place, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
def constantsToValuationRing (P : GlobalPlace k F) :
    k →+* valuationRing P :=
  (algebraMap k F).codRestrict (valuationRing P) fun a =>
    (mem_valuationRing_iff P _).mpr
      (FiniteField.valuation_algebraMap_le_one P.valuation a)
noncomputable def constantsToResidue (P : GlobalPlace k F) : k →+* residueField P :=
  (residue P).comp (constantsToValuationRing P)
@[reducible]
noncomputable def residueAlgebra (P : GlobalPlace k F) : Algebra k (residueField P) :=
  (constantsToResidue P).toAlgebra
def HasFiniteResidueDegree (P : GlobalPlace k F) : Prop := by
  letI : Algebra k (residueField P) := residueAlgebra P
  exact FiniteDimensional k (residueField P)
noncomputable def residueDegreeOfFinite (P : GlobalPlace k F)
    (_hfinite : HasFiniteResidueDegree P) : ℕ := by
  letI : Algebra k (residueField P) := residueAlgebra P
  letI : FiniteDimensional k (residueField P) := _hfinite
  exact Module.finrank k (residueField P)
end GlobalPlace
structure RationalPlace (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F] where
  place : GlobalPlace k F
  constantsEquiv : k ≃+* GlobalPlace.residueField place
  constantsEquiv_apply (a : k) :
    constantsEquiv a = GlobalPlace.constantsToResidue place a
namespace RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
noncomputable def evaluate (Q : RationalPlace k F) :
    GlobalPlace.valuationRing Q.place →+* k :=
  Q.constantsEquiv.symm.toRingHom.comp (GlobalPlace.residue Q.place)
noncomputable def evaluateRegular (Q : RationalPlace k F) (f : F)
    (hf : GlobalPlace.RegularAt Q.place f) : k :=
  Q.evaluate ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
theorem constants_regular (Q : RationalPlace k F) (a : k) :
    GlobalPlace.RegularAt Q.place (algebraMap k F a) :=
  (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
    (FiniteField.valuation_algebraMap_le_one Q.place.valuation a)
theorem hasFiniteResidueDegree (Q : RationalPlace k F) :
    GlobalPlace.HasFiniteResidueDegree Q.place := by
  letI : Algebra k (GlobalPlace.residueField Q.place) :=
    GlobalPlace.residueAlgebra Q.place
  change FiniteDimensional k (GlobalPlace.residueField Q.place)
  apply FiniteDimensional.of_surjective
    (Algebra.linearMap k (GlobalPlace.residueField Q.place))
  intro x
  obtain ⟨a, ha⟩ := Q.constantsEquiv.surjective x
  refine ⟨a, ?_⟩
  change GlobalPlace.constantsToResidue Q.place a = x
  rw [← Q.constantsEquiv_apply a]
  exact ha
end RationalPlace
end QEC.Coding.AlgebraicGeometry


