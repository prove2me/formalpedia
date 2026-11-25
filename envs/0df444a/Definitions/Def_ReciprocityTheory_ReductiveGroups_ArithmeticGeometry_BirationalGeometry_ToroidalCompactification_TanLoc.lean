-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:44:09.667015+00:00
-- url     : https://prove2.me/theorems/e920928f-93ef-5f2e-8c8b-5097b3d4ee6d
-- title:
--   Tan Loc
-- statement:
--   Definitions and structural lemmas for Tan Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Theorems.Thm_Bl_FirstBlockLemmaK_goal1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Chart
section TanLoc
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]
def dualMapS {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A') :
    DualNumber A →ₐ[S] DualNumber A' := Bl.ThirdBlockLemmaB.goal1 ι
def scaleS {A : Type} [CommRing A] [Algebra S A] (c : A) : DualNumber A →ₐ[S] DualNumber A :=
  (scaleD c).restrictScalars S
variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
def IsTanAt (h : B →ₐ[S] DualNumber A) : Prop := ∀ b, (h b).fst = e b
section Lin
variable [Module B A] [IsScalarTower S B A] (hsm : ∀ (b : B) (a : A), b • a = e b * a)
include hsm in

def derOf (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) : Derivation S B A where
  toFun b := (h b).snd
  map_add' a b := by simp
  map_smul' r b := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by
    show (h (a * b)).snd = a • (h b).snd + b • (h a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hsm, hsm, hh, hh]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
include hsm in

def ofLin (g : Ω[B⁄S] →ₗ[B] A) : B →ₐ[S] DualNumber A where
  toFun b := TrivSqZeroExt.inl (e b) + TrivSqZeroExt.inr (g (KaehlerDifferential.D S B b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [map_mul, Derivation.leibniz, map_add, map_smul, hsm, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
end Lin
variable {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
end TanLoc
section Main
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] [Algebra.FinitePresentation S B]
  {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
end Main
end ReciprocityTheory.ChartRestriction.G.Chart


