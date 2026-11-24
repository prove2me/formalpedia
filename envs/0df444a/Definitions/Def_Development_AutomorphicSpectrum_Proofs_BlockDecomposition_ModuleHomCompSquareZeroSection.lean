-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:13:54.578609+00:00
-- url     : https://prove2.me/theorems/06465d17-de80-4cdc-a9e2-8429b4745f4f
-- title:
--   Module Hom Comp Square Zero Section
-- statement:
--   Definitions and structural lemmas for Module Hom Comp Square Zero Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.AxForm
section Pair
variable {R S S' B M N : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S'] [CommRing B]
  [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N]
abbrev OverR (R : Type) [CommRing R] {S B M : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (t : S →+* TrivSqZeroExt B M) : Prop :=
  t.comp (algebraMap R S) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B)
theorem tower_pair (t : S →+* TrivSqZeroExt B M) (ht : OverR R t) :
    letI : Module S M := Module.compHom M ((TrivSqZeroExt.fstHom B B M).toRingHom.comp t)
    letI : Module R M := Module.compHom M (algebraMap R B)
    IsScalarTower R S M :=
  letI : Module S M := Module.compHom M ((TrivSqZeroExt.fstHom B B M).toRingHom.comp t)
  letI : Module R M := Module.compHom M (algebraMap R B)
  ⟨fun r a m ↦ by
    change (TrivSqZeroExt.fst (t (r • a))) • m = algebraMap R B r • (TrivSqZeroExt.fst (t a)) • m
    have e : (t (algebraMap R S r)).fst = algebraMap R B r := by
      have := congrArg (fun q ↦ (q r).fst) ht
      simpa using this
    rw [Algebra.smul_def, map_mul, TrivSqZeroExt.fst_mul, e, mul_smul]⟩
def pair (t : S →+* TrivSqZeroExt B M) (ht : OverR R t) : Ω[S⁄R] →+ M :=
  letI : Module S M := Module.compHom M ((TrivSqZeroExt.fstHom B B M).toRingHom.comp t)
  letI : Module R M := Module.compHom M (algebraMap R B)
  haveI : IsScalarTower R S M := tower_pair t ht
  let d : Derivation R S M := Derivation.mk'
    { toFun := fun a ↦ (t a).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r a ↦ by
        have e : t (algebraMap R S r) = TrivSqZeroExt.inl (algebraMap R B r) :=
          congrArg (fun q ↦ q r) ht
        change (t (r • a)).snd = algebraMap R B r • (t a).snd
        rw [Algebra.smul_def, map_mul, e]
        simp }
    fun a b ↦ by
      change (t (a * b)).snd = (t a).fst • (t b).snd + (t b).fst • (t a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  d.liftKaehlerDifferential.toAddMonoidHom
def mkT (ε : S →+* B) (l : Ω[S⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω) : S →+* TrivSqZeroExt B M where
  toFun a := TrivSqZeroExt.inl (ε a) + TrivSqZeroExt.inr (l (D R S a))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, hl, add_comm]
end Pair
section Pts
variable {R : Type} [CommRing R] {X : Scheme.{0}}
end Pts
section Axis
variable {R : Type} [CommRing R] {X X' : Scheme.{0}}
end Axis
section Split
variable {R : Type} [CommRing R]
abbrev TT {C : Type} [CommRing C] (ρ : R →+* C) : Over (Sp R) := Over.mk (spMap ρ)
def pt {C C' : Type} [CommRing C] [CommRing C'] {ρ : R →+* C} {ρ' : R →+* C'} (f : C →+* C')
    (h : f.comp ρ = ρ') : TT ρ' ⟶ TT ρ :=
  Over.homMk (spMap f) (by change spMap f ≫ spMap ρ = spMap ρ'; rw [← h, spMap_comp])
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M]
abbrev r1 (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : R →+* TrivSqZeroExt B M :=
  (TrivSqZeroExt.inlHom B M).comp (algebraMap R B)
abbrev mH {N : Type} [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (u : M →ₗ[B] N) :
    TrivSqZeroExt B M →+* TrivSqZeroExt B N := (TrivSqZeroExt.map u).toRingHom
theorem module_hom_comp_square_zero_section {N : Type} [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (u : M →ₗ[B] N) :
    (mH u).comp (r1 R B M) = r1 R B N := by
  ext r <;> simp
theorem fst_comp_square_zero_section : (TrivSqZeroExt.fstHom B B M).toRingHom.comp (r1 R B M) = algebraMap R B := by
  ext r; simp
abbrev x0 (A : Over (Sp R)) [MonObj A] (B : Type) [CommRing B] [Algebra R B] : TT (algebraMap R B) ⟶ A :=
  toUnit _ ≫ η[A]
end Split
section Core
variable {R : Type} [CommRing R]
end Core
section Final
variable {R : Type} [CommRing R]
end Final
end GlobalTheory.CompanionTheory.AxForm


