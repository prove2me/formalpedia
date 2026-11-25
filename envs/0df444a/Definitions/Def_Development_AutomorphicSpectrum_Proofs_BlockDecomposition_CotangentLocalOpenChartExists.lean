-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:08:57.49331+00:00
-- url     : https://prove2.me/theorems/b021a348-f151-4ca5-8260-9cc2461d149a
-- title:
--   Cotangent Local Open Chart Exists
-- statement:
--   Definitions and structural lemmas for Cotangent Local Open Chart Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.CotLoc
section Rel
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}
variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]
def Good (ψ : A →+* TrivSqZeroExt R' M) : Prop :=
  (TrivSqZeroExt.fstHom R' R' M).toRingHom.comp ψ = algebraMap A R' ∧
    ψ.comp (algebraMap C A) =
      (TrivSqZeroExt.inlHom R' M).comp ((algebraMap A R').comp (algebraMap C A))
variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]
def phiOf (d : A →+ M)
    (hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a) :
    A →+* TrivSqZeroExt R' M where
  toFun a := TrivSqZeroExt.inl (algebraMap A R' a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    have h1 : d 1 = 0 := by simpa using hm 1 1
    ext <;> simp [h1]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [hm, add_comm]
end Rel
section Final
@[reducible] def opAct (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] : Module Bᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id B).fromOpposite (fun x y => mul_comm x y))
end Final
end GlobalTheory.CompanionTheory.CotLoc


