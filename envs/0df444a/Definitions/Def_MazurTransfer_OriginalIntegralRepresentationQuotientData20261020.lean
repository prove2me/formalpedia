-- Prove2me | Definitions.Def_MazurTransfer_OriginalIntegralRepresentationQuotientData20261020
-- name    : MazurTransfer_OriginalIntegralRepresentationQuotientData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T07:04:23.28728+00:00
-- url     : https://prove2.me/theorems/3f16331f-b653-46da-84b2-0154e21dd3ea
-- title:
--   Original selected representation quotient of every same arithmetic model
-- statement:
--   Retain both complete original predicates: a quotient of the given arithmetic Hopf model with genuine injective bialgebra inclusion, original labels and exact point restriction; and the universal assertion over every original finite-flat cocommutative model carrying compatible labels. Retain all five original group, module and arithmetic action providers. Both original predicate types and whole values, all provider types and four whole provider values, and original coefficient and fixed-representation contexts are independently checked. Named downstream consumer: selected actual pi and conjugate-pi arithmetic character quotients at nineteen and original integral Kummer pushforwards.
-- source:
--   MazurTheorem Order13IntegralRepresentationQuotient by Vas and contributors; preserve every original model, selected intertwining map and point labels, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalActualArithmeticKernelAdditiveActionData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraPointRestrictionData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: extend a selected equivariant surjection from the SAME
arithmetic norm-kernel Hopf model to a finite-flat bialgebra quotient.
The arithmetic label and selected quotient are retained pointwise.
Named downstream consumer: the previously selected pi and conjugate-pi
character quotients at nineteen and their integral Kummer pushforwards.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralRepresentationQuotient
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardNormKernelGaloisAction Order13ActualArithmeticKernelAdditiveAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime]
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralRepresentationQuotient : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralRepresentationQuotient : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
local instance instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Kernel K φ)) := kernelAdditiveAction K φ
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (ρ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (p : Representation.IntertwiningMap (kernelRepresentation K φ) ρ)

/-- The quotient extends the given label of the given source Hopf algebra.
Restriction is a bialgebra point map over every coefficient algebra. -/
def HasQuotientOfModel (G : Type) [CommRing G] [HopfAlgebra (LocalRing q) G]
    (e : WithConv (G →ₐ[LocalRing q] K) ≃ Additive (Kernel K φ)) : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (LocalRing q) H),
    Module.Finite (LocalRing q) H ∧ Module.Flat (LocalRing q) H ∧
      Coalgebra.IsCocomm (LocalRing q) H ∧
    ∃ (j : H →ₐc[LocalRing q] G) (e' : WithConv (H →ₐ[LocalRing q] K) ≃ V),
      Function.Injective j ∧
      (∀ f g, e' (f * g) = e' f + e' g) ∧
      (∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[LocalRing q] K)),
        (∀ x : H, g x = σ (f x)) → e' g = ρ σ (e' f)) ∧
      ∀ f, e' (BialgebraPointRestriction.restrictPoint j f) = p (e f)

/-- Universal over models so this applies to the same witness that retains
all-algebra integral points and their arithmetic compatibility. -/
def EveryArithmeticModelHasQuotient : Prop :=
  ∀ (G : Type) [CommRing G] [HopfAlgebra (LocalRing q) G]
    [Module.Finite (LocalRing q) G] [Module.Flat (LocalRing q) G]
    [Coalgebra.IsCocomm (LocalRing q) G]
    (e : WithConv (G →ₐ[LocalRing q] K) ≃ Additive (Kernel K φ)),
    (∀ f g, e (f * g) = e f + e g) →
    (∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (G →ₐ[LocalRing q] K)),
      (∀ x : G, g x = σ (f x)) → e g = σ • e f) →
    HasQuotientOfModel q K φ ρ p G e



end MazurTransfer.Order13IntegralRepresentationQuotient
#print axioms MazurTransfer.Order13IntegralRepresentationQuotient.HasQuotientOfModel
#print axioms MazurTransfer.Order13IntegralRepresentationQuotient.EveryArithmeticModelHasQuotient
#print axioms MazurTransfer.Order13IntegralRepresentationQuotient.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient
#print axioms MazurTransfer.Order13IntegralRepresentationQuotient.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient
#print axioms MazurTransfer.Order13IntegralRepresentationQuotient.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralRepresentationQuotient
#print axioms MazurTransfer.Order13IntegralRepresentationQuotient.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient
#print axioms MazurTransfer.Order13IntegralRepresentationQuotient.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralRepresentationQuotient


