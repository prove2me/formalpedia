-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFixedNormQuotientScopedProvidersData20261019
-- name    : MazurTransfer_Order13ActualDyadicOriginalFixedNormQuotientScopedProvidersData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T11:19:43.799118+00:00
-- url     : https://prove2.me/theorems/35d6fbe4-aacc-4df7-9580-60a69c1e045d
-- title:
--   Original fixed norm quotient group and Galois constructors
-- statement:
--   For the fixed original arithmetic Picard scheme $P$ and its two actual norm endomorphisms, retain the original group, finite-morphism and algebraic-closure Galois structures used by the two fixed quotients
--
--   $$Q_\pi=P(\mathbf{Q})/\pi P(\mathbf{Q}),\qquad Q_{\pi^{\ast}}=P(\mathbf{Q})/\pi^{\ast}P(\mathbf{Q}).$$
--
--   The original nonproof group constructor is preserved. The existing accepted norm theorem supplies the same finiteness evidence. Named downstream consumer: the two original continuous quotient Kummer injections and their dyadic restriction conditions.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: ONLY original topology, action and scoped group/provider constructors; all substantial dyadic Kummer proofs are separate theorem submissions.
Named downstream consumer: vanishing of the two fixed actual continuous norm quotient Kummer classes on every genuine valuation inertia subgroup above two.
Original file header, all provider types and all nonproof constructor bodies are preserved below. Finiteness evidence is supplied by the accepted public norm theorem.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalContinuousKummerTopologyAndScopedActionsData20261019
import Definitions.Def_MazurTransfer_Order13ActualConcreteContinuousNormKummerGroupHomData
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionF19ConcreteData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_isMonHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_isMonHom

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two FIXED actual continuous Kummer injections from
the rational norm quotients have zero restriction to every genuine
valuation inertia subgroup above TWO. All geometric lift existence and
finiteness inputs are proved for the actual maps.
Named downstream consumer: actual norm Selmer conditions at thirteen
and nineteen, followed by the rational rank bound.
-/

noncomputable section
namespace MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormContinuousCohomology
open scoped CategoryTheory.MonObj
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualDyadicNormQuotientKummerCondition : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom
local instance instIsFiniteLeftSchemeSchemePi_order13ActualDyadicNormQuotientKummerCondition : IsFinite schemePi.left := (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1
local instance instIsFiniteLeftSchemeSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition : IsFinite schemePiConjugate.left := (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1
local instance instIsGaloisRatAlgebraicClosure_order13ActualDyadicNormQuotientKummerCondition : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois





end MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition

end
#print axioms MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
#print axioms MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
#print axioms MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualDyadicNormQuotientKummerCondition
#print axioms MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
#print axioms MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePi_order13ActualDyadicNormQuotientKummerCondition
#print axioms MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
#print axioms MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsGaloisRatAlgebraicClosure_order13ActualDyadicNormQuotientKummerCondition


