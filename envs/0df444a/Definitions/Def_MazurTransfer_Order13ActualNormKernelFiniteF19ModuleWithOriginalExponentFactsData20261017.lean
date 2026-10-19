-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelFiniteF19ModuleWithOriginalExponentFactsData20261017
-- name    : MazurTransfer_Order13ActualNormKernelFiniteF19ModuleWithOriginalExponentFactsData20261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T22:55:27.640408+00:00
-- url     : https://prove2.me/theorems/e3ffa9c6-1f2b-4eb8-8703-49e273f003ca
-- title:
--   Original finite F19 norm-kernel module and both actual exponent-nineteen facts
-- statement:
--   Let P be the same actual rational Picard group scheme, K a characteristic-zero field, and phi a finite internal group endomorphism. If its field-valued kernel is killed by nineteen, retain the original finite module structure $$M_\varphi=\ker(\varphi:P(K)\to P(K)),\qquad 19M_\varphi=0,\qquad M_\varphi\text{ a finite }\mathbf F_{19}\text{-module}.$$ The two complete original exponent-nineteen facts for the actual norm maps pi and pi-bar are retained, as is the immediate module-finiteness fact. The named downstream consumers are the original cardinality-as-rank-power formula, nineteen-torsion dimension comparisons and norm Selmer modules. No individual kernel rank is asserted.
-- source:
--   Original MazurTheorem Order13ActualNormKernelFiniteModule.kernelZModModule and kernel_module_finite, together with both original Order13ActualPicardNormKernelGaloisAction exponent-nineteen theorems. Four complete original declaration types, the original module constructor value, original group/module providers and relevant dependency providers are compared. Packaged structural facts receive no extra owned theorem credit. Apache-2.0. Design boundary: the original finite F19 kernel module and original actual exponent facts. Named consumer: kernel_card_eq_pow_finrank and actual norm Selmer finite modules.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels are finite groups,
and their exponent nineteen makes them finite modules over F19.
Named downstream consumer: finite splitting fields and Galois module
structure needed for the actual norm Selmer bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelFiniteModule_kernel_finite
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_kernel_killed_nineteen
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_kernel_killed_nineteen
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: field automorphisms act on the actual geometric norm
kernel groups, and the preimage difference is a cocycle valued in that
kernel group. Continuity remains a separate obligation.
Named downstream consumer: continuous norm Kummer classes.
-/
noncomputable section
namespace MazurTransfer.Order13ActualPicardNormKernelGaloisAction
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormKernelF19ExponentProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKernelF19ExponentProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormKernelF19ExponentProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormKernelF19ExponentProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
theorem pi_kernel_exponent_nineteen (z : Kernel K schemePi) : z ^ 19 = 1 := by
  apply Subtype.ext
  change z.val ^ 19 = (1 : Points K)
  exact schemePi_kernel_killed_nineteen _ z.val z.property

theorem piConjugate_kernel_exponent_nineteen (z : Kernel K schemePiConjugate) : z ^ 19 = 1 := by
  apply Subtype.ext
  change z.val ^ 19 = (1 : Points K)
  exact schemePiConjugate_kernel_killed_nineteen _ z.val z.property

end MazurTransfer.Order13ActualPicardNormKernelGaloisAction

namespace MazurTransfer.Order13ActualNormKernelFiniteModule
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardGaloisFixedPointDescent
open scoped CategoryTheory.MonObj
local instance actualNormKernelF19DataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKernelF19DataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable [IsFinite φ.left]
local instance actualNormKernelF19DataProvider320261017 : Finite (Kernel K φ) := MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite K φ
variable [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]

abbrev kernelZModModule : Module (ZMod 19) (Additive (Kernel K φ)) :=
  AddCommGroup.zmodModule (fun z => by
    change z.toMul ^ 19 = 1
    exact (Fact.out : ∀ z : Kernel K φ, z ^ 19 = 1) z.toMul)

local instance actualNormKernelF19DataProvider420261017 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ

theorem kernel_module_finite : Module.Finite (ZMod 19) (Additive (Kernel K φ)) := inferInstance

end MazurTransfer.Order13ActualNormKernelFiniteModule
#print axioms MazurTransfer.Order13ActualNormKernelFiniteModule.kernelZModModule
#print axioms MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_module_finite

#print axioms MazurTransfer.Order13ActualPicardNormKernelGaloisAction.pi_kernel_exponent_nineteen
#print axioms MazurTransfer.Order13ActualPicardNormKernelGaloisAction.piConjugate_kernel_exponent_nineteen


