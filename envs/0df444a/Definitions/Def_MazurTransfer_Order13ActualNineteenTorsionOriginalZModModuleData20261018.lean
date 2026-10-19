-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionOriginalZModModuleData20261018
-- name    : MazurTransfer_Order13ActualNineteenTorsionOriginalZModModuleData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T10:24:43.473593+00:00
-- url     : https://prove2.me/theorems/27b3cfdd-b4e1-4e50-85f8-9f3e1de99260
-- title:
--   The original F19-module structure on actual Picard nineteen-torsion
-- statement:
--   This constructor equips the same actual nineteen-torsion carrier on the designated rational Picard with the original scalar action of the field with nineteen elements. It uses the fact that multiplication by nineteen vanishes on that carrier. It asserts no numerical dimension and no individual norm-kernel rank.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionCardinality.nineteenTorsionZModModule, original constructor and nonproof value preserved.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original scalar action of ZMod 19 on the SAME
actual Picard nineteen-torsion carrier. This constructor makes no
numerical dimension or degree assertion.
Named downstream consumer: original geometric nineteen-torsion finrank
four and actual norm-kernel dimension-sum contracts.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
namespace MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality
open Order13ActualNormKernelProductCardinality
variable (K : Type) [Field K] [CharZero K]

abbrev nineteenTorsionZModModule : Module (ZMod 19) (NineteenTorsion K) :=
  AddCommGroup.zmodModule (fun z => by
    apply Subtype.ext
    exact z.property)
end MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality
#print axioms MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.nineteenTorsionZModModule


