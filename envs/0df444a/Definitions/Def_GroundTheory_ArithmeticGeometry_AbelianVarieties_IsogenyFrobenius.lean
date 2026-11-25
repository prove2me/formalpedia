-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:29.805719+00:00
-- url     : https://prove2.me/theorems/19f3047f-f832-44ce-806f-4a7c66e286ed
-- title:
--   Isogeny Frobenius
-- statement:
--   Definitions and structural lemmas for Isogeny Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
section Torsion
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
noncomputable def yPoly (x : F) : F[X] :=
  X ^ 2 + C (E.a₁ * x + E.a₃) * X - C (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)
end Torsion
section TorsionP
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]
end TorsionP
section Pow
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
instance charP_functionField : CharP E.toAffine.FunctionField p :=
  charP_of_injective_algebraMap (algebraMap F E.toAffine.FunctionField).injective p
noncomputable def powField : IntermediateField F E.toAffine.FunctionField :=
  F⟮genX E ^ p, genY E ^ p⟯
variable [PerfectRing F p]
noncomputable def frobImage (K : IntermediateField F E.toAffine.FunctionField) :
    IntermediateField F E.toAffine.FunctionField :=
  (K.toSubfield.map (frobenius E.toAffine.FunctionField p)).toIntermediateField fun c => by
    refine ⟨algebraMap F E.toAffine.FunctionField ((frobeniusEquiv F p).symm c),
      IntermediateField.algebraMap_mem K _, ?_⟩
    rw [frobenius_def, ← map_pow]
    congr 1
    exact frobenius_apply_frobeniusEquiv_symm F p c
end Pow
end GroundTheory.Arith.Abelian


