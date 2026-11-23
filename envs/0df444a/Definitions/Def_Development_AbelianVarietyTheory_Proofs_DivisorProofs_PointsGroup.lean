-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:09.445316+00:00
-- url     : https://prove2.me/theorems/49d44b8c-984e-4cf2-99ce-4529c5a97ff2
-- title:
--   Points Group
-- statement:
--   Definitions and structural lemmas for Points Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct WithConv
namespace GlobalTheory.HopfShear
variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]
open Algebra.TensorProduct Bialgebra HopfAlgebra in

@[reducible] noncomputable def pointsGroup : Group (WithConv (A →ₐ[R] X)) where
  __ := (inferInstance : Monoid (WithConv (A →ₐ[R] X)))
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)
  inv_mul_cancel f := by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
    trans toConv <| ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] X)
    rw [LinearMap.antipode_mul_id]
    ext
    simp
attribute [local instance] pointsGroup
noncomputable def pre (f : B →ₐc[R] A) : WithConv (A →ₐ[R] X) →* WithConv (B →ₐ[R] X) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (x.ofConv.comp (f : B →ₐ[R] A))) fun x y => by
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]
noncomputable def post (h : X →ₐ[R] Y) : WithConv (A →ₐ[R] X) →* WithConv (A →ₐ[R] Y) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (h.comp x.ofConv)) fun x y => by
    rw [AlgHom.comp_convMul_distrib, toConv_ofConv]
end GlobalTheory.HopfShear


