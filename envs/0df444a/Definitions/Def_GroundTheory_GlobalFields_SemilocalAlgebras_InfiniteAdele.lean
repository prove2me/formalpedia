-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:41.935587+00:00
-- url     : https://prove2.me/theorems/6fa9809c-a9f6-4b48-b366-2b94b0512a9d
-- title:
--   Infinite Adele
-- statement:
--   Definitions and structural lemmas for Infinite Adele, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
namespace InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) :=
  (liesOver_iff_comap_eq _ w).2 rfl
def piPlacesOverEquiv :
    ((v : InfinitePlace K) → PiPlacesOver (L := L) v) ≃ₐ[L] InfiniteAdeleRing L where
  toFun x w := x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩
  invFun y v w := y w
  left_inv x := by
    funext v w
    obtain ⟨w, hw⟩ := w
    have h : w.comap (algebraMap K L) = v := (liesOver_iff_comap_eq v w).1 hw
    subst h
    rfl
  right_inv y := rfl
  map_mul' x y := rfl
  map_add' x y := rfl
  commutes' l := rfl
variable [NumberField K] [NumberField L]
open scoped Classical in

def tensorInfiniteAdeleRingEquiv :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L :=
  (Algebra.TensorProduct.piRight K L L (fun v : InfinitePlace K => v.Completion)).trans <|
    (AlgEquiv.piCongrRight fun v => tensorPiEquivLeft (L := L) v).trans piPlacesOverEquiv
omit [NumberField K] [NumberField L] in

def infiniteAdeleRingMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w : InfinitePlace L =>
    (algebraMap (w.comap (algebraMap K L)).Completion w.Completion).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))
end InfinitePlace
end GroundTheory.Global


