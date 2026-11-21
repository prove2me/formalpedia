-- Prove2me | Definitions.Def_RiemannMasullo_InfinitePlaceRealPowers
-- name    : RiemannMasullo_InfinitePlaceRealPowers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T01:56:09.252388+00:00
-- url     : https://prove2.me/theorems/0326e667-ca6e-4222-b587-fec19980eb01
-- title:
--   Sec2
-- statement:
--   Definitions and structural lemmas for Sec2, from Ryan McCorvie and RiemannMasullo contributors; manuscript by Alessandro Maria Masullo's pinned Masullo formalization: partial supporting library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
namespace RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
section NormSections
def infinitePlaceRealPower (v : InfinitePlace F) (r : ℝ) : ℝ≥0ˣ →* v.Completionˣ :=
  let realScalars := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace F))
  let atPlace := (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v).comp realScalars
  Units.map ((atPlace.comp NNReal.toRealHom).toMonoidHom.comp (NNReal.rpowMonoidHom r))
end NormSections
end RiemannMasullo


