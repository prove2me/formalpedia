-- Prove2me | Definitions.Def_MazurTransfer_OriginalBialgebraPointRestrictionData20261020
-- name    : MazurTransfer_OriginalBialgebraPointRestrictionData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:53:00.938946+00:00
-- url     : https://prove2.me/theorems/04f0b3db-e6be-41c9-a12f-367208474a9c
-- title:
--   Original bialgebra arithmetic point restriction
-- statement:
--   Retain the exact point restriction along the original bialgebra inclusion over every original coefficient algebra. Its complete original type and whole value are independently checked. Multiplication, identity preservation and naturality are separate theorem interfaces. Named downstream consumer: actual integral norm-kernel character quotients and their torsor cocycles.
-- source:
--   MazurTheorem BialgebraPointRestriction by Vas and contributors; complete original types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine bialgebra inclusion induces multiplicative
point restriction over EVERY coefficient algebra, naturally under every
coefficient map. Named downstream consumer: actual integral norm-kernel
character quotients and their torsor cocycles.
-/
import Mathlib.RingTheory.Bialgebra.Convolution

noncomputable section
namespace MazurTransfer.BialgebraPointRestriction
universe u
variable {R H G : Type u} [CommRing R] [CommRing H] [CommRing G]
variable [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G)

def restrictPoint {T : Type u} [CommRing T] [Algebra R T]
    (f : WithConv (G →ₐ[R] T)) : WithConv (H →ₐ[R] T) :=
  .toConv (f.ofConv.comp (ι : H →ₐ[R] G))







end MazurTransfer.BialgebraPointRestriction
#print axioms MazurTransfer.BialgebraPointRestriction.restrictPoint


