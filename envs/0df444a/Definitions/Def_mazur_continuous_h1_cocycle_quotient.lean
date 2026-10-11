-- Prove2me | Definitions.Def_mazur_continuous_h1_cocycle_quotient
-- name    : mazur_continuous_h1_cocycle_quotient
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-10T19:52:45.728735+00:00
-- url     : https://prove2.me/theorems/4175d367-1392-4d3f-a5ff-32212dcf90d5
-- title:
--   Continuous first cohomology through continuous cocycles
-- statement:
--   Let G be a topological group acting on an abelian topological group M. The continuous cocycles form an additive subgroup of the algebraic one-cocycles. Define continuous first cohomology as this group modulo its coboundaries, represented by the kernel of the algebraic cohomology quotient map. The interface supplies the continuous cocycle group, its class map, and a forgetful homomorphism to algebraic first cohomology. Its intended consumer is the continuous Kummer map for the actual Picard norm isogenies.
-- source:
--   Owned MazurTheorem continuous norm descent interface, Apache-2.0, built on Mathlib cocycles₁, H1π and quotient groups at revision 0df444a360eaa60ab8c11dca51a86af692955474. Design boundary: continuous cocycles modulo coboundaries, with an algebraic H1 comparison; comparison to Mathlib homological continuous cohomology requires a separate theorem.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous H1 is continuous 1-cocycles modulo
1-coboundaries, presented inside Mathlib algebraic group cohomology.
The forgetful map is checked injective; comparison to Mathlib homological
continuous cohomology is a separate boundary. Named downstream consumer:
the actual norm Kummer injection and the local Selmer conditions.
-/
import Mathlib
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

noncomputable section
namespace MazurTransfer.PublicContinuousFirstCohomologyPresentation
variable (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]

abbrev rep : Rep ℤ G := Rep.ofMulDistribMulAction G M

def continuousCocycles : AddSubgroup (groupCohomology.cocycles₁ (rep G M)) where
  carrier := {z | Continuous (fun g : G => (Additive.toMul (z g) : M))}
  zero_mem' := continuous_const
  add_mem' hx hy := hx.mul hy
  neg_mem' hx := hx.inv

def forgetCocycles : continuousCocycles G M →+ groupCohomology.H1 (rep G M) :=
  (groupCohomology.H1π (rep G M)).hom.toAddMonoidHom.comp
    (continuousCocycles G M).subtype

abbrev H1 := continuousCocycles G M ⧸ (forgetCocycles G M).ker

def classMap : continuousCocycles G M →+ H1 G M :=
  QuotientAddGroup.mk' (forgetCocycles G M).ker

def forgetH1 : H1 G M →+ groupCohomology.H1 (rep G M) :=
  QuotientAddGroup.kerLift (forgetCocycles G M)


end MazurTransfer.PublicContinuousFirstCohomologyPresentation

#print axioms MazurTransfer.PublicContinuousFirstCohomologyPresentation.continuousCocycles
#print axioms MazurTransfer.PublicContinuousFirstCohomologyPresentation.forgetH1


