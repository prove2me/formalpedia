-- Prove2me | Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData
-- name    : MazurTransfer_ContinuousFirstCohomologyPresentationData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T23:29:23.227682+00:00
-- url     : https://prove2.me/theorems/dd18811e-30e4-4766-87ca-91f815098035
-- title:
--   Continuous first cocycles modulo algebraic coboundaries, with injective forgetful map
-- statement:
--   Let G act by group automorphisms on an abelian topological group M. Retain the original subgroup Z1_cont(G,M) of continuous algebraic 1-cocycles and its map to algebraic H1. The presented continuous first cohomology group is $$H^1_{\mathrm{cont}}(G,M)=Z^1_{\mathrm{cont}}(G,M)/\ker(Z^1_{\mathrm{cont}}(G,M)\to H^1(G,M)).$$ Retain its quotient class map, injective forgetful map, and the original criterion that a class vanishes exactly when its cocycle is an algebraic coboundary. All ten complete original types and six constructor values are compared. The named downstream consumers are actual continuous norm Kummer classes and local Selmer conditions. Comparison with Mathlib homological continuous cohomology remains separate.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologyPresentation constructors and immediate quotient laws, unchanged. Apache-2.0. Complete original types and constructor values compared; structural laws receive no extra owned theorem credit.

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
namespace MazurTransfer.ContinuousFirstCohomologyPresentation
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

theorem forgetCocycles_eq_zero_iff (z : continuousCocycles G M) :
    forgetCocycles G M z = 0 ↔
      (z.val : G → Additive M) ∈ groupCohomology.coboundaries₁ (rep G M) :=
  groupCohomology.H1π_eq_zero_iff z.val

abbrev H1 := continuousCocycles G M ⧸ (forgetCocycles G M).ker

def classMap : continuousCocycles G M →+ H1 G M :=
  QuotientAddGroup.mk' (forgetCocycles G M).ker

def forgetH1 : H1 G M →+ groupCohomology.H1 (rep G M) :=
  QuotientAddGroup.kerLift (forgetCocycles G M)

theorem forgetH1_injective : Function.Injective (forgetH1 G M) :=
  QuotientAddGroup.kerLift_injective (forgetCocycles G M)

@[simp] theorem forgetH1_classMap (z : continuousCocycles G M) :
    forgetH1 G M (classMap G M z) = groupCohomology.H1π (rep G M) z.val := rfl

theorem classMap_eq_zero_iff (z : continuousCocycles G M) :
    classMap G M z = 0 ↔
      (z.val : G → Additive M) ∈ groupCohomology.coboundaries₁ (rep G M) := by
  rw [← (forgetH1_injective G M).eq_iff, map_zero, forgetH1_classMap]
  exact groupCohomology.H1π_eq_zero_iff z.val

end MazurTransfer.ContinuousFirstCohomologyPresentation
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.rep
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.continuousCocycles
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.forgetCocycles
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.forgetCocycles_eq_zero_iff
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.H1
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.classMap
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.forgetH1
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.forgetH1_injective
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.forgetH1_classMap
#print axioms MazurTransfer.ContinuousFirstCohomologyPresentation.classMap_eq_zero_iff


