-- Prove2me | Definitions.Def_MazurTransfer_Order13PositiveInfinityReciprocalImage
-- name    : MazurTransfer_Order13PositiveInfinityReciprocalImage
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:44:37.892811+00:00
-- url     : https://prove2.me/theorems/945595c4-54a3-4db0-b953-c0cfecb052ac
-- title:
--   The actual closed image of the positive infinity evaluation
-- statement:
--   Let $R$ be a commutative ring. The actual positive-infinity evaluation defines a closed immersion $\operatorname{Spec}R\to\operatorname{Spec}A^\vee$ into the reciprocal chart. Its image consists exactly of primes containing both $z$ and $w-1$: $$\mathfrak p\in\operatorname{im}(\operatorname{Spec}\varepsilon)\iff z\in\mathfrak p\;\text{and}\;w-1\in\mathfrak p.$$ These are the literal image and point-membership interfaces used to identify the intersection of the two actual finite charts.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Four original declarations from Order13PositiveInfinityReciprocalImage.lean, with every retained body unchanged and the import replaced by the public literal evaluation-kernel interface. The separate substantial complement theorem is omitted; the existing Proved first-chart theorem supplies the complement identity needed downstream. All four original closed types and the original scheme-map value are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual first/inverse chart intersection in unchanged integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual positive infinity closed image in the reciprocal
chart and its exact principal-open complement. Named downstream consumer:
identification of the positive section complement in the glued curve.
No whole-curve gluing or single-section affine identification is asserted.
-/
import Definitions.Def_MazurTransfer_Order13PositiveInfinityEvaluationKernel

noncomputable section
universe u
namespace MazurTransfer.Order13PositiveInfinityReciprocalImage
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13PositiveInfinityEvaluationKernel
open Order13SingleSectionReciprocalPatch
variable (R : Type u) [CommRing R]

def evaluationSchemeMap : Spec (.of R) ⟶ reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (evaluation R))

theorem evaluationSchemeMap_isClosedImmersion : IsClosedImmersion (evaluationSchemeMap R) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (evaluation R)) (evaluation_surjective R)

theorem evaluationSchemeMap_range : Set.range (evaluationSchemeMap R) =
    PrimeSpectrum.zeroLocus (sectionIdeal R : Set (ReciprocalRing R)) := by
  change Set.range (PrimeSpectrum.comap (evaluation R)) = _
  rw [range_comap_of_surjective R (evaluation R) (evaluation_surjective R),evaluation_kernel]

theorem mem_evaluationSchemeMap_range (p : PrimeSpectrum (ReciprocalRing R)) :
    p ∈ Set.range (evaluationSchemeMap R) ↔ zCoordinate R ∈ p.asIdeal ∧ wCoordinate R - 1 ∈ p.asIdeal := by
  change p ∈ Set.range (PrimeSpectrum.comap (evaluation R)) ↔ _
  have h : Set.range (PrimeSpectrum.comap (evaluation R)) =
      PrimeSpectrum.zeroLocus (sectionIdeal R : Set (ReciprocalRing R)) := evaluationSchemeMap_range R
  rw [h,sectionIdeal,PrimeSpectrum.zeroLocus_span,PrimeSpectrum.mem_zeroLocus]
  simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
  rfl



end MazurTransfer.Order13PositiveInfinityReciprocalImage



#print axioms MazurTransfer.Order13PositiveInfinityReciprocalImage.evaluationSchemeMap
#print axioms MazurTransfer.Order13PositiveInfinityReciprocalImage.mem_evaluationSchemeMap_range


