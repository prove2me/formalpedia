-- Prove2me | Definitions.Def_MazurTransfer_RationalSectionClosedPointData
-- name    : MazurTransfer_RationalSectionClosedPointData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T12:55:04.908914+00:00
-- url     : https://prove2.me/theorems/b3a81311-d42c-4d5d-a563-45cd0c312617
-- title:
--   The original point of a field section and its closedness certificate
-- statement:
--   For a scheme $X$ over a field $K$, each section $p:\operatorname{Spec}K\to X$ of the structure morphism determines its original image point, and that point is closed: $$x_p=p(*),\qquad\{x_p\}\text{ is closed in }X.$$ These exact section and point constructors supply the actual curve closed-point and degree-one section dictionary.
-- source:
--   Original complete RationalSection, pointOfSection and sectionPoint_isClosed declarations and bodies from MazurTheorem RationalSectionsDegreeOnePointsOverRigidField.lean, Apache-2.0, Vas and contributors. Three complete original closed types and two data values are kernel-compared. Publishes only the selected section/point data and closedness certificate; the retained header describes the larger source module. Direct public data imports replace unused residue-field dependencies. Design boundary and named downstream consumer: actual order-thirteen degree-one section points and canonical infinity centers.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete rational-section and residue-field dictionary proofs adapted from
MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: rational sections of any scheme over a field with unique
ring endomorphism correspond to actual closed points of residue degree one.
Named downstream consumer: rational sections of the literal order-13 curve
inject into its arithmetic degree-zero divisor class group.
-/
/- Design boundary: the original field section point and its closedness certificate.
Named downstream consumer: literal order-thirteen section closed points and infinity centers. -/
import Mathlib
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
noncomputable section
universe u
namespace MazurTransfer.RigidFieldRationalSections
open AlgebraicGeometry CategoryTheory NeronModelInfra
variable {R : Type u} [Field R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
abbrev RationalSection := NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) c

def pointOfSection (p : RationalSection c) : X := p.1 (IsLocalRing.closedPoint R)

theorem sectionPoint_isClosed (p : RationalSection c) :
    IsClosed ({pointOfSection c p} : Set X) := by
  let : IsClosedImmersion p.1 := isClosedImmersion_of_comp_eq_id c p.1 p.2
  have h := p.1.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint R} isClosed_singleton
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨IsLocalRing.closedPoint R, Set.mem_singleton _, ?_⟩
    exact (Set.mem_singleton_iff.mp hx).symm
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact Set.mem_singleton _

end MazurTransfer.RigidFieldRationalSections
#print axioms MazurTransfer.RigidFieldRationalSections.sectionPoint_isClosed


