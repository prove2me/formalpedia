-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:19.44716+00:00
-- url     : https://prove2.me/theorems/2a3ae06b-e0c5-45e1-99dd-f221da5209d0
-- title:
--   Spec Hom Comp Coaction
-- statement:
--   Definitions and structural lemmas for Spec Hom Comp Coaction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TensorProduct Algebra.TensorProduct
namespace GlobalTheory.AffineQuotient
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
abbrev specOver (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    Over (Spec (CommRingCat.of R)) :=
  (Spec (.of S)).asOver (Spec (.of R))
section
variable {S T T' : Type} [CommRing S] [CommRing T] [CommRing T'] [Algebra R S] [Algebra R T]
  [Algebra R T']
def specHom (φ : S →ₐ[R] T) : specOver R T ⟶ specOver R S :=
  (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver _
end
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  (i : specOver R Λ ⟶ A) (v : specOver R B ⟶ A) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v))
include hρ
end GlobalTheory.AffineQuotient


