-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:09.734408+00:00
-- url     : https://prove2.me/theorems/6e57534e-365a-48a8-959f-1adee2596460
-- title:
--   Cube Val
-- statement:
--   Definitions and structural lemmas for Cube Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
section Alg
variable {A U : Type} [CommGroup A] [CommGroup U]
structure IsCub (θ : A → A → A → U) : Prop where
  face : ∀ x y, θ 1 x y = 1
  s01 : ∀ x y z, θ x y z = θ y x z
  s12 : ∀ x y z, θ x y z = θ x z y
  coc : ∀ x x' x'' y, θ (x * x') x'' y * θ x x' y = θ x (x' * x'') y * θ x' x'' y
def cubN (θ : A → A → A → U) (k : ℕ) (a m x : A) : U := ∏ i ∈ Finset.range k, θ (a * m ^ i) m x
namespace IsCub
variable {θ : A → A → A → U} (h : IsCub θ)
include h
end IsCub
end Alg
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
def cubV {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (x x' y : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t (lift x (lift x' y)).left z J
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


