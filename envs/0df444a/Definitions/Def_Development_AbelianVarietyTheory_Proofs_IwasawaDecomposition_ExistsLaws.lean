-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:59.412547+00:00
-- url     : https://prove2.me/theorems/581d483b-f4cf-400e-a1a5-c82dca4d4004
-- title:
--   Exists Laws
-- statement:
--   Definitions and structural lemmas for Exists Laws, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
section Nest
variable {X W Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]
  (φ : I → (W ⟶ X)) (δ : I → ℤ) (ψ : K → (Y ⟶ W)) (ε : K → ℤ)
abbrev flatφ : K × I → (Y ⟶ X) := fun p => ψ p.1 ≫ φ p.2
abbrev flatε : K × I → ℤ := fun p => ε p.1 * δ p.2
theorem nest_le (j : K → I → L.ι) :
    LB.wchart (LB.LinComb L φ δ) ψ j ≤ LB.wchart L (flatφ φ ψ) (fun p => j p.1 p.2) :=
  fun _ hy => Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
def nest (t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))) :
    LB.Gen (LB.LinComb (LB.LinComb L φ δ) ψ ε) :=
  ⟨fun j => res (nest_le L φ δ ψ j) (t.s fun p => j p.1 p.2)⟩
variable {L φ δ ψ ε}
def adj (φ : I → (W ⟶ X)) (δ : I → ℤ) (z : Z) (JP : (Z ⟶ W) → I → L.ι) (J : (Z ⟶ X) → L.ι) (χ : Z ⟶ W) :
    (Z.presheaf.stalk z)ˣ :=
  trF (L := L) φ δ χ z (JP χ) (fun i => J (χ ≫ φ i))
end Nest
section Group
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
variable (G) in

abbrev lamφ : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down).left
abbrev lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
abbrev lamLB (L : RigLB G) : LB (G2 G).left := LB.LinComb L.L (lamφ G) lamε
end Group
end GlobalTheory.LamBiext


