-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:07.651461+00:00
-- url     : https://prove2.me/theorems/3e97367a-afc3-4ede-8a3d-a9462d2b5885
-- title:
--   Fderiv Eq Zero Of Affine
-- statement:
--   Definitions and structural lemmas for Fderiv Eq Zero Of Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FderivEqZeroOfAffine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
namespace AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
theorem differentiableAt_val {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) 0 := (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds h)
def dirDeriv {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) : Γ(A.left, U) →+ ℂ :=
  AddMonoidHom.mk' (fun f => fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w) fun f f' => by
    simp only [valAt'_add]
    rw [fderiv_fun_add (differentiableAt_val u h f) (differentiableAt_val u h f')]
    rfl
end AdaptedCoord
end GlobalTheory


