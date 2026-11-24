-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:24.021572+00:00
-- url     : https://prove2.me/theorems/37ea82d2-60b6-4797-9f9a-d90e3052bb0c
-- title:
--   Fibre Curve
-- statement:
--   Definitions and structural lemmas for Fibre Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets.FibreCurve
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
abbrev B1 : Unit → Type := fun _ => Fin 2
abbrev B2 : Fin 2 → Type := fun _ => Fin 2
section Curve
variable {Ω : Type} [Field Ω]
def pt (u : Ω) : (Σ k, B2 k) → Ω :=
  fun p => if p.1 = 0 then ![1, u] p.2 else ![1, u ^ 2] p.2
def eqn : MRing B2 :=
  X ⟨0, 0⟩ ^ 2 * X ⟨1, 1⟩ - X ⟨0, 1⟩ ^ 2 * X ⟨1, 0⟩
instance mCoordIdeal_isPrime (u : Ω) : (mCoordIdeal (pt u)).IsPrime :=
  RingHom.ker_isPrime _
def gen (u : Ω) : GenFibre (ι := B1) (ι' := B2) (blkV (Fin 2) 1) (mCoordIdeal (pt u)) :=
  Inter.genFibreOf _ _
def fb : FibreBlock (blkOf 1) := ⟨0, by rintro ⟨_, h⟩; simp [blkOf] at h⟩
def chart : ∀ k : FibreBlock (blkOf 1), fibreIdx B2 (blkOf 1) k := fun _ => (0 : Fin 2)
def fibrePoly (u : Ω) : MRingOver (gen u).Φ (fibreIdx B2 (blkOf 1)) :=
  C ((gen u).x ⟨(), 1⟩) * X ⟨fb, (0 : Fin 2)⟩ ^ 2 - C ((gen u).x ⟨(), 0⟩) * X ⟨fb, (1 : Fin 2)⟩ ^ 2
end Curve
end GroundTheory.Heights₂.Heights.Targets.FibreCurve


