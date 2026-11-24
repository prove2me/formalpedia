-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:23:53.038038+00:00
-- url     : https://prove2.me/theorems/3ca2e7a9-d3d4-48a9-89a6-7f473eab2c5c
-- title:
--   Torus Proj Period Zero Eq Real
-- statement:
--   Definitions and structural lemmas for Torus Proj Period Zero Eq Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_H_smul_left
import Theorems.Thm_GlobalTheory_AnArc_H_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
namespace PolarisedLattice
end PolarisedLattice
namespace AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
def kappa : (Fin A.gB → ℂ) →ₗ[ℂ] (A.X →+ ℂ) where
  toFun z :=
    { toFun := fun x => A.H z (A.ct x) / (2 * Complex.I)
      map_zero' := by simp
      map_add' := fun x x' => by rw [map_add, H_add_right, add_div] }
  map_add' z z' := AddMonoidHom.ext fun x => by
    show A.H (z + z') _ / _ = _ / _ + _ / _
    rw [H_add_left, add_div]
  map_smul' c z := AddMonoidHom.ext fun x => by
    show A.H (c • z) _ / _ = c * (_ / _)
    rw [H_smul_left, mul_div_assoc]
@[simp] theorem kappa_apply (z : Fin A.gB → ℂ) (x : A.X) : A.kappa z x = A.H z (A.ct x) / (2 * Complex.I) := rfl
def torusProj : A.V →ₗ[ℂ] (A.X →+ ℂ) := LinearMap.fst ℂ _ _ + A.kappa ∘ₗ LinearMap.snd ℂ _ _
def Bw (w : ℂ) : A.X →+ A.X →+ ℝ :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun x => (A.T y x + w * A.be y x + A.kappa (A.ct y) x).im)
    fun x x' => by simp only [map_add, ← Complex.add_im]; push_cast; ring_nf)
    fun y y' => AddMonoidHom.ext fun x => by
      simp only [map_add, AddMonoidHom.add_apply, LinearMap.add_apply, AddMonoidHom.mk'_apply, ← Complex.add_im]
      push_cast; ring_nf
def BwMat (w : ℂ) : Matrix (Module.Free.ChooseBasisIndex ℤ A.X) (Module.Free.ChooseBasisIndex ℤ A.X) ℝ :=
  Matrix.of fun i j => A.Bw w (Module.Free.chooseBasis ℤ A.X i) (Module.Free.chooseBasis ℤ A.X j)
open Classical in

def dualForm (w : ℂ) : (A.X →+ ℂ) →ₗ[ℂ] (A.X →+ ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun r r' => A.coord r ⬝ᵥ ((A.BwMat w)⁻¹.map Complex.ofReal) *ᵥ star (A.coord r'))
    (fun _ _ _ => by rw [map_add, add_dotProduct])
    (fun _ _ _ => by rw [map_smul, smul_dotProduct]; rfl)
    (fun _ _ _ => by rw [map_add, star_add, mulVec_add, dotProduct_add])
    (fun _ _ _ => by rw [map_smul, star_smul, mulVec_smul, dotProduct_smul]; rfl)
def BwC (w : ℂ) (y : A.X) : A.X →+ ℂ := Complex.ofRealHom.toAddMonoidHom.comp (A.Bw w y)
@[simp] theorem BwC_apply (w : ℂ) (y x : A.X) : A.BwC w y x = A.Bw w y x := rfl
def Hw (w : ℂ) : A.V →ₗ[ℂ] A.V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v v' => A.H v.2 v'.2 + A.dualForm w (A.torusProj v) (A.torusProj v'))
    (fun _ _ _ => by simp only [Prod.snd_add, H_add_left, map_add, LinearMap.add_apply]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_snd, H_smul_left, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
    (fun _ _ _ => by simp only [Prod.snd_add, H_add_right, map_add]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_snd, H_smul_right, map_smul, LinearMap.map_smulₛₗ, smul_eq_mul]; ring)
def HwMat (w : ℂ) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => A.Hw w (h.symm (Pi.single i 1)) (h.symm (Pi.single j 1))
end AnArc
end GlobalTheory


