-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:16.847617+00:00
-- url     : https://prove2.me/theorems/167abe2a-796d-44f3-84e0-b705d72a2d24
-- title:
--   Is Unit Phi Of Mem Monos
-- statement:
--   Definitions and structural lemmas for Is Unit Phi Of Mem Monos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_X_e9b8826858c3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
namespace TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
theorem isUnit_phi_of_mem_monos {I : Finset (Fin (N + 1))} (hI : ∀ i ∈ I, x i ≠ 0)
    {s : Poly (Sy S r) N} (hs : s ∈ monos I) : IsUnit (phi x η S s) := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [phi_X]
    refine isUnit_iff_exists_inv.mpr ⟨single ((-1 : ℤ), (0 : ℤ)) (x i)⁻¹, ?_⟩
    rw [single_mul_single, mul_inv_cancel₀ (hI i (Finset.mem_coe.mp hi)), AddMonoidAlgebra.one_def]
    simp only [Prod.mk_add_mk, add_neg_cancel, add_zero]
    rfl
  | one => rw [map_one]; exact isUnit_one
  | mul a b _ _ ha hb => rw [map_mul]; exact ha.mul hb
theorem isUnit_end {I : Finset (Fin (N + 1))} (hI : ∀ i ∈ I, x i ≠ 0) (s : monos (S := Sy S r) I) :
    IsUnit (algebraMap (Poly (Sy S r) N) (Module.End (Poly (Sy S r) N) (Amb x η)) s) := by
  rw [Module.End.isUnit_iff]
  obtain ⟨u, hu⟩ := isUnit_phi_of_mem_monos x η S hI s.2
  constructor
  · intro a b hab
    simp only [Module.algebraMap_end_apply] at hab
    have h1 : phi x η S s * toA x η a = phi x η S s * toA x η b := by
      rw [← toA_smulP, ← toA_smulP, hab]
    rw [← hu] at h1
    exact (toA x η).injective ((Units.mul_right_inj u).mp h1)
  · intro b
    refine ⟨(toA x η).symm (↑u⁻¹ * toA x η b), ?_⟩
    simp only [Module.algebraMap_end_apply]
    apply (toA x η).injective
    rw [toA_smulP, AddEquiv.apply_symm_apply, ← hu, Units.mul_inv_cancel_left]
def locL (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) :
    LocMod (Sy S r) N (TMod x η S n0 d0 g0) I →ₗ[Poly (Sy S r) N] Amb x η :=
  LocalizedModule.lift _ (TMod x η S n0 d0 g0).subtype (isUnit_end x η S hI)
def idx0 (i : Fin (N + 1)) : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.subset_univ _⟩, Finset.card_singleton i⟩
theorem mem_chartCell_ne_zero {i0 : Fin (N + 1)} (hi0 : x i0 ≠ 0) : ∀ i ∈ (idx0 i0).1.1, x i ≠ 0 := by
  intro i hi
  rw [Finset.mem_singleton.mp hi]
  exact hi0
def evalIdx (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) :
    Cech.cocyDeg (locSys (Sy S r) N (TMod x η S n0 d0 g0)) (degLoc (tgraded x η S n0 d0 g0) 0) locResS 0
      →ₗ[Sy S r] Amb x η where
  toFun z := locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0)
    ((z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) (idx0 i0))
  map_add' a b := by
    rw [Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' c z := by
    rw [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact LinearMap.map_smul_of_tower _ _ _
def readChartH0 (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) :
    cohom (tgraded x η S n0 d0 g0) 0 0 →ₗ[Sy S r] Amb x η :=
  Submodule.liftQ _ (evalIdx x η S n0 d0 g0 i0 hi0) (by
      intro z hz
      have h0 : (z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) = 0 := by
        simpa [Cech.bdryDeg] using hz
      rw [LinearMap.mem_ker]
      change locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0)
        ((z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) (idx0 i0)) = 0
      rw [h0, Pi.zero_apply, map_zero])
end TwistFin
end
end GroundTheory.Heights₂.Heights.Kleiman


