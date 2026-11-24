-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:56.331078+00:00
-- url     : https://prove2.me/theorems/b2d3f6f4-1a4a-41a5-9a7c-fd7e45304805
-- title:
--   Mem MCoord Ideal Of Aeval Eq Zero
-- statement:
--   Definitions and structural lemmas for Mem MCoord Ideal Of Aeval Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
section Homog
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Homog
section Cone
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
end Cone
section Trivial
variable {Ω : Type} [Field Ω] {κ : Type}
def trivLat (x : κ → Ω) (N : ℕ) (i : κ) : AddSubgroup (Fin N → Ω) :=
  AddSubgroup.pi Set.univ fun _ => (chartRing ℤ x i).toSubring.toAddSubgroup
theorem mem_trivLat {x : κ → Ω} {N : ℕ} {i : κ} {e : Fin N → Ω} :
    e ∈ trivLat x N i ↔ ∀ q, e q ∈ chartRing ℤ x i := by
  simp [trivLat, AddSubgroup.mem_pi]
theorem trivial_frame_iff (x : κ → Ω) (N : ℕ) (i : κ) (e : Fin N → Ω) :
    (∃ n : ℕ, (1 : Ω) ^ n • e ∈ trivLat x N i) ↔
      ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, (1 : Ω) ^ n * a q ∈ chartRing ℤ x i) ∧
        e = ∑ q, a q • (Pi.basisFun Ω (Fin N)) q := by
  constructor
  · rintro ⟨n, hn⟩
    rw [one_pow, one_smul, mem_trivLat] at hn
    refine ⟨e, fun q => ⟨0, by simpa using hn q⟩, ?_⟩
    exact ((Pi.basisFun Ω (Fin N)).sum_repr e).symm.trans (by simp)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul, mem_trivLat]
    intro q
    obtain ⟨n, hn⟩ := ha q
    simpa [Finset.sum_apply, Pi.single_apply] using hn
def trivialBundle (x : κ → Ω) (N : ℕ) : ChartBundle ℤ x N (Fin N → Ω) where
  lat := trivLat x N
  stable i a ha e he := mem_trivLat.2 fun q => by
    simpa [smul_eq_mul] using mul_mem ha (mem_trivLat.1 he q)
  frame i _ := ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp,
    fun _ => ⟨Pi.basisFun Ω (Fin N), (Pi.basisFun Ω (Fin N)).linearIndependent,
      (Pi.basisFun Ω (Fin N)).span_eq, trivial_frame_iff x N i⟩⟩
  overlap i j hi hj e he := by
    have h := fun q => exists_pow_mul_mem_chartRing (o := ℤ) x i j hi (mem_trivLat.1 he q)
    choose m hm using h
    refine ⟨∑ q, m q, mem_trivLat.2 fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have : (x i / x j) ^ (∑ q, m q) * e q =
        (x i / x j) ^ (∑ q, m q - m q) * ((x i / x j) ^ m q * e q) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact mul_mem (pow_mem (div_mem_chartRing x j i) _) (hm q)
end Trivial
end GroundTheory.Heights₂.Heights.LowerBoundFree


