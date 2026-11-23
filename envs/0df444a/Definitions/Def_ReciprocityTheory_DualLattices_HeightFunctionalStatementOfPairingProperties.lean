-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
-- name    : ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:52.276072+00:00
-- url     : https://prove2.me/theorems/5b5adfd1-5a1b-4787-9edf-c96e0698cb0a
-- title:
--   Height Functional Statement Of Pairing Properties
-- statement:
--   Definitions and structural lemmas for Height Functional Statement Of Pairing Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HeightFunctionalStatementOfPairingProperties.lean

import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Definitions.Def_ReciprocityTheory_DualLattices_ToSigmaAddFstZeroFst
import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable {B : BX R₀}
lemma nsmul_X {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0)
    (v : B.gg) : N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by
  have hk : N • Dp.ηk = 0 := by
    apply Subtype.ext
    show N • Dp.η = (0 : (Dp.D : Type u))
    rw [nsmul_eq_mul, ← map_natCast Dp.σ.1 N, hN, map_zero, zero_mul]
  have ht : N • (v ⊗ₜ[R₀] Dp.ηk : B.gg ⊗[R₀] Dp.π.ker) = v ⊗ₜ[R₀] (N • Dp.ηk) :=
    (map_nsmul (TensorProduct.mk R₀ B.gg Dp.π.ker v) N Dp.ηk).symm
  rw [← map_nsmul, ht, hk, TensorProduct.tmul_zero, map_zero]
lemma pair_zero (h1 : PairingPropertiesStatement B) {S : LAlg R₀} (N : ℕ) (y : B.G S)
    (w : (S : Type u)ˣ) (hw : B.IsPairing N 0 y w) : w = 1 := by
  have h := h1.2.2.1 S N 0 0 y w w w hw hw (by rwa [add_zero])
  have h' : w * 1 = w * w := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm
lemma c_unique (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (x y : B.G Dp.D) (c c' : (R : Type u)) (z z' : (Dp.D : Type u)ˣ)
    (hz : B.IsPairing N x y z) (hz' : B.IsPairing N x y z')
    (e : (z : (Dp.D : Type u)) = 1 + Dp.σ.1 c * Dp.η)
    (e' : (z' : (Dp.D : Type u)) = 1 + Dp.σ.1 c' * Dp.η) : c = c' := by
  have hzz := h1.2.1 Dp.D N x y z z' hz hz'
  have h : (z : (Dp.D : Type u)) = (z' : (Dp.D : Type u)) := by rw [hzz]
  rw [e, e'] at h
  apply sub_eq_zero.mp
  apply Dp.free
  rw [map_sub, sub_mul]
  linear_combination h
lemma exists_c (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (v : B.gg) :
    ∃ c : (R : Type u), ∃ z : (Dp.D : Type u)ˣ,
      B.IsPairing N (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y) z ∧
        (z : (Dp.D : Type u)) = 1 + Dp.σ.1 c * Dp.η := by
  obtain ⟨z, hz⟩ := h1.1 Dp.D N _ (B.map Dp.σ y) (nsmul_X (B := B) Dp N hN v)
    (by rw [← map_nsmul, hy, map_zero])
  have hp := h1.2.2.2.2.2.2.1 Dp.D R Dp.π N _ _ z hz
  have hX : B.map Dp.π (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = 0 :=
    (B.tg_ker Dp.π Dp.sqZero _).mpr ⟨_, rfl⟩
  rw [hX] at hp
  have h1z := pair_zero h1 N _ _ hp
  have hz1 : Dp.π.1 (z : (Dp.D : Type u)) = 1 := by
    have := congrArg Units.val h1z
    simpa using this
  have hmem : (z : (Dp.D : Type u)) - 1 ∈ RingHom.ker Dp.π.1 := by
    rw [RingHom.mem_ker, map_sub, hz1, map_one, sub_self]
  rw [Dp.ker_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem
  have hd' : d - Dp.σ.1 (Dp.π.1 d) ∈ RingHom.ker Dp.π.1 := by
    rw [RingHom.mem_ker, map_sub, Dp.sect, sub_self]
  rw [Dp.ker_eq, Ideal.mem_span_singleton'] at hd'
  obtain ⟨e, he⟩ := hd'
  exact ⟨Dp.π.1 d, z, hz, by linear_combination -hd - Dp.η * he + e * Dp.η_sq⟩
def cf (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (v : B.gg) : (R : Type u) :=
  Classical.choose (exists_c h1 Dp N hN y hy v)
lemma cf_spec (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (v : B.gg) :
    ∃ z : (Dp.D : Type u)ˣ,
      B.IsPairing N (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y) z ∧
        (z : (Dp.D : Type u)) = 1 + Dp.σ.1 (cf h1 Dp N hN y hy v) * Dp.η :=
  Classical.choose_spec (exists_c h1 Dp N hN y hy v)
lemma cf_add (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (v v' : B.gg) :
    cf h1 Dp N hN y hy (v + v') = cf h1 Dp N hN y hy v + cf h1 Dp N hN y hy v' := by
  obtain ⟨z, hz, ez⟩ := cf_spec h1 Dp N hN y hy v
  obtain ⟨z', hz', ez'⟩ := cf_spec h1 Dp N hN y hy v'
  obtain ⟨w, hw, ew⟩ := cf_spec h1 Dp N hN y hy (v + v')
  rw [TensorProduct.add_tmul, map_add] at hw
  have hwz := h1.2.2.1 Dp.D N _ _ _ z z' w hz hz' hw
  have h : (w : (Dp.D : Type u)) = z * z' := by rw [hwz, Units.val_mul]
  rw [ew, ez, ez'] at h
  apply sub_eq_zero.mp
  apply Dp.free
  rw [map_sub, map_add]
  linear_combination h + (Dp.σ.1 (cf h1 Dp N hN y hy v) * Dp.σ.1 (cf h1 Dp N hN y hy v')) * Dp.η_sq
lemma cf_smul (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (r : R₀) (v : B.gg) :
    cf h1 Dp N hN y hy (r • v) = algebraMap R₀ (R : Type u) r * cf h1 Dp N hN y hy v := by
  have hπη : Dp.π.1 Dp.η = 0 := by
    have := Dp.η_mem
    simpa [LHom.ker, RingHom.mem_ker] using this
  set c := algebraMap R₀ (R : Type u) r with hc
  have hf : ∀ a ∈ Dp.π.ker, (Dp.μL c).1.toLinearMap a ∈ Dp.π.ker := by
    intro a ha
    have ha' : Dp.π.1 a = 0 := by simpa [LHom.ker, RingHom.mem_ker] using ha
    have h0 : Dp.π.1 (Dp.fμ c a) = 0 := by simp [DualPair.fμ, Dp.sect, ha']
    have e : (Dp.μL c).1.toLinearMap a = Dp.fμ c a := rfl
    rw [e]
    simpa [LHom.ker, RingHom.mem_ker] using h0
  have key := B.tg_nat Dp.π Dp.π Dp.sqZero Dp.sqZero (Dp.μL c) hf (v ⊗ₜ Dp.ηk)
  have hv : LinearMap.lTensor B.gg ((Dp.μL c).1.toLinearMap.restrict hf) (v ⊗ₜ[R₀] Dp.ηk) =
      (r • v) ⊗ₜ[R₀] Dp.ηk := by
    rw [LinearMap.lTensor_tmul, TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    show Dp.fμ c Dp.η = r • Dp.η
    rw [Algebra.smul_def, ← Dp.σ.1.commutes r]
    simp [DualPair.fμ, hπη, hc]
  rw [hv] at key
  have hμσ : (Dp.μL c).comp Dp.σ = Dp.σ := Subtype.ext (AlgHom.ext fun a => by
    show Dp.fμ c (Dp.σ.1 a) = Dp.σ.1 a
    simp [DualPair.fμ, Dp.sect])
  obtain ⟨z, hz, ez⟩ := cf_spec h1 Dp N hN y hy v
  obtain ⟨w, hw, ew⟩ := cf_spec h1 Dp N hN y hy (r • v)
  have hp := h1.2.2.2.2.2.2.1 Dp.D Dp.D (Dp.μL c) N _ _ z hz
  rw [← key, ← B.map_comp, hμσ] at hp
  refine c_unique h1 Dp N _ _ _ _ _ _ hw hp ew ?_
  rw [Units.coe_map]
  show Dp.fμ c (z : (Dp.D : Type u)) = _
  rw [ez]
  simp [DualPair.fμ, Dp.sect, hπη] <;> ring
def hgt (h1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) : B.gg →ₗ[R₀] (R : Type u) where
  toFun := cf h1 Dp N hN y hy
  map_add' := cf_add h1 Dp N hN y hy
  map_smul' r v := by rw [cf_smul h1 Dp N hN y hy, RingHom.id_apply, Algebra.smul_def]
end BX
end ReciprocityTheory.PGsh


