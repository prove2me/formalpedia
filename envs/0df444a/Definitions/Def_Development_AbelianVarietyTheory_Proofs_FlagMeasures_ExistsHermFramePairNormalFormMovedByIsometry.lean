-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:07:58.058288+00:00
-- url     : https://prove2.me/theorems/a4556c3a-2de9-50fe-8e70-488b576eee3d
-- title:
--   Exists Herm Frame Pair Normal Form Moved By Isometry
-- statement:
--   Definitions and structural lemmas for Exists Herm Frame Pair Normal Form Moved By Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_isomGrp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
noncomputable section
namespace GlobalTheory.DegMove
section Gen
variable {G R M : Type*} [Group G] [Ring R] [AddCommGroup M] [Module R M] [DistribMulAction G M]
  [SMulCommClass G R M]
theorem mem_iff (s : G) (A : Submodule R M) (x : M) : s • x ∈ s • A ↔ x ∈ A := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, hb, h⟩
    rwa [← MulAction.injective s h]
  · intro h; exact ⟨x, h, rfl⟩
end Gen
section Lat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
omit [StarRing K] in
theorem memK (s : V ≃ₗ[K] V) (A : Submodule K V) (x : V) : s x ∈ s • A ↔ x ∈ A := mem_iff s A x
def mv (hs : s ∈ isomGrp H) (F : FlagD H r) : FlagD H r where
  e a := s (F.e a)
  T := F.T
  indep := F.indep.map' (s : V →ₗ[K] V) s.ker
  iso a b := by rw [(mem_isomGrp H s).1 hs, F.iso]
  zperp a := by rw [(mem_isomGrp H s).1 hs, F.zperp]
  zz := by rw [(mem_isomGrp H s).1 hs, F.zz]
  hT := F.hT
variable (hs : s ∈ isomGrp H) (F F' : FlagD H r)
theorem mv_e (a : Fin (r + 1)) : (mv hs F).e a = s (F.e a) := rfl
theorem move_z : (mv hs F).z = s F.z := rfl
theorem mv_Xa (a : ℕ) : (mv hs F).Xa a = s • F.Xa a := by
  unfold FlagD.Xa
  rw [Submodule.smul_span, ← Set.image_smul, Set.image_image]
  rfl
theorem mv_X : (mv hs F).X = s • F.X := mv_Xa hs F r
theorem mv_posDef (σ : K →+* ℂ) (h : F.PosDefAt σ) : (mv hs F).PosDefAt σ := by
  intro w
  obtain ⟨w, rfl⟩ := s.surjective w
  simp only [mv_e, mv_X, memK, (mem_isomGrp H s).1 hs]
  exact h w
end Lat
section Form
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
def mvN (hs : s ∈ isomGrp H) (N : NF H r) : NF H r where
  F := mv hs N.F
  F' := mv hs N.F'
  j := N.j
  j_le := N.j_le
  c := N.c
  c_norm := N.c_norm
  T := N.T
  hT := N.hT
  hT' := N.hT'
  same a ha := by rw [mv_e, mv_e, N.same a ha, map_smul]
  w := N.w
  sgn := N.sgn
  pair a b := by rw [mv_e, mv_e, (mem_isomGrp H s).1 hs, N.pair]
  ist b := s (N.ist b)
  ist_e a b hb := by rw [mv_e, (mem_isomGrp H s).1 hs, N.ist_e a b hb]
  ist_e' a b ha hb := by rw [mv_e, (mem_isomGrp H s).1 hs, N.ist_e' a b ha hb]
  normalForm_dual_orthogonal_last b hb := by rw [move_z, (mem_isomGrp H s).1 hs, N.normalForm_dual_orthogonal_last b hb]
  ist_iso a b ha hb := by rw [(mem_isomGrp H s).1 hs, N.ist_iso a b ha hb]
  posdef σ := mv_posDef hs N.F σ (N.posdef σ)
  𝔡 := N.𝔡
  𝔡_ne := N.𝔡_ne
  𝔡_star := N.𝔡_star
variable (hs : s ∈ isomGrp H) (N : NF H r)
end Form
end GlobalTheory.DegMove


