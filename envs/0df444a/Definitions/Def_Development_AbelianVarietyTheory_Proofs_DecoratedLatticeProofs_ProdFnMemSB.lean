-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:24.223271+00:00
-- url     : https://prove2.me/theorems/530fedb6-47fb-408e-90d6-0c97edccb46f
-- title:
--   Prod Fn Mem SB
-- statement:
--   Definitions and structural lemmas for Prod Fn Mem SB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ProdFnMemSB.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LocFlat.CFac
def prodFn {X Y : Type} (f : X → ℂ) (g : Y → ℂ) : X × Y → ℂ := fun p => f p.1 * g p.2
theorem prodFn_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : prodFn f g ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hg.1.comp_continuous continuous_snd), ?_⟩
  refine HasCompactSupport.intro' (IsCompact.prod hf.2 hg.2) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
  intro p hp
  simp only [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [prodFn, image_eq_zero_of_notMem_tsupport h]
  · simp [prodFn, image_eq_zero_of_notMem_tsupport h]
def prodSB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) : SB (X × Y) :=
  ⟨prodFn f.1 g.1, prodFn_mem_SB f.2 g.2⟩
@[simp] theorem prodSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) (p : X × Y) :
    (prodSB f g).1 p = f.1 p.1 * g.1 p.2 := rfl
def comapH {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : SB Y →ₗ[ℂ] SB X where
  toFun F := ⟨fun x => F.1 (e x), F.2.1.comp_continuous e.continuous, F.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem comapH_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (F : SB Y) (x : X) :
    (comapH e F).1 x = F.1 (e x) := rfl
def mulLC {X : Type} [TopologicalSpace X] (φ : X → ℂ) (hφ : IsLocallyConstant φ) : SB X →ₗ[ℂ] SB X where
  toFun F := ⟨fun x => φ x * F.1 x, hφ.mul F.2.1, F.2.2.mul_left⟩
  map_add' F G := by ext x; simp [mul_add]
  map_smul' c F := by ext x; simp; ring
end GlobalTheory.LocFlat.CFac


