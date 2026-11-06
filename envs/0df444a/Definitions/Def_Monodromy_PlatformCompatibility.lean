-- Prove2me | Definitions.Def_Monodromy_PlatformCompatibility
-- name    : Monodromy_PlatformCompatibility
-- status  : Definition
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:17:47.306133+00:00
-- url     : https://prove2.me/theorems/70a7293d-0490-4271-9052-4b915a359f3e
-- title:
--   Seven upstream library lemmas for Lean 4.33.1
-- statement:
--   The covering-lift endpoint, conditional equality, and function-extension lemmas listed below, with their original proofs and upstream source references.
-- source:
--   IsCoveringMap.coe_monodromy_mk: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Homotopy/Lifting.lean#L392-L394; declaration/proof SHA-256 2b856be2d8be6870646e59a9272202f8019167fc66fa5cf18787b2d17fecdf1d
--   IsCoveringMap.monodromy_eq_apply_one: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Homotopy/Lifting.lean#L396-L399; declaration/proof SHA-256 58d2f7424d83aaecba0c2368d395fa614b1edad780cd4c30f194ff8a8431e8b8
--   ite_eq_left: https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Core.lean#L1179-L1182; declaration/proof SHA-256 a8efc7fb197a3268499ef90e2b6e21661e10299a156ccd1b76c0a75fb5377e55
--   ite_eq_right: https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Core.lean#L1188-L1191; declaration/proof SHA-256 0e5219de5a8a43f02f982ff6a92ccde3407012b0dc06d82f7075a998c7b5acb8
--   dite_eq_left: https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Core.lean#L1204-L1207; declaration/proof SHA-256 266cc1bdd89103978eee188c43ac84154a336fdf4c5cb18173c8fdb2881fa9b8
--   dite_eq_right: https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Core.lean#L1213-L1216; declaration/proof SHA-256 10a9832c704bdbc2ab90dff4454ac488e9f49df29dd305b34ce32b8727eb24ec
--   Function.Injective.extend_update: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Function/Basic.lean#L923-L931; declaration/proof SHA-256 f51b89db093a5ef92f516774bb3965d18510a789a184f29ebc9c9d9ad913acee

/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the Mathlib and Lean LICENSE files.
Authors: Junyan Xu, Johannes Hölzl, Mario Carneiro; Lean core contributors

Compatibility backport from Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Topology/Homotopy/Lifting.lean, lines 392-399.
The IsCoveringMap declarations and their proofs below are verbatim from that source.
The ite_eq_left/right and dite_eq_left/right declarations and proofs are
verbatim from Lean v4.35.0, src/Init/Core.lean, lines 1179-1182, 1188-1191,
1204-1207, and 1213-1216. The Function.Injective.extend_update declaration
and proof are verbatim from the same Mathlib commit,
Mathlib/Logic/Function/Basic.lean, lines 923-931.
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Logic.Function.Basic

noncomputable section

@[expose] public section

open Function Topology unitInterval

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

universe u

theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬ c → α} : (dite c t e) = t hc :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬ c → α} : (dite c t e) = e hnc :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

namespace Function

variable {α β γ : Sort*} {f : α → β}

theorem Injective.extend_update [DecidableEq α] [DecidableEq β] (hf : Injective f) (g : α → γ)
    (e : β → γ) (i : α) (a : γ) :
    extend f (update g i a) e = update (extend f g e) (f i) a := by
  ext j
  by_cases h : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := h
    simp [hf, update_apply, hf.eq_iff]
  · grind [extend_apply']

end Function

namespace IsCoveringMap

variable (cov : IsCoveringMap p)

theorem coe_monodromy_mk {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) :
    (cov.monodromy (.mk γ) e : E) = cov.liftPath γ e (γ.source.trans e.2.symm) 1 :=
  rfl

lemma monodromy_eq_apply_one {x y : X} {γ : Path x y} {e : p ⁻¹' {x}} {Γ : C(I, E)}
    (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) : cov.monodromy (.mk γ) e = Γ 1 := by
  rw [show Γ = cov.liftPath γ e (γ.source.trans e.2.symm) from (eq_liftPath_iff' ..).mpr ⟨hpΓ, Γ_0⟩,
    coe_monodromy_mk]

end IsCoveringMap


