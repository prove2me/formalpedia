-- Prove2me | Definitions.Def_Csg_QualitativeAlmostSure
-- name    : Csg_QualitativeAlmostSure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:53:45.512296+00:00
-- url     : https://prove2.me/theorems/775c9592-0ba6-4fbe-b7ec-a18899770c09
-- title:
--   Qualitative Almost Sure
-- statement:
--   Definitions and structural lemmas for Qualitative Almost Sure, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeAlmostSure.lean

import Definitions.Def_Csg_QualitativeSure
import Theorems.Thm_OrderHom_gfp_mono_of_le

set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def A (v2 : Set A2) (y : Set S) (s : S) : Set A1 :=
  {a1 | ∀ a2, a2 ∈ v2 ∨ (C.K s a1 a2).support ⊆ y}
theorem A_mono_y (v2 : Set A2) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) :
    C.A v2 y1 s ≤ C.A v2 y2 s := by
  intro a1 ha1 a2
  rcases ha1 a2 with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hy)
noncomputable def B (v1 : Set A1) (x : Set S) (s : S) : Set A2 :=
  {a2 | ∃ a1 ∈ v1, ((C.K s a1 a2).support ∩ x).Nonempty}
theorem B_mono_v1 (x : Set S) {v1 v1' : Set A1} (hv : v1 ≤ v1') (s : S) :
    C.B v1 x s ≤ C.B v1' x s := by
  intro a2 ha2
  obtain ⟨a1, ha1, hne⟩ := ha2
  exact ⟨a1, hv ha1, hne⟩
theorem B_mono_x (v1 : Set A1) {x1 x2 : Set S} (hx : x1 ≤ x2) (s : S) :
    C.B v1 x1 s ≤ C.B v1 x2 s := by
  intro a2 ha2
  obtain ⟨a1, ha1, s', hs'⟩ := ha2
  exact ⟨a1, ha1, s', hs'.1, hx hs'.2⟩
theorem A_mono_v2 (y : Set S) {v2 v2' : Set A2} (hv : v2 ≤ v2') (s : S) :
    C.A v2 y s ≤ C.A v2' y s := by
  intro a1 ha1 a2
  rcases ha1 a2 with h | h
  · exact Or.inl (hv h)
  · exact Or.inr h
noncomputable def Apre1 (x y : Set S) : Set S :=
  {s | C.B (C.A ∅ y s) x s = Set.univ}
theorem Apre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.Apre1 x1 y ≤ C.Apre1 x2 y := by
  intro s hs
  have hsub : C.B (C.A ∅ y s) x1 s ≤ C.B (C.A ∅ y s) x2 s := C.B_mono_x (C.A ∅ y s) hx s
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub
theorem Apre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) :
    C.Apre1 x y1 ≤ C.Apre1 x y2 := by
  intro s hs
  have hsub : C.B (C.A ∅ y1 s) x s ≤ C.B (C.A ∅ y2 s) x s :=
    C.B_mono_v1 x (C.A_mono_y ∅ hy s) s
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub
noncomputable def AFInnerFun (b y x : Set S) : Set S := C.Apre1 x y ∪ b
theorem AFInnerFun_mono (b y : Set S) : Monotone (C.AFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl (C.Apre1_mono_x hx y h)
  · exact Or.inr h
noncomputable def AFInner (b y : Set S) : Set S →o Set S where
  toFun := C.AFInnerFun b y
  monotone' := C.AFInnerFun_mono b y
theorem AFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.AFInnerFun b y1 x ≤ C.AFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl (C.Apre1_mono_y x hy h)
  · exact Or.inr h
noncomputable def AFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.AFInner b y).lfp
  monotone' := fun _y1 _y2 hy => OrderHom.lfp_mono_of_le (fun x => C.AFInnerFun_mono_y b hy x)
noncomputable def AF (b : Set S) : Set S := (C.AFOuter b).gfp
noncomputable def AGFInnerFun (b y x : Set S) : Set S := (C.Apre1 x y ∩ bᶜ) ∪ (C.Pre1 y ∩ b)
theorem AGFInnerFun_mono (b y : Set S) : Monotone (C.AGFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Apre1_mono_x hx y h.1, h.2⟩
  · exact Or.inr h
noncomputable def AGFInner (b y : Set S) : Set S →o Set S where
  toFun := C.AGFInnerFun b y
  monotone' := C.AGFInnerFun_mono b y
theorem AGFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.AGFInnerFun b y1 x ≤ C.AGFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Apre1_mono_y x hy h.1, h.2⟩
  · exact Or.inr ⟨C.Pre1_mono hy h.1, h.2⟩
noncomputable def AGFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.AGFInner b y).lfp
  monotone' := fun _y1 _y2 hy => OrderHom.lfp_mono_of_le (fun x => C.AGFInnerFun_mono_y b hy x)
noncomputable def AGF (b : Set S) : Set S := (C.AGFOuter b).gfp
noncomputable def AFVStep (x y z : Set S) (s : S) : Set A1 →o Set A1 where
  toFun V := C.A ∅ z s ∩ C.A (C.B V x s) y s
  monotone' := by
    intro V1 V2 hV a1 ha1
    exact ⟨ha1.1, C.A_mono_v2 y (C.B_mono_v1 x hV s) s ha1.2⟩
noncomputable def AFV (x y z : Set S) (s : S) : Set A1 := (C.AFVStep x y z s).gfp
theorem AFVStepFun_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) (V : Set A1) :
    C.AFVStep x y z1 s V ≤ C.AFVStep x y z2 s V := by
  intro a1 ha1
  exact ⟨C.A_mono_y ∅ hz s ha1.1, ha1.2⟩
theorem AFV_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) :
    C.AFV x y z1 s ≤ C.AFV x y z2 s :=
  OrderHom.gfp_mono_of_le (fun V => C.AFVStepFun_mono_z x y hz s V)
theorem AFVStepFun_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) (s : S)
    (V : Set A1) : C.AFVStep x y1 z s V ≤ C.AFVStep x y2 z s V := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_y (C.B V x s) hy s ha1.2⟩
theorem AFV_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) (s : S) :
    C.AFV x y1 z s ≤ C.AFV x y2 z s :=
  OrderHom.gfp_mono_of_le (fun V => C.AFVStepFun_mono_y x hy z s V)
theorem AFVStepFun_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) (s : S) (V : Set A1) :
    C.AFVStep x1 y z s V ≤ C.AFVStep x2 y z s V := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_v2 y (C.B_mono_x V hx s) s ha1.2⟩
theorem AFV_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) (s : S) :
    C.AFV x1 y z s ≤ C.AFV x2 y z s :=
  OrderHom.gfp_mono_of_le (fun V => C.AFVStepFun_mono_x hx y z s V)
noncomputable def AFpre1 (x y z : Set S) : Set S := {s | (C.AFV x y z s).Nonempty}
theorem AFpre1_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.AFpre1 x y z1 ≤ C.AFpre1 x y z2 := fun s hs => hs.mono (C.AFV_mono_z x y hz s)
theorem AFpre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) :
    C.AFpre1 x y1 z ≤ C.AFpre1 x y2 z := fun s hs => hs.mono (C.AFV_mono_y x hy z s)
theorem AFpre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) :
    C.AFpre1 x1 y z ≤ C.AFpre1 x2 y z := fun s hs => hs.mono (C.AFV_mono_x hx y z s)
noncomputable def AFGInnerFun (b z x y : Set S) : Set S :=
  (C.AFpre1 x y z ∩ b) ∪ (bᶜ ∩ C.Apre1 x z)
theorem AFGInnerFun_mono_y (b z x : Set S) : Monotone (C.AFGInnerFun b z x) := by
  intro y1 y2 hy s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.AFpre1_mono_y x hy z h.1, h.2⟩
  · exact Or.inr h
noncomputable def AFGInner (b z x : Set S) : Set S →o Set S where
  toFun := C.AFGInnerFun b z x
  monotone' := C.AFGInnerFun_mono_y b z x
noncomputable def AFGY (b z x : Set S) : Set S := (C.AFGInner b z x).gfp
theorem AFGInnerFun_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.AFGInnerFun b z x1 y ≤ C.AFGInnerFun b z x2 y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.AFpre1_mono_x hx y z h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Apre1_mono_x hx z h.2⟩
theorem AFGY_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) :
    C.AFGY b z x1 ≤ C.AFGY b z x2 :=
  OrderHom.gfp_mono_of_le (fun y => C.AFGInnerFun_mono_x b z hx y)
noncomputable def AFGMiddle (b z : Set S) : Set S →o Set S where
  toFun x := C.AFGY b z x
  monotone' := fun _x1 _x2 hx => C.AFGY_mono_x b z hx
noncomputable def AFGX (b z : Set S) : Set S := (C.AFGMiddle b z).lfp
theorem AFGInnerFun_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x y : Set S) :
    C.AFGInnerFun b z1 x y ≤ C.AFGInnerFun b z2 x y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.AFpre1_mono_z x y hz h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Apre1_mono_y x hz h.2⟩
theorem AFGY_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x : Set S) :
    C.AFGY b z1 x ≤ C.AFGY b z2 x :=
  OrderHom.gfp_mono_of_le (fun y => C.AFGInnerFun_mono_z b hz x y)
theorem AFGX_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.AFGX b z1 ≤ C.AFGX b z2 :=
  OrderHom.lfp_mono_of_le (fun x => C.AFGY_mono_z b hz x)
noncomputable def AFGOuter (b : Set S) : Set S →o Set S where
  toFun z := C.AFGX b z
  monotone' := fun _z1 _z2 hz => C.AFGX_mono_z b hz
noncomputable def AFG (b : Set S) : Set S := (C.AFGOuter b).gfp
end CSG
end Csg


