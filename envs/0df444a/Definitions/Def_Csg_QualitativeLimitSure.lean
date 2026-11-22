-- Prove2me | Definitions.Def_Csg_QualitativeLimitSure
-- name    : Csg_QualitativeLimitSure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:54:11.332073+00:00
-- url     : https://prove2.me/theorems/d22c1c9a-fc1c-4cd7-8ad4-4dd89a12ae57
-- title:
--   Qualitative Limit Sure
-- statement:
--   Definitions and structural lemmas for Qualitative Limit Sure, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeLimitSure.lean

import Definitions.Def_Csg_QualitativeAlmostSure
import Theorems.Thm_OrderHom_gfp_mono_of_le

set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
theorem LStepFun_mono (x y : Set S) (s : S) :
    Monotone (fun w : Set A1 => C.A (C.B w x s) y s) :=
  fun _w1 _w2 hw => C.A_mono_v2 y (C.B_mono_v1 x hw s) s
noncomputable def LStep (x y : Set S) (s : S) : Set A1 →o Set A1 where
  toFun w := C.A (C.B w x s) y s
  monotone' := C.LStepFun_mono x y s
noncomputable def LW (x y : Set S) (s : S) : Set A1 := (C.LStep x y s).lfp
theorem LStepFun_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) (w : Set A1) :
    C.A (C.B w x s) y1 s ≤ C.A (C.B w x s) y2 s :=
  C.A_mono_y (C.B w x s) hy s
theorem LW_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) :
    C.LW x y1 s ≤ C.LW x y2 s :=
  OrderHom.lfp_mono_of_le (fun w => C.LStepFun_mono_y x hy s w)
theorem LStepFun_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) (s : S) (w : Set A1) :
    C.A (C.B w x1 s) y s ≤ C.A (C.B w x2 s) y s :=
  C.A_mono_v2 y (C.B_mono_x w hx s) s
theorem LW_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) (s : S) :
    C.LW x1 y s ≤ C.LW x2 y s :=
  OrderHom.lfp_mono_of_le (fun w => C.LStepFun_mono_x hx y s w)
noncomputable def Lpre1 (x y : Set S) : Set S := {s | C.B (C.LW x y s) x s = Set.univ}
theorem Lpre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) :
    C.Lpre1 x y1 ≤ C.Lpre1 x y2 := by
  intro s hs
  have hsub : C.B (C.LW x y1 s) x s ≤ C.B (C.LW x y2 s) x s :=
    C.B_mono_v1 x (C.LW_mono_y x hy s) s
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub
theorem Lpre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.Lpre1 x1 y ≤ C.Lpre1 x2 y := by
  intro s hs
  have hstep1 : C.B (C.LW x1 y s) x1 s ≤ C.B (C.LW x2 y s) x1 s :=
    C.B_mono_v1 x1 (C.LW_mono_x hx y s) s
  have hstep2 : C.B (C.LW x2 y s) x1 s ≤ C.B (C.LW x2 y s) x2 s :=
    C.B_mono_x (C.LW x2 y s) hx s
  have hsub := hstep1.trans hstep2
  rw [hs] at hsub
  exact Set.Subset.antisymm (Set.subset_univ _) hsub
noncomputable def LFInnerFun (b y x : Set S) : Set S := C.Lpre1 x y ∪ b
theorem LFInnerFun_mono (b y : Set S) : Monotone (C.LFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl (C.Lpre1_mono_x hx y h)
  · exact Or.inr h
noncomputable def LFInner (b y : Set S) : Set S →o Set S where
  toFun := C.LFInnerFun b y
  monotone' := C.LFInnerFun_mono b y
theorem LFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.LFInnerFun b y1 x ≤ C.LFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl (C.Lpre1_mono_y x hy h)
  · exact Or.inr h
noncomputable def LFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.LFInner b y).lfp
  monotone' := fun _y1 _y2 hy => OrderHom.lfp_mono_of_le (fun x => C.LFInnerFun_mono_y b hy x)
noncomputable def LF (b : Set S) : Set S := (C.LFOuter b).gfp
noncomputable def LGFInnerFun (b y x : Set S) : Set S := (C.Lpre1 x y ∩ bᶜ) ∪ (C.Pre1 y ∩ b)
theorem LGFInnerFun_mono (b y : Set S) : Monotone (C.LGFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Lpre1_mono_x hx y h.1, h.2⟩
  · exact Or.inr h
noncomputable def LGFInner (b y : Set S) : Set S →o Set S where
  toFun := C.LGFInnerFun b y
  monotone' := C.LGFInnerFun_mono b y
theorem LGFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.LGFInnerFun b y1 x ≤ C.LGFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Lpre1_mono_y x hy h.1, h.2⟩
  · exact Or.inr ⟨C.Pre1_mono hy h.1, h.2⟩
noncomputable def LGFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.LGFInner b y).lfp
  monotone' := fun _y1 _y2 hy => OrderHom.lfp_mono_of_le (fun x => C.LGFInnerFun_mono_y b hy x)
noncomputable def LGF (b : Set S) : Set S := (C.LGFOuter b).gfp
noncomputable def LFWStep (v : Set A1) (x y z : Set S) (s : S) : Set A1 →o Set A1 where
  toFun W := C.A (C.B W x s) z s ∩ C.A (C.B v x s) y s
  monotone' := by
    intro W1 W2 hW a1 ha1
    exact ⟨C.A_mono_v2 z (C.B_mono_v1 x hW s) s ha1.1, ha1.2⟩
noncomputable def LFW (v : Set A1) (x y z : Set S) (s : S) : Set A1 := (C.LFWStep v x y z s).lfp
theorem LFWStep_mono_v (x y z : Set S) {v1 v2 : Set A1} (hv : v1 ≤ v2) (s : S) (W : Set A1) :
    C.LFWStep v1 x y z s W ≤ C.LFWStep v2 x y z s W := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_v2 y (C.B_mono_v1 x hv s) s ha1.2⟩
theorem LFW_mono_v (x y z : Set S) {v1 v2 : Set A1} (hv : v1 ≤ v2) (s : S) :
    C.LFW v1 x y z s ≤ C.LFW v2 x y z s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_v x y z hv s W)
theorem LFWStep_mono_x (v : Set A1) (y z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (s : S)
    (W : Set A1) : C.LFWStep v x1 y z s W ≤ C.LFWStep v x2 y z s W := by
  intro a1 ha1
  exact ⟨C.A_mono_v2 z (C.B_mono_x W hx s) s ha1.1, C.A_mono_v2 y (C.B_mono_x v hx s) s ha1.2⟩
theorem LFW_mono_x (v : Set A1) (y z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (s : S) :
    C.LFW v x1 y z s ≤ C.LFW v x2 y z s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_x v y z hx s W)
theorem LFWStep_mono_y (v : Set A1) (x z : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S)
    (W : Set A1) : C.LFWStep v x y1 z s W ≤ C.LFWStep v x y2 z s W := by
  intro a1 ha1
  exact ⟨ha1.1, C.A_mono_y (C.B v x s) hy s ha1.2⟩
theorem LFW_mono_y (v : Set A1) (x z : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (s : S) :
    C.LFW v x y1 z s ≤ C.LFW v x y2 z s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_y v x z hy s W)
theorem LFWStep_mono_z (v : Set A1) (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S)
    (W : Set A1) : C.LFWStep v x y z1 s W ≤ C.LFWStep v x y z2 s W := by
  intro a1 ha1
  exact ⟨C.A_mono_y (C.B W x s) hz s ha1.1, ha1.2⟩
theorem LFW_mono_z (v : Set A1) (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) :
    C.LFW v x y z1 s ≤ C.LFW v x y z2 s :=
  OrderHom.lfp_mono_of_le (fun W => C.LFWStep_mono_z v x y hz s W)
noncomputable def LFVStep (x y z : Set S) (s : S) : Set A1 →o Set A1 where
  toFun V := C.LFW V x y z s
  monotone' := fun _v1 _v2 hv => C.LFW_mono_v x y z hv s
noncomputable def LFV (x y z : Set S) (s : S) : Set A1 := (C.LFVStep x y z s).gfp
theorem LFV_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) (s : S) :
    C.LFV x1 y z s ≤ C.LFV x2 y z s :=
  OrderHom.gfp_mono_of_le (fun V => C.LFW_mono_x V y z hx s)
theorem LFV_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) (s : S) :
    C.LFV x y1 z s ≤ C.LFV x y2 z s :=
  OrderHom.gfp_mono_of_le (fun V => C.LFW_mono_y V x z hy s)
theorem LFV_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (s : S) :
    C.LFV x y z1 s ≤ C.LFV x y z2 s :=
  OrderHom.gfp_mono_of_le (fun V => C.LFW_mono_z V x y hz s)
noncomputable def LFpre1 (x y z : Set S) : Set S := {s | (C.LFV x y z s).Nonempty}
theorem LFpre1_mono_x {x1 x2 : Set S} (hx : x1 ≤ x2) (y z : Set S) :
    C.LFpre1 x1 y z ≤ C.LFpre1 x2 y z := fun s hs => hs.mono (C.LFV_mono_x hx y z s)
theorem LFpre1_mono_y (x : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (z : Set S) :
    C.LFpre1 x y1 z ≤ C.LFpre1 x y2 z := fun s hs => hs.mono (C.LFV_mono_y x hy z s)
theorem LFpre1_mono_z (x y : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.LFpre1 x y z1 ≤ C.LFpre1 x y z2 := fun s hs => hs.mono (C.LFV_mono_z x y hz s)
noncomputable def LFGInnerFun (b z x y : Set S) : Set S :=
  (C.LFpre1 x y z ∩ b) ∪ (bᶜ ∩ C.Lpre1 x z)
theorem LFGInnerFun_mono_y (b z x : Set S) : Monotone (C.LFGInnerFun b z x) := by
  intro y1 y2 hy s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.LFpre1_mono_y x hy z h.1, h.2⟩
  · exact Or.inr h
noncomputable def LFGInner (b z x : Set S) : Set S →o Set S where
  toFun := C.LFGInnerFun b z x
  monotone' := C.LFGInnerFun_mono_y b z x
noncomputable def LFGY (b z x : Set S) : Set S := (C.LFGInner b z x).gfp
theorem LFGInnerFun_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) (y : Set S) :
    C.LFGInnerFun b z x1 y ≤ C.LFGInnerFun b z x2 y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.LFpre1_mono_x hx y z h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Lpre1_mono_x hx z h.2⟩
theorem LFGY_mono_x (b z : Set S) {x1 x2 : Set S} (hx : x1 ≤ x2) :
    C.LFGY b z x1 ≤ C.LFGY b z x2 :=
  OrderHom.gfp_mono_of_le (fun y => C.LFGInnerFun_mono_x b z hx y)
noncomputable def LFGMiddle (b z : Set S) : Set S →o Set S where
  toFun x := C.LFGY b z x
  monotone' := fun _x1 _x2 hx => C.LFGY_mono_x b z hx
noncomputable def LFGX (b z : Set S) : Set S := (C.LFGMiddle b z).lfp
theorem LFGInnerFun_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x y : Set S) :
    C.LFGInnerFun b z1 x y ≤ C.LFGInnerFun b z2 x y := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.LFpre1_mono_z x y hz h.1, h.2⟩
  · exact Or.inr ⟨h.1, C.Lpre1_mono_y x hz h.2⟩
theorem LFGY_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) (x : Set S) :
    C.LFGY b z1 x ≤ C.LFGY b z2 x :=
  OrderHom.gfp_mono_of_le (fun y => C.LFGInnerFun_mono_z b hz x y)
theorem LFGX_mono_z (b : Set S) {z1 z2 : Set S} (hz : z1 ≤ z2) :
    C.LFGX b z1 ≤ C.LFGX b z2 :=
  OrderHom.lfp_mono_of_le (fun x => C.LFGY_mono_z b hz x)
noncomputable def LFGOuter (b : Set S) : Set S →o Set S where
  toFun z := C.LFGX b z
  monotone' := fun _z1 _z2 hz => C.LFGX_mono_z b hz
noncomputable def LFG (b : Set S) : Set S := (C.LFGOuter b).gfp
end CSG
end Csg


