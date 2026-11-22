-- Prove2me | Definitions.Def_Csg_QualitativeSure
-- name    : Csg_QualitativeSure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:48:58.555412+00:00
-- url     : https://prove2.me/theorems/3fb322cb-10c6-445b-bda2-8a926111b2f7
-- title:
--   Qualitative Sure
-- statement:
--   Definitions and structural lemmas for Qualitative Sure, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/QualitativeSure.lean

import Definitions.Def_Csg_BuchiOp
set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def Pre1 (x : Set S) : Set S := {s | ∃ a1, ∀ a2, (C.K s a1 a2).support ⊆ x}
theorem Pre1_mono : Monotone C.Pre1 := by
  intro x1 x2 hx s hs
  obtain ⟨a1, ha1⟩ := hs
  exact ⟨a1, fun a2 => (ha1 a2).trans hx⟩
noncomputable def GOrderHom (safe : Set S) : Set S →o Set S where
  toFun x := C.Pre1 x ∩ safe
  monotone' := by
    intro x1 x2 hx s hs
    exact ⟨C.Pre1_mono hx hs.1, hs.2⟩
noncomputable def G (safe : Set S) : Set S := (C.GOrderHom safe).gfp
noncomputable def SFOrderHom (b : Set S) : Set S →o Set S where
  toFun x := C.Pre1 x ∪ b
  monotone' := by
    intro x1 x2 hx s hs
    rcases hs with h | h
    · exact Or.inl (C.Pre1_mono hx h)
    · exact Or.inr h
noncomputable def SF (b : Set S) : Set S := (C.SFOrderHom b).lfp
noncomputable def SFG (b : Set S) : Set S := C.SF (C.G b)
noncomputable def SGFInnerFun (b y x : Set S) : Set S := (C.Pre1 x ∩ bᶜ) ∪ (C.Pre1 y ∩ b)
theorem SGFInnerFun_mono (b y : Set S) : Monotone (C.SGFInnerFun b y) := by
  intro x1 x2 hx s hs
  rcases hs with h | h
  · exact Or.inl ⟨C.Pre1_mono hx h.1, h.2⟩
  · exact Or.inr h
noncomputable def SGFInner (b y : Set S) : Set S →o Set S where
  toFun := C.SGFInnerFun b y
  monotone' := C.SGFInnerFun_mono b y
theorem SGFInnerFun_mono_y (b : Set S) {y1 y2 : Set S} (hy : y1 ≤ y2) (x : Set S) :
    C.SGFInnerFun b y1 x ≤ C.SGFInnerFun b y2 x := by
  intro s hs
  rcases hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨C.Pre1_mono hy h.1, h.2⟩
noncomputable def SGFOuter (b : Set S) : Set S →o Set S where
  toFun y := (C.SGFInner b y).lfp
  monotone' := fun _y1 _y2 hy => OrderHom.lfp_mono_of_le (fun x => C.SGFInnerFun_mono_y b hy x)
noncomputable def SGF (b : Set S) : Set S := (C.SGFOuter b).gfp
end CSG
end Csg


