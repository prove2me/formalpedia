-- Prove2me | Definitions.Def_ShannonColouring_Kempe
-- name    : ShannonColouring_Kempe
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:42:19.193091+00:00
-- url     : https://prove2.me/theorems/d4f8a833-c5e9-4872-98bc-904329715e1b
-- title:
--   Kempe
-- statement:
--   Definitions and structural lemmas for Kempe, from Juan Pablo Traverso Gianini (jtraverso/shannon-edge-colouring; see pinned Apache-2.0 LICENSE and source headers)'s pinned Shannon's theorem on edge colourings of multigraphs and its sharpness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Kempe.lean

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_PathEnds
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ShannonColouring
variable {V ι : Type*}
def ProperOn (ends : ι → V × V) (s : Finset ι) {k : ℕ} (c : ι → Fin k) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∃ v, Incident ends i v ∧ Incident ends j v) → c i ≠ c j
def Misses (ends : ι → V × V) (s : Finset ι) {k : ℕ} (c : ι → Fin k) (x : V) (δ : Fin k) :
    Prop :=
  ∀ i ∈ s, Incident ends i x → c i ≠ δ
variable {ends : ι → V × V} {k : ℕ}
theorem ProperOn.ne_of_incident {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) {x : V} (hix : Incident ends i x)
    (hjx : Incident ends j x) : c i ≠ c j := h i hi j hj hij ⟨x, hix, hjx⟩
def kempeGraph (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (α γ : Fin k) :
    SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ i ∈ s, (c i = α ∨ c i = γ) ∧
    ((ends i).1 = a ∧ (ends i).2 = b ∨ (ends i).1 = b ∧ (ends i).2 = a)
  symm := ⟨by
    rintro a b ⟨hab, i, hi, hc, h⟩
    exact ⟨hab.symm, i, hi, hc, h.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩
open Classical in
/-- The Kempe change: swap `α` and `γ` on the `α`/`γ`-coloured edges with first end in `T`. -/
noncomputable def kempeSwap (ends : ι → V × V) (c : ι → Fin k) (α γ : Fin k) (T : Set V) :
    ι → Fin k :=
  fun i => if (ends i).1 ∈ T ∧ (c i = α ∨ c i = γ) then Equiv.swap α γ (c i) else c i
def KempeClosed (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (α γ : Fin k) (T : Set V) :
    Prop :=
  ∀ i ∈ s, (c i = α ∨ c i = γ) → ((ends i).1 ∈ T ↔ (ends i).2 ∈ T)
theorem KempeClosed.mem_of_incident {s : Finset ι} {c : ι → Fin k} {α γ : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α γ T) {i : ι} (hi : i ∈ s) (hc : c i = α ∨ c i = γ) {x : V}
    (hx : Incident ends i x) : x ∈ T ↔ (ends i).1 ∈ T := by
  rcases hx with rfl | rfl
  · exact Iff.rfl
  · exact (hT i hi hc).symm
theorem kempeSwap_of_not {c : ι → Fin k} {α γ : Fin k} {T : Set V} {i : ι}
    (hc : ¬ (c i = α ∨ c i = γ)) : kempeSwap ends c α γ T i = c i := by
  simp [kempeSwap, hc]
open Classical in
theorem kempeSwap_mem_or {c : ι → Fin k} {α γ : Fin k} {T : Set V} {i : ι}
    (hc : c i = α ∨ c i = γ) :
    kempeSwap ends c α γ T i = (if (ends i).1 ∈ T then Equiv.swap α γ (c i) else c i) := by
  simp [kempeSwap, hc]
theorem swap_mem_or {α γ d : Fin k} (hd : d = α ∨ d = γ) :
    Equiv.swap α γ d = α ∨ Equiv.swap α γ d = γ := by
  rcases hd with rfl | rfl
  · right; exact Equiv.swap_apply_left _ _
  · left; exact Equiv.swap_apply_right _ _
theorem ProperOn.kempeSwap {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {α γ : Fin k}
    {T : Set V} (hT : KempeClosed ends s c α γ T) :
    ProperOn ends s (kempeSwap ends c α γ T) := by
  intro i hi j hj hij ⟨x, hix, hjx⟩
  have hne := h.ne_of_incident hi hj hij hix hjx
  by_cases hci : c i = α ∨ c i = γ <;> by_cases hcj : c j = α ∨ c j = γ
  · rw [kempeSwap_mem_or hci, kempeSwap_mem_or hcj]
    have ei := hT.mem_of_incident hi hci hix
    have ej := hT.mem_of_incident hj hcj hjx
    by_cases hxT : x ∈ T
    · rw [if_pos (ei.mp hxT), if_pos (ej.mp hxT)]
      exact fun heq => hne ((Equiv.swap α γ).injective heq)
    · rw [if_neg (fun h' => hxT (ei.mpr h')), if_neg (fun h' => hxT (ej.mpr h'))]
      exact hne
  · rw [kempeSwap_of_not hcj, kempeSwap_mem_or hci]
    split_ifs
    · intro heq; exact hcj (heq ▸ swap_mem_or hci)
    · exact hne
  · rw [kempeSwap_of_not hci, kempeSwap_mem_or hcj]
    split_ifs
    · intro heq; exact hci (heq ▸ swap_mem_or hcj)
    · exact hne
  · rw [kempeSwap_of_not hci, kempeSwap_of_not hcj]
    exact hne
end ShannonColouring


