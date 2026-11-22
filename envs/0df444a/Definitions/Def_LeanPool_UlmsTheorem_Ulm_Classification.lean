-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
-- name    : LeanPool_UlmsTheorem_Ulm_Classification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:57:25.810893+00:00
-- url     : https://prove2.me/theorems/22a71760-4f73-4a24-a26b-dbdffdf579a3
-- title:
--   Classification
-- statement:
--   Definitions and structural lemmas for Classification, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Classification.lean

module
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
abbrev BFIsoStep := UlmStage p (G := G) (H := H)
abbrev BFForthPolicy :=
  ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
    ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a
abbrev BFBackPolicy :=
  ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
    ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a
def BFIsoStep.init : BFIsoStep p (G := G) (H := H) where
  A    := ⊥
  B    := ⊥
  hAfinite := by
    rw [show ((⊥ : AddSubgroup G) : Set G) = {0} by ext; simp]
    exact Set.finite_singleton 0
  hBfinite := by
    rw [show ((⊥ : AddSubgroup H) : Set H) = {0} by ext; simp]
    exact Set.finite_singleton 0
  e    := {
    toFun    := fun a ↦ ⟨0, AddSubgroup.zero_mem _⟩
    invFun   := fun b ↦ ⟨0, AddSubgroup.zero_mem _⟩
    left_inv := fun a ↦ Subtype.ext (by simp [AddSubgroup.mem_bot.mp a.prop])
    right_inv:= fun b ↦ Subtype.ext (by simp [AddSubgroup.mem_bot.mp b.prop])
    map_add' := fun a b ↦ by
      simp }
  hφ   := by
    intro a α
    have ha : (a : G) = 0 := AddSubgroup.mem_bot.mp a.prop
    constructor <;> intro h <;> simp [ha]
omit hp in
/-- Combine one forth step and one back step into a single chain step. -/
lemma bf_forth_back
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (s : BFIsoStep p (G := G) (H := H)) (g : G) (h : H) :
    ∃ (s' : BFIsoStep p (G := G) (H := H)) (hle : s.A ≤ s'.A),
      s.B ≤ s'.B ∧ g ∈ s'.A ∧ h ∈ s'.B ∧
      ∀ a : s.A, (s'.e ⟨a.val, hle a.prop⟩ : H) = s.e a := by
  obtain ⟨s₁, h₁, h₂, hg₁, h₃⟩ := hforth s g
  obtain ⟨s₂, h₄, h₅, hh₂, h₆⟩ := hback s₁ h
  exact ⟨s₂, h₁.trans h₄, h₂.trans h₅, h₄ hg₁, hh₂,
         fun a ↦ by simpa [h₃ a] using h₆ ⟨a, h₁ a.2⟩⟩
noncomputable def bf_chain
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) : ℕ → BFIsoStep p (G := G) (H := H)
  | 0     => BFIsoStep.init p
  | n + 1 => (bf_forth_back p hforth hback
                (bf_chain hforth hback enumG enumH n) (enumG n) (enumH n)).choose
omit hp in
/-- Key monotonicity and coverage properties of consecutive chain steps. -/
lemma bf_chain_step_props
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) (n : ℕ) :
    let c := bf_chain p hforth hback enumG enumH
    ∃ (hle : (c n).A ≤ (c (n+1)).A),
      (c n).B ≤ (c (n+1)).B ∧ enumG n ∈ (c (n+1)).A ∧ enumH n ∈ (c (n+1)).B ∧
      ∀ a : (c n).A, ((c (n+1)).e ⟨a.val, hle a.prop⟩ : H) = (c n).e a :=
  (bf_forth_back p hforth hback
    (bf_chain p hforth hback enumG enumH n) (enumG n) (enumH n)).choose_spec
omit hp in
/-- The A-subgroups of the chain are monotone. -/
lemma bf_chain_A_le
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n) :
    (bf_chain p hforth hback enumG enumH m).A ≤
      (bf_chain p hforth hback enumG enumH n).A := by
  induction n with
  | zero => aesop
  | succ n ih =>
    obtain rfl | hmn := hmn.eq_or_lt
    · rfl
    · obtain ⟨hle, _, _, _, _⟩ := bf_chain_step_props p hforth hback enumG enumH n
      exact le_trans (ih (Nat.le_of_lt_succ hmn)) hle
noncomputable def bf_limit_map
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H) (g : G) : H :=
  let n     := (hG_surj g).choose
  let c     := bf_chain p hforth hback enumG enumH
  let props := bf_chain_step_props p hforth hback enumG enumH n
  c (n + 1) |>.e ⟨g, by rw [← (hG_surj g).choose_spec]; exact props.choose_spec.2.1⟩
end UlmsTheorem


