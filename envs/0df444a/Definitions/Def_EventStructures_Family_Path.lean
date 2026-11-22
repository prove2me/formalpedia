-- Prove2me | Definitions.Def_EventStructures_Family_Path
-- name    : EventStructures_Family_Path
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:51:15.651655+00:00
-- url     : https://prove2.me/theorems/a9a83062-da36-4737-8348-e0048a29d625
-- title:
--   Path
-- statement:
--   Definitions and structural lemmas for Path, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Nat.Find
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_ConfFamily_TraceEquivFrom_append_left
import Theorems.Thm_ConfFamily_TraceEquivFrom_append_right
import Theorems.Thm_ConfFamily_TraceEquivFrom_symm
import Theorems.Thm_ConfFamily_TraceEquivFrom_trans

set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
local infix:50 " ⊢ " => enables F
structure Edge (c₁ c₂ : Conf F) where
  event : F.Event
  conf₁_enables : (c₁.val) ⊢ event
  conf₂_equals : c₂.val = (c₁.val ∪ {event})
inductive Path : Conf F → Conf F → Type _
  | refl {c : Conf F} : Path c c
  | step {c₁ c₂ c₃ : Conf F} (hEdge : Edge F c₁ c₂) (hPath : Path c₂ c₃) : Path c₁ c₃
namespace Path
def path_id (c : Conf F) : Path F c c :=
  Path.refl
def path_comp {c₁ c₂ c₃ : Conf F} (h₁₂ : Path F c₁ c₂) (h₂₃ : Path F c₂ c₃) :
    Path F c₁ c₃ :=
  match h₁₂ with
  | refl => h₂₃
  | step hEdge hPath => Path.step hEdge (path_comp hPath h₂₃)
def nextConf (c : Conf F) (e : F.Event) (h : c.val ⊢ e) : Conf F :=
  ⟨c.val ∪ {e}, h.2⟩
inductive ExecList : Conf F → List F.Event → Conf F → Type _
  | nil (c : Conf F) : ExecList c [] c
  | cons {c c' : Conf F} {t : List F.Event} (e : F.Event)
      (h : c.val ⊢ e)
      (hnext : ExecList (nextConf F c e h) t c') :
      ExecList c (e :: t) c'
lemma path_comp_id {c₁ c₂ : Conf F} (h : Path F c₁ c₂) :
    path_comp F h (path_id F c₂) = h := by
  induction h with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [path_comp, path_id] at ih ⊢
    rw [ih]
lemma path_id_comp {c₁ c₂ : Conf F} (h : Path F c₁ c₂) :
    path_comp F (path_id F c₁) h = h := rfl
lemma path_comp_assoc {c₁ c₂ c₃ c₄ : Conf F}
    (h₁₂ : Path F c₁ c₂) (h₂₃ : Path F c₂ c₃) (h₃₄ : Path F c₃ c₄) :
    path_comp F (path_comp F h₁₂ h₂₃) h₃₄ = path_comp F h₁₂ (path_comp F h₂₃ h₃₄) := by
  induction h₁₂ with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [path_comp]
    rw [ih]
def trace {c₁ c₂ : Conf F} (hPath : Path F c₁ c₂) : List F.Event :=
  match hPath with
  | refl => []
  | step hEdge hPath' => hEdge.event :: trace hPath'
def length {c₁ c₂ : Conf F} (hPath : Path F c₁ c₂) : Nat :=
  (trace F hPath).length
@[simp] def labels {c₁ c₂ : Conf F} (p : Path F c₁ c₂) : List L :=
  (trace F p).map F.label
@[simp] lemma length_refl {c : Conf F} : length F (Path.refl (c:=c)) = 0 :=
  rfl
@[simp] lemma length_step {c₁ c₂ c₃ : Conf F} (hEdge : Edge F c₁ c₂)
    (hPath : Path F c₂ c₃) :
    length F (Path.step hEdge hPath) = Nat.succ (length F hPath) := by
  simp [length, trace]
def execList_to_path {c₁ c₂ : Conf F} {t : List F.Event} (h : ExecList F c₁ t c₂) :
    Path F c₁ c₂ :=
  match h with
  | ExecList.nil c => Path.refl
  | ExecList.cons e h hnext =>
      Path.step
        { event := e
          conf₁_enables := h
          conf₂_equals := rfl }
        (execList_to_path hnext)
@[simp] lemma execList_trace {c₁ c₂ : Conf F} {t : List F.Event}
    (h : ExecList F c₁ t c₂) : trace F (execList_to_path (F:=F) h) = t := by
  induction h with
  | nil c => rfl
  | cons e h hnext ih =>
      simp [execList_to_path, trace, ih]
@[simp] lemma execList_length {c₁ c₂ : Conf F} {t : List F.Event}
    (h : ExecList F c₁ t c₂) : length F (execList_to_path (F:=F) h) = t.length := by
  simp [length, execList_trace (F:=F) h]
lemma execList_target_eq_union {c₁ c₂ : Conf F} {t : List F.Event}
    (h : ExecList F c₁ t c₂) :
    c₂.1 = c₁.1 ∪ {e | e ∈ t} := by
  induction h with
  | nil c =>
    ext x
    simp
  | cons e h hnext ih =>
    ext x
    simp [nextConf, ih, List.mem_cons, Set.mem_union]
    tauto
noncomputable def execList_lift {c_small c_large c_target : Conf F} {t : List F.Event}
    (hsub : c_small.1 ⊆ c_large.1)
    (hmono : ∀ {c₁ c₂ : Conf F} {e : F.Event}, c₁.1 ⊆ c₂.1 → c₁.1 ⊢ e → c₂.1 ⊢ e)
    (h : ExecList F c_small t c_target) :
    Σ c_target', ExecList F c_large t c_target' := by
  induction h generalizing c_large with
  | nil c =>
    exact ⟨c_large, ExecList.nil _⟩
  | @cons c c' t e h hnext ih =>
    have h' : c_large.1 ⊢ e := hmono hsub h
    let c_large' := nextConf F c_large e h'
    have hsub_next : (nextConf F c e h).1 ⊆ c_large'.1 := by
      intro x hx
      have hx' : x = e ∨ x ∈ c.1 := by
        simpa [nextConf, Set.mem_union, Set.mem_singleton_iff] using hx
      have hx'' : x ∈ c_large.1 ∪ {e} := by
        cases hx' with
        | inl hxe => exact Or.inr hxe
        | inr hxc => exact Or.inl (hsub hxc)
      simpa [c_large', nextConf, Set.mem_union, Set.mem_singleton_iff] using hx''
    obtain ⟨c_target', h_exec'⟩ := ih hsub_next
    exact ⟨c_target', ExecList.cons e h' h_exec'⟩
lemma pathLengthExists {c₁ c₂ : Conf F} (h : Nonempty (Path F c₁ c₂)) :
    ∃ n, ∃ p : Path F c₁ c₂, length F p = n := by
  rcases h with ⟨p⟩
  exact ⟨length F p, p, rfl⟩
noncomputable def minPathLength {c₁ c₂ : Conf F} (h : Nonempty (Path F c₁ c₂)) : Nat := by
  classical
  exact Nat.find (pathLengthExists (F := F) h)
def execList_of_path {c₁ c₂ : Conf F} (p : Path F c₁ c₂) : ExecList F c₁ (trace F p) c₂ :=
  match p with
  | Path.refl => ExecList.nil _
  | Path.step (c₁:=c₁) (c₂:=c₂) (c₃:=c₃) hEdge hPath =>
      have hconf : nextConf F c₁ hEdge.event hEdge.conf₁_enables = c₂ := by
        apply Subtype.ext
        simpa [nextConf] using hEdge.conf₂_equals.symm
      have hnext : ExecList F (nextConf F c₁ hEdge.event hEdge.conf₁_enables)
          (trace F hPath) c₃ := by
        simpa [hconf] using execList_of_path hPath
      ExecList.cons hEdge.event hEdge.conf₁_enables hnext
instance pathSetoid (c₁ c₂ : Conf F) : Setoid (Path F c₁ c₂) where
  r p q := ConfFamily.TraceEquivFrom F c₁.val (trace F p) (trace F q)
  iseqv :=
    ⟨fun p => .refl (trace F p), fun h => h.symm, fun h₁ h₂ => .trans h₁ h₂⟩
lemma path_target_eq_reach {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    c₂.val = reach F c₁.val (trace F p) :=
  execList_target_eq_union F (execList_of_path F p)
def PathEquiv {c₁ c₂ : Conf F} (p₁ p₂ : Path F c₁ c₂) : Prop :=
  (pathSetoid F c₁ c₂).r p₁ p₂
local infixr:60 " ≈ₚ " => PathEquiv F
instance pathEquiv_refl {c₁ c₂ : Conf F} :
    Std.Refl (PathEquiv (F := F) (c₁ := c₁) (c₂ := c₂)) :=
  ⟨(pathSetoid F c₁ c₂).iseqv.refl⟩
instance pathEquiv_symm {c₁ c₂ : Conf F} :
    Std.Symm (PathEquiv (F := F) (c₁ := c₁) (c₂ := c₂)) :=
  ⟨fun _ _ => (pathSetoid F c₁ c₂).iseqv.symm⟩
instance pathEquiv_trans {c₁ c₂ : Conf F} :
    IsTrans (Path F c₁ c₂) (PathEquiv (F := F) (c₁ := c₁) (c₂ := c₂)) :=
  ⟨fun _ _ _ => (pathSetoid F c₁ c₂).iseqv.trans⟩
lemma trace_comp {c₁ c₂ c₃ : Conf F} (p₁₂ : Path F c₁ c₂) (p₂₃ : Path F c₂ c₃) :
    trace F (path_comp F p₁₂ p₂₃) = trace F p₁₂ ++ trace F p₂₃ := by
  induction p₁₂ with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [path_comp, trace, ih]
    rw [List.cons_append]
def Async (c₁ c₂ : Conf F) : Type _ :=
  Quotient (pathSetoid F c₁ c₂)
namespace Async
def mk {c₁ c₂ : Conf F} (p : Path F c₁ c₂) : Async F c₁ c₂ :=
  Quotient.mk (pathSetoid F c₁ c₂) p
def async_path_id (c : Conf F) : Async F c c :=
  mk F (Path.path_id F c)
def async_path_comp {c₁ c₂ c₃ : Conf F}
    (p₁₂ : Async F c₁ c₂) (p₂₃ : Async F c₂ c₃) : Async F c₁ c₃ :=
  Quotient.lift₂
    (fun p₁₂ p₂₃ => mk F (Path.path_comp F p₁₂ p₂₃))
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound <| by
      change ConfFamily.TraceEquivFrom F c₁.val (Path.trace F (Path.path_comp F a₁ b₁))
        (Path.trace F (Path.path_comp F a₂ b₂))
      rw [Path.trace_comp F a₁ b₁, Path.trace_comp F a₂ b₂]
      refine .trans (ConfFamily.TraceEquivFrom.append_left ha _) ?_
      refine ConfFamily.TraceEquivFrom.append_right _ ?_
      rw [← path_target_eq_reach F a₂]
      exact hb)
    p₁₂ p₂₃
lemma async_path_id_comp {c₁ c₂ : Conf F} (p : Async F c₁ c₂) :
    async_path_comp F (async_path_id F c₁) p = p := by
  induction p using Quotient.ind
  rfl
lemma async_path_comp_id {c₁ c₂ : Conf F} (p : Async F c₁ c₂) :
    async_path_comp F p (async_path_id F c₂) = p := by
  induction p using Quotient.ind
  exact congrArg (mk F) (Path.path_comp_id F _)
lemma assoc {c₁ c₂ c₃ c₄ : Conf F}
    (p₁₂ : Async F c₁ c₂) (p₂₃ : Async F c₂ c₃) (p₃₄ : Async F c₃ c₄) :
    async_path_comp F (async_path_comp F p₁₂ p₂₃) p₃₄ =
    async_path_comp F p₁₂ (async_path_comp F p₂₃ p₃₄) := by
  induction p₁₂ using Quotient.ind
  induction p₂₃ using Quotient.ind
  induction p₃₄ using Quotient.ind
  simp only [async_path_comp]
  apply Quotient.sound
  rw [Path.path_comp_assoc]
end Async
end Path
instance pathCategory : CategoryTheory.Category (Conf F) where
  Hom := Path F
  id := Path.path_id F
  comp := Path.path_comp F
  id_comp := Path.path_id_comp F
  comp_id := Path.path_comp_id F
  assoc := Path.path_comp_assoc F
instance asyncPathCategory : CategoryTheory.Category (Conf F) where
  Hom := Path.Async F
  id := Path.Async.async_path_id F
  comp := Path.Async.async_path_comp F
  id_comp := Path.Async.async_path_id_comp F
  comp_id := Path.Async.async_path_comp_id F
  assoc := Path.Async.assoc F


