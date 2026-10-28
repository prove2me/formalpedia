-- Prove2me | Definitions.Def_OAIQ18Pg007
-- name    : OAIQ18Pg007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:57:21.191731+00:00
-- url     : https://prove2.me/theorems/48f7fc82-478d-4139-8921-bf9f66769c32
-- title:
--   Definitions bundle OAIQ18Pg007 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 311 declarations of OpenAI's Lean: 108 definitions, 7 inductive types or structures, 4 instances and 192 theorems. The definitions and types are `OAI.SourceBurnside.DirectCancellation.chunkSum`, `OAI.SourceBurnside.DirectCancellation.pickPacket`, `OAI.SourceBurnside.FiniteTable.BinaryAt`, `OAI.SourceBurnside.FiniteTable.Cell.LockedReads`, `OAI.SourceBurnside.FiniteTable.Cell.eraseColor`, `OAI.SourceBurnside.FiniteTable.Cell.transactionRank`, `OAI.SourceBurnside.FiniteTable.CheckedReach`, `OAI.SourceBurnside.FiniteTable.CheckedSwap`, `OAI.SourceBurnside.FiniteTable.CheckedZero`, `OAI.SourceBurnside.FiniteTable.Coherent`, `OAI.SourceBurnside.FiniteTable.Committed.PivotAt`, `OAI.SourceBurnside.FiniteTable.Committed.value`, `OAI.SourceBurnside.FiniteTable.Component.left`, `OAI.SourceBurnside.FiniteTable.Component.members`, `OAI.SourceBurnside.FiniteTable.Component.offset`, `OAI.SourceBurnside.FiniteTable.Component.region`, `OAI.SourceBurnside.FiniteTable.Component.right`, `OAI.SourceBurnside.FiniteTable.Component.size`, `OAI.SourceBurnside.FiniteTable.Exterior`, `OAI.SourceBurnside.FiniteTable.Own`, `OAI.SourceBurnside.FiniteTable.Region.SideOK`, `OAI.SourceBurnside.FiniteTable.Region.clause`, `OAI.SourceBurnside.FiniteTable.Region.controlPhase`, `OAI.SourceBurnside.FiniteTable.Region.controlPosition`, `OAI.SourceBurnside.FiniteTable.Region.dataWord`, `OAI.SourceBurnside.FiniteTable.Region.phase`, `OAI.SourceBurnside.FiniteTable.Region.position`, `OAI.SourceBurnside.FiniteTable.Region.realize`, `OAI.SourceBurnside.FiniteTable.Region.realizeCell`, `OAI.SourceBurnside.FiniteTable.Rigid.cell`, `OAI.SourceBurnside.FiniteTable.Rigid.core`, `OAI.SourceBurnside.FiniteTable.Rigid.palCell`, `OAI.SourceBurnside.FiniteTable.SameRegion`, `OAI.SourceBurnside.FiniteTable.Syntax`, `OAI.SourceBurnside.FiniteTable.Verification.AllGood`, `OAI.SourceBurnside.FiniteTable.Verification.Good`, `OAI.SourceBurnside.FiniteTable.Verification.WordGood`, `OAI.SourceBurnside.FiniteTable.Verification.holds`, `OAI.SourceBurnside.FiniteTable.Verification.leftSum`, `OAI.SourceBurnside.FiniteTable.Verification.passed` and 75 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Algebra_MatrixTests`, `PeriodicGroups_Algebra_PacketIntervals`, `PeriodicGroups_Algebra_WordAlgebra`, `PeriodicGroups_Frames_ElementaryFrames`, `PeriodicGroups_Frames_ExteriorComplex`, `PeriodicGroups_Homology_FiniteNormalHomology`, `PeriodicGroups_Homology_LocallyFiniteActions`, `PeriodicGroups_Homology_RelativeHomology`, `PeriodicGroups_Machines_TapePrograms`, `PeriodicGroups_Presentation_FinitePresentation`, `PeriodicGroups_Presentation_MatrixStabilizers`, `PeriodicGroups_Presentation_SmallFaithful`, `PeriodicGroups_Presentation_SmallSwapActions`, `PeriodicGroups_Rules_CommittedWords`, `PeriodicGroups_Rules_ConnectedWords`, `PeriodicGroups_Rules_DataWords`, `PeriodicGroups_Rules_GeometricRelations`, `PeriodicGroups_Rules_HeadTour`, `PeriodicGroups_Rules_LocalSyntax`, `PeriodicGroups_Rules_Palette`, `PeriodicGroups_Rules_TableEncoding`, `PeriodicGroups_Rules_TemplateHierarchy`, `PeriodicGroups_Rules_Transactions`, `PeriodicGroups_Rules_WordComponents`, `PeriodicGroups_Rules_WordRewriting`, `PeriodicGroups_Steinberg_BandFactorization`, `PeriodicGroups_Steinberg_BlockEmbeddings`, `PeriodicGroups_Steinberg_DiagonalActions`, `PeriodicGroups_Steinberg_KernelRelations`, `PeriodicGroups_Steinberg_PresentationModel`, `PeriodicGroups_Steinberg_RankActions`.
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundles `OAIQ18Pg000`, `OAIQ18Pg001` and `OAIQ18Pg002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ18Pg009` and `OAIQ18Pg010`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg000
import Definitions.Def_OAIQ18Pg001
import Definitions.Def_OAIQ18Pg002

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_LocalSyntax
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.instFintypeMarker _root_.OAI.SourceBurnside.FiniteTable.instFintypeMetadata _root_.OAI.SourceBurnside.FiniteTable.instFintypePosition _root_.OAI.SourceBurnside.FiniteTable.instFintypeSkeleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.LocalSyntax

namespace Skeleton
variable {q k : ℕ}

lemma structural_mark_left (a b : Skeleton q k) (m : Marker) :
    Structural (a.mark m) b ↔ Structural a b := Iff.rfl
lemma structural_mark_right (a b : Skeleton q k) (m : Marker) :
    Structural a (b.mark m) ↔ Structural a b := Iff.rfl
lemma internal_mark_left (a b : Skeleton q k) (m : Marker) :
    Internal (a.mark m) b ↔ Internal a b := Iff.rfl
lemma internal_mark_right (a b : Skeleton q k) (m : Marker) :
    Internal a (b.mark m) ↔ Internal a b := Iff.rfl

lemma left_wing_head (a b : Skeleton q k) (m : Marker)
    (hm : m = .left ∨ m = .boundary ∨ m = .full) :
    Pair a (b.mark m) ↔ Pair a (b.mark .left) := by
  rcases hm with rfl | rfl | rfl <;>
    cases h : a.marker <;>
    simp [Pair, structural_mark_right, internal_mark_right, leftExternal,
      rightExternal, acceptsLeft, acceptsRight, h]

lemma right_wing_head (a b : Skeleton q k) :
    Pair (a.mark .full) b ↔ Pair (a.mark .right) b := by
  cases h : b.marker <;>
    simp [Pair, structural_mark_left, internal_mark_left, leftExternal,
      rightExternal, acceptsLeft, acceptsRight, h]

lemma cursor_right (a b : Skeleton q k) :
    Pair (a.mark .boundary) b ↔ Pair (a.mark .idle) b := by
  simp [Pair, structural_mark_left, internal_mark_left, leftExternal,
    rightExternal, acceptsLeft, acceptsRight]

lemma create_left (a b : Skeleton q k) (hb : b.first) :
    Pair a (b.mark .boundary) ↔ Pair a (b.mark .idle) := by
  simp [Pair, structural_mark_right, internal_mark_right, leftExternal,
    rightExternal, acceptsLeft, acceptsRight, hb]

lemma finish_right (a b : Skeleton q k) (ha : a.last) :
    Pair (a.mark .boundary) b ↔ Pair (a.mark .full) b := by
  simp [Pair, structural_mark_left, internal_mark_left, leftExternal,
    rightExternal, acceptsLeft, acceptsRight, ha]

lemma full_move_pair (a b : Skeleton q k) :
    Pair (a.mark .full) (b.mark .right) ↔
      Pair (a.mark .left) (b.mark .full) := by
  simp only [Pair, structural_mark_left, structural_mark_right, rightExternal,
    leftExternal, mark_marker, mark_last, mark_first, acceptsRight, acceptsLeft,
    internal_mark_left, internal_mark_right]
  simp
  unfold Internal
  tauto

def Link : Option (Skeleton q k) → Option (Skeleton q k) → Prop
  | none, none => True
  | none, some b => b.leftExternal
  | some a, none => a.rightExternal
  | some a, some b => Pair a b

def Closed (w : List (Skeleton q k)) : Prop :=
  (∀ c ∈ w, c.Admissible) ∧
    List.IsChain Link (none :: (w.map some ++ [none]))

lemma link_left_wing_head (a : Option (Skeleton q k)) (b : Skeleton q k) (m : Marker)
    (hm : m = .left ∨ m = .boundary ∨ m = .full) :
    Link a (some (b.mark m)) ↔ Link a (some (b.mark .left)) := by
  cases a with
  | none => rcases hm with rfl | rfl | rfl <;> simp [Link, leftExternal]
  | some a => exact left_wing_head a b m hm

lemma link_right_wing_head (a : Skeleton q k) (b : Option (Skeleton q k)) :
    Link (some (a.mark .full)) b ↔ Link (some (a.mark .right)) b := by
  cases b with
  | none => simp [Link, rightExternal]
  | some b => exact right_wing_head a b

lemma link_cursor_right (a : Skeleton q k) (b : Option (Skeleton q k)) :
    Link (some (a.mark .boundary)) b ↔ Link (some (a.mark .idle)) b := by
  cases b with
  | none => simp [Link, rightExternal]
  | some b => exact cursor_right a b

lemma link_create_left (a : Option (Skeleton q k)) (b : Skeleton q k) (hb : b.first) :
    Link a (some (b.mark .boundary)) ↔ Link a (some (b.mark .idle)) := by
  cases a with
  | none => simp [Link, leftExternal, hb]
  | some a => exact create_left a b hb

lemma link_finish_right (a : Skeleton q k) (b : Option (Skeleton q k)) (ha : a.last) :
    Link (some (a.mark .boundary)) b ↔ Link (some (a.mark .full)) b := by
  cases b with
  | none => simp [Link, rightExternal, ha]
  | some b => exact finish_right a b ha

end Skeleton

namespace Skeleton
variable {q k : ℕ}

lemma closed_replace_one (p s : List (Skeleton q k)) (a b : Skeleton q k)
    (ha : a.Admissible ↔ b.Admissible)
    (hl : ∀ c, Link c (some a) ↔ Link c (some b))
    (hr : ∀ c, Link (some a) c ↔ Link (some b) c) :
    Closed (p ++ a :: s) ↔ Closed (p ++ b :: s) := by
  have hn : (∀ c ∈ p ++ a :: s, c.Admissible) ↔
      (∀ c ∈ p ++ b :: s, c.Admissible) := by
    simp only [List.forall_mem_append, List.forall_mem_cons, ha]
  have hc := chain_replace_one (none :: p.map some) (s.map some ++ [none])
    (some a) (some b) hl hr
  exact and_congr hn (by simpa only [List.map_append, List.map_cons,
    List.append_assoc, List.cons_append] using hc)

lemma closed_replace_two (p s : List (Skeleton q k)) (a b a' b' : Skeleton q k)
    (ha : a.Admissible) (hb : b.Admissible)
    (ha' : a'.Admissible) (hb' : b'.Admissible)
    (hl : ∀ c, Link c (some a) ↔ Link c (some a'))
    (hr : ∀ c, Link (some b) c ↔ Link (some b') c)
    (hm : Pair a b ↔ Pair a' b') :
    Closed (p ++ a :: b :: s) ↔ Closed (p ++ a' :: b' :: s) := by
  have hn : (∀ c ∈ p ++ a :: b :: s, c.Admissible) ↔
      (∀ c ∈ p ++ a' :: b' :: s, c.Admissible) := by
    simp only [List.forall_mem_append, List.forall_mem_cons, ha, hb, ha', hb']
  have hc := chain_replace_two (none :: p.map some) (s.map some ++ [none])
    (some a) (some b) (some a') (some b') hl hr hm
  exact and_congr hn (by simpa only [List.map_append, List.map_cons,
    List.append_assoc, List.cons_append] using hc)

lemma admissible_idle (a : Skeleton q k) : (a.mark .idle).Admissible := by
  simp [Admissible]
lemma admissible_boundary (a : Skeleton q k) : (a.mark .boundary).Admissible := by
  simp [Admissible]
lemma admissible_full (a : Skeleton q k) : (a.mark .full).Admissible := by
  simp [Admissible]
lemma admissible_left (a : Skeleton q k) (h : ¬ a.last) : (a.mark .left).Admissible := by
  simp [Admissible, h]
lemma admissible_right (a : Skeleton q k) (h : ¬ a.first) : (a.mark .right).Admissible := by
  simp [Admissible, h]

lemma acquire_conditions {a b : Skeleton q k}
    (h : Pair (a.mark .left) (b.mark .boundary)) :
    Structural a b ∧ ¬ a.last := by
  rcases h with ⟨hs, he | hi⟩
  · simp [rightExternal] at he
  · exact ⟨hs, hi.2.2.2.2.2.2.2.2⟩

lemma full_conditions {a b : Skeleton q k}
    (h : Pair (a.mark .full) (b.mark .right)) : ¬ a.last ∧ ¬ b.first := by
  rcases h with ⟨_, he | hi⟩
  · simp [leftExternal] at he
  · exact ⟨hi.2.2.2.2.2.2.2.2, hi.2.2.2.2.2.2.2.1⟩

inductive Replacement : List (Skeleton q k) → List (Skeleton q k) → Prop
  | create (c : Skeleton q k) (hc : c.first) :
      Replacement [c.mark .idle] [c.mark .boundary]
  | acquire (a b : Skeleton q k) (h : Pair (a.mark .left) (b.mark .boundary)) :
      Replacement [a.mark .boundary, b.mark .idle] [a.mark .left, b.mark .boundary]
  | finish (c : Skeleton q k) (hc : c.last) :
      Replacement [c.mark .boundary] [c.mark .full]
  | sweep (a b : Skeleton q k) (h : Pair (a.mark .full) (b.mark .right)) :
      Replacement [a.mark .full, b.mark .right] [a.mark .left, b.mark .full]

theorem replacement_context {v w : List (Skeleton q k)} (h : Replacement v w)
    (p s : List (Skeleton q k)) : Closed (p ++ v ++ s) ↔ Closed (p ++ w ++ s) := by
  cases h with
  | create c hc =>
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_one
    · exact iff_of_true (admissible_idle c) (admissible_boundary c)
    · intro a; exact (link_create_left a c hc).symm
    · intro b; exact (link_cursor_right c b).symm
  | acquire a b h =>
    obtain ⟨hst, hlast⟩ := acquire_conditions h
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_two _ _ _ _ _ _ (admissible_boundary a) (admissible_idle b)
      (admissible_left a hlast) (admissible_boundary b)
    · intro c; exact link_left_wing_head c a _ (Or.inr (Or.inl rfl))
    · intro c; exact (link_cursor_right b c).symm
    · apply iff_of_true _ h
      simp [Pair, structural_mark_left, structural_mark_right, rightExternal,
        leftExternal, hst]
  | finish c hc =>
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_one
    · exact iff_of_true (admissible_boundary c) (admissible_full c)
    · intro a
      exact (link_left_wing_head a c _ (Or.inr (Or.inl rfl))).trans
        (link_left_wing_head a c _ (Or.inr (Or.inr rfl))).symm
    · intro b; exact link_finish_right c b hc
  | sweep a b h =>
    obtain ⟨ha, hb⟩ := full_conditions h
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply closed_replace_two _ _ _ _ _ _ (admissible_full a) (admissible_right b hb)
      (admissible_left a ha) (admissible_full b)
    · intro c; exact link_left_wing_head c a _ (Or.inr (Or.inr rfl))
    · intro c; exact (link_right_wing_head b c).symm
    · exact full_move_pair a b

def InternalPair (a b : Skeleton q k) : Prop := Pair a b ∧ ¬ a.rightExternal

instance instDecidableIsHead (c : Skeleton q k) : Decidable c.IsHead :=
  inferInstanceAs (Decidable (c.marker = .boundary ∨ c.marker = .full))

lemma internal_marker_rule {a b : Skeleton q k} (h : InternalPair a b) :
    (a.marker = .left ∧ (b.marker = .left ∨ b.marker = .boundary ∨ b.marker = .full)) ∨
    ((a.marker = .full ∨ a.marker = .right) ∧ b.marker = .right) := by
  obtain ⟨⟨_, he | hi⟩, hx⟩ := h
  · exact (hx he.1).elim
  · have hr := hi.2.2.1
    cases hm : a.marker <;> simp [rightExternal, hm] at hx <;>
      simp_all [acceptsRight]

def LeftClosedComponent (w : List (Skeleton q k)) : Prop :=
  ∀ c ∈ w.head?, c.leftExternal

lemma closed_pair_chain {w : List (Skeleton q k)} (h : Closed w) : w.IsChain Pair := by
  have hc := h.2.tail.left_of_append
  simpa only [List.isChain_map, Link] using hc

lemma closed_right {w : List (Skeleton q k)} (h : Closed w) :
    ∀ c ∈ w.getLast?, c.rightExternal := by
  have hc := (List.isChain_append.mp h.2.tail).2.2
  intro c hc'
  have hh : some c ∈ (w.map some).getLast? := by simpa using hc'
  simpa [Link] using hc (some c) hh none (by simp)

lemma closed_left {w : List (Skeleton q k)} (h : Closed w) : LeftClosedComponent w := by
  cases w with
  | nil => simp [LeftClosedComponent]
  | cons a w =>
    have hh := (List.isChain_cons_cons.mp h.2).1
    simpa [LeftClosedComponent, Link] using hh

end Skeleton
end SourceBurnside.LocalSyntax

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_RelativeHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical
namespace RationalExtension
open RationalBar
variable {X G : Type} [Group X] [Group G] (S : RationalExtension X G)

def chosenSection : G → X := S.toGroupExtension.surjInvRightHom

end RationalExtension
end
end SourceBurnside.Stability

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Palette
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.instFintypeCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Palette

variable {C : Type u} {A : Type v}

variable (head : A → Prop)

def Syntax (w : List (Cell C A)) : Prop :=
  List.IsChain (fun a b => Pair a.check b.check) w ∧
    ∀ c ∈ w.getLast?, LastOK c.check

def Form (w : List (Cell C A)) : Prop :=
  (∀ c ∈ w, c.check = .idle) ∨
    ∃ p c s x, w = p ++ c :: s ∧ c.check = .head x ∧
      (∀ a ∈ p, a.check = .passed x) ∧ (∀ a ∈ s, a.check = .idle)

lemma syntax_tail {c : Cell C A} {w : List (Cell C A)} (h : Syntax (c :: w)) :
    Syntax w := by
  refine ⟨h.1.tail, ?_⟩
  intro a ha
  cases w with
  | nil => simp at ha
  | cons d t => exact h.2 a (by simpa using ha)

lemma syntax_form (w : List (Cell C A)) (h : Syntax w) : Form w := by
  induction w with
  | nil => exact Or.inl (by simp)
  | cons c w ih =>
    have ht := ih (syntax_tail h)
    cases w with
    | nil =>
      have hc := h.2 c (by simp)
      cases hck : c.check with
      | idle => exact Or.inl (by simp [hck])
      | passed x => simp [LastOK, hck] at hc
      | head x => exact Or.inr ⟨[], c, [], x, by simp, hck, by simp, by simp⟩
    | cons d t =>
      have hp : Pair c.check d.check := h.1.rel
      generalize hcc : c.check = cc at hp
      generalize hdc : d.check = dc at hp
      cases hp with
      | idle =>
        rcases ht with ht | ⟨p, a, s, x, heq, ha, hpre, hs⟩
        · exact Or.inl (by simp_all)
        · cases p with
          | nil => simp only [List.nil_append, List.cons.injEq] at heq
                   obtain ⟨rfl, rfl⟩ := heq
                   simp_all
          | cons e p => simp only [List.cons_append, List.cons.injEq] at heq
                        obtain ⟨rfl, heq⟩ := heq
                        have := hpre d (by simp)
                        simp_all
      | passed x =>
        rcases ht with ht | ⟨p, a, s, y, heq, ha, hpre, hs⟩
        · have := ht d (by simp); simp_all
        · cases p with
          | nil => simp only [List.nil_append, List.cons.injEq] at heq
                   obtain ⟨rfl, rfl⟩ := heq
                   simp_all
          | cons e p =>
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, heq⟩ := heq
            have hxy := hpre d (by simp)
            have hxy' : x = y := by simpa [hdc] using hxy
            subst y
            exact Or.inr ⟨c :: d :: p, a, s, x,
              by simp [heq], ha, by simp_all, hs⟩
      | next x =>
        rcases ht with ht | ⟨p, a, s, y, heq, ha, hpre, hs⟩
        · have := ht d (by simp); simp_all
        · cases p with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            have hxy : x = y := by simpa [hdc] using ha
            subst y
            exact Or.inr ⟨[c], d, t, x, rfl, ha, by simp_all, hs⟩
          | cons e p =>
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, heq⟩ := heq
            have := hpre d (by simp)
            simp_all
      | rest x =>
        rcases ht with ht | ⟨p, a, s, y, heq, ha, hpre, hs⟩
        · exact Or.inr ⟨[], c, d :: t, x, rfl, hcc, by simp, ht⟩
        · cases p with
          | nil => simp only [List.nil_append, List.cons.injEq] at heq
                   obtain ⟨rfl, rfl⟩ := heq
                   simp_all
          | cons e p => simp only [List.cons_append, List.cons.injEq] at heq
                        obtain ⟨rfl, heq⟩ := heq
                        have := hpre d (by simp)
                        simp_all

def Zero (w : List (Cell C A)) : Prop :=
  (∃ a ∈ w, ∃ x, a.check = .passed x ∧ a.color = x) ∨
  (∃ p a b s, w = p ++ a :: b :: s ∧ a.color = b.color) ∨
  (∃ p a x, w = p ++ [a] ∧ a.check = .head x ∧ a.color ≠ x)

end SourceBurnside.Palette

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_HeadTour
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.HeadTour
open scoped BigOperators

structure State (N : ℕ) where
  ctrl : Control N
  reg : Registers
  side : Bool
  deriving DecidableEq

variable {N : ℕ}

namespace Payload
variable (P : Payload N)

lemma partialSum_succ (p : Fin N) : P.partialSum (p.val+1) = P.partialSum p.val + P.delta p := by
  have hh : ∀ q : Fin N, (if q.val < p.val+1 then P.delta q else 0) =
      (if q.val < p.val then P.delta q else 0) + (if q = p then P.delta p else 0) := by
    intro q
    by_cases h : q.val < p.val
    · have hn : q ≠ p := by intro e; subst q; omega
      simp [h, show q.val < p.val+1 by omega, hn]
    · by_cases e : q = p
      · subst q; simp
      · have hn : ¬ q.val < p.val+1 := by have : q.val ≠ p.val := Fin.val_ne_of_ne e; omega
        simp [h,hn,e]
  simp only [partialSum,hh,Finset.sum_add_distrib]
  simp

lemma partialSum_last : P.partialSum P.last.val = P.total := by
  have h := P.partialSum_succ P.last
  have he : P.last.val+1 = N := by have := P.nonempty; simp only [last]; omega
  rw [he,P.partialSum_N] at h
  simpa only [last,P.last_zero,add_zero] using h.symm

def potential : Control N → Registers
  | .acquisition => 0
  | .readLeft p => P.total - P.partialSum p.val
  | .readRight _ => P.total
  | .beforeGate => P.total
  | .afterGate => P.total
  | .undoLeft _ => P.total
  | .undoRight p => P.total + P.partialSum p.val
  | .finish => 0

def Good (s : State N) : Prop :=
  s.reg = P.potential s.ctrl ∧ (passed s.ctrl → P.gate P.total)

def SemanticZero (s : State N) : Prop :=
  ((s.ctrl = .acquisition ∨ s.ctrl = .finish) ∧ s.reg ≠ 0) ∨
    (s.ctrl = .afterGate ∧ ¬ P.gate s.reg)

inductive Edge : State N → State N → Prop
  | enter (r s) : Edge ⟨.acquisition,r,s⟩ ⟨.readLeft P.last,r,s⟩
  | read_left (p q : Fin N) (hp : q.val+1=p.val) (r s) :
      Edge ⟨.readLeft p,r,s⟩ ⟨.readLeft q,r+P.delta q,s⟩
  | read_turn (r s) : Edge ⟨.readLeft P.first,r,s⟩ ⟨.readRight P.first,r,s⟩
  | read_right (p q : Fin N) (hp : p.val+1=q.val) (r s) :
      Edge ⟨.readRight p,r,s⟩ ⟨.readRight q,r,s⟩
  | read_exit (r s) : Edge ⟨.readRight P.last,r,s⟩ ⟨.beforeGate,r,s⟩
  | gate (r s) (h : P.gate r) : Edge ⟨.beforeGate,r,s⟩ ⟨.afterGate,r,s⟩
  | undo_enter (r s) : Edge ⟨.afterGate,r,s⟩ ⟨.undoLeft P.last,r,s⟩
  | undo_left (p q : Fin N) (hp : q.val+1=p.val) (r s) :
      Edge ⟨.undoLeft p,r,s⟩ ⟨.undoLeft q,r,s⟩
  | undo_turn (r s) : Edge ⟨.undoLeft P.first,r,s⟩ ⟨.undoRight P.first,r,s⟩
  | undo_right (p q : Fin N) (hp : p.val+1=q.val) (r s) :
      Edge ⟨.undoRight p,r,s⟩ ⟨.undoRight q,r+P.delta p,s⟩
  | undo_exit (r s) : Edge ⟨.undoRight P.last,r,s⟩ ⟨.finish,r,s⟩

def Step (s t : State N) : Prop := P.Edge s t ∨ P.Edge t s
abbrev Reach := Relation.ReflTransGen P.Step

lemma edge_good {s t : State N} (he : P.Edge s t) : P.Good s ↔ P.Good t := by
  cases he with
  | enter r s => simp [Good,potential,passed,P.partialSum_last]
  | read_left p q h r s =>
    have hp : P.partialSum p.val = P.partialSum q.val + P.delta q := by
      rw [←h,P.partialSum_succ]
    simp only [Good,potential,passed,false_implies,and_true]
    rw [hp]
    constructor <;> intro hr
    · rw [hr]; abel
    · have hh := congrArg (fun x => x - P.delta q) hr
      simpa only [add_sub_cancel_right,sub_add_eq_sub_sub] using hh
  | read_turn r s => simp [Good,potential,passed,first]
  | read_right p q h r s => rfl
  | read_exit r s => rfl
  | gate r s hg =>
    simp only [Good,potential,passed,false_implies,and_true,true_implies]
    exact ⟨fun h => ⟨h,h ▸ hg⟩, And.left⟩
  | undo_enter r s => rfl
  | undo_left p q h r s => rfl
  | undo_turn r s => simp [Good,potential,passed,first]
  | undo_right p q h r s =>
    have hp : P.partialSum q.val = P.partialSum p.val + P.delta p := by
      rw [←h,P.partialSum_succ]
    simp only [Good,potential,passed,true_implies,hp]
    constructor
    · rintro ⟨hr,hg⟩; exact ⟨by rw [hr]; abel,hg⟩
    · rintro ⟨hr,hg⟩
      refine ⟨?_,hg⟩
      apply add_right_cancel (b := P.delta p)
      rw [hr]; abel
  | undo_exit r s => simp [Good,potential,passed,P.partialSum_last,CharTwo.add_self_eq_zero]

lemma good_not_zero {s : State N} (h : P.Good s) : ¬P.SemanticZero s := by
  rintro (⟨hc,hr⟩ | ⟨hc,hg⟩)
  · rcases hc with hc | hc <;> exact hr (h.1.trans (by simp [hc,potential]))
  · have hp : passed s.ctrl := by simp [hc,passed]
    have hh := h.2 hp
    apply hg
    simpa only [h.1,hc,potential] using hh

lemma good_initial (s : Bool) : P.Good ⟨.acquisition,0,s⟩ := by simp [Good,potential,passed]

lemma predecessor (s : State N) (h : s.ctrl ≠ .acquisition) :
    P.SemanticZero s ∨ ∃ t, P.Edge t s ∧ rank t.ctrl < rank s.ctrl ∧ t.side=s.side := by
  have hn := P.nonempty
  rcases s with ⟨c,r,b⟩
  cases c with
  | acquisition => exact (h rfl).elim
  | readLeft p =>
    by_cases hp : p = P.last
    · subst p
      exact Or.inr ⟨⟨.acquisition,r,b⟩,Edge.enter r b,by simp [rank],rfl⟩
    · have hp' : p.val+1 < N := by
        have hh : p.val ≠ N-1 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val+1,hp'⟩
      refine Or.inr ⟨⟨.readLeft q,r-P.delta p,b⟩,?_,by simp only [rank,q]; omega,rfl⟩
      simpa only [sub_add_cancel] using Edge.read_left (P:=P) q p rfl (r-P.delta p) b
  | readRight p =>
    by_cases hp : p=P.first
    · subst p
      exact Or.inr ⟨⟨.readLeft P.first,r,b⟩,Edge.read_turn r b,
        by simp only [rank,first]; omega,rfl⟩
    · have hp' : 0 < p.val := by
        have hh : p.val ≠ 0 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val-1,by omega⟩
      exact Or.inr ⟨⟨.readRight q,r,b⟩,Edge.read_right q p (by dsimp [q]; omega) r b,
        by dsimp [rank,q]; omega,rfl⟩
  | beforeGate =>
    exact Or.inr ⟨⟨.readRight P.last,r,b⟩,Edge.read_exit r b,
      by simp only [rank,last]; omega,rfl⟩
  | afterGate =>
    by_cases hg : P.gate r
    · exact Or.inr ⟨⟨.beforeGate,r,b⟩,Edge.gate r b hg,by simp [rank],rfl⟩
    · exact Or.inl (Or.inr ⟨rfl,hg⟩)
  | undoLeft p =>
    by_cases hp : p = P.last
    · subst p
      exact Or.inr ⟨⟨.afterGate,r,b⟩,Edge.undo_enter r b,by simp [rank,last],rfl⟩
    · have hp' : p.val+1 < N := by
        have hh : p.val ≠ N-1 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val+1,hp'⟩
      exact Or.inr ⟨⟨.undoLeft q,r,b⟩,Edge.undo_left q p rfl r b,
        by simp only [rank,q]; omega,rfl⟩
  | undoRight p =>
    by_cases hp : p=P.first
    · subst p
      exact Or.inr ⟨⟨.undoLeft P.first,r,b⟩,Edge.undo_turn r b,
        by simp only [rank,first]; omega,rfl⟩
    · have hp' : 0 < p.val := by
        have hh : p.val ≠ 0 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val-1,by omega⟩
      refine Or.inr ⟨⟨.undoRight q,r-P.delta q,b⟩,?_,by dsimp [rank,q]; omega,rfl⟩
      simpa only [sub_add_cancel] using
        Edge.undo_right (P:=P) q p (by dsimp [q]; omega) (r-P.delta q) b
  | finish =>
    exact Or.inr ⟨⟨.undoRight P.last,r,b⟩,Edge.undo_exit r b,
      by simp only [rank,last]; omega,rfl⟩

theorem rollback (s : State N) :
    P.Reach s ⟨.acquisition,0,s.side⟩ ∨ ∃ z, P.Reach s z ∧ P.SemanticZero z := by
  generalize he : rank s.ctrl = i
  induction i using Nat.strong_induction_on generalizing s with
  | h i ih =>
    by_cases hc : s.ctrl=.acquisition
    · by_cases hr : s.reg=0
      · left; convert (Relation.ReflTransGen.refl : P.Reach s s) using 1
        cases s; simp_all
      · exact Or.inr ⟨s,.refl,Or.inl ⟨Or.inl hc,hr⟩⟩
    · rcases P.predecessor s hc with hz | ⟨t,ht,hl,hs⟩
      · exact Or.inr ⟨s,.refl,hz⟩
      · have hb : P.Reach s t := Relation.ReflTransGen.single (Or.inr ht)
        rcases ih (rank t.ctrl) (by omega) t rfl with h | ⟨z,h,hz⟩
        · exact Or.inl (by simpa only [hs] using hb.trans h)
        · exact Or.inr ⟨z,hb.trans h,hz⟩

end Payload

structure FullState (m N : ℕ) where
  ctrl : FullControl m N
  reg : Registers
  side : Bool
  deriving DecidableEq

def atClause {m N : ℕ} (j : Fin m) (s : State N) : FullState m N :=
  ⟨.clause j s.ctrl,s.reg,s.side⟩

namespace Plan
variable {m : ℕ} (Q : Plan m N)

def first : Fin m := ⟨0,Q.nonempty⟩
def last : Fin m := ⟨m-1,by have := Q.nonempty; omega⟩

def Before (j : Fin m) : Prop := ∀ i : Fin m, i.val < j.val → Q.Holds i

def Good (s : FullState m N) : Prop := match s.ctrl with
  | .clause j c => (Q.payload j).Good ⟨c,s.reg,s.side⟩ ∧ Q.Before j
  | .success => s.reg=0 ∧ ∀ j, Q.Holds j

def Bad (s : FullState m N) : Prop := match s.ctrl with
  | .clause j c => (Q.payload j).SemanticZero ⟨c,s.reg,s.side⟩
  | .success => s.reg ≠ 0

def SemanticZero (s : FullState m N) : Prop :=
  Q.Bad s ∨ (s.ctrl=.success ∧ Q.zeroTask=true)

inductive Edge : FullState m N → FullState m N → Prop
  | tour (j : Fin m) {s t : State N} (h : (Q.payload j).Edge s t) :
      Edge (atClause j s) (atClause j t)
  | next (i j : Fin m) (h : i.val+1=j.val) (s : Bool) :
      Edge (atClause i ⟨.finish,0,s⟩) (atClause j ⟨.acquisition,0,s⟩)
  | done (s : Bool) : Edge (atClause Q.last ⟨.finish,0,s⟩) ⟨.success,0,s⟩
  | flip (s : Bool) (h : Q.zeroTask=false) : Edge ⟨.success,0,s⟩ ⟨.success,0,!s⟩

def Step (s t : FullState m N) : Prop := Q.Edge s t ∨ Q.Edge t s
abbrev Reach := Relation.ReflTransGen Q.Step

lemma before_next (i j : Fin m) (h : i.val+1=j.val) :
    Q.Before j ↔ Q.Holds i ∧ Q.Before i := by
  constructor
  · intro hb; exact ⟨hb i (by omega),fun t ht => hb t (by omega)⟩
  · rintro ⟨hi,hb⟩ t ht
    by_cases he : t=i
    · simpa only [he] using hi
    · apply hb
      have hne : t.val ≠ i.val := Fin.val_ne_of_ne he
      omega

lemma before_last : (Q.Holds Q.last ∧ Q.Before Q.last) ↔ ∀ i, Q.Holds i := by
  constructor
  · rintro ⟨hh,hb⟩ i
    by_cases he : i=Q.last
    · simpa only [he] using hh
    · apply hb
      have hne : i.val ≠ m-1 := by intro h; apply he; apply Fin.ext; exact h
      have := i.isLt
      dsimp [last]; omega
  · intro h; exact ⟨h _,fun i _ => h i⟩

lemma edge_good {s t : FullState m N} (h : Q.Edge s t) : Q.Good s ↔ Q.Good t := by
  cases h with
  | tour j h => exact and_congr_left (fun _ => (Q.payload j).edge_good h)
  | next i j h s =>
    simp only [Good,atClause,Payload.Good,Payload.potential,Payload.passed,
      true_implies,false_implies,and_true,true_and]
    exact (Q.before_next i j h).symm
  | done s =>
    simp only [Good,atClause,Payload.Good,Payload.potential,Payload.passed,
      true_implies,true_and]
    exact Q.before_last
  | flip s h => rfl

lemma reach_good {s t : FullState m N} (h : Q.Reach s t) (hg : Q.Good s) : Q.Good t := by
  induction h with
  | refl => exact hg
  | tail h e ih =>
    exact e.elim (fun he => (Q.edge_good he).mp ih) (fun he => (Q.edge_good he).mpr ih)

lemma good_not_bad {s : FullState m N} (h : Q.Good s) : ¬Q.Bad s := by
  cases hc : s.ctrl with
  | clause j c =>
    have hh : (Q.payload j).Good ⟨c,s.reg,s.side⟩ ∧ Q.Before j :=
      by simpa only [Good,hc] using h
    simpa only [Bad,hc] using (Q.payload j).good_not_zero hh.1
  | success =>
    have hh : s.reg=0 ∧ ∀ j, Q.Holds j := by simpa only [Good,hc] using h
    simpa only [Bad,hc] using not_not.mpr hh.1

lemma good_initial (s : Bool) : Q.Good (atClause Q.first ⟨.acquisition,0,s⟩) := by
  exact ⟨(Q.payload Q.first).good_initial s,fun i hi => (by dsimp [first] at hi; omega)⟩

theorem success_sound {r : Registers} {s t : Bool}
    (h : Q.Reach (atClause Q.first ⟨.acquisition,0,s⟩) ⟨.success,r,t⟩) :
    r=0 ∧ ∀ j, Q.Holds j := Q.reach_good h (Q.good_initial s)

lemma lift_reach (j : Fin m) {s t : State N} (h : (Q.payload j).Reach s t) :
    Q.Reach (atClause j s) (atClause j t) := by
  induction h with
  | refl => exact .refl
  | tail h e ih =>
    exact ih.tail (e.elim (fun he => Or.inl (Edge.tour j he))
      (fun he => Or.inr (Edge.tour j he)))

lemma rollback_clause (j : Fin m) (s : State N) :
    Q.Reach (atClause j s) (atClause Q.first ⟨.acquisition,0,s.side⟩) ∨
      ∃ z, Q.Reach (atClause j s) z ∧ Q.Bad z := by
  generalize he : j.val = i
  induction i using Nat.strong_induction_on generalizing j s with
  | h i ih =>
    rcases (Q.payload j).rollback s with hr | ⟨z,hz,hb⟩
    · have hr' := Q.lift_reach j hr
      by_cases hj : j=Q.first
      · left; simpa only [hj] using hr'
      · have hp : 0 < j.val := by
          have hh : j.val ≠ 0 := by intro h; apply hj; apply Fin.ext; exact h
          omega
        let p : Fin m := ⟨j.val-1,by omega⟩
        have hm : Q.Reach (atClause j ⟨.acquisition,0,s.side⟩)
            (atClause p ⟨.finish,0,s.side⟩) :=
          Relation.ReflTransGen.single (Or.inr (Edge.next p j (by dsimp [p]; omega) s.side))
        rcases ih p.val (by dsimp [p]; omega) p ⟨.finish,0,s.side⟩ rfl with hh | ⟨z,hz,hb⟩
        · exact Or.inl (hr'.trans (hm.trans hh))
        · exact Or.inr ⟨z,hr'.trans (hm.trans hz),hb⟩
    · exact Or.inr ⟨atClause j z,Q.lift_reach j hz,hb⟩

theorem rollback (s : FullState m N) :
    Q.Reach s (atClause Q.first ⟨.acquisition,0,s.side⟩) ∨
      ∃ z, Q.Reach s z ∧ Q.Bad z := by
  rcases s with ⟨c,r,b⟩
  cases c with
  | clause j c => exact Q.rollback_clause j ⟨c,r,b⟩
  | success =>
    by_cases hr : r=0
    · subst r
      have hm : Q.Reach ⟨.success,0,b⟩ (atClause Q.last ⟨.finish,0,b⟩) :=
        Relation.ReflTransGen.single (Or.inr (Edge.done b))
      rcases Q.rollback_clause Q.last ⟨.finish,0,b⟩ with hh | ⟨z,hz,hb⟩
      · exact Or.inl (hm.trans hh)
      · exact Or.inr ⟨z,hm.trans hz,hb⟩
    · exact Or.inr ⟨⟨.success,r,b⟩,.refl,hr⟩

lemma reach_symm {s t : FullState m N} (h : Q.Reach s t) : Q.Reach t s := by
  induction h with
  | refl => exact .refl
  | tail h e ih =>
    exact (Relation.ReflTransGen.single (show Q.Step _ _ from e.symm)).trans ih

theorem success_iff (s : Bool) :
    Q.Reach (atClause Q.first ⟨.acquisition,0,s⟩) ⟨.success,0,s⟩ ↔
      ∀ j, Q.Holds j := by
  constructor
  · intro h; exact (Q.success_sound h).2
  · intro hg
    have hgood : Q.Good ⟨.success,0,s⟩ := ⟨rfl,hg⟩
    rcases Q.rollback ⟨.success,0,s⟩ with h | ⟨z,h,hz⟩
    · exact Q.reach_symm h
    · exact (Q.good_not_bad (Q.reach_good h hgood) hz).elim

end Plan
end SourceBurnside.HeadTour

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton

variable {q : ℕ} [NeZero q]

def Zero (S : Schedule q) (dataSize : ℕ) (v : List (Cell q)) : Prop :=
  (∃ c, v=[c] ∧ UnaryZero S dataSize c) ∨
  (∃ a b, v=[a,b] ∧ BinaryZero a b)

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TableEncoding
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.LocalSyntax.Skeleton
variable {q k : ℕ}

lemma closed_idle_metadata (p s : List (Skeleton q k)) (c : Skeleton q k)
    (m : Metadata k) :
    Closed (p ++ ⟨c.pos,.idle,m⟩ :: s) ↔ Closed (p ++ c.mark .idle :: s) := by
  apply closed_replace_one
  · simp [Admissible]
  · intro a
    cases a with
    | none => simp [Link,leftExternal]
    | some a =>
      simp [Link,Pair,Structural,leftExternal,rightExternal,mark]
  · intro b
    cases b with
    | none => simp [Link,rightExternal]
    | some b =>
      simp [Link,Pair,Structural,leftExternal,rightExternal,mark]

lemma palette_link_left (c : Option (Skeleton q k)) (a : Skeleton q k) (x y : Fin q) :
    Link c (some {a with pos := .palette x}) ↔
      Link c (some {a with pos := .palette y}) := by
  cases c with
  | none => simp [Link,leftExternal,first]
  | some c =>
    cases h : c.pos <;>
      simp [Link,Pair,Structural,Internal,leftExternal,rightExternal,first,last,acceptsLeft,h]

lemma palette_link_right (a : Skeleton q k) (c : Option (Skeleton q k)) (x y : Fin q) :
    Link (some {a with pos := .palette x}) c ↔
      Link (some {a with pos := .palette y}) c := by
  cases c with
  | none => simp [Link,rightExternal,last]
  | some c =>
    cases h : c.pos <;>
      simp [Link,Pair,Structural,Internal,leftExternal,rightExternal,first,last,acceptsRight,h]

lemma closed_palette_color (p s : List (Skeleton q k)) (a : Skeleton q k) (x y : Fin q) :
    Closed (p ++ {a with pos := .palette x} :: s) ↔
      Closed (p ++ {a with pos := .palette y} :: s) := by
  apply closed_replace_one
  · simp [Admissible,first,last]
  · exact fun c => palette_link_left c a x y
  · exact fun c => palette_link_right a c x y

end SourceBurnside.LocalSyntax.Skeleton

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q]

lemma binary_transaction_context {S : Schedule q} {a b a' b' : Cell q}
    (h : Binary S a b a' b') (p s : List (Skeleton q 10)) :
    Closed (p ++ a.skeleton :: b.skeleton :: s) ↔
      Closed (p ++ a'.skeleton :: b'.skeleton :: s) := by
  cases h with
  | acquire a b side hp =>
    have hi := closed_idle_metadata (p ++ [a.skeleton.mark .boundary]) s b.skeleton defaultMeta
    have hh := (Skeleton.replacement_context (Skeleton.Replacement.acquire a.skeleton b.skeleton hp) p s)
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hi hh
    simpa only [Cell.boundary,Cell.wing,Cell.idle,Cell.pos] using hi.trans hh
  | read_left a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      ((Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)).symm
  | read_right a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      (Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)
  | undo_left a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      ((Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)).symm
  | undo_right a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      (Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)
  | checker_create => exact Iff.rfl
  | checker_advance => exact Iff.rfl
  | swap a b x y ha hb he hf hf' =>
    have hx : {a.skeleton with pos := .palette x} = a.skeleton := by
      cases a with | mk aa ac ad acf ah => cases aa; simp_all [Cell.pos]
    have hy : {a.skeleton with pos := .palette y} = b.skeleton := by
      exact congrArg Cell.skeleton he
    have h₁ := closed_palette_color p (b.skeleton :: s) a.skeleton x y
    have h₂ := closed_palette_color (p ++ [b.skeleton]) s a.skeleton y x
    rw [hx,hy] at h₁ h₂
    exact h₁.trans (by simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using h₂)

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax
variable {q : ℕ} [NeZero q]

omit [NeZero q] in
lemma checker_right_idle_head (b c : Cell q) (x : Fin q) :
    CheckerPair (b.setChecker .idle) c ↔ CheckerPair (b.setChecker (.head x)) c := by
  simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos,Palette.LastOK]

omit [NeZero q] in
lemma checker_left_head_passed (a c : Cell q) (x : Fin q) :
    CheckerPair c (a.setChecker (.head x)) ↔ CheckerPair c (a.setChecker (.passed x)) := by
  simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos]

omit [NeZero q] in
lemma checker_color_left (a c : Cell q) (x y : Fin q) :
    CheckerPair c (a.setColor x) ↔ CheckerPair c (a.setColor y) := by
  simp [CheckerPair,Cell.setColor,Cell.isPalette,Cell.pos]

omit [NeZero q] in
lemma checker_color_right (a c : Cell q) (x y : Fin q) :
    CheckerPair (a.setColor x) c ↔ CheckerPair (a.setColor y) c := by
  simp [CheckerPair,Cell.setColor,Cell.isPalette,Cell.pos]

lemma binary_checker_context {S : Schedule q} {a b a' b' : Cell q}
    (h : Binary S a b a' b') (p s : List (Cell q)) :
    List.IsChain CheckerPair (p ++ a :: b :: s) ↔
      List.IsChain CheckerPair (p ++ a' :: b' :: s) := by
  cases h with
  | acquire | read_left | read_right | undo_left | undo_right =>
    apply chain_replace_two <;> intros <;> exact Iff.rfl
  | checker_create a b r x ha hr hb =>
    apply chain_replace_two
    · intro c; exact Iff.rfl
    · exact fun c => checker_right_idle_head b c x
    · have hap : ¬ a.isPalette := by simp [Cell.isPalette,ha]
      rcases hb with ⟨v,hv⟩
      simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos,
        show a.skeleton.pos = .core r from ha]
  | checker_advance a b v x ha hb hv =>
    apply chain_replace_two
    · exact fun c => checker_left_head_passed a c x
    · exact fun c => checker_right_idle_head b c x
    · rcases hb with ⟨y,hy⟩
      simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos,
        Palette.LastOK,show b.skeleton.pos = .palette y from hy]
  | swap a b x y ha hb he hf hf' =>
    have hx : a.setColor x = a := by
      cases a with
      | mk aa ac ad ace ah => cases aa; simp_all [Cell.pos,Cell.setColor]
    apply chain_replace_two
    · intro c
      have hh := checker_color_left a c x y
      simpa only [hx,he] using hh
    · intro c
      have hh := checker_color_right a c y x
      simpa only [hx,he] using hh
    · have h₁ := checker_color_right a b x y
      have h₂ := checker_color_left a b y x
      rw [hx,he] at h₁ h₂
      exact h₁.trans h₂

def Syntax (S : Schedule q) (d : ℕ) (w : List (Cell q)) : Prop :=
  LocalSyntax.Skeleton.Closed (w.map Cell.skeleton) ∧
    List.IsChain CheckerPair w ∧ ∀ c ∈ w, c.Format S d

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

def idleCore (p : Fin q) : Cell q :=
  ⟨⟨.core p,.idle,defaultMeta⟩,.idle,0,0,defaultHead⟩

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Transactions
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Cell

def LockedReads (a b : Cell q) : Prop :=
  a.marker ≠ .idle → b.marker ≠ .idle → ∀ x : Address q, a.read x = b.read x
end Cell

namespace Region
variable (R : Region q d) (S : Schedule q)

def controlPosition : HeadTour.Control R.size → Fin R.size
  | .readLeft p | .readRight p | .undoLeft p | .undoRight p => p
  | _ => R.last

def controlPhase : HeadTour.Control R.size → Phase
  | .acquisition => .acquisition
  | .readLeft _ => .readLeft
  | .readRight _ => .readRight
  | .beforeGate => .beforeGate
  | .afterGate => .afterGate
  | .undoLeft _ => .undoLeft
  | .undoRight _ => .undoRight
  | .finish => .finish

def position (s : HeadTour.FullState (S.count R.task).val R.size) : Fin R.size :=
  match s.ctrl with
  | .clause _ c => R.controlPosition c
  | .success => R.last

def phase (s : HeadTour.FullState (S.count R.task).val R.size) : Phase :=
  match s.ctrl with
  | .clause _ c => R.controlPhase c
  | .success => .success

def clause (s : HeadTour.FullState (S.count R.task).val R.size) : Fin q :=
  match s.ctrl with
  | .clause j _ => R.clauseIndex S j
  | .success => 0

def realizeCell (s : HeadTour.FullState (S.count R.task).val R.size) (i : Fin R.size) : Cell q :=
  if i.val < (R.position S s).val then (R.cell i).wing .left
  else if (R.position S s).val < i.val then (R.cell i).wing .right
  else (R.cell i).full s.side (R.clause S s) (R.phase S s) s.reg

def realize (s : HeadTour.FullState (S.count R.task).val R.size) : List (Cell q) :=
  List.ofFn (R.realizeCell S s)

lemma realize_head (s : HeadTour.FullState (S.count R.task).val R.size) :
    R.realizeCell S s (R.position S s) =
      (R.cell (R.position S s)).full s.side (R.clause S s) (R.phase S s) s.reg := by
  simp [realizeCell]

omit [NeZero q] in
lemma endpoint_position (s : HeadTour.FullState (S.count R.task).val R.size)
    (h : Cell.endpoint (R.phase S s)) : R.position S s = R.last := by
  cases hs : s.ctrl with
  | success => simp [position,hs]
  | clause j c =>
    cases c <;> simp_all [Cell.endpoint,phase,controlPhase,position,controlPosition]

lemma realizeCell_format (s : HeadTour.FullState (S.count R.task).val R.size)
    (hs : R.task.zeroTask=true → s.side=false) (i : Fin R.size) :
    (R.realizeCell S s i).Format S d := by
  have hbase := R.payload_format i
  have htask := R.task_eq i
  have ht : (R.cell i).metadata.zeroTask=R.task.zeroTask := congrArg Task.zeroTask htask
  unfold realizeCell
  split
  · rename_i hi
    simp only [Cell.Format,Cell.wing,Cell.marker,Cell.metadata,Skeleton.mark,Cell.pos,
      Skeleton.Admissible,Skeleton.IsHead,Cell.isPalette,Cell.isCore]
    dsimp [Cell.PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hbase
    refine ⟨?_,hbase.1,hbase.2.1,hbase.2.2,?_⟩ <;> simp
    intro hlast
    have hlast' := (R.last_iff i).mp hlast
    have := (R.position S s).isLt
    omega
  · rename_i hi
    split
    · rename_i hi'
      simp only [Cell.Format,Cell.wing,Cell.marker,Cell.metadata,Skeleton.mark,Cell.pos,
        Skeleton.Admissible,Skeleton.IsHead,Cell.isPalette,Cell.isCore]
      dsimp [Cell.PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hbase
      refine ⟨?_,hbase.1,hbase.2.1,hbase.2.2,?_⟩ <;> simp
      intro hfirst
      have hfirst' := (R.first_iff i).mp hfirst
      omega
    · rename_i hi'
      have he : i=R.position S s := Fin.ext (by omega)
      subst i
      simp only [Cell.Format,Cell.full,Cell.marker,Cell.metadata,Skeleton.mark,Cell.pos,
        Skeleton.Admissible,Skeleton.IsHead,Cell.isPalette,Cell.isCore]
      dsimp [Cell.PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hbase
      refine ⟨?_,hbase.1,hbase.2.1,hbase.2.2,?_⟩ <;> simp
      refine ⟨?_,?_,?_,?_⟩
      · rw [←ht] at hs
        exact hs
      · intro he
        cases hc : s.ctrl with
        | success => simp [clause,hc]
        | clause j c => cases c <;> simp [phase,hc,controlPhase] at he
      · intro hn
        cases hc : s.ctrl with
        | success => exact (hn (by simp [phase,hc])).elim
        | clause j c =>
          change (R.clause S s).val < (S.count (R.cell (R.position S s)).metadata.task).val
          rw [htask]
          simpa only [clause,hc,clauseIndex] using j.isLt
      · intro hep
        have hey := R.endpoint_position S s hep
        change (R.cell (R.position S s)).skeleton.last
        rw [hey]
        exact R.last_last
end Region

namespace Region
variable (R : Region q d) (S : Schedule q)

def SideOK (s : HeadTour.FullState (S.count R.task).val R.size) : Prop :=
  R.task.zeroTask=true → s.side=false

omit [NeZero q] in
lemma edge_side {s t : HeadTour.FullState (S.count R.task).val R.size}
    (h : (R.plan S).Edge s t) : R.SideOK S s ↔ R.SideOK S t := by
  cases h with
  | tour j h => cases h <;> rfl
  | next i j h b => rfl
  | done b => rfl
  | flip b h =>
    change R.task.zeroTask=false at h
    simp [SideOK,h]

omit [NeZero q] in
lemma adjacent_pair (i j : Fin R.size) (hij : i.val+1=j.val) :
    Skeleton.Pair ((R.cell i).skeleton.mark .full) ((R.cell j).skeleton.mark .right) := by
  obtain ⟨hstr,hi⟩ := R.adjacent i j hij
  refine ⟨hstr,Or.inr ?_⟩
  simp only [Skeleton.rightExternal,Skeleton.leftExternal,Skeleton.mark_marker,
    Skeleton.mark_last,Skeleton.mark_first,Skeleton.acceptsRight,Skeleton.acceptsLeft,
    Skeleton.internal_mark_left,Skeleton.internal_mark_right]
  simpa using And.intro hi.2.2.2.2 hi

lemma realizeCell_eq_off_head (s t : HeadTour.FullState (S.count R.task).val R.size)
    (hp : R.position S s = R.position S t) (i : Fin R.size) (hi : i ≠ R.position S s) :
    R.realizeCell S s i = R.realizeCell S t i := by
  simp only [realizeCell,←hp]
  split
  · rfl
  · rename_i h1
    split
    · rfl
    · rename_i h2
      exact (hi (Fin.ext (by omega))).elim

lemma realizeCell_eq_off_adjacent (s t : HeadTour.FullState (S.count R.task).val R.size)
    (i j : Fin R.size) (hij : i.val+1=j.val)
    (hs : R.position S s=i ∨ R.position S s=j)
    (ht : R.position S t=i ∨ R.position S t=j)
    (k : Fin R.size) (hki : k≠i) (hkj : k≠j) :
    R.realizeCell S s k = R.realizeCell S t k := by
  have hne : k.val≠i.val := Fin.val_ne_of_ne hki
  have hne' : k.val≠j.val := Fin.val_ne_of_ne hkj
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    simp only [realizeCell,hs,ht]
  all_goals by_cases hk : k.val < i.val
  all_goals first
    | simp [hk,show k.val < j.val by omega]
    | simp [hk,show ¬k.val < j.val by omega,show i.val < k.val by omega,show j.val < k.val by omega]

omit [NeZero q] in
lemma reach_side {s t : HeadTour.FullState (S.count R.task).val R.size}
    (h : (R.plan S).Reach s t) (hs : R.SideOK S s) : R.SideOK S t := by
  induction h with
  | refl => exact hs
  | tail h e ih =>
    exact e.elim (fun e => (R.edge_side S e).mp ih)
      (fun e => (R.edge_side S e).mpr ih)

lemma realize_semanticZero (s : HeadTour.FullState (S.count R.task).val R.size)
    (hz : (R.plan S).SemanticZero s) :
    SemanticZero S (R.realizeCell S s (R.position S s)) := by
  rw [R.realize_head]
  refine ⟨rfl,?_⟩
  rcases hz with hz | ⟨hc,hz⟩
  · cases hc : s.ctrl with
    | success =>
      simp only [HeadTour.Plan.Bad,hc] at hz
      exact Or.inl ⟨Or.inr (Or.inr (by simp [phase,hc,Cell.full])),hz⟩
    | clause j c =>
      simp only [HeadTour.Plan.Bad,hc,HeadTour.Payload.SemanticZero] at hz
      rcases hz with ⟨hc',hr⟩ | ⟨rfl,hg⟩
      · left
        constructor
        · rcases hc' with rfl | rfl
          · exact Or.inl (by simp [phase,hc,controlPhase,Cell.full])
          · exact Or.inr (Or.inl (by simp [phase,hc,controlPhase,Cell.full]))
        · exact hr
      · right; left
        refine ⟨by simp [phase,hc,controlPhase,Cell.full],?_⟩
        simp only [Cell.full,clause,hc]
        change (S.clause (R.cell (R.position S s)).metadata.task (R.clauseIndex S j)).truth s.reg=false
        rw [R.task_eq]
        exact Bool.eq_false_of_not_eq_true hg
  · right; right
    refine ⟨by simp [phase,hc,Cell.full],?_⟩
    change (R.cell (R.position S s)).metadata.zeroTask=true
    have he := congrArg Task.zeroTask (R.task_eq (R.position S s))
    exact he.trans hz

end Region

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_ConnectedWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton

variable {q N : ℕ}

def cellCut (f : Fin N → Cell q) (i : Fin N) : Prop := (f i).skeleton.rightExternal
instance instDecidableCellCut (f : Fin N → Cell q) (i : Fin N) : Decidable (cellCut f i) := by
  unfold cellCut Skeleton.rightExternal Skeleton.last
  infer_instance

abbrev SameRegion (f : Fin N → Cell q) := Connected (cellCut f)

def Coherent (f : Fin N → Cell q) : Prop :=
  ∀ i j, i.val+1=j.val → Skeleton.Pair (f i).skeleton (f j).skeleton

lemma Coherent.internal {f : Fin N → Cell q} (hf : Coherent f)
    (i j : Fin N) (hij : i.val+1=j.val) (hc : SameRegion f i j) :
    Skeleton.InternalPair (f i).skeleton (f j).skeleton :=
  ⟨hf i j hij,(Connected.adjacent_iff hij).mp hc⟩

lemma SameRegion.task {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hc : SameRegion f i j) : (f i).metadata.task=(f j).metadata.task := by
  suffices ∀ (a b : Fin N), a.val ≤ b.val → SameRegion f a b →
      (f a).metadata.task=(f b).metadata.task by
    by_cases hij : i.val ≤ j.val
    · exact this i j hij hc
    · exact (this j i (by omega) hc.symm).symm
  intro a b hab hc
  generalize hdiff : b.val-a.val=n
  induction n generalizing b with
  | zero =>
    have he : a=b := Fin.ext (by omega)
    simp [he]
  | succ n ih =>
    let p : Fin N := ⟨b.val-1,by omega⟩
    have hp : p.val+1=b.val := by dsimp [p]; omega
    have hpa : a.val ≤ p.val := by dsimp [p]; omega
    have he : p.val-a.val=n := by dsimp [p]; omega
    have hcp : SameRegion f a p := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hcb : SameRegion f p b := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hint := (hf.internal p b hp hcb).1.2.resolve_left
      (fun hh => (hf.internal p b hp hcb).2 hh.1)
    have hmeta := hint.2.2.2.2
    exact (ih p hpa hcp he).trans (congrArg₂ Task.mk hmeta.1 hmeta.2.1)

lemma Coherent.left_barrier {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (he : (f i).skeleton.leftExternal) (hji : j.val < i.val) : ¬SameRegion f j i := by
  intro hc
  let p : Fin N := ⟨i.val-1,by omega⟩
  have hp : p.val+1=i.val := by dsimp [p]; omega
  have hcp : SameRegion f p i := hc.subinterval (by dsimp [p]; omega)
    (by dsimp [p]; omega) (by omega) (by omega)
  have hpair := hf p i hp
  rcases hpair.2 with hh | hh
  · exact ((Connected.adjacent_iff hp).mp hcp) hh.1
  · exact hh.2.1 he

lemma Coherent.idle_component {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hj : (f j).marker=.idle) (hc : SameRegion f i j) : i=j := by
  apply Fin.ext
  by_contra hne
  by_cases hh : i.val < j.val
  · exact hf.left_barrier (Or.inl hj) hh hc
  · exact hc.symm.right_barrier (by omega) (Or.inl hj)

lemma Coherent.right_wing {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hi : (f i).marker=.full ∨ (f i).marker=.right)
    (hij : i.val < j.val) (hc : SameRegion f i j) : (f j).marker=.right := by
  generalize hdiff : j.val-i.val=n
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    let p : Fin N := ⟨j.val-1,by omega⟩
    have hp : p.val+1=j.val := by dsimp [p]; omega
    have hip : i.val ≤ p.val := by dsimp [p]; omega
    have hcp : SameRegion f i p := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hpc : SameRegion f p j := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hh : (f p).marker=.full ∨ (f p).marker=.right := by
      by_cases he : i=p
      · simpa only [←he] using hi
      · right
        apply ih (j:=p) (by have := Fin.val_ne_of_ne he; omega) hcp
        dsimp [p]; omega
    have hm := Skeleton.internal_marker_rule (hf.internal p j hp hpc)
    rcases hm with ⟨hm,_⟩ | ⟨_,hm⟩
    · rcases hh with hh | hh <;> simp [Cell.marker,hm] at hh
    · exact hm

lemma Coherent.unique_head {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hi : (f i).skeleton.IsHead) (hj : (f j).skeleton.IsHead)
    (hc : SameRegion f i j) : i=j := by
  have hforward (a b : Fin N) (ha : (f a).skeleton.IsHead)
      (hb : (f b).skeleton.IsHead) (hab : a.val < b.val) (h : SameRegion f a b) : False := by
    rcases ha with ha | ha
    · exact h.right_barrier hab (Or.inr (Or.inl ha))
    · have hh := hf.right_wing (Or.inl ha) hab h
      rcases hb with hb | hb <;> simp [Cell.marker,hb] at hh
  apply Fin.ext
  by_contra hn
  by_cases hij : i.val < j.val
  · exact hforward i j hi hj hij hc
  · exact hforward j i hj hi (by omega) hc.symm

lemma Coherent.region_locked {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hj : (f j).skeleton.IsHead) (hc : SameRegion f i j) : (f i).marker≠.idle := by
  intro hi
  have he := hf.idle_component hi hc.symm
  subst j
  change (f i).skeleton.marker=.idle at hi
  rcases hj with hj | hj <;> simp [hi] at hj

variable [NeZero q]

structure BinaryAt (S : Schedule q) (f g : Fin N → Cell q) (i j : Fin N) : Prop where
  adjacent : i.val+1=j.val
  off : ∀ h, h≠i → h≠j → f h=g h
  edge : Binary S (f i) (f j) (g i) (g j)

namespace Verification
open scoped BigOperators
variable (S : Schedule q)

noncomputable def sum (f : Fin N → Cell q) (h : Fin N) (j : Fin q) (t : ℕ) : Reg :=
  ∑ i : Fin N, if SameRegion f h i ∧ i.val < t then
    (f i).delta (S.clause (f h).metadata.task j) else 0
noncomputable def total (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Reg := sum S f h j N
noncomputable def leftSum (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Reg := sum S f h j h.val

noncomputable def potential (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Phase → Reg
  | .readLeft => total S f h j-leftSum S f h j
  | .undoRight => total S f h j+leftSum S f h j
  | .readRight | .beforeGate | .afterGate | .undoLeft => total S f h j
  | _ => 0

def passed : Phase → Prop
  | .afterGate | .undoLeft | .undoRight | .finish => True
  | _ => False

def holds (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Prop :=
  (S.clause (f h).metadata.task j).truth (total S f h j)=true

def Good (f : Fin N → Cell q) (h : Fin N) : Prop :=
  let hd := (f h).head
  hd.reg=potential S f h hd.clause hd.phase ∧
    if hd.phase=.success then ∀ j : Fin q, j.val < (S.count (f h).metadata.task).val → holds S f h j
    else (∀ j : Fin q, j.val < hd.clause.val → holds S f h j) ∧
      (passed hd.phase → holds S f h hd.clause)

def AllGood (f : Fin N → Cell q) : Prop := ∀ h, (f h).marker=.full → Good S f h

end Verification
end SourceBurnside.FiniteTable
end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_CommittedWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]
namespace Verification
open scoped BigOperators
variable (S : Schedule q)

def WordGood (w : List (Cell q)) : Prop := AllGood S w.get

lemma coherent_of_syntax {f : Fin N → Cell q} {d : ℕ} (hf : Syntax S d (List.ofFn f)) : Coherent f := by
  have hh := Skeleton.closed_pair_chain hf.1
  rw [List.map_ofFn,List.isChain_ofFn] at hh
  intro i j hij
  have hj : i.val+1<N := by omega
  have h' := hh i.val hj
  simpa only [show (⟨i.val,by omega⟩ : Fin N)=i from Fin.ext rfl,
    show (⟨i.val+1,hj⟩ : Fin N)=j from Fin.ext hij,Function.comp_apply] using h'

end Verification

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

def Own (f : Fin N → Cell q) (i h : Fin N) : Prop :=
  SameRegion f i h ∧ (f h).skeleton.IsHead

namespace Committed

noncomputable def value (f : Fin N → Cell q) (i : Fin N) : ZMod 2 := by
  classical
  exact if (f i).marker=.idle then (f i).data false
    else if h : ∃ k, Own f i k then (f i).data (f (Classical.choose h)).head.side else 0

def PivotAt (f g : Fin N → Cell q) (i : Fin N) : Prop :=
  ∃ (a : Cell q) (s : Bool), f i=a.full s 0 .success 0 ∧ g i=a.full (!s) 0 .success 0 ∧
    (∀ h, h≠i → f h=g h) ∧ a.skeleton.last ∧ a.metadata.zeroTask=false

end Committed

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordComponents
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

lemma Binary.shape {S : Schedule q} {a b a' b' : Cell q} (hb : Binary S a b a' b') :
    a.shape=a'.shape ∧ b.shape=b'.shape := by
  cases hb with
  | acquire a b s hp => exact ⟨rfl,rfl⟩
  | read_left a b s j r hp => exact ⟨rfl,rfl⟩
  | read_right a b s j r hp => exact ⟨rfl,rfl⟩
  | undo_left a b s j r hp => exact ⟨rfl,rfl⟩
  | undo_right a b s j r hp => exact ⟨rfl,rfl⟩
  | checker_create a b p x ha hp hb => exact ⟨rfl,rfl⟩
  | checker_advance a b v x ha hb hv => exact ⟨rfl,rfl⟩
  | swap a b x y ha hb he hf hf' => simp [Cell.shape,ha,hb]

def Exterior (f : Fin N → Cell q) : Prop :=
  (∀ i, i.val=0 → (f i).skeleton.leftExternal) ∧
  (∀ i, i.val+1=N → (f i).skeleton.rightExternal)

lemma exterior_of_syntax {S : Schedule q} {d : ℕ} {f : Fin N → Cell q}
    (hf : Syntax S d (List.ofFn f)) : Exterior f := by
  have hh : Skeleton.Closed (List.ofFn (fun i => (f i).skeleton)) := by
    simpa only [List.map_ofFn,Function.comp_def] using hf.1
  constructor
  · intro i hi
    apply Skeleton.closed_left hh
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by simp only [List.length_ofFn]; have := i.isLt; omega)]
    simp only [List.getElem_ofFn,Option.mem_def,Option.some.injEq]
    apply congrArg (fun j => (f j).skeleton)
    exact Fin.ext hi.symm
  · intro i hi
    apply Skeleton.closed_right hh
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_ofFn]
    rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; have := i.isLt; omega)]
    simp only [List.getElem_ofFn,Option.mem_def,Option.some.injEq]
    apply congrArg (fun j => (f j).skeleton)
    exact Fin.ext (by dsimp; omega)

omit [NeZero q] in
lemma Coherent.owner_right {f : Fin N → Cell q} (hf : Coherent f)
    (he : Exterior f) (i : Fin N) (hi : (f i).marker=.left) :
    ∃ h, i.val < h.val ∧ Own f i h := by
  change (f i).skeleton.marker=.left at hi
  generalize hdiff : N-i.val=n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    have hn : i.val+1 < N := by
      by_contra h
      have hx := he.2 i (by have := i.isLt; omega)
      simp [Skeleton.rightExternal,hi] at hx
    let j : Fin N := ⟨i.val+1,hn⟩
    have hij : i.val+1=j.val := rfl
    have hcut : ¬cellCut f i := by
      simp [cellCut,Skeleton.rightExternal,hi]
    have hc : SameRegion f i j := (Connected.adjacent_iff hij).mpr hcut
    have hm := Skeleton.internal_marker_rule (hf.internal i j hij hc)
    have hj : (f j).marker=.left ∨ (f j).marker=.boundary ∨ (f j).marker=.full := by
      simpa [Cell.marker,hi] using hm
    rcases hj with hj | hj | hj
    · obtain ⟨h,hh,ho⟩ := ih (N-j.val) (by dsimp [j]; omega) j hj rfl
      exact ⟨h,by dsimp [j] at hh; omega,hc.trans ho.1,ho.2⟩
    · exact ⟨j,by dsimp [j]; omega,hc,Or.inl hj⟩
    · exact ⟨j,by dsimp [j]; omega,hc,Or.inr hj⟩

omit [NeZero q] in
lemma Coherent.owner_left {f : Fin N → Cell q} (hf : Coherent f)
    (he : Exterior f) (i : Fin N) (hi : (f i).marker=.right) :
    ∃ h, h.val < i.val ∧ Own f i h := by
  change (f i).skeleton.marker=.right at hi
  generalize hdiff : i.val=n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    have hn : 0 < i.val := by
      by_contra h
      have hx := he.1 i (by omega)
      simp [Skeleton.leftExternal,hi] at hx
    let j : Fin N := ⟨i.val-1,by have := i.isLt; omega⟩
    have hij : j.val+1=i.val := by dsimp [j]; omega
    have hp := hf j i hij
    have hcut : ¬cellCut f j := by
      rcases hp.2 with hp | hp
      · simp [Skeleton.leftExternal,hi] at hp
      · exact hp.1
    have hc : SameRegion f j i := (Connected.adjacent_iff hij).mpr hcut
    have hm := (hf.internal j i hij hc).1.2
    have hj : (f j).marker=.full ∨ (f j).marker=.right := by
      rcases hm with hm | hm
      · exact (hcut hm.1).elim
      · simpa [Skeleton.acceptsLeft,Cell.marker,hi] using hm.2.2.2.1
    rcases hj with hj | hj
    · exact ⟨j,by dsimp [j]; omega,hc.symm,Or.inr hj⟩
    · obtain ⟨h,hh,ho⟩ := ih j.val (by dsimp [j]; omega) j hj rfl
      exact ⟨h,by dsimp [j] at hh; omega,hc.symm.trans ho.1,ho.2⟩

omit [NeZero q] in
theorem Coherent.owner {f : Fin N → Cell q} (hf : Coherent f)
    (he : Exterior f) (i : Fin N) (hi : (f i).marker≠.idle) : ∃ h, Own f i h := by
  cases hm : (f i).marker with
  | idle => exact (hi hm).elim
  | left => obtain ⟨h,_,hh⟩ := hf.owner_right he i hm; exact ⟨h,hh⟩
  | right => obtain ⟨h,_,hh⟩ := hf.owner_left he i hm; exact ⟨h,hh⟩
  | boundary => exact ⟨i,Connected.refl _ _,Or.inl hm⟩
  | full => exact ⟨i,Connected.refl _ _,Or.inr hm⟩

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
def members : Finset (Fin N) := Finset.univ.filter (SameRegion f i)
omit [NeZero q] in
lemma mem_iff (j : Fin N) : j ∈ members f i ↔ SameRegion f i j := by simp [members]
omit [NeZero q] in
lemma nonempty : (members f i).Nonempty := ⟨i,(mem_iff f i i).mpr (.refl _ _)⟩
noncomputable def left : Fin N := (members f i).min' (nonempty f i)
noncomputable def right : Fin N := (members f i).max' (nonempty f i)
omit [NeZero q] in
lemma connected_left : SameRegion f i (left f i) := by
  exact (mem_iff f i _).mp (Finset.min'_mem _ _)
omit [NeZero q] in
lemma connected_right : SameRegion f i (right f i) := by
  exact (mem_iff f i _).mp (Finset.max'_mem _ _)
omit [NeZero q] in
lemma left_le {j : Fin N} (hj : SameRegion f i j) : left f i ≤ j := by
  exact Finset.min'_le _ _ ((mem_iff f i _).mpr hj)
omit [NeZero q] in
lemma le_right {j : Fin N} (hj : SameRegion f i j) : j ≤ right f i := by
  exact Finset.le_max' _ _ ((mem_iff f i _).mpr hj)
omit [NeZero q] in
lemma left_le_self : left f i ≤ i := left_le f i (.refl _ _)
omit [NeZero q] in
lemma self_le_right : i ≤ right f i := le_right f i (.refl _ _)
omit [NeZero q] in
lemma left_le_right : left f i ≤ right f i := left_le f i (connected_right f i)
omit [NeZero q] in
lemma interval (j : Fin N) : SameRegion f i j ↔ left f i ≤ j ∧ j ≤ right f i := by
  constructor
  · intro h; exact ⟨left_le f i h,le_right f i h⟩
  · rintro ⟨hl,hr⟩
    have h := (connected_left f i).symm.trans (connected_right f i)
    exact h.subinterval (by have := left_le_self f i; have := left_le_right f i; omega)
      (by have := self_le_right f i; have := left_le_right f i; omega)
      (by have := left_le_right f i; omega) (by have := left_le_right f i; omega)

omit [NeZero q] in
lemma exterior_left (hf : Coherent f) (he : Exterior f) : (f (left f i)).skeleton.leftExternal := by
  by_cases hh : (left f i).val=0
  · exact he.1 _ hh
  · let p : Fin N := ⟨(left f i).val-1,by have := (left f i).isLt; omega⟩
    have hp : p.val+1=(left f i).val := by dsimp [p]; omega
    have hc : cellCut f p := by
      by_contra hn
      have hc : SameRegion f i p := (connected_left f i).trans ((Connected.adjacent_iff hp).mpr hn).symm
      have hle := left_le f i hc
      dsimp [p] at hle
      omega
    rcases (hf p (left f i) hp).2 with h | h
    · exact h.2
    · exact (h.1 hc).elim

omit [NeZero q] in
lemma exterior_right (_hf : Coherent f) (he : Exterior f) : cellCut f (right f i) := by
  by_cases hh : (right f i).val+1=N
  · exact he.2 _ hh
  · let p : Fin N := ⟨(right f i).val+1,by have := (right f i).isLt; omega⟩
    have hp : (right f i).val+1=p.val := rfl
    by_contra hn
    have hc : SameRegion f i p := (connected_right f i).trans ((Connected.adjacent_iff hp).mpr hn)
    have hle := le_right f i hc
    dsimp [p] at hle
    omega

omit [NeZero q] in
lemma first (hf : Coherent f) (he : Exterior f) (hi : (f i).skeleton.IsHead) :
    (f (left f i)).skeleton.first := by
  have hn := hf.region_locked hi (connected_left f i).symm
  have hh := exterior_left f i hf he
  rcases hh with hh | hh
  · exact (hn hh).elim
  · exact hh.2

omit [NeZero q] in
lemma last (hf : Coherent f) (he : Exterior f) (hi : (f i).marker=.full) :
    (f (right f i)).skeleton.last := by
  have hih : (f i).skeleton.IsHead := Or.inr hi
  have hn := hf.region_locked hih (connected_right f i).symm
  have hh := exterior_right f i hf he
  rcases hh with hh | hh | hh
  · exact (hn hh).elim
  · have heq := hf.unique_head hih (Or.inl hh) (connected_right f i)
    simp only [←heq] at hh
    change (f i).marker=.boundary at hh
    simp [hi] at hh
  · exact hh.2

noncomputable def size : ℕ := (right f i).val+1-(left f i).val
omit [NeZero q] in
lemma size_pos : 0 < size f i := by
  have := left_le_right f i
  unfold size
  omega
noncomputable def offset (j : Fin (size f i)) : Fin N :=
  ⟨(left f i).val+j.val,by
    have := (right f i).isLt
    have := j.isLt
    have := left_le_right f i
    dsimp [size] at *
    omega⟩
omit [NeZero q] in
lemma connected_offset (j : Fin (size f i)) : SameRegion f i (offset f i j) := by
  apply (interval f i _).mpr
  have := j.isLt
  have := left_le_right f i
  dsimp [size] at *
  constructor
  · change (left f i).val ≤ (left f i).val+j.val; omega
  · change (left f i).val+j.val ≤ (right f i).val; omega
omit [NeZero q] in
lemma offset_adjacent (j k : Fin (size f i)) (hj : j.val+1=k.val) :
    (offset f i j).val+1=(offset f i k).val := by dsimp [offset]; omega
omit [NeZero q] in
lemma offset_internal (hf : Coherent f) (j k : Fin (size f i)) (hj : j.val+1=k.val) :
    Skeleton.Internal (f (offset f i j)).skeleton (f (offset f i k)).skeleton := by
  exact (hf.internal _ _ (offset_adjacent f i j k hj)
    ((connected_offset f i j).symm.trans (connected_offset f i k))).1.2.resolve_left
      (fun h => ((Connected.adjacent_iff (offset_adjacent f i j k hj)).mp
        ((connected_offset f i j).symm.trans (connected_offset f i k))) h.1) |>.2.2.2.2

omit [NeZero q] in
lemma offset_first_iff (hf : Coherent f) (he : Exterior f) (hi : (f i).skeleton.IsHead)
    (j : Fin (size f i)) : (f (offset f i j)).skeleton.first ↔ j.val=0 := by
  constructor
  · intro hj
    by_contra hn
    let k : Fin (size f i) := ⟨j.val-1,by have := j.isLt; omega⟩
    have hk : k.val+1=j.val := by dsimp [k]; omega
    exact (offset_internal f i hf k j hk).2.2.2.1 hj
  · intro hj
    have hh : offset f i j=left f i := Fin.ext (by simp [offset,hj])
    rw [hh]
    exact first f i hf he hi

omit [NeZero q] in
lemma offset_last_iff (hf : Coherent f) (he : Exterior f) (hi : (f i).marker=.full)
    (j : Fin (size f i)) : (f (offset f i j)).skeleton.last ↔ j.val+1=size f i := by
  constructor
  · intro hj
    by_contra hn
    let k : Fin (size f i) := ⟨j.val+1,by have := j.isLt; omega⟩
    have hk : j.val+1=k.val := rfl
    exact (offset_internal f i hf j k hk).2.2.2.2 hj
  · intro hj
    have hh : offset f i j=right f i := Fin.ext (by
      have := left_le_right f i
      dsimp [offset,size] at *
      omega)
    rw [hh]
    exact last f i hf he hi

noncomputable def region {S : Schedule q} {d : ℕ}
    (hs : Syntax S d (List.ofFn f)) (hi : (f i).marker=.full) : Region q d where
  size := size f i
  positive := size_pos f i
  task := (f i).metadata.task
  cell := fun j => f (offset f i j)
  task_eq j := SameRegion.task (Verification.coherent_of_syntax S hs) (connected_offset f i j).symm
  first_iff := offset_first_iff f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) (Or.inr hi)
  last_iff := offset_last_iff f i (Verification.coherent_of_syntax S hs) (exterior_of_syntax hs) hi
  adjacent j k hj := ⟨(Verification.coherent_of_syntax S hs _ _ (offset_adjacent f i j k hj)).1,
    offset_internal f i (Verification.coherent_of_syntax S hs) j k hj⟩
  payload_format j := by
    have hh : (f (offset f i j)).Format S d := hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)
    exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

omit [NeZero q] in
lemma offset_surjective {j : Fin N} (hj : SameRegion f i j) : ∃ k, offset f i k=j := by
  have hh := (interval f i j).mp hj
  let k : Fin (size f i) := ⟨j.val-(left f i).val,by dsimp [size]; omega⟩
  refine ⟨k,Fin.ext ?_⟩
  change (left f i).val+(j.val-(left f i).val)=j.val
  omega

end Component

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_TapePrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.OneTape

instance instFintypeMove : Fintype Move := ⟨{.left,.stay,.right},by intro a; cases a <;> simp⟩

end SourceBurnside.OneTape

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Cell

def transactionRank (c : Cell q) : ℕ := match c.marker with
  | .left => 0 | .boundary | .full => 1 | .right => 2 | .idle => 3

def eraseColor (c : Cell q) : Cell q := c.setColor 0

end Cell

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

def cell (b : Fin n) (p : Fin (width q)) : Fin (n*width q) :=
  ⟨b.val*width q+p.val,by
    have hh := Nat.mul_le_mul_right (width q) (show b.val+1≤n from b.isLt)
    have hp := p.isLt
    nlinarith⟩
def core (b : Fin n) (p : Fin q) : Fin (n*width q) := cell b ⟨p.val,by
  have := p.isLt; simp [width]; omega⟩

omit [NeZero q] in
lemma coord_cell (b : Fin n) (p : Fin (width q)) : coord (cell b p)=p := by
  apply Fin.ext
  simp [coord,cell,Nat.add_mod,Nat.mod_eq_of_lt p.isLt]
omit [NeZero q] in
lemma block_cell (b : Fin n) (p : Fin (width q)) : block (cell b p)=b := by
  apply Fin.ext
  change (b.val*width q+p.val)/width q=b.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ width_pos,Nat.div_eq_of_lt p.isLt]
  simp

lemma block_next {i j : Fin (n*width q)} (h : i.val+1=j.val) :
    (block j).val=(block i).val+if i.val%width q=2*q then 1 else 0 := by
  change j.val/width q=i.val/width q+_
  rw [←h]
  have h1 : 1<width q := by have := NeZero.pos q; dsimp [width]; omega
  by_cases ht : i.val%width q=2*q
  · have hz : (i.val+1)%width q=0 := by
      rw [Nat.add_mod,Nat.mod_eq_of_lt h1,ht]
      exact Nat.mod_self (2*q+1)
    rw [ite_eq_left ht,Nat.succ_div_of_mod_eq_zero hz]
  · have hk : i.val%width q+1<width q := by
      have := Nat.mod_lt i.val (width_pos (q:=q))
      unfold width at *
      omega
    have hz : (i.val+1)%width q≠0 := by
      rw [Nat.add_mod,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt hk]
      omega
    rw [ite_eq_right ht,Nat.succ_div_of_mod_ne_zero hz,Nat.add_zero]

end Rigid
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_DataWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d n : ℕ} [NeZero q]
namespace Region
noncomputable def dataWord (R : Region q d) (hd : d≤q) (s : Bool) : List (Fin d → ZMod 2) :=
  List.ofFn (fun b p => R.slot s b (p.castLE hd))
end Region

inductive CheckedSwap (S : Schedule q) (hd : d≤q) : List (Fin d → ZMod 2) → List (Fin d → ZMod 2) → Prop
  | mk (R : Region q d) (s : Bool) (hz : R.task.zeroTask=false)
      (hc : ∀j,(R.plan S).Holds j) (p t : List (Fin d → ZMod 2)) :
      CheckedSwap S hd (p++R.dataWord hd s++t) (p++R.dataWord hd (!s)++t)

def CheckedZero (S : Schedule q) (hd : d≤q) (w : List (Fin d → ZMod 2)) : Prop :=
  ∃ (R : Region q d) (p t : List (Fin d → ZMod 2)), R.task.zeroTask=true ∧
    (∀j,(R.plan S).Holds j) ∧ w=p++R.dataWord hd false++t

def CheckedReach (S : Schedule q) (hd : d≤q) := Relation.ReflTransGen (CheckedSwap S hd)

end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d n : ℕ} [NeZero q]
namespace Rigid

def palCell (b : Fin n) (p : Fin q) : Fin (n*width q) := cell b ⟨q+p.val,by
  have := p.isLt; dsimp [width]; omega⟩

end Rigid
end

open LocalSyntax LocalSyntax.Skeleton
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable FiniteTable.Codec
variable {q d h D : ℕ} [NeZero q]
def regionData (R : Region q d) : DataAddress q → Bool :=
  fun a => physicalBits R (.data a.1 a.2.1 a.2.2)
def regionCert (R : Region q d) : Fin q → Bool :=
  fun p => physicalBits R (.certificate p)
end
end SourceBurnside.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.WordAlgebra

noncomputable section
open Classical

variable {α : Type u} {K : Type v} [Ring K]

namespace Table

variable (T : Table α)

def Vanishes (w : Word α) : Prop :=
  ∃ p z s, z ∈ T.zero ∧ T.Reach w (p * z * s)

lemma word_reach {v w : Word α} (h : T.Reach v w) : T.word (K := K) v = T.word w := by
  let f : Word α →* T.Algebra (K := K) :=
    { toFun := T.word
      map_one' := T.word_one
      map_mul' := T.word_mul }
  have hc : conGen T.rep ≤ Con.ker f := by
    apply Con.conGen_le.mpr
    intro a b hab
    exact T.word_rep hab
  exact hc h

lemma word_eq_zero_of_vanishes {w : Word α} (h : T.Vanishes w) : T.word (K := K) w = 0 := by
  obtain ⟨p, z, s, hz, hr⟩ := h
  rw [T.word_reach hr, word_mul, word_mul, T.word_zero hz, mul_zero, zero_mul]

end Table

end

end SourceBurnside.WordAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_PacketIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.PacketIntervals
variable {Γ : Type*}

def Selection.join (p : Selection Γ) : List Γ := p.before ++ p.inside ++ p.after

end SourceBurnside.PacketIntervals

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T : Type*}

def pickPacket (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (s : List Γ) : Cancellation.Packet Γ :=
  let a := (range ((spell label s).map erase)).1
  let e := (range ((spell label s).map erase)).2
  let p := PacketIntervals.select (fun c => (label c).length) s a e
  ⟨p.before,p.inside,p.after⟩

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T K A : Type*} [Fintype Γ] [CommRing K] [CharP K 2]
  [Ring A] [Algebra K A]

def chunkSum {d : ℕ} (label : Γ → List α) (W : Γ → Matrix (Fin d) (Fin d) K)
    (f : α → A) (n : ℕ) (i j : Fin d) : A :=
  ∑ s ∈ (candidates Γ n).filter (fun s => (spell label s).length = n),
    Cancellation.chunkWeight W s i j • eval f (spell label s)

end
end SourceBurnside.DirectCancellation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_MatrixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def letterSum {α : Type*} [Fintype α] (W : α → Matrix ι ι K) (f : α → A) (n : ℕ) : Matrix ι ι A :=
  CutReduction.letterSum (fun a=>tensor (W a) (f a)) n

variable {α Γ : Type*} [Fintype α] [Fintype Γ]
def chunkSum (label : Γ → List α) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) : Matrix ι ι A :=
  CutReduction.chunkSum (fun c=>(label c).length) (fun c=>tensor (W c) (DirectCancellation.eval f (label c))) n
end
end SourceBurnside.MatrixTests

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_ExteriorComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical Module

variable (V : Type*)

variable {V}

variable [LinearOrder V]

variable {F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]

section EnoughRank
variable (ρ : V → W) [FiniteDimensional F W]

def coneSupply (hρ : Submodule.span F (Set.range ρ) = ⊤) (N : ℕ)
    (hN : N < Module.finrank F W) : ConeSupply (F := F) ρ N where
  pick s := if hs : s.card ≤ N then
      (exists_outside_labels ρ hρ s (lt_of_le_of_lt hs hN)).choose
    else (exists_outside_labels ρ hρ ∅ (by simpa using lt_of_le_of_lt (Nat.zero_le N) hN)).choose
  outside s hs := by
    simp only [dite_eq_left hs]
    exact (exists_outside_labels ρ hρ s (lt_of_le_of_lt hs hN)).choose_spec

end EnoughRank

end
end SourceBurnside.Stability.Frames

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_PresentationModel
attribute [-instance] _root_.OAI.SourceBurnside.FiniteSteinbergPresentation.root_finite _root_.OAI.SourceBurnside.MonomialCompletion.rootSubgroup_comm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside

namespace Steinberg

variable {n : ℕ} {R : Type u} [Ring R]

theorem closure_range_x : Subgroup.closure (Set.range (fun g : Generator n R => x g.1 g.2)) = ⊤ :=
  PresentedGroup.closure_range_of _

end Steinberg

end SourceBurnside

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_KernelRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
open scoped BigOperators
noncomputable section
open Classical

variable {n : ℕ} {R : Type u} [Ring R]

variable (H L : Finset (Fin n)) (hHL : Disjoint H L)

lemma rectMatrix_single (p : RectIndex H L) (a : R) :
    rectMatrix H L (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Matrix.single p.1.val p.2.val a := by
  ext i j
  by_cases hi : i ∈ H
  · by_cases hj : j ∈ L
    · simp only [rectMatrix, dite_eq_left hi, dite_eq_left hj, Matrix.single_apply]
      by_cases hp : p = (⟨i, hi⟩, ⟨j, hj⟩)
      · subst p
        simp
      · have hp' : ¬ (p.1.val = i ∧ p.2.val = j) := by
          rintro ⟨h₁, h₂⟩
          apply hp
          exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
        simp [hp, hp']
    · have hn : p.2.val ≠ j := by intro h; exact hj (h ▸ p.2.property)
      simp [rectMatrix, hi, hj, hn]
  · have hn : p.1.val ≠ i := by intro h; exact hi (h ▸ p.1.property)
    simp [rectMatrix, hi, hn]

@[simp] lemma rectUnits_single (p : RectIndex H L) (a : R) :
    rectUnits H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Elementary.e (rectPosition H L hHL p) a := by
  apply Units.ext
  rw [coe_rectUnits, rectMatrix_single]
  rfl

lemma representation_rectRoot :
    Elementary.representation.comp (rectRoot H L hHL (R := R)) = rectUnits H L hHL := by
  apply MonoidHom.pi_ext
  intro p a
  change Elementary.representation (rectRoot H L hHL (Pi.mulSingle p a)) =
    rectUnits H L hHL (Pi.mulSingle p a)
  change Elementary.representation
    (rectRoot H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a.toAdd))) =
    rectUnits H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a.toAdd))
  rw [rectRoot_single, rectUnits_single, Elementary.representation_x]

lemma rectUnits_injective : Function.Injective (rectUnits H L hHL (R := R)) := by
  intro A B h
  have hm := congrArg (fun x : (Matrix (Fin n) (Fin n) R)ˣ => x.val) h
  have he : rectMatrix H L A = rectMatrix H L B := add_left_cancel hm
  funext p
  apply Multiplicative.toAdd.injective
  simpa using congrArg (fun M : Matrix (Fin n) (Fin n) R => M p.1.val p.2.val) he

def Strip : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃ (p : RectIndex H L) (a : R),
    g = Steinberg.x (rectPosition H L hHL p) a}

lemma strip_le_range : Strip H L hHL ≤ (rectRoot H L hHL (R := R)).range := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p, a, rfl⟩
  exact ⟨Pi.mulSingle p (Multiplicative.ofAdd a), rectRoot_single H L hHL p a⟩

theorem strip_faithful {g : Steinberg n R} (hg : g ∈ Strip H L hHL)
    (hmat : Elementary.representation g = 1) : g = 1 := by
  obtain ⟨A, rfl⟩ := strip_le_range H L hHL hg
  have hr : rectUnits H L hHL A = 1 := by
    rw [← MonoidHom.comp_apply, representation_rectRoot] at hmat
    exact hmat
  have ha : A = 1 := rectUnits_injective H L hHL (hr.trans (map_one _).symm)
  rw [ha, map_one]

end
end SourceBurnside.Kernel

namespace SourceBurnside

namespace Steinberg
variable {n m : ℕ} {R : Type u} [Ring R]

lemma conjugate_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    x ⟨i,j,hij⟩ a * x ⟨j,k,hjk⟩ b * (x ⟨i,j,hij⟩ a)⁻¹ =
      x ⟨i,k,hik⟩ (a*b) * x ⟨j,k,hjk⟩ b := by
  calc
    _ = bracket (x ⟨i,j,hij⟩ a) (x ⟨j,k,hjk⟩ b) * x ⟨j,k,hjk⟩ b := by
      simp [bracket, mul_assoc]
    _ = _ := by rw [x_mul]

lemma conjugate_reverse (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    x ⟨j,k,hjk⟩ b * x ⟨i,j,hij⟩ a * (x ⟨j,k,hjk⟩ b)⁻¹ =
      x ⟨i,k,hik⟩ (-(a*b)) * x ⟨i,j,hij⟩ a := by
  calc
    _ = (bracket (x ⟨i,j,hij⟩ a) (x ⟨j,k,hjk⟩ b))⁻¹ * x ⟨i,j,hij⟩ a := by
      simp [bracket, mul_assoc]
    _ = _ := by rw [x_mul, x_neg]

lemma conjugate_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : x p a * x q b * (x p a)⁻¹ = x q b := by
  rw [(x_commute p q h₁ h₂ a b).eq, mul_inv_cancel_right]

end Steinberg
end SourceBurnside

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
def columnStrip (t : Fin n) : Subgroup (Steinberg n R) := Strip (awayCoordinates t) {t} (away_disjoint t)
def rowStrip (t : Fin n) : Subgroup (Steinberg n R) := Strip {t} (awayCoordinates t) (away_disjoint t).symm
lemma column_root_mem (t i : Fin n) (hi : i≠t) (a : R) :
    Steinberg.x ⟨i,t,hi⟩ a∈columnStrip t := by
  apply Subgroup.subset_closure
  refine ⟨(⟨i,by simp [awayCoordinates,hi]⟩,⟨t,by simp⟩),a,rfl⟩
lemma row_root_mem (t i : Fin n) (hi : t≠i) (a : R) :
    Steinberg.x ⟨t,i,hi⟩ a∈rowStrip t := by
  apply Subgroup.subset_closure
  refine ⟨(⟨t,by simp⟩,⟨i,by simp [awayCoordinates,Ne.symm hi]⟩),a,rfl⟩
lemma conjugate_column_root_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) (i : Fin n) (hi : i≠t) (b : R) :
    Steinberg.x p a * Steinberg.x ⟨i,t,hi⟩ b * (Steinberg.x p a)⁻¹∈columnStrip t := by
  by_cases hc : p.col=i
  · have he := Steinberg.conjugate_chain p.row i t (hc ▸ p.ne) hi hpt a b
    have hp : p=⟨p.row,i,hc ▸ p.ne⟩ := by cases p;cases hc;rfl
    rw [hp,he]
    exact (columnStrip t).mul_mem (column_root_mem t _ hpt _) (column_root_mem t _ hi _)
  · rw [Steinberg.conjugate_commute p ⟨i,t,hi⟩ hc hpt]
    exact column_root_mem t i hi b
lemma conjugate_row_root_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) (i : Fin n) (hi : t≠i) (b : R) :
    Steinberg.x p a * Steinberg.x ⟨t,i,hi⟩ b * (Steinberg.x p a)⁻¹∈rowStrip t := by
  by_cases hr : p.row=i
  · have he := Steinberg.conjugate_reverse t i p.col hi (hr ▸ p.ne) hct.symm b a
    have hp : p=⟨i,p.col,hr ▸ p.ne⟩ := by cases p;cases hr;rfl
    rw [hp,he]
    exact (rowStrip t).mul_mem (row_root_mem t _ hct.symm _) (row_root_mem t _ hi _)
  · rw [Steinberg.conjugate_commute p ⟨t,i,hi⟩ hct hr]
    exact row_root_mem t i hi b
lemma conjugate_column_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) {g : Steinberg n R} (hg : g∈columnStrip t) :
    Steinberg.x p a * g * (Steinberg.x p a)⁻¹∈columnStrip t := by
  have H : columnStrip (R:=R) t ≤ (columnStrip t).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,b,rfl⟩
    have hj' : j=t := Finset.mem_singleton.mp hj
    subst j
    have hi' : i≠t := by simpa [awayCoordinates] using hi
    exact conjugate_column_root_mem t p hpt hct a i hi' b
  exact H hg
lemma conjugate_row_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) {g : Steinberg n R} (hg : g∈rowStrip t) :
    Steinberg.x p a * g * (Steinberg.x p a)⁻¹∈rowStrip t := by
  have H : rowStrip (R:=R) t ≤ (rowStrip t).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,b,rfl⟩
    have hi' : i=t := Finset.mem_singleton.mp hi
    subst i
    have hj' : j≠t := by simpa [awayCoordinates] using hj
    exact conjugate_row_root_mem t p hpt hct a j hj'.symm b
  exact H hg

def away (t : Fin n) : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃(p : Root n)(a : R),p.row≠t ∧ p.col≠t ∧ g=Steinberg.x p a}
lemma away_le_column_normalizer (t : Fin n) :
    away (R:=R) t ≤ Subgroup.normalizer (columnStrip (R:=R) t : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hpt,hct,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact conjugate_column_mem t p hpt hct a
  · intro hx
    have H := conjugate_column_mem t p hpt hct (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using H
lemma away_le_row_normalizer (t : Fin n) :
    away (R:=R) t ≤ Subgroup.normalizer (rowStrip (R:=R) t : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hpt,hct,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact conjugate_row_mem t p hpt hct a
  · intro hx
    have H := conjugate_row_mem t p hpt hct (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using H
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]

def padSteinberg : Steinberg n R →* Steinberg (n+1) R :=
  Steinberg.coordinateMap (coordinateIndex n) (coordinateIndex_injective n)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Elementary
variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]
lemma map_e (f : R →+* S) (p : Root n) (a : R) :
    Units.map f.mapMatrix.toMonoidHom (e p a)=e p (f a) := by
  apply Units.ext
  change f.mapMatrix (1+Matrix.single p.row p.col a)=1+Matrix.single p.row p.col (f a)
  rw [map_add,map_one]
  congr 1
  exact Matrix.map_single p.row p.col a f

lemma representation_map (f : R →+* S) :
    representation.comp (Steinberg.map (n:=n) f)=
      (Units.map f.mapMatrix.toMonoidHom).comp representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,Steinberg.map_x,representation_x,map_e]
end SourceBurnside.Elementary

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BlockEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]

def triangular (height : Fin n→ℕ) (k : ℕ) : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃(p : Root n)(a : R),k≤height p.row ∧ height p.row<height p.col ∧ g=Steinberg.x p a}
end
end SourceBurnside.Kernel

namespace SourceBurnside.Steinberg
variable {n : ℕ} {R G : Type*} [Ring R] [Group G]
lemma hom_images_commute (f g : Steinberg n R →* G)
    (h : ∀p q a b,Commute (f (x p a)) (g (x q b))) (u v : Steinberg n R) :
    Commute (f u) (g v) := by
  have hx (p : Root n) (a : R) : Commute (f (x p a)) (g v) := by
    have he : (MulAut.conj (f (x p a))).toMonoidHom.comp g=g := by
      apply hom_ext
      intro q b
      exact CommutatorCalculus.conj_of_commute (h p q a b)
    have hv := DFunLike.congr_fun he v
    change f (x p a)*g v*(f (x p a))⁻¹=g v at hv
    exact mul_inv_eq_iff_eq_mul.mp hv
  have he : (MulAut.conj (g v)).toMonoidHom.comp f=f := by
    apply hom_ext
    intro p a
    exact CommutatorCalculus.conj_of_commute (hx p a).symm
  have hu := DFunLike.congr_fun he u
  change g v*f u*(g v)⁻¹=f u at hu
  exact (show Commute (g v) (f u) from mul_inv_eq_iff_eq_mul.mp hu).symm
end SourceBurnside.Steinberg
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma blockIndex_ne_inner (i j : Fin n) {s t : Fin N} (h : s≠t) : blockIndex i s≠blockIndex j t := by
  intro he
  exact h (congrArg Prod.snd (finProdFinEquiv.injective he))
lemma copy_commute {s t : Fin N} (h : s≠t) (u v : Steinberg n R) :
    Commute (copyMap s u) (copyMap t v) := by
  apply Steinberg.hom_images_commute
  intro p q a b
  rw [copyMap_x,copyMap_x]
  apply Steinberg.x_commute
  · exact blockIndex_ne_inner _ _ h
  · exact blockIndex_ne_inner _ _ h
def copyFamily : (Fin N→Steinberg n R) →* Steinberg (n*N) R :=
  MonoidHom.noncommPiCoprod copyMap (fun _ _ h u v=>copy_commute h u v)

def diagonalCopy : Steinberg n R →* Steinberg (n*N) R where
  toFun u := copyFamily (fun _=>u)
  map_one' := map_one copyFamily
  map_mul' u v := map_mul copyFamily (fun _=>u) (fun _=>v)
def diagonalBlockHom (p : Root n) : (Fin N→Multiplicative R) →* Steinberg (n*N) R where
  toFun v := blockRoot p (Matrix.diagonal (fun s=>(v s).toAdd))
  map_one' := by simpa using blockRoot_zero (R:=R) (N:=N) p
  map_mul' u v := by
    change blockRoot p (Matrix.diagonal (fun s=>(u s).toAdd+(v s).toAdd))=_
    rw [←Matrix.diagonal_add,blockRoot_add]
def copyRoots (p : Root n) : (Fin N→Multiplicative R) →* Steinberg (n*N) R :=
  MonoidHom.noncommPiCoprod (fun s=>(copyMap s).comp (rootHom p))
    (fun _ _ h a b=>copy_commute h (rootHom p a) (rootHom p b))
@[simp] lemma innerHeight_blockIndex (i : Fin n) (s : Fin N) : innerHeight (blockIndex i s)=s.val := by
  simp [innerHeight,blockIndex]
def upper : Subgroup (Steinberg (n*N) R) := triangular innerHeight 0
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def highBand (w : ℕ) : Finset (Fin (n*N)) := Finset.univ.filter (fun i=>N ≤ innerHeight i+w)
def lowBand (w : ℕ) : Finset (Fin (n*N)) := Finset.univ.filter (fun i=>innerHeight i<w)
lemma bands_disjoint (w : ℕ) (h : 2*w ≤ N) : Disjoint (highBand (n:=n) (N:=N) w) (lowBand w) := by
  apply Finset.disjoint_left.mpr
  intro i hi hl
  simp only [highBand,lowBand,Finset.mem_filter,Finset.mem_univ,true_and] at hi hl
  omega
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma rowMatrix_single (t : ι) (j : {j : ι // j≠t}) (a : R) :
    rowMatrix t (Pi.mulSingle j (Multiplicative.ofAdd a)) = Matrix.single t j.val a := by
  ext i k
  by_cases hi : i=t
  · subst i
    by_cases hk : k=t
    · subst k; simp [rowMatrix,j.property]
    · simp only [rowMatrix,dite_eq_left hk,Matrix.single_apply,true_and]
      by_cases he : j.val=k
      · have hh : j=⟨k,hk⟩ := Subtype.ext he
        subst j; simp
      · have hh : j≠⟨k,hk⟩ := fun h => he (congrArg Subtype.val h)
        simp [he,hh]
  · simp [rowMatrix,hi,Ne.symm hi]

@[simp] lemma rowUnits_single (t : ι) (j : {j : ι // j≠t}) (a : R) :
    rowUnits t (Pi.mulSingle j (Multiplicative.ofAdd a)) = elementary t j.val j.property.symm a := by
  apply Units.ext
  change 1+rowMatrix t _ = 1+Matrix.single _ _ _
  rw [rowMatrix_single]

lemma evaluate_rowHom (t : ι) : evaluate.comp (rowHom (R := R) t) = rowUnits t := by
  apply MonoidHom.pi_ext
  intro j a
  change evaluate (rowHom t (Pi.mulSingle j (Multiplicative.ofAdd a.toAdd))) =
    rowUnits t (Pi.mulSingle j (Multiplicative.ofAdd a.toAdd))
  rw [rowHom_single,rowUnits_single,evaluate_root]

@[simp] lemma evaluate_rowHom_apply (t : ι) (A : {j : ι // j≠t} → Multiplicative R) :
    evaluate (rowHom t A) = rowUnits t A := DFunLike.congr_fun (evaluate_rowHom t) A

lemma rowUnits_injective (t : ι) : Function.Injective (rowUnits (R := R) t) := by
  intro A B h
  have hh : rowMatrix t A = rowMatrix t B := add_left_cancel (congrArg Units.val h)
  funext j
  apply Multiplicative.toAdd.injective
  simpa using congrArg (fun M : Matrix ι ι R => M t j.val) hh

lemma row_faithful (t : ι) {g h : Group (ι := ι) (R := R)}
    (hg : g∈rowGroup t) (hh : h∈rowGroup t) (he : evaluate g=evaluate h) : g=h := by
  obtain ⟨A,rfl⟩ := hg
  obtain ⟨B,rfl⟩ := hh
  simp only [evaluate_rowHom_apply] at he
  rw [rowUnits_injective t he]

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_MatrixStabilizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

@[simp] lemma rectangleLower_single (i : κ) (j : ι) (a : R) :
    rectangleLower (Pi.mulSingle (i,j) (Multiplicative.ofAdd a)) =
      elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [rectangleLower,Pi.mulSingle,Function.update,Matrix.add_apply,
      Matrix.one_apply,Matrix.single_apply,Matrix.fromBlocks,eq_comm,and_comm]
  split_ifs <;> rfl

lemma rectangleLower_mem {P : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ}
    (hP : ∀i j a, elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a ∈ P)
    (A : κ × ι → Multiplicative R) : rectangleLower A ∈ P := by
  change A ∈ P.comap rectangleLower
  apply Subgroup.pi_mem_of_mulSingle_mem
  rintro ⟨i,j⟩
  change rectangleLower (Pi.mulSingle (i,j) (A (i,j))) ∈ P
  change rectangleLower (Pi.mulSingle (i,j) (Multiplicative.ofAdd ((A (i,j)).toAdd))) ∈ P
  rw [rectangleLower_single]
  exact hP _ _ _

lemma rightFixer_decomposition (U : rightFixer (ι := ι) (κ := κ) (R := R)) :
    U.val = blockInclusion (rightProjection U) *
      rectangleLower (fun p : κ × ι => Multiplicative.ofAdd (U.val.val (Sum.inr p.1) (Sum.inl p.2))) := by
  apply Units.ext
  rw [Units.val_mul,blockInclusion_val]
  change U.val.val = Matrix.fromBlocks _ 0 0 1 * Matrix.fromBlocks 1 0 _ 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one,Matrix.one_mul,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
  exact rightFixer_shape U

lemma elementary_mem_fixer (S : Finset ι) (i j : ι) (h : i ≠ j) (a : R) (hj : j ∉ S) :
    elementary i j h a ∈ fixer S := by
  apply (mem_fixer_iff S _).mpr
  intro k hk l
  have hjk : j ≠ k := fun he => hj (he ▸ hk)
  simp [elementary,Matrix.add_apply,hjk]

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma root_conjugate_reverse (t i j : ι) (hti : t≠i) (htj : t≠j) (hij : i≠j) (a b : R) :
    root i j hij a * root t i hti b * (root i j hij a)⁻¹ =
      root t j htj (-(b*a)) * root t i hti b := by
  let S : Finset ι := {t,i,j}
  have h1 := root_mem_local S i j hij a (by simp [S]) (by simp [S])
  have h2 := root_mem_local S t i hti b (by simp [S]) (by simp [S])
  have h3 := root_mem_local S t j htj (-(b*a)) (by simp [S]) (by simp [S])
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem h1 h2) ((localGroup S).inv_mem h1))
    ((localGroup S).mul_mem h3 h2)
  simp only [map_mul,map_inv,evaluate_root]
  apply Units.ext
  change (1+Matrix.single i j a) * (1+Matrix.single t i b) * (1+Matrix.single i j (-a)) =
    (1+Matrix.single t j (-(b*a))) * (1+Matrix.single t i b)
  simp [add_mul,mul_add,htj.symm,hij.symm,←Matrix.single_neg]
  abel

lemma root_conjugate_row_mem (t i j : ι) (hij : i≠j) (_hit : i≠t) (hjt : j≠t)
    (a : R) (k : ι) (htk : t≠k) (b : R) :
    root i j hij a * root t k htk b * (root i j hij a)⁻¹ ∈ rowGroup t := by
  by_cases hk : k=i
  · subst k
    rw [root_conjugate_reverse t i j htk hjt.symm hij]
    exact (rowGroup t).mul_mem (root_mem_row _ _ _ _) (root_mem_row _ _ _ _)
  · rw [(root_commute i j t k hij htk hjt (Ne.symm hk) a b).eq,mul_inv_cancel_right]
    exact root_mem_row _ _ _ _

lemma diag_conjugate_root_matrix (i t j : ι) (htj : t≠j) (u : Rˣ) (b : R) :
    singleDiagonal i u * elementary t j htj b * (singleDiagonal i u)⁻¹ =
    elementary t j htj ((if t=i then (u:R) else 1)*b*(if j=i then (u⁻¹:Rˣ).val else 1)) := by
  apply Units.ext
  ext k l
  change ((Matrix.diagonal (fun k => (if k=i then u else 1).val) *
    (1+Matrix.single t j b)) * Matrix.diagonal (fun k => (if k=i then u else 1).inv)) k l = _
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,elementary_val,Matrix.add_apply,
    Matrix.one_apply,Matrix.single_apply]
  by_cases hkl : k=l
  · subst l
    have hn : ¬(t=k ∧ j=k) := by rintro ⟨rfl,rfl⟩; exact htj rfl
    simp only [ite_eq_right hn,add_zero]
    by_cases hk : k=i <;> simp [hk]
  · by_cases hkt : t=k
    · subst k
      by_cases hjl : j=l
      · subst l; by_cases hti : t=i <;> by_cases hji : j=i <;> simp_all
      · simp [hkl,hjl]
    · simp [hkl,hkt]

lemma diag_conjugate_root (i t j : ι) (htj : t≠j) (u : Rˣ) (b : R) :
    diag i u * root t j htj b * (diag i u)⁻¹ =
    root t j htj ((if t=i then (u:R) else 1)*b*(if j=i then (u⁻¹:Rˣ).val else 1)) := by
  let S : Finset ι := {i,t,j}
  have h1 := diag_mem_local S i u (by simp [S])
  have h2 := root_mem_local S t j htj b (by simp [S]) (by simp [S])
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem h1 h2) ((localGroup S).inv_mem h1))
    (root_mem_local S _ _ _ _ (by simp [S]) (by simp [S]))
  simpa only [map_mul,map_inv,evaluate_root,evaluate_diag] using diag_conjugate_root_matrix i t j htj u b

lemma root_normalizes_row (t i j : ι) (hij : i≠j) (hit : i≠t) (hjt : j≠t) (a : R) :
    root i j hij a ∈ Subgroup.normalizer (rowGroup (R := R) t : Set _) := by
  have hh (a : R) : rowGroup t ≤ (rowGroup t).comap (MulAut.conj (root i j hij a)).toMonoidHom := by
    apply rowGroup_le
    intro k htk b
    exact root_conjugate_row_mem t i j hij hit hjt a k htk b
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx; exact hh a hx
  · intro hx
    have he := hh (-a) hx
    change root i j hij (-a) * (root i j hij a * x * (root i j hij a)⁻¹) * (root i j hij (-a))⁻¹ ∈ rowGroup t at he
    simpa only [MulAut.conj_apply,root_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

lemma diag_normalizes_row (t i : ι) (u : Rˣ) :
    diag i u ∈ Subgroup.normalizer (rowGroup (R := R) t : Set _) := by
  have hh (u : Rˣ) : rowGroup t ≤ (rowGroup t).comap (MulAut.conj (diag i u)).toMonoidHom := by
    apply rowGroup_le
    intro j htj b
    change diag i u * root t j htj b * (diag i u)⁻¹ ∈ rowGroup t
    rw [diag_conjugate_root]
    exact root_mem_row _ _ _ _
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx; exact hh u hx
  · intro hx
    have he := hh u⁻¹ hx
    change diag i u⁻¹ * (diag i u * x * (diag i u)⁻¹) * (diag i u⁻¹)⁻¹ ∈ rowGroup t at he
    simpa only [MulAut.conj_apply,diag_inv,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

def complementary (t : ι) : Subgroup (Group (ι := ι) (R := R)) := localGroup (Finset.univ.erase t)
def parabolic (t : ι) : Subgroup (Group (ι := ι) (R := R)) := complementary t ⊔ rowGroup t

lemma complementary_normalizes_row (t : ι) :
    complementary (R := R) t ≤ Subgroup.normalizer (rowGroup (R := R) t : Set (Group (ι := ι) (R := R))) := by
  rw [complementary,localGroup_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g,hg,rfl⟩
  cases g with
  | root i j h a =>
    obtain ⟨hi,hj⟩ := Finset.insert_subset_iff.mp hg
    have hi' : i≠t := (Finset.mem_erase.mp hi).1
    have hj' : j≠t := (Finset.mem_erase.mp (Finset.singleton_subset_iff.mp hj)).1
    exact root_normalizes_row t i j h hi' hj' a
  | diag i u => exact diag_normalizes_row t i u

lemma parabolic_decomposition (t : ι) {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) :
    ∃l∈complementary t, ∃r∈rowGroup t, g=l*r := by
  have he := Subgroup.coe_mul_of_left_le_normalizer_right (complementary (R := R) t) (rowGroup t)
    (complementary_normalizes_row t)
  change g∈(↑(complementary (R := R) t ⊔ rowGroup t) : Set (Group (ι := ι) (R := R))) at hg
  rw [he] at hg
  obtain ⟨l,hl,r,hr,hg⟩ := hg
  exact ⟨l,hl,r,hr,hg.symm⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma embedded_row_eq_one (S : Finset ι) (t : ι) (ht : t∉S)
    (U : (Matrix {i // i∈S} {i // i∈S} R)ˣ)
    (A : {j : ι // j≠t} → Multiplicative R)
    (h : embed (Function.Embedding.subtype (·∈S)) U * rowUnits t A =1) : U=1 := by
  have hx : embed (Function.Embedding.subtype (·∈S)) U = rowUnits t A⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  apply Units.ext
  ext i j
  have hh := congrArg (fun V : (Matrix ι ι R)ˣ => V.val i.val j.val) hx
  have hh : U.val i j = (rowUnits t A⁻¹).val i.val j.val :=
    (embed_entry (R := R) (Function.Embedding.subtype (·∈S)) U i j).symm.trans hh
  have hi : i.val≠t := fun he => ht (he ▸ i.property)
  change U.val i j = (1+rowMatrix t A⁻¹) i.val j.val at hh
  simpa only [Matrix.add_apply,rowMatrix,ite_eq_right hi,add_zero,Units.val_one,Matrix.one_apply,Subtype.coe_inj] using hh

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma root_mem_parabolic (t i j : ι) (h : i≠j) (a : R) (hj : j≠t) :
    root i j h a ∈ parabolic t := by
  by_cases hi : i=t
  · subst i
    exact (show rowGroup t ≤ parabolic (R := R) t from le_sup_right) (root_mem_row _ _ _ _)
  · apply (show complementary t ≤ parabolic (R := R) t from le_sup_left)
    exact root_mem_local _ _ _ _ _ (by simp [hi]) (by simp [hj])

lemma diag_mem_parabolic (t i : ι) (u : Rˣ) (hi : i≠t) : diag i u ∈ parabolic t := by
  apply (show complementary t ≤ parabolic (R := R) t from le_sup_left)
  exact diag_mem_local _ _ _ (by simp [hi])

lemma parabolic_le {t : ι} {P : Subgroup (Group (ι := ι) (R := R))}
    (he : ∀ i j h a, j≠t → root i j h a∈P)
    (hd : ∀ i u, i≠t → diag i u∈P) : parabolic t ≤ P := by
  apply sup_le
  · rw [complementary,localGroup_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨g,hg,rfl⟩
    cases g with
    | root i j h a =>
      exact he _ _ _ _ (Finset.mem_erase.mp (Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp hg).2)).1
    | diag i u => exact hd _ _ (Finset.mem_erase.mp (Finset.singleton_subset_iff.mp hg)).1
  · apply rowGroup_le
    intro j h a
    exact he _ _ _ _ h.symm

lemma evaluate_parabolic_le (t : ι) : (parabolic (R := R) t).map evaluate ≤ fixer {t} := by
  rw [Subgroup.map_le_iff_le_comap]
  apply parabolic_le
  · intro i j h a hj
    change evaluate (root i j h a) ∈ fixer {t}
    rw [evaluate_root]
    exact elementary_mem_fixer _ _ _ _ _ (by simpa using hj)
  · intro i u hi
    change evaluate (diag i u) ∈ fixer {t}
    rw [evaluate_diag]
    exact singleDiagonal_mem_fixer _ _ _ (by simpa using hi)

lemma parabolic_product_kernel (t : ι)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    (l : Group (ι := {i // i∈Finset.univ.erase t}) (R := R))
    (A : {j : ι // j≠t} → Multiplicative R)
    (he : evaluate (inclusion (Function.Embedding.subtype (·∈Finset.univ.erase t)) l * rowHom t A)=1) :
    inclusion (Function.Embedding.subtype (·∈Finset.univ.erase t)) l * rowHom t A=1 := by
  have hmap : embed (Function.Embedding.subtype (·∈Finset.univ.erase t)) (evaluate l) * rowUnits t A = 1 := by
    simpa only [map_mul,evaluate_inclusion_apply,evaluate_rowHom_apply] using he
  have hl1 : evaluate l=1 := embedded_row_eq_one (Finset.univ.erase t) t
    (Finset.notMem_erase t Finset.univ) (evaluate l) A hmap
  have hl0 : l=1 := ih (hl1.trans (evaluate.map_one).symm)
  simp only [hl0,map_one,one_mul] at he ⊢
  exact row_faithful (R := R) t (g := rowHom t A) (h := 1) ⟨A,rfl⟩ (rowGroup t).one_mem (he.trans (evaluate.map_one).symm)

lemma parabolic_kernel_trivial (t : ι)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) (he : evaluate g=1) : g=1 := by
  obtain ⟨l,hl,r,hr,rfl⟩ := parabolic_decomposition t hg
  rw [complementary,←range_inclusion] at hl
  obtain ⟨l,rfl⟩ := hl
  obtain ⟨A,rfl⟩ := hr
  exact parabolic_product_kernel t ih l A he

lemma parabolic_faithful (t : ι)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    {g h : Group (ι := ι) (R := R)} (hg : g∈parabolic t) (hh : h∈parabolic t)
    (he : evaluate g=evaluate h) : g=h := by
  apply mul_inv_eq_one.mp
  apply parabolic_kernel_trivial t ih ((parabolic t).mul_mem hg ((parabolic t).inv_mem hh))
  simp [he]

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma permutation_conjugate_elementary (p : Equiv.Perm ι) (i j : ι) (h : i≠j) (a : R) :
    permutation p * elementary i j h a * (permutation p)⁻¹ =
      elementary (p i) (p j) (p.injective.ne h) a := by
  rw [permutation_conjugate,relabel_elementary]

lemma permutation_smul (p : Equiv.Perm ι) (v : ι → R) :
    permutation (R := R) p • v = v ∘ p.symm := by
  ext i
  change ∑ j, (permutation p).val i j * v j = v (p.symm i)
  simp only [permutation_entry,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_eq_single (p.symm i)]
  · simp
  · intro j _ hj
    rw [ite_eq_right]
    intro he
    exact hj ((p.injective (by simpa using he.symm)))
  · simp

@[simp] lemma permutation_smul_single (p : Equiv.Perm ι) (i : ι) :
    permutation (R := R) p • (Pi.single i 1 : ι → R) = Pi.single (p i) 1 := by
  rw [permutation_smul]
  ext j
  simp [Pi.single_apply,Function.comp_apply,Equiv.symm_apply_eq]

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def swap (i j : ι) (h : i≠j) : Group (ι := ι) (R := R) :=
  root i j h 1 * root j i h.symm (-1) * root i j h 1 * diag i (-1)

lemma swap_mem_local (S : Finset ι) (i j : ι) (h : i≠j) (hi : i∈S) (hj : j∈S) :
    swap (R := R) i j h ∈ localGroup S :=
  (localGroup S).mul_mem ((localGroup S).mul_mem
    ((localGroup S).mul_mem (root_mem_local S i j h 1 hi hj) (root_mem_local S j i h.symm (-1) hj hi))
    (root_mem_local S i j h 1 hi hj)) (diag_mem_local S i (-1) hi)

lemma evaluate_swap (i j : ι) (h : i≠j) : evaluate (swap (R := R) i j h) = permutation (Equiv.swap i j) := by
  simp only [swap,map_mul,evaluate_root,evaluate_diag]
  apply Units.ext
  ext k l
  change (((1+Matrix.single i j (1:R)) * (1+Matrix.single j i (-1:R)) *
    (1+Matrix.single i j (1:R))) * Matrix.diagonal (fun k => (if k=i then (-1:Rˣ) else 1).val)) k l = _
  rw [Matrix.mul_diagonal,permutation_entry]
  simp only [add_mul,mul_add,one_mul,mul_one]
  simp only [Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,mul_one,mul_neg]
  simp only [Matrix.add_apply,Matrix.single_apply,Matrix.one_apply,add_zero]
  by_cases hki : k=i <;> by_cases hkj : k=j <;> by_cases hli : l=i <;> by_cases hlj : l=j <;>
    simp_all [Equiv.swap_apply_def,eq_comm]

lemma swap_square (i j : ι) (h : i≠j) : swap (R := R) i j h * swap i j h =1 := by
  have hm := swap_mem_local (R := R) {i,j} i j h (by simp) (by simp)
  apply local_faithful {i,j} (by have := Finset.card_insert_le i ({j}:Finset ι); simp only [Finset.card_singleton] at this; omega)
    ((localGroup _).mul_mem hm hm) (localGroup _).one_mem
  rw [map_mul,evaluate_swap,←map_mul,Equiv.swap_mul_self,map_one,map_one]

lemma swap_braid (i j k : ι) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    swap (R := R) i j hij * swap j k hjk * swap i j hij = swap j k hjk * swap i j hij * swap j k hjk := by
  let S : Finset ι := {i,j,k}
  have hs := swap_mem_local (R := R) S i j hij (by simp [S]) (by simp [S])
  have ht := swap_mem_local (R := R) S j k hjk (by simp [S]) (by simp [S])
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem hs ht) hs)
    ((localGroup S).mul_mem ((localGroup S).mul_mem ht hs) ht)
  simp only [map_mul,evaluate_swap]
  rw [←map_mul,←map_mul,←map_mul,←map_mul]
  congr 1
  rw [Equiv.swap_mul_swap_mul_swap hij hik]
  rw [Equiv.swap_comm i j,Equiv.swap_comm j k,Equiv.swap_mul_swap_mul_swap hjk.symm hik.symm,Equiv.swap_comm]

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_SmallSwapActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma swap_inv (i j : ι) (h : i≠j) : (swap (R := R) i j h)⁻¹ = swap i j h :=
  (eq_inv_of_mul_eq_one_left (swap_square i j h)).symm

lemma swap_conjugate_root (a b : ι) (hab : a≠b) (i j : ι) (hij : i≠j) (r : R) :
    swap a b hab * root i j hij r * (swap a b hab)⁻¹ =
    root (Equiv.swap a b i) (Equiv.swap a b j) ((Equiv.swap a b).injective.ne hij) r := by
  let S : Finset ι := {a,b,i,j}
  have hs := swap_mem_local (R := R) S a b hab (by simp [S]) (by simp [S])
  have hr := root_mem_local S i j hij r (by simp [S]) (by simp [S])
  have hi : Equiv.swap a b i ∈ S := by simp only [Equiv.swap_apply_def]; split_ifs <;> simp [S]
  have hj : Equiv.swap a b j ∈ S := by simp only [Equiv.swap_apply_def]; split_ifs <;> simp [S]
  apply local_faithful S (card_quad_le _ _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem hs hr) ((localGroup S).inv_mem hs))
    (root_mem_local S _ _ _ _ hi hj)
  simpa only [map_mul,map_inv,evaluate_swap,evaluate_root] using permutation_conjugate_elementary (Equiv.swap a b) i j hij r

lemma swap_conjugate_diag (a b : ι) (hab : a≠b) (i : ι) (u : Rˣ) :
    swap a b hab * diag i u * (swap a b hab)⁻¹ = diag (Equiv.swap a b i) u := by
  let S : Finset ι := {a,b,i}
  have hs := swap_mem_local (R := R) S a b hab (by simp [S]) (by simp [S])
  have hd := diag_mem_local S i u (by simp [S])
  have hi : Equiv.swap a b i ∈ S := by simp only [Equiv.swap_apply_def]; split_ifs <;> simp [S]
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem hs hd) ((localGroup S).inv_mem hs))
    (diag_mem_local S _ _ hi)
  simpa only [map_mul,map_inv,evaluate_swap,evaluate_diag] using permutation_conjugate_diagonal (Equiv.swap a b) i u

lemma swap_mem_parabolic (t i j : ι) (hij : i≠j) (hi : i≠t) (hj : j≠t) :
    swap (R := R) i j hij∈parabolic t := by
  unfold swap
  exact (parabolic t).mul_mem ((parabolic t).mul_mem
    ((parabolic t).mul_mem (root_mem_parabolic t i j hij 1 hj) (root_mem_parabolic t j i hij.symm (-1) hi))
    (root_mem_parabolic t i j hij 1 hj)) (diag_mem_parabolic t i (-1) hi)

lemma parabolic_swap_generates (t a : ι) (hta : t≠a) :
    Subgroup.closure ((parabolic (R := R) t : Set (Group (ι := ι) (R := R))) ∪ {swap t a hta}) = ⊤ := by
  let P : Subgroup (Group (ι := ι) (R := R)) := Subgroup.closure ((parabolic (R := R) t : Set (Group (ι := ι) (R := R))) ∪ {swap t a hta})
  have hp : parabolic t ≤ P := fun _ hg => Subgroup.subset_closure (Or.inl hg)
  have hs : swap t a hta ∈ P := Subgroup.subset_closure (Or.inr rfl)
  apply top_unique
  rw [←supported_gen_all]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g,rfl⟩
  cases g with
  | root i j h r =>
    change root i j h r ∈ P
    by_cases hj : j≠t
    · exact hp (root_mem_parabolic t i j h r hj)
    · have hjt := not_ne_iff.mp hj
      let p := Equiv.swap t a
      have hpa : p j≠t := by simp [p,hjt,hta.symm]
      have hm := P.mul_mem (P.mul_mem hs (hp (root_mem_parabolic t (p i) (p j) (p.injective.ne h) r hpa))) (P.inv_mem hs)
      rw [swap_conjugate_root] at hm
      simpa only [p,Equiv.swap_apply_self] using hm
  | diag i u =>
    change diag i u ∈ P
    by_cases hi : i≠t
    · exact hp (diag_mem_parabolic t i u hi)
    · have hit := not_ne_iff.mp hi
      let p := Equiv.swap t a
      have hpa : p i≠t := by simp [p,hit,hta.symm]
      have hm := P.mul_mem (P.mul_mem hs (hp (diag_mem_parabolic t (p i) u hpa))) (P.inv_mem hs)
      rw [swap_conjugate_diag] at hm
      simpa only [p,Equiv.swap_apply_self] using hm

def fixingGroup (S : Finset ι) : Subgroup (Group (ι := ι) (R := R)) :=
  Subgroup.closure ({g | ∃i j h a, j∉S ∧ g=root i j h a} ∪ {g | ∃i u, i∉S ∧ g=diag i u})

lemma fixingGroup_le_parabolic (S : Finset ι) (t : ι) (ht : t∈S) : fixingGroup (R := R) S ≤ parabolic t := by
  apply (Subgroup.closure_le _).mpr
  rintro x (⟨i,j,h,a,hj,rfl⟩ | ⟨i,u,hi,rfl⟩)
  · exact root_mem_parabolic t i j h a (fun he => hj (he ▸ ht))
  · exact diag_mem_parabolic t i u (fun he => hi (he ▸ ht))

lemma swap_conjugate_fixingGroup_le (t a : ι) (hta : t≠a) :
    fixingGroup (R := R) {t,a} ≤ (parabolic t).comap (MulAut.conj (swap t a hta)).toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  rintro x (⟨i,j,h,r,hj,rfl⟩ | ⟨i,u,hi,rfl⟩)
  · change swap t a hta * root i j h r * (swap t a hta)⁻¹ ∈ parabolic t
    rw [swap_conjugate_root]
    exact root_mem_parabolic _ _ _ _ _ (by
      have hjt : j≠t := fun he => hj (by simp [he])
      have hja : j≠a := fun he => hj (by simp [he])
      simpa only [Equiv.swap_apply_of_ne_of_ne hjt hja] using hjt)
  · change swap t a hta * diag i u * (swap t a hta)⁻¹ ∈ parabolic t
    rw [swap_conjugate_diag]
    exact diag_mem_parabolic _ _ _ (by
      have hit : i≠t := fun he => hi (by simp [he])
      have hia : i≠a := fun he => hi (by simp [he])
      simpa only [Equiv.swap_apply_of_ne_of_ne hit hia] using hit)

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.ColumnFrames
noncomputable section
open Classical MatrixGenerators
open scoped Matrix
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def cones (hι : 5 < Fintype.card ι) : Frames.ConeSupply (F := ZMod 2) (rho (ι := ι) ε) 5 := by
  letI : LinearOrder (Vertex (ι := ι) ε) := linearOrderOfSTO WellOrderingRel
  exact Frames.coneSupply (F := ZMod 2) (rho ε) (rho_spanning ε) 5 (by simpa using hι)

@[simp] lemma permutation_standard (p : Equiv.Perm ι) (i : ι) :
    permutation (R := R) p • standard ε i = standard ε (p i) := by
  apply Subtype.ext
  exact permutation_smul_single p i

lemma complete {κ : Type*} (hI : MatrixNilKernel ε.toRingHom) (j : κ ↪ ι)
    (v : κ → Vertex (ι := ι) ε) (hv : LinearIndependent (ZMod 2) (rho ε ∘ v)) :
    ∃U : (Matrix ι ι R)ˣ, ∀k, U • standard ε (j k) = v k := by
  obtain ⟨U,hU⟩ := LinearAlgebra.complete_columns ε hI j (fun k => (v k).val) hv
  refine ⟨U,fun k => ?_⟩
  apply Subtype.ext
  ext i
  change (U.val *ᵥ Pi.single (j k) 1) i = (v k).val i
  simpa using hU k i

end
end SourceBurnside.Stability.ColumnFrames

end
section
namespace SourceBurnside.Stability.ColumnFrames
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
open scoped Matrix
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

lemma mem_fixer_iff_standard (S : Finset ι) (U : (Matrix ι ι R)ˣ) :
    U∈fixer S ↔ ∀k∈S, U • standard ε k = standard ε k := by
  simp only [fixer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h k hk
    exact Subtype.ext (h ⟨k,hk⟩)
  · intro h k
    exact congrArg Subtype.val (h k.val k.property)

lemma edge_transitive (hI : MatrixNilKernel ε.toRingHom) (t a : ι) (hta : t≠a)
    (v : Vertex (ι := ι) ε) (hv : FrameTransport.Edge (F := ZMod 2) (rho ε) (standard ε t) v) :
    ∃U : (Matrix ι ι R)ˣ, U∈fixer {t} ∧ U • standard ε a = v := by
  let j : Fin 2 ↪ ι := ⟨![t,a],pair_injective t a hta⟩
  let w : Fin 2 → Vertex (ι := ι) ε := ![standard ε t,v]
  have hw : LinearIndependent (ZMod 2) (rho ε ∘ w) := by
    apply (linearIndepOn_range_iff (pair_injective (standard ε t) v hv.1) (rho ε)).mp
    simpa only [Matrix.range_cons_cons_empty] using hv.2
  obtain ⟨U,hU⟩ := complete ε hI j w hw
  refine ⟨U,?_,?_⟩
  · rw [mem_fixer_iff_standard ε]
    intro k hk
    have hkt : k=t := by simpa using hk
    subst k
    simpa [j,w] using hU 0
  · simpa [j,w] using hU 1

lemma triangle_transitive (hI : MatrixNilKernel ε.toRingHom) (t a b : ι)
    (hta : t≠a) (htb : t≠b) (hab : a≠b) (v w : Vertex (ι := ι) ε)
    (htv : standard ε t ≠ v) (htw : standard ε t ≠ w) (hvw : v≠w)
    (h : LinearIndepOn (ZMod 2) (rho ε) {standard ε t,v,w}) :
    ∃U : (Matrix ι ι R)ˣ, U∈fixer {t} ∧ U • standard ε a=v ∧ U • standard ε b=w := by
  let j : Fin 3 ↪ ι := ⟨![t,a,b],triple_injective t a b hta htb hab⟩
  let f : Fin 3 → Vertex (ι := ι) ε := ![standard ε t,v,w]
  have hf : LinearIndependent (ZMod 2) (rho ε ∘ f) := by
    apply (linearIndepOn_range_iff (triple_injective (standard ε t) v w htv htw hvw) (rho ε)).mp
    simpa [Set.insert_comm,Set.pair_comm] using h
  obtain ⟨U,hU⟩ := complete ε hI j f hf
  refine ⟨U,?_,?_,?_⟩
  · rw [mem_fixer_iff_standard ε]
    intro k hk
    have hkt : k=t := by simpa using hk
    subst k
    simpa [j,f] using hU 0
  · simpa [j,f] using hU 1
  · simpa [j,f] using hU 2

end
end SourceBurnside.Stability.ColumnFrames

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_SmallFaithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

instance columnAction : MulAction (Group (ι := ι) (R := R)) (ColumnFrames.Vertex (ι := ι) ε) :=
  MulAction.compHom _ evaluate

@[simp] lemma column_smul (g : Group (ι := ι) (R := R)) (v : ColumnFrames.Vertex (ι := ι) ε) :
    g • v = evaluate g • v := rfl

lemma parabolic_fix (t : ι) {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) :
    g • ColumnFrames.standard ε t = ColumnFrames.standard ε t := by
  apply (ColumnFrames.mem_fixer_iff_standard ε {t} (evaluate g)).mp
    (evaluate_parabolic_le t ⟨g,hg,rfl⟩) t (by simp)

lemma swap_smul (t a : ι) (hta : t≠a) (i : ι) :
    swap (R := R) t a hta • ColumnFrames.standard ε i = ColumnFrames.standard ε (Equiv.swap t a i) := by
  rw [column_smul,evaluate_swap,ColumnFrames.permutation_standard]

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical
universe u v

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_DiagonalActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.MatrixK1
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def E : Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure {g | ∃i j h a, g = elementary i j h a}

lemma elementary_mem (i j : ι) (h : i≠j) (a : R) : elementary i j h a ∈ E :=
  Subgroup.subset_closure ⟨i,j,h,a,rfl⟩

end
end SourceBurnside.Stability.MatrixK1

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_ElementaryFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.MatrixK1
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end SourceBurnside.Stability.MatrixK1

namespace SourceBurnside.Stability
open Classical MatrixGenerators MatrixK1 CategoryTheory
namespace ColumnRelabel
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (e : ι ≃ κ)

omit [Algebra (ZMod 2) R] in
lemma relabel_elementary_mem {U : (Matrix ι ι R)ˣ} (hU : U∈E) : relabel e U∈E := by
  have h : E (R := R) (ι := ι) ≤ (E (R := R) (ι := κ)).comap (relabel e) := by
    apply (Subgroup.closure_le _).mpr
    rintro U ⟨i,j,hij,a,rfl⟩
    change relabel e (elementary i j hij a) ∈ E
    rw [relabel_elementary]
    exact elementary_mem _ _ _ _
  exact h hU

def elementaryEquiv : E (R := R) (ι := ι) ≃* E (R := R) (ι := κ) where
  toFun U := ⟨relabel e U.val,relabel_elementary_mem e U.property⟩
  invFun U := ⟨relabel e.symm U.val,relabel_elementary_mem e.symm U.property⟩
  left_inv U := Subtype.ext (LinearAlgebra.relabel_symm_apply e.symm U.val)
  right_inv U := Subtype.ext (LinearAlgebra.relabel_symm_apply e U.val)
  map_mul' _left _right := Subtype.ext (map_mul _ _ _)

def vertexEquiv : ColumnFrames.Vertex (ι := ι) ε ≃ ColumnFrames.Vertex (ι := κ) ε where
  toFun v := ⟨v.val ∘ e.symm,by
    intro hz
    apply v.property
    ext i
    have h := congrFun hz (e i)
    simpa [ColumnFrames.residue,Function.comp_def] using h⟩
  invFun v := ⟨v.val ∘ e,by
    intro hz
    apply v.property
    ext i
    have h := congrFun hz (e.symm i)
    simpa [ColumnFrames.residue,Function.comp_def] using h⟩
  left_inv v := Subtype.ext (by funext i; simp)
  right_inv v := Subtype.ext (by funext i; simp)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma rho_vertex (v : ColumnFrames.Vertex (ι := ι) ε) :
    ColumnFrames.rho ε (vertexEquiv ε e v) = coordinateEquiv (F := ZMod 2) e (ColumnFrames.rho ε v) := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma independent (s : Set (ColumnFrames.Vertex (ι := ι) ε))
    (hs : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) s) :
    LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) (vertexEquiv ε e '' s) := by
  have h := hs.map_injOn (coordinateEquiv (F := ZMod 2) e).toLinearMap
    (fun a _ b _ hab => (coordinateEquiv (F := ZMod 2) e).injective hab)
  have hh : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε ∘ vertexEquiv ε e) s :=
    h.congr (fun v _ => (rho_vertex ε e v).symm)
  exact hh.image_of_comp (vertexEquiv ε e) (ColumnFrames.rho ε)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma independent_symm (s : Set (ColumnFrames.Vertex (ι := κ) ε))
    (hs : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) s) :
    LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) ((vertexEquiv ε e).symm '' s) :=
  independent ε e.symm s hs

lemma vertex_action (g : E (R := R) (ι := ι)) (v : ColumnFrames.Vertex (ι := ι) ε) :
    vertexEquiv ε e (g • v) = elementaryEquiv e g • vertexEquiv ε e v := by
  apply Subtype.ext
  ext j
  change (∑i, g.val.val (e.symm j) i * v.val i) =
    ∑k, g.val.val (e.symm j) (e.symm k) * v.val (e.symm k)
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

lemma independent_action (g : E (R := R) (ι := ι))
    (s : Set (ColumnFrames.Vertex (ι := ι) ε)) (hs : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) s) :
    LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) ((g • ·) '' s) := ColumnFrames.independent_map ε g.val hs

variable [LinearOrder (ColumnFrames.Vertex (ι := ι) ε)]
variable [LinearOrder (ColumnFrames.Vertex (ι := κ) ε)]

def homologyIso (k n : ℕ) :
    groupHomology (Frames.chainRep (E (R := R) (ι := ι)) (ρ := ColumnFrames.rho ε) (independent_action ε) k) n ≅
    groupHomology (Frames.chainRep (E (R := R) (ι := κ)) (ρ := ColumnFrames.rho ε) (independent_action ε) k) n :=
  Frames.chainHomologyIso (ColumnFrames.rho ε) (ColumnFrames.rho ε) (vertexEquiv ε e)
    (independent ε e) (independent_symm ε e) (independent_action ε) (independent_action ε)
    (elementaryEquiv e) (vertex_action ε e) k n

end ColumnRelabel
end SourceBurnside.Stability

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_LocallyFiniteActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.UnorderedStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators MatrixK1
open scoped Pointwise
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

abbrev rightVertex (j : κ) : ColumnFrames.Vertex (ι := ι ⊕ κ) ε :=
  ColumnFrames.standard ε (Sum.inr j)

lemma rightVertex_injective : Function.Injective (rightVertex (ι := ι) (κ := κ) ε) :=
  (ColumnFrames.standard_injective ε).comp Sum.inr_injective

abbrev K : Subgroup (E (R := R) (ι := ι ⊕ κ)) :=
  MulAction.stabilizer _ (Set.range (rightVertex (ι := ι) (κ := κ) ε))

def permRight : Equiv.Perm κ →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
  permutation.comp (Equiv.Perm.sumCongrHom ι κ |>.comp ((1 : Equiv.Perm κ →* Equiv.Perm ι).prod (MonoidHom.id _)))

end SourceBurnside.Stability.UnorderedStabilizer

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_FiniteNormalHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
namespace FrameStabilizer
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)]

abbrev V := ColumnFrames.Vertex (ι := ι ⊕ κ) ε
abbrev G := E (R := R) (ι := ι ⊕ κ)
abbrev rho := ColumnFrames.rho (ι := ι ⊕ κ) ε
omit [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)] in
lemma independent_action (g : G (R := R) (ι := ι) (κ := κ))
    (s : Set (V (ι := ι) (κ := κ) ε)) (hs : LinearIndepOn (ZMod 2) (rho ε) s) :
    LinearIndepOn (ZMod 2) (rho ε) ((g • ·) '' s) := ColumnFrames.independent_map ε g.val hs

abbrev index := Frames.Index (F := ZMod 2) (rho (ι := ι) (κ := κ) ε) (Fintype.card κ)
local instance instMulActionSubtypeUnitsMatrixSumMemSubgroupGIndex : MulAction (G (R := R) (ι := ι) (κ := κ)) (index (ι := ι) (κ := κ) ε) :=
  Frames.indexAction (rho ε) (G (R := R) (ι := ι) (κ := κ)) (independent_action ε) (Fintype.card κ)

abbrev right := UnorderedStabilizer.rightVertex (ι := ι) (κ := κ) ε

def base : index (ι := ι) (κ := κ) ε :=
  ⟨Finset.univ.image (right ε), by
    constructor
    · exact Finset.card_image_of_injective _ (UnorderedStabilizer.rightVertex_injective ε)
    · have hi := ColumnFrames.standard_independent (ι := ι ⊕ κ) ε (Set.range Sum.inr)
      simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ,←Set.range_comp,
        rho,right,UnorderedStabilizer.rightVertex,Function.comp_def] using hi⟩

lemma base_coe : ((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε)) = Set.range (right ε) := by
  simp [base]

lemma stabilizer_eq : MulAction.stabilizer (G (R := R) (ι := ι) (κ := κ)) (base (ι := ι) (κ := κ) ε) =
    UnorderedStabilizer.K (ι := ι) (κ := κ) ε := by
  ext g
  rw [MulAction.mem_stabilizer_iff,MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hh := congrArg (fun x : index (ι := ι) (κ := κ) ε => (x.val : Set (V (ι := ι) (κ := κ) ε))) h
    simpa only [Frames.indexAction_val,Finset.coe_image,base_coe,Set.image_smul] using hh
  · intro h
    apply Subtype.ext
    apply Finset.coe_injective
    rw [Frames.indexAction_val,Finset.coe_image,base_coe,Set.image_smul]
    exact h

def stabilizerEquiv : MulAction.stabilizer (G (R := R) (ι := ι) (κ := κ)) (base (ι := ι) (κ := κ) ε) ≃*
    UnorderedStabilizer.K (ι := ι) (κ := κ) ε := MulEquiv.subgroupCongr (stabilizer_eq (ι := ι) (κ := κ) ε)

end FrameStabilizer
end SourceBurnside.Stability

namespace SourceBurnside.Stability.FrameStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise

end SourceBurnside.Stability.FrameStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory MatrixGenerators MatrixK1 Representation

namespace SingletonFrameEdge
variable {R ι : Type} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ Fin 1) ε)]
local notation "G" => E (R := R) (ι := ι ⊕ Fin 1)
local instance instMulActionSubtypeUnitsMatrixSumFinOfNatNatMemSubgroupEIndex : MulAction G (FrameStabilizer.index (ι := ι) (κ := Fin 1) ε) :=
  Frames.indexAction (FrameStabilizer.rho ε) G (FrameStabilizer.independent_action ε) 1

end SingletonFrameEdge
end SourceBurnside.Stability

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_RankActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.ElementaryRanks
open Classical CategoryTheory MatrixGenerators MatrixK1
variable {R : Type} [Ring R]

abbrev Group (n : ℕ) := E (R := R) (ι := Fin n)

end SourceBurnside.Stability.ElementaryRanks

end

end OAI
end


