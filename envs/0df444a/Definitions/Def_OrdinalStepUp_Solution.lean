-- Prove2me | Definitions.Def_OrdinalStepUp_Solution
-- name    : OrdinalStepUp_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T04:47:07.618808+00:00
-- url     : https://prove2.me/theorems/24e759b6-adee-4493-abe5-db91d2155ca1
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from bjrtx/ordinal-step-up contributors (see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Erdos-Rado negative stepping-up lemma for ordinal order types development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
set_option autoImplicit true
namespace OrdinalStepUp.ErdosRado
open Ordinal
universe u
abbrev SetOrd := Set Ordinal
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
noncomputable def disc (a b : SetOrd) : Ordinal := sInf (symmDiff a b)
lemma disc_comm (a b : SetOrd) : disc a b = disc b a := by
  rw [disc, disc, symmDiff_comm]
lemma disc_mem_symmDiff (_ : a ≠ b) : disc a b ∈ (a \ b) ∪ (b \ a) := by
  apply csInf_mem
  simp_all [← Set.symmDiff_def]
lemma mem_iff_of_lt_disc (h : α < disc a b) : α ∈ a ↔ α ∈ b := by
  have : α ∉ (a \ b) ∪ (b \ a) := fun hmem => absurd (csInf_le' hmem) (not_le.mpr h)
  constructor <;> simp_all
def LexLT (a b : SetOrd) : Prop := disc a b ∈ b \ a
@[inherit_doc LexLT] scoped infix:50 " ≺ " => LexLT
lemma disc_eq_of_agree_before_and_differ_at
    (hagree : ∀ β < α, (β ∈ a ↔ β ∈ b)) (ha : α ∉ a) (hb : α ∈ b) :
    disc a b = α := by
  have hab : a ≠ b := (·.symm ▸ hb |> ha)
  refine le_antisymm (csInf_le' (Or.inr ⟨hb, ha⟩)) (not_lt.1 fun hlt => ?_)
  rcases disc_mem_symmDiff hab <;> simp_all [hagree _ hlt]
lemma lexLT_of_agree_before_and_differ_at
    (hagree : ∀ β < α, (β ∈ a ↔ β ∈ b)) (ha : α ∉ a) (hb : α ∈ b) : a ≺ b := by
  split_ands <;> simp_all [disc_eq_of_agree_before_and_differ_at hagree ha hb]
lemma lexLT_trans (hab : a ≺ b) (hbc : b ≺ c) : a ≺ c := by
  unfold LexLT at *
  -- Below either split point `a` and `c` agree, both agreeing with `b` there.
  have key {s t} (h1: t ≤ disc a b) (h2: t ≤ disc b c) (hs: s < t): (s ∈ a ↔ s ∈ c) :=
    (mem_iff_of_lt_disc (hs.trans_le h1)).trans (mem_iff_of_lt_disc (hs.trans_le h2))
  -- The earlier split wins. The middle case is impossible: `b` would both
  -- contain and lack the common split point.
  rcases lt_trichotomy (disc a b) (disc b c) with hlt | heqdisc | hlt
  · exact lexLT_of_agree_before_and_differ_at (@key · _ le_rfl hlt.le) hab.2
      (mem_iff_of_lt_disc hlt |>.mp hab.1)
  · simp_all
  · exact lexLT_of_agree_before_and_differ_at (@key · _ hlt.le le_rfl)
      (mem_iff_of_lt_disc hlt |>.mp · |> hbc.2) hbc.1
instance instIsStrictTotalOrderLexLT : IsStrictTotalOrder SetOrd LexLT where
  irrefl := by simp [LexLT]
  trichotomous := by grind only [LexLT, disc_comm, !disc_mem_symmDiff, = Set.mem_union]
  trans := by apply lexLT_trans
abbrev WO : WellOrder := ⟨Set Ordinal, WellOrderingRel, WellOrderingRel.isWellOrder⟩
@[inherit_doc WO] scoped infix:50 " ≺w " => WO.r
def Agree (a b : SetOrd) : Prop := a ≺w b ↔ a ≺ b
def Mono {V : Type*} (f : Finset V → Set.Iio μ) (r : ℕ) (𝒜 : Set V) (ι : Set.Iio μ) : Prop :=
  ∀ 𝒯 : Finset V, ↑𝒯 ⊆ 𝒜 → 𝒯.card = r → f 𝒯 = ι
noncomputable def otpOf (wo : WellOrder)
    (𝒜 : Set wo.α) : Ordinal.{u} := .type (Subrel wo.r (· ∈ 𝒜))
noncomputable abbrev otp := otpOf WO
def ArrowsOrdToOrd (wo : WellOrder) (r : ℕ) (μ : Ordinal) (τ : Set.Iio μ → Ordinal.{u}) : Prop :=
  ∀ 𝒜 : Set _, otpOf wo 𝒜 = θ →
  ∀ f : Finset _ → Set.Iio μ,
    ∃ ι : Set.Iio μ, ∃ ℬ ⊆ 𝒜, otpOf wo ℬ = τ ι ∧ Mono f r ℬ ι
abbrev FinChain (n : ℕ) := @RelEmbedding (Fin n) _ (· < ·) WO.r
def FinChain.mk (f : Fin n → SetOrd)
    (mono : ∀ i j : Fin n, i < j → f i ≺w f j) : FinChain n :=
  RelEmbedding.ofMonotone f mono
@[simp] lemma FinChain.mk_apply (f : Fin n → SetOrd)
    (mono : ∀ i j : Fin n, i < j → f i ≺w f j) (i : Fin n) :
    FinChain.mk f mono i = f i := rfl
def AgreeAt (u : FinChain (n + 1)) (j : Fin n) : Prop := u j.castSucc ≺ u j.succ
def InK0 (u : FinChain (n + 1)) : Prop := ∀ j, AgreeAt u j
def InK1 (u : FinChain (n + 1)) : Prop := ∀ j, ¬ AgreeAt u j
def InK01 (u : FinChain (n + 3)) : Prop := AgreeAt u 0 ∧ ¬ AgreeAt u 1
def InK10 (u : FinChain (n + 3)) : Prop := ¬ AgreeAt u 0 ∧ AgreeAt u 1
noncomputable def discSeq (u : FinChain (n + 1)) (j : Fin n) : Ordinal :=
  disc (u j.castSucc) (u j.succ)
def InP0 (u : FinChain (n + 2)) : Prop :=
  (InK0 ⊔ InK1) u ∧ ∀ j : Fin n, discSeq u j.castSucc < discSeq u j.succ
structure IsIndec (θ : Ordinal) : Prop where
  principal : Ordinal.IsPrincipal (· + ·) θ
  one_lt : 1 < θ
def AllAgree (𝒜 : Set SetOrd) : Prop := 𝒜.Pairwise Agree
def AllDisagree (𝒜 : Set SetOrd) : Prop := 𝒜.Pairwise (¬ Agree · ·)
abbrev HomAgree (𝒜 : Set SetOrd) : Prop := AllAgree 𝒜 ∨ AllDisagree 𝒜
noncomputable def nextIn (𝒜 : Set wo.α) (x : wo.α) : wo.α :=
  open Classical in
  if h : ∃ y, y ∈ 𝒜 ∧ wo.r x y then wo.wo.wf.min {y | y ∈ 𝒜 ∧ wo.r x y} h else x
abbrev ordWO : WellOrder := ⟨Ordinal, (· < ·), inferInstance⟩
noncomputable abbrev otpOrd := otpOf ordWO
noncomputable def discNext (𝒜 : Set SetOrd) (a : SetOrd) : Ordinal :=
  disc a (nextIn (wo := WO) 𝒜 a)
def WOle (a b : SetOrd) : Prop := a = b ∨ a ≺w b
noncomputable instance : DecidableRel WOle := fun _ _ => Classical.dec _
instance : IsTrans SetOrd WOle := ⟨by
  rintro a b c (rfl | h) (rfl | h')
  exacts [Or.inl rfl, Or.inr h', Or.inr h, Or.inr (_root_.trans h h')]⟩
instance : Std.Antisymm WOle := ⟨fun a _ hab hba =>
  Or.elim hab id fun h => Or.elim hba Eq.symm fun h' =>
    absurd (_root_.trans h h') (irrefl a)⟩
instance : Std.Total WOle := ⟨by
  intro a b
  rcases WellOrderingRel.isWellOrder.toTrichotomous.rel_or_eq_or_rel_swap (a := a) (b := b)
  with h | rfl | h
  exacts [Or.inl (Or.inr h), Or.inl (Or.inl rfl), Or.inr (Or.inr h)]⟩
noncomputable def chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) :
    FinChain n :=
  FinChain.mk (fun i => (𝒯.sort WOle).get (i.cast (by rw [Finset.length_sort, hT])))
    (fun {i j} hij => by
      have hp := (List.pairwise_iff_get.1 (Finset.pairwise_sort (r := WOle) 𝒯))
        (i.cast (by rw [Finset.length_sort, hT])) (j.cast (by rw [Finset.length_sort, hT])) hij
      rcases hp with heq | hlt
      · exact absurd (((𝒯.sort WOle).nodup_iff_injective_get.1 (Finset.sort_nodup _ _)) heq)
          (by simpa using hij.ne)
      · exact hlt)
open scoped Classical in
/-- The underlying finite set of a chain: the other half of the bridge. -/
noncomputable def FinChain.toFinset (u : FinChain n) : Finset SetOrd :=
  Finset.image u Finset.univ
@[simp] lemma FinChain.card_toFinset (u : FinChain n) : u.toFinset.card = n := by
  rw [FinChain.toFinset, Finset.card_image_of_injective _ u.injective, Finset.card_univ,
    Fintype.card_fin]
open scoped Classical in
/-- `σ u`: the discrepancies of `u`'s consecutive pairs, as a finite set. A
chain of `r + 1` points has `r` of them, and on a `P₀`-set they are distinct
because they strictly increase. -/
noncomputable def sigmaOf (u : FinChain (n + 1)) : Finset Ordinal :=
  Finset.image (discSeq u) Finset.univ
def iterNext (𝒜 : Set SetOrd) (x : SetOrd) (n : ℕ) : SetOrd
  := (nextIn (wo := WO) 𝒜)^[n] x
def InP01 (u : FinChain (n + 4)) : Prop :=
  (InK0 ⊔ InK1) u ∧ discSeq u 0 < discSeq u 1 ∧ discSeq u 2 < discSeq u 1
def InP10 (u : FinChain (n + 4)) : Prop :=
  (InK0 ⊔ InK1) u ∧ discSeq u 1 < discSeq u 0 ∧ discSeq u 1 < discSeq u 2
def NoHomogOrd (κ : Ordinal) (f : Finset Ordinal → Set.Iio μ) (r : ℕ) (θ : Ordinal) : Prop :=
  ∀ 𝒜 : Set Ordinal, 𝒜 ⊆ Set.Iio κ → otpOf ordWO 𝒜 = θ → ∀ ι, ¬ Mono f r 𝒜 ι
def NoHomog (κ : Ordinal) (f : Finset (Set Ordinal) → Set.Iio μ) (r : ℕ) (θ : Ordinal) : Prop :=
  ∀ 𝒜 : Set (Set Ordinal), 𝒜 ⊆ Set.powerset (Set.Iio κ) → otpOf WO 𝒜 = θ →
    ∀ ι, ¬ Mono f r 𝒜 ι
def colour₀ (hμ : 1 < μ) : Set.Iio μ := ⟨0, zero_lt_one.trans hμ⟩
@[inherit_doc colour₀]
def colour₁ (hμ : 1 < μ) : Set.Iio μ := ⟨1, hμ⟩
open scoped Classical in
/-- The stepped-up colouring. A chain is
looked at through its two patterns, and gets:

* colour `1` if it deviates *first one way* — `ε`-pattern beginning `0,1`, or
  discrepancies rising then falling;
* `g (σ u)` if it is well behaved (`P₀`): pattern constant, discrepancies
  rising. This is [dG21]'s `Iₙ*`;
* colour `0` otherwise, which includes the other first deviation — pattern
  `1,0`, or discrepancies falling then rising.

Splitting the two deviations between colours `1` and `0` is the point. A
homogeneous set of colour `1` can contain no chain of the second kind, and a
homogeneous set of any other colour none of the first, so *whichever* colour it
takes it avoids one of the two exceptional patterns — which is exactly the
hypothesis Lemmas 4.16 and 4.17 need in order to shrink it. Note no colour
beyond `g`'s own range and `{0, 1}` is used.

Sets of the wrong size are parked on colour `0`; they are never looked at. -/
noncomputable def stepUpColour (hμ : 1 < μ) (g : Finset Ordinal → Set.Iio μ)
    (T : Finset SetOrd) : Set.Iio μ :=
  if h : T.card = n + 4 then
    if (InK01 ⊔ InP01) (chainOfFinset T h) then colour₁ hμ
    else if InP0 (chainOfFinset T h) then g (sigmaOf (chainOfFinset T h)) else colour₀ hμ
  else colour₀ hμ
end OrdinalStepUp.ErdosRado


