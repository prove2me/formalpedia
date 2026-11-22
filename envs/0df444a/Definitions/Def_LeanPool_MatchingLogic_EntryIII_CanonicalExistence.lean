-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
-- name    : LeanPool_MatchingLogic_EntryIII_CanonicalExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:32:29.056409+00:00
-- url     : https://prove2.me/theorems/ebde0a93-7f12-43e9-a917-2f9cab804e79
-- title:
--   Canonical Existence
-- statement:
--   Definitions and structural lemmas for Canonical Existence, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_singleton_argument_locConsistent
public import Theorems.Thm_MatchingLogic_LocProvable_mono
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_LocProvable_of_mem
public import Theorems.Thm_MatchingLogic_LocProvable_of_provable
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Provable_and_elim_left
public import Theorems.Thm_MatchingLogic_Provable_and_elim_right
public import Theorems.Thm_MatchingLogic_Provable_imp_and
public import Theorems.Thm_MatchingLogic_Provable_imp_of
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_provable_top
attribute [local simp] MatchingLogic.CanonicalCarrier.coe_mk
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.mem_canonicalInterp


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
def CanonicalExistenceProperty (S : Signature) : Prop :=
  ∀ (Gamma : CanonicalCarrier S) (sigma : S.Sym)
    (args : Fin (S.arity sigma) → Pattern S Nat),
    Pattern.app sigma args ∈ Gamma.val →
      ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
        (∀ i, args i ∈ (components i).val) ∧
          Gamma ∈ canonicalInterp sigma components
structure NaryStageSystem (sigma : S.Sym) (Gamma : CanonicalCarrier S)
    (phi : Fin (S.arity sigma) → Pattern S Nat) (enum : Nat → Pattern S Nat) where
  /-- The finite theory accumulated at each stage and argument position. -/
  stages : Nat → Fin (S.arity sigma) → List (Pattern S Nat)
  base : ∀ i, phi i ∈ stages 0 i
  mono : ∀ k i, ∀ q ∈ stages k i, q ∈ stages (k + 1) i
  app_mem : ∀ k, Pattern.app sigma (fun i => conj (stages k i)) ∈ Gamma.val
  decide : ∀ k i, enum k ∈ stages (k + 1) i ∨ Pattern.nt (enum k) ∈ stages (k + 1) i
  witness : ∀ k i x p, enum k = Pattern.ex x p →
    ∃ y, y ∉ p.allVars ∧
      Pattern.imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ stages (k + 1) i
namespace Pattern
def tupleAllVars (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) : Finset Nat :=
  p.allVars ∪ Finset.univ.biUnion (fun i => (Phi i).allVars)
def tupleFreshBase (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) : Nat :=
  (insert 0 (tupleAllVars p Phi)).max' (by simp)
def freshTuple (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) : Fin n → Nat :=
  fun i => tupleFreshBase p Phi + 1 + i.val
end Pattern
namespace NaryStageSystem
variable {sigma : S.Sym} {Gamma : CanonicalCarrier S}
  {phi : Fin (S.arity sigma) → Pattern S Nat} {enum : Nat → Pattern S Nat}
  (T : NaryStageSystem sigma Gamma phi enum)
def limit (i : Fin (S.arity sigma)) : Set (Pattern S Nat) :=
  {q | ∃ k, q ∈ T.stages k i}
theorem stage_mono {k l : Nat} (hkl : k ≤ l) (i : Fin (S.arity sigma))
    {q : Pattern S Nat} (hq : q ∈ T.stages k i) : q ∈ T.stages l i := by
  induction l, hkl using Nat.le_induction with
  | base => exact hq
  | succ l hle ih => exact T.mono l i _ ih
theorem conj_imp_mem (l : List (Pattern S Nat)) {q : Pattern S Nat}
    (hq : q ∈ l) :
    Provable (∅ : Set (Pattern S Nat)) (.imp (conj l) q) := by
  induction l with
  | nil => simp at hq
  | cons a l ih =>
      rcases List.mem_cons.mp hq with rfl | hq
      · simpa [conj] using Provable.and_elim_left (∅ : Set (Pattern S Nat)) _ _
      · simpa [conj] using
          (Provable.and_elim_right (∅ : Set (Pattern S Nat)) _ _).imp_trans (ih hq)
theorem conj_imp_of_subset (l r : List (Pattern S Nat))
    (hsub : ∀ q ∈ r, q ∈ l) :
    Provable (∅ : Set (Pattern S Nat)) (.imp (conj l) (conj r)) := by
  induction r with
  | nil =>
      simpa [conj] using
        (provable_top (∅ : Set (Pattern S Nat))).imp_of (psi := conj l)
  | cons q r ih =>
      simpa [conj] using
        (conj_imp_mem l (hsub q (by simp))).imp_and
          (ih (fun p hp => hsub p (by simp [hp])))
theorem stage_locConsistent (k : Nat) (i : Fin (S.arity sigma)) :
    LocConsistent ({q | q ∈ T.stages k i} : Set (Pattern S Nat)) := by
  intro hbad
  rcases hbad with ⟨r, hr, hbot⟩
  have hsub : ∀ q ∈ r, q ∈ T.stages k i := by
    intro q hq
    exact hr q hq
  have hconjbot : Provable (∅ : Set (Pattern S Nat))
      (.imp (conj (T.stages k i)) .bot) :=
    (conj_imp_of_subset (T.stages k i) r hsub).imp_trans hbot
  have hsingle : LocConsistent ({conj (T.stages k i)} : Set (Pattern S Nat)) :=
    (CanonicalCarrier.isMCS Gamma).singleton_argument_locConsistent (T.app_mem k) i
  apply hsingle
  exact (LocProvable.of_mem (by simp)).mp (LocProvable.of_provable hconjbot)
theorem finite_limit_covered (i : Fin (S.arity sigma))
    (l : List (Pattern S Nat)) (hl : ∀ q ∈ l, q ∈ T.limit i) :
    ∃ k, ∀ q ∈ l, q ∈ T.stages k i := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons q l ih =>
      rcases hl q (by simp) with ⟨kq, hkq⟩
      rcases ih (by intro p hp; exact hl p (by simp [hp])) with ⟨kl, hkl⟩
      refine ⟨max kq kl, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact T.stage_mono (Nat.le_max_left _ _) i hkq
      · exact T.stage_mono (Nat.le_max_right _ _) i (hkl p hp)
theorem limit_locConsistent (i : Fin (S.arity sigma)) : LocConsistent (T.limit i) := by
  intro hbad
  rcases hbad with ⟨l, hl, hbot⟩
  rcases T.finite_limit_covered i l hl with ⟨k, hk⟩
  exact T.stage_locConsistent k i ⟨l, hk, hbot⟩
theorem limit_freshWitnessed (henum : Function.Surjective enum)
    (i : Fin (S.arity sigma)) : FreshWitnessed (T.limit i) := by
  intro x p _hp
  obtain ⟨k, hk⟩ := henum (.ex x p)
  obtain ⟨y, hyfresh, hy⟩ := T.witness k i x p hk
  exact ⟨y, hyfresh, k + 1, hy⟩
theorem limit_isMCS (henum : Function.Surjective enum) (i : Fin (S.arity sigma)) :
    IsMCS (T.limit i) := by
  constructor
  · exact T.limit_locConsistent i
  · intro Delta hstrict hDelta
    rcases Set.ssubset_iff_subset_ne.mp hstrict with ⟨hsub, hne⟩
    have hnot : ¬ Delta ⊆ T.limit i := by
      intro h
      exact hne (Set.Subset.antisymm hsub h)
    rcases Set.not_subset.mp hnot with ⟨q, hqD, hqL⟩
    rcases henum q with ⟨k, rfl⟩
    rcases T.decide k i with hpos | hneg
    · exact hqL ⟨k + 1, hpos⟩
    · apply hDelta
      exact (LocProvable.of_mem hqD).mp (LocProvable.of_mem (hsub ⟨k + 1, hneg⟩))
end NaryStageSystem
end
end MatchingLogic


