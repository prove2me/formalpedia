-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
-- name    : LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:35:59.787302+00:00
-- url     : https://prove2.me/theorems/95f4bfaf-cf83-413d-83be-2bfd17a32186
-- title:
--   Canonical Construction
-- statement:
--   Definitions and structural lemmas for Canonical Construction, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalConstruction.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_freshWitnessed
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_app_mem_of_mono
public import Theorems.Thm_MatchingLogic_IsMCS_exists_joint_choice
public import Theorems.Thm_MatchingLogic_IsMCS_witnessPush_elim
public import Theorems.Thm_MatchingLogic_LocProvable_mono
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_freshTuple_injective
public import Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_body_allVars
public import Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_component_allVars
public import Theorems.Thm_MatchingLogic_Provable_imp_and
public import Theorems.Thm_MatchingLogic_Provable_imp_of
public import Theorems.Thm_MatchingLogic_Provable_imp_refl
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
variable {S : Signature}
def pfAndCanonicalConstruction (u v : PForm) : PForm := .imp (.imp u (.imp v .bot)) .bot
theorem taut_and_comm : PForm.Taut
    (.imp (.imp (.imp (.atom 0) (.imp (.atom 1) .bot)) .bot)
      (.imp (.imp (.atom 1) (.imp (.atom 0) .bot)) .bot)) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
theorem provable_and_comm (p q : Pattern S Nat) :
    Provable (∅ : Set (Pattern S Nat)) (.imp (Pattern.and p q) (Pattern.and q p)) := by
  simpa [PForm.subst, Pattern.and, Pattern.nt] using
    (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
      (θ := fun n => if n = 0 then p else q) taut_and_comm)
theorem provable_to_singleton_conj (p : Pattern S Nat) :
    Provable (∅ : Set (Pattern S Nat)) (.imp p (conj [p])) := by
  simpa [conj] using
    (Provable.imp_refl (∅ : Set (Pattern S Nat)) p).imp_and
      ((provable_top (∅ : Set (Pattern S Nat))).imp_of (psi := p))
structure StageData (sigma : S.Sym) (Gamma : CanonicalCarrier S) where
  lists : Fin (S.arity sigma) → List (Pattern S Nat)
  app_mem : Pattern.app sigma (fun i => conj (lists i)) ∈ Gamma.val
def initialStageData {sigma : S.Sym} (Gamma : CanonicalCarrier S)
    (args : Fin (S.arity sigma) → Pattern S Nat)
    (happ : Pattern.app sigma args ∈ Gamma.val) :
    StageData sigma Gamma := by
  refine ⟨fun i => [args i], ?_⟩
  exact (CanonicalCarrier.isMCS Gamma).app_mem_of_mono
    (fun i => provable_to_singleton_conj (args i)) happ
def selected (psi : Pattern S Nat) (b : Bool) : Pattern S Nat :=
  if b then psi else Pattern.nt psi
theorem app_mem_prepend {sigma : S.Sym} {Gamma : CanonicalCarrier S}
    (L : Fin (S.arity sigma) → List (Pattern S Nat))
    (a : Fin (S.arity sigma) → Pattern S Nat)
    (h : Pattern.app sigma (fun i => Pattern.and (conj (L i)) (a i)) ∈ Gamma.val) :
    Pattern.app sigma (fun i => conj (a i :: L i)) ∈ Gamma.val := by
  apply (CanonicalCarrier.isMCS Gamma).app_mem_of_mono (fun i => ?_) h
  simpa [conj] using provable_and_comm (conj (L i)) (a i)
theorem app_mem_prepend_two {sigma : S.Sym} {Gamma : CanonicalCarrier S}
    (L : Fin (S.arity sigma) → List (Pattern S Nat))
    (a b : Fin (S.arity sigma) → Pattern S Nat)
    (h : Pattern.app sigma
      (fun i => Pattern.and (Pattern.and (conj (L i)) (a i)) (b i)) ∈ Gamma.val) :
    Pattern.app sigma (fun i => conj (b i :: a i :: L i)) ∈ Gamma.val := by
  apply (CanonicalCarrier.isMCS Gamma).app_mem_of_mono (fun i => ?_) h
  -- `(L ∧ a) ∧ b` entails `b ∧ (a ∧ L)` by a propositional tautology.
  have ht : PForm.Taut
      (.imp (pfAndCanonicalConstruction (pfAndCanonicalConstruction (.atom 0) (.atom 1)) (.atom 2))
        (pfAndCanonicalConstruction (.atom 2) (pfAndCanonicalConstruction (.atom 1) (.atom 0)))) := by
    intro v
    cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
      simp [pfAndCanonicalConstruction, PForm.eval, h0, h1, h2]
  -- This local shape is deliberately discharged through `taut`; it pins the
  -- bracketing rather than treating finite conjunctions as associative.
  have hproof := Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
    (θ := fun n => if n = 0 then conj (L i) else if n = 1 then a i else b i) ht
  change Provable (∅ : Set (Pattern S Nat)) (PForm.subst (fun n => if n = 0 then conj (L i) else if n = 1 then a i else b i) (.imp (pfAndCanonicalConstruction (pfAndCanonicalConstruction (.atom 0) (.atom 1)) (.atom 2)) (pfAndCanonicalConstruction (.atom 2) (pfAndCanonicalConstruction (.atom 1) (.atom 0)))))
  exact hproof
theorem successorStageData {sigma : S.Sym} (Gamma : CanonicalCarrier S)
    (D : StageData sigma Gamma) (psi : Pattern S Nat) :
    ∃ E : StageData sigma Gamma,
      (∀ i q, q ∈ D.lists i → q ∈ E.lists i) ∧
      (∀ i, psi ∈ E.lists i ∨ Pattern.nt psi ∈ E.lists i) ∧
      (∀ x p, psi = Pattern.ex x p →
        ∀ i, ∃ y, y ∉ p.allVars ∧
          Pattern.imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ E.lists i) := by
  obtain ⟨b, hb⟩ := (CanonicalCarrier.isMCS Gamma).exists_joint_choice D.lists psi D.app_mem
  let choice : Fin (S.arity sigma) → Pattern S Nat := fun i => selected psi (b i)
  by_cases hex : ∃ x p, psi = Pattern.ex x p
  · rcases hex with ⟨x, p, rfl⟩
    let Phi : Fin (S.arity sigma) → Pattern S Nat :=
      fun i => Pattern.and (conj (D.lists i)) (choice i)
    let y := Pattern.freshTuple p Phi
    obtain ⟨z, hzP, _hzPhi, hzapp⟩ := (CanonicalCarrier.isMCS Gamma).witnessPush_elim
      (CanonicalCarrier.freshWitnessed Gamma) Phi p x y
      (Pattern.freshTuple_injective p Phi)
      (Pattern.freshTuple_not_mem_body_allVars p Phi)
      (Pattern.freshTuple_not_mem_component_allVars p Phi) (by
        simpa only [Phi, choice, selected] using hb)
    let impz : Fin (S.arity sigma) → Pattern S Nat := fun i =>
      Pattern.imp (.ex x p) (Pattern.captureAvoidingSubst x (z i) p)
    refine ⟨⟨fun i => impz i :: choice i :: D.lists i, ?_⟩, ?_, ?_, ?_⟩
    · simpa [Phi, impz] using app_mem_prepend_two D.lists choice impz hzapp
    · intro i q hq
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
    · intro i
      by_cases hbi : b i
      · left; simp [choice, selected, hbi]
      · right; simp [choice, selected, hbi]
    · intro x' p' heq i
      cases heq
      exact ⟨z i, hzP i, by simp [impz]⟩
  · refine ⟨⟨fun i => choice i :: D.lists i, ?_⟩, ?_, ?_, ?_⟩
    · simpa [choice] using app_mem_prepend D.lists choice hb
    · intro i q hq
      exact List.mem_cons_of_mem _ hq
    · intro i
      by_cases hbi : b i
      · left; simp [choice, selected, hbi]
      · right; simp [choice, selected, hbi]
    · intro x p h
      exact False.elim (hex ⟨x, p, h⟩)
noncomputable def nextStageData {sigma : S.Sym} (Gamma : CanonicalCarrier S)
    (D : StageData sigma Gamma) (psi : Pattern S Nat) : StageData sigma Gamma :=
  Classical.choose (successorStageData Gamma D psi)
theorem nextStageData_spec {sigma : S.Sym} (Gamma : CanonicalCarrier S)
    (D : StageData sigma Gamma) (psi : Pattern S Nat) :
    (∀ i q, q ∈ D.lists i → q ∈ (nextStageData Gamma D psi).lists i) ∧
    (∀ i, psi ∈ (nextStageData Gamma D psi).lists i ∨
      Pattern.nt psi ∈ (nextStageData Gamma D psi).lists i) ∧
    (∀ x p, psi = Pattern.ex x p → ∀ i, ∃ y, y ∉ p.allVars ∧
      Pattern.imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈
        (nextStageData Gamma D psi).lists i) := by
  exact Classical.choose_spec (successorStageData Gamma D psi)
noncomputable def stageData {sigma : S.Sym} (Gamma : CanonicalCarrier S)
    (args : Fin (S.arity sigma) → Pattern S Nat)
    (happ : Pattern.app sigma args ∈ Gamma.val) (enum : Nat → Pattern S Nat) :
    Nat → StageData sigma Gamma
  | 0 => initialStageData Gamma args happ
  | k + 1 => nextStageData Gamma (stageData Gamma args happ enum k) (enum k)
theorem stageData_succ_spec {sigma : S.Sym} (Gamma : CanonicalCarrier S)
    (args : Fin (S.arity sigma) → Pattern S Nat)
    (happ : Pattern.app sigma args ∈ Gamma.val) (enum : Nat → Pattern S Nat) (k : Nat) :
    let D := stageData Gamma args happ enum k
    let E := stageData Gamma args happ enum (k + 1)
    (∀ i q, q ∈ D.lists i → q ∈ E.lists i) ∧
    (∀ i, enum k ∈ E.lists i ∨ Pattern.nt (enum k) ∈ E.lists i) ∧
    (∀ x p, enum k = Pattern.ex x p → ∀ i, ∃ y, y ∉ p.allVars ∧
      Pattern.imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ E.lists i) := by
  simp only [stageData]
  exact nextStageData_spec Gamma (stageData Gamma args happ enum k) (enum k)
noncomputable def constructedStages {sigma : S.Sym} (Gamma : CanonicalCarrier S)
    (args : Fin (S.arity sigma) → Pattern S Nat)
    (happ : Pattern.app sigma args ∈ Gamma.val) (enum : Nat → Pattern S Nat) :
    NaryStageSystem sigma Gamma args enum where
  stages k := (stageData Gamma args happ enum k).lists
  base i := by
    change args i ∈ [args i]
    simp
  mono k i q hq := (stageData_succ_spec Gamma args happ enum k).1 i q hq
  app_mem k := (stageData Gamma args happ enum k).app_mem
  decide k i := (stageData_succ_spec Gamma args happ enum k).2.1 i
  witness k i x p heq := (stageData_succ_spec Gamma args happ enum k).2.2 x p heq i
end MatchingLogic


