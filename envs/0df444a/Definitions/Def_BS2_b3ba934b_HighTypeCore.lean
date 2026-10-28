-- Prove2me | Definitions.Def_BS2_b3ba934b_HighTypeCore
-- name    : BS2_b3ba934b_HighTypeCore
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:25:35.097977+00:00
-- url     : https://prove2.me/theorems/a5eefc7e-0d20-4cd7-bdbb-f9470b2641a2
-- title:
--   Sensitivity separation: HighTypeCore (complete source module)
-- statement:
--   Complete Lean source module `HighTypeCore` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/HighTypeCore.lean; original SHA-256 52f6a181be2fcb17f9b44bc27d99100f93c6edef7d4e31921bd74c65a489647b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes

abbrev Kind (q : ℕ) := Fin (3*q+2)

def OfKind (q : ℕ) (P G : ℕ → Prop) (k : Kind q) : Prop :=
  if k.val ≤ q then P k.val ∧ (k.val=0 ∨ ¬ G (k.val-1))
  else if k.val ≤ 2*q+1 then G (k.val-(q+1)) ∧ (k.val=2*q+1 ∨ ¬ P (k.val-q))
  else P (k.val-(2*q+1)) ∧ G (k.val-(2*q+2))

def budget (q : ℕ) (k : Kind q) : ℕ :=
  if k.val ≤ q then k.val else if k.val ≤ 2*q+1 then k.val-q else k.val-(2*q+1)

def isGuard (q : ℕ) (k : Kind q) : Bool := decide (q+1 ≤ k.val)

def positivePrefix (q b : ℕ) (k : Kind q) : Bool :=
  decide ((k.val ≤ q ∧ k.val ≤ b) ∨ (2*q+2 ≤ k.val ∧ k.val-(2*q+1) ≤ b))

theorem exists_kind (q d : ℕ) (P G : ℕ → Prop)
    (hp : ∀ b, P b → b ≤ q ∧ d=b)
    (hg : ∀ b, G b → b ≤ q ∧ d=b+1)
    (h : (∃ b, P b) ∨ ∃ b, G b) : ∃ k : Kind q, OfKind q P G k := by
  classical
  rcases h with ⟨b,hb⟩ | ⟨b,hb⟩
  · obtain ⟨hbq,hbd⟩ := hp b hb
    by_cases hz : b=0
    · subst b
      refine ⟨⟨0,by omega⟩,?_⟩
      simp only [OfKind,Fin.val_mk,Nat.zero_le,ite_true,true_or,and_true]
      simpa only [hz] using hb
    · by_cases hh : G (b-1)
      · refine ⟨⟨2*q+1+b,by omega⟩,?_⟩
        have h1 : ¬ 2*q+1+b ≤ q := by omega
        have h2 : ¬ 2*q+1+b ≤ 2*q+1 := by omega
        have he1 : 2*q+1+b-(2*q+1)=b := by omega
        have he2 : 2*q+1+b-(2*q+2)=b-1 := by omega
        simpa only [OfKind,Fin.val_mk,if_neg h1,if_neg h2,he1,he2] using And.intro hb hh
      · refine ⟨⟨b,by omega⟩,?_⟩
        simp only [OfKind,Fin.val_mk,if_pos hbq]
        exact ⟨hb,Or.inr hh⟩
  · obtain ⟨hbq,hbd⟩ := hg b hb
    by_cases hlast : b=q
    · subst b
      refine ⟨⟨2*q+1,by omega⟩,?_⟩
      have h1 : ¬ 2*q+1 ≤ q := by omega
      have he : 2*q+1-(q+1)=q := by omega
      simp [OfKind,h1,he,hb]
    · by_cases hh : P (b+1)
      · refine ⟨⟨2*q+2+b,by omega⟩,?_⟩
        have h1 : ¬ 2*q+2+b ≤ q := by omega
        have h2 : ¬ 2*q+2+b ≤ 2*q+1 := by omega
        have he1 : 2*q+2+b-(2*q+1)=b+1 := by omega
        have he2 : 2*q+2+b-(2*q+2)=b := by omega
        simpa only [OfKind,Fin.val_mk,if_neg h1,if_neg h2,he1,he2] using And.intro hh hb
      · refine ⟨⟨q+1+b,by omega⟩,?_⟩
        have h1 : ¬ q+1+b ≤ q := by omega
        have h2 : q+1+b ≤ 2*q+1 := by omega
        have he1 : q+1+b-(q+1)=b := by omega
        have he2 : q+1+b-q=b+1 := by omega
        simp only [OfKind,Fin.val_mk,if_neg h1,if_pos h2,he1,he2]
        exact ⟨hb,Or.inr hh⟩

theorem ofKind_count (q d : ℕ) (P G : ℕ → Prop) (k : Kind q)
    (hp : ∀ b, P b → d=b) (hg : ∀ b, G b → d=b+1) (hk : OfKind q P G k) :
    d=budget q k := by
  unfold OfKind at hk
  unfold budget
  split_ifs at hk ⊢ with h1 h2
  · exact hp _ hk.1
  · have h := hg _ hk.1
    omega
  · exact hp _ hk.1

theorem ofKind_high (q : ℕ) (P G : ℕ → Prop) (k : Kind q) (hk : OfKind q P G k) :
    (∃ b, P b) ∨ ∃ b, G b := by
  unfold OfKind at hk
  split_ifs at hk
  · exact Or.inl ⟨_,hk.1⟩
  · exact Or.inr ⟨_,hk.1⟩
  · exact Or.inl ⟨_,hk.1⟩

theorem budget_le (q : ℕ) (k : Kind q) : budget q k ≤ q+1 := by
  have hk := k.isLt
  unfold budget
  split_ifs <;> omega

theorem guard_iff (q d : ℕ) (P G : ℕ → Prop) (k : Kind q)
    (hp : ∀ b, P b → b ≤ q ∧ d=b)
    (hg : ∀ b, G b → b ≤ q ∧ d=b+1) (hk : OfKind q P G k) :
    (∃ b, G b) ↔ isGuard q k = true := by
  unfold OfKind at hk
  simp only [isGuard,decide_eq_true_eq]
  split_ifs at hk with h1 h2
  · constructor
    · rintro ⟨b,hb⟩
      obtain ⟨_,hdp⟩ := hp _ hk.1
      obtain ⟨_,hdg⟩ := hg _ hb
      rcases hk.2 with hz | hn
      · omega
      · have he : b=k.val-1 := by omega
        exact False.elim (hn (he ▸ hb))
    · omega
  · exact ⟨fun _ => by omega,fun _ => ⟨_,hk.1⟩⟩
  · exact ⟨fun _ => by omega,fun _ => ⟨_,hk.2⟩⟩

theorem positivePrefix_iff (q d b : ℕ) (P G : ℕ → Prop) (k : Kind q)
    (hp : ∀ c, P c → c ≤ q ∧ d=c)
    (hg : ∀ c, G c → c ≤ q ∧ d=c+1) (hk : OfKind q P G k) :
    (∃ c, c ≤ b ∧ P c) ↔ positivePrefix q b k = true := by
  unfold OfKind at hk
  simp only [positivePrefix,decide_eq_true_eq]
  split_ifs at hk with h1 h2
  · have hd := (hp _ hk.1).2
    constructor
    · rintro ⟨c,hcb,hc⟩
      have hdc := (hp _ hc).2
      exact Or.inl ⟨h1,by omega⟩
    · intro hh
      refine ⟨k.val,?_,hk.1⟩
      rcases hh with hh | hh <;> omega
  · constructor
    · rintro ⟨c,hcb,hc⟩
      have hdc := hp _ hc
      have hdg := hg _ hk.1
      rcases hk.2 with hz | hn
      · omega
      · have he : c=k.val-q := by omega
        exact False.elim (hn (he ▸ hc))
    · intro hh
      rcases hh with hh | hh <;> omega
  · have hd := (hp _ hk.1).2
    constructor
    · rintro ⟨c,hcb,hc⟩
      have hdc := (hp _ hc).2
      exact Or.inr ⟨by omega,by omega⟩
    · intro hh
      refine ⟨k.val-(2*q+1),?_,hk.1⟩
      rcases hh with hh | hh <;> omega

end ThreeBoundHighTypes

#print axioms ThreeBoundHighTypes.exists_kind
#print axioms ThreeBoundHighTypes.positivePrefix_iff


