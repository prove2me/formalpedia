-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxPairM
-- name    : BS2_b3ba934b_MinmaxPairM
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:27:47.234987+00:00
-- url     : https://prove2.me/theorems/37055776-c2b8-4558-adc7-231057fd9a39
-- title:
--   Sensitivity separation: MinmaxPairM (complete source module)
-- statement:
--   Complete Lean source module `MinmaxPairM` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxPairM.lean; original SHA-256 9814c9e6e0030cd165de999d63739e06884c4d4238b6c0bacbd7634d76cbe338; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Conditional destruction of the actual oriented min/max witness row.
The selected orientation is a genuine component of the symmetric parent. -/
import Definitions.Def_BS2_b3ba934b_MinmaxB

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def orientedRow (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) : Prop :=
  F t (child x w (!c))=true ∧ F u (child x w c)=true ∧ (guardFailures S F g x w).card ≤ q

def orientedRowBool (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u g : L) (q : ℕ) (w : V) (c : Bool) (x : ((V × Bool) × I) → Bool) : Bool :=
  decide (orientedRow S F t u g q x w c)

theorem oriented_row_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u g : L) (q : ℕ) (w : V) (c : Bool) (x : ((V × Bool) × I) → Bool) :
    orientedRowBool S F t u g q w c x=true ↔ orientedRow S F t u g q x w c := by
  simp only [orientedRowBool,decide_eq_true_eq]

theorem oriented_row_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u g : L) (q : ℕ) (w : V) (c : Bool) (x : ((V × Bool) × I) → Bool) :
    orientedRowBool S F t u g q w c x=false ↔ ¬orientedRow S F t u g q x w c := by
  simp only [orientedRowBool,decide_eq_false_iff_not]

theorem oriented_implies_parent (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤ S.tolerance l → t b ≤ u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ) (c : Bool) (hd : d ≤ S.tolerance l)
    (hrow : orientedRow S F (t d) (u d) (S.guard l) d x w c) : parent S F l x=true :=
  oriented_component_accepts S F hF l t u ht hu hlu hdef x w d c hd hrow.2.2 hrow.1 hrow.2.1

theorem parent_down_subset_oriented (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤ S.tolerance l → t b ≤ u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ) (c : Bool) (hd : d ≤ S.tolerance l) :
    flipsTo (parent S F l) false x ⊆
      flipsTo (orientedRowBool S F (t d) (u d) (S.guard l) d w c) false x := by
  intro bit hbit
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  apply (oriented_row_false S F _ _ _ d w c _).2
  intro hrow
  have hon := oriented_implies_parent S F hF l t u ht hu hlu hdef _ w d c hd hrow
  have hoff := (Finset.mem_filter.mp hbit).2
  rw [hoff] at hon
  contradiction

theorem oriented_down_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tj uj gi gj : L) (ht : ti ≤ tj) (hu : ui ≤ uj) (hg : gj ≤ gi)
    (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) (c₀ : Bool)
    (hj : orientedRow S F tj uj gj q x v c₀) :
    flipsTo (orientedRowBool S F ti ui gi q v c₀) false x ⊆
      orientedBits F ti ui x v c₀ ∪ ordinaryGuardBits S F gi gj x v := by
  intro bit hbit
  obtain ⟨⟨w,c⟩,a⟩ := bit
  have hoff := (oriented_row_false S F ti ui gi q v c₀ _).1 (Finset.mem_filter.mp hbit).2
  by_cases he : S.Adj v w ∧ S.label v w=c ∧ F gj (child x w c)=false ∧ F gi (flip (child x w c) {a})=true
  · apply Finset.mem_union_right
    obtain ⟨hR,hl,hbefore,hafter⟩ := he
    apply Finset.mem_biUnion.mpr
    refine ⟨w,(mem_passingGuards S F gj x v w).2 ⟨hR,by simpa only [hl] using hbefore⟩,?_⟩
    apply (mem_liftBits _ _ _ _ _ _).2
    exact ⟨rfl,hl.symm,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hl] using hafter⟩⟩
  · have hsub : guardFailures S F gi (flip x {((w,c),a)}) v ⊆ guardFailures S F gj x v := by
      intro z hz
      obtain ⟨hR,hf⟩ := (mem_guardFailures S F gi _ v z).1 hz
      apply (mem_guardFailures S F gj x v z).2
      refine ⟨hR,?_⟩
      by_cases hp : (z,S.label v z)=(w,c)
      · have hzw : z=w := congrArg Prod.fst hp
        have hl : S.label v z=c := congrArg Prod.snd hp
        subst z
        rw [hl,child_flip_same] at hf
        cases hb : F gj (child x w c) with
        | true => simpa only [hl] using hb
        | false => exact False.elim (he ⟨hR,hl,hb,hf⟩)
      · rw [child_flip_other x w z c (S.label v z) a hp] at hf
        exact hF _ _ hg _ hf
    have hc : (guardFailures S F gi (flip x {((w,c),a)}) v).card ≤ q :=
      (Finset.card_le_card hsub).trans hj.2.2
    have hfalse : F ti (child (flip x {((w,c),a)}) v (!c₀))=false ∨
        F ui (child (flip x {((w,c),a)}) v c₀)=false := by
      cases hl : F ti (child (flip x {((w,c),a)}) v (!c₀)) with
      | false => exact Or.inl rfl
      | true =>
          cases hh : F ui (child (flip x {((w,c),a)}) v c₀) with
          | false => exact Or.inr rfl
          | true => exact False.elim (hoff ⟨hl,hh,hc⟩)
    apply Finset.mem_union_left
    rcases hfalse with hl | hh
    · have hp : (v,!c₀)=(w,c) := by
        by_contra hn
        rw [child_flip_other x w v c (!c₀) a hn] at hl
        have htrue := hF _ _ ht _ hj.1
        rw [hl] at htrue
        contradiction
      have hw : w=v := (congrArg Prod.fst hp).symm
      have hcc : c= !c₀ := (congrArg Prod.snd hp).symm
      subst w
      subst c
      rw [child_flip_same] at hl
      exact Finset.mem_union_left _ ((mem_liftBits _ _ _ _ _ _).2
        ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩⟩)
    · have hp : (v,c₀)=(w,c) := by
        by_contra hn
        rw [child_flip_other x w v c c₀ a hn] at hh
        have htrue := hF _ _ hu _ hj.2.1
        rw [hh] at htrue
        contradiction
      have hw : w=v := (congrArg Prod.fst hp).symm
      have hcc : c=c₀ := (congrArg Prod.snd hp).symm
      subst w
      subst c
      rw [child_flip_same] at hh
      exact Finset.mem_union_right _ ((mem_liftBits _ _ _ _ _ _).2
        ⟨rfl,rfl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩)

def pairMTarget (tj uj tk uk : L) (m0 m1 b0 b1 : ℕ) : ℕ :=
  max (if tj<tk ∧ uj<uk then m0+m1 else 0)
    (max (if tj<tk then m0+b1 else 0) (if uj<uk then b0+m1 else 0))

def pairMCost (degree q : ℕ) (tj uj tk uk gj gk : L) (a m0 m1 b0 b1 p : ℕ) : ℕ :=
  max (if tj<tk ∨ uj<uk then pairMTarget tj uj tk uk m0 m1 b0 b1+(degree-q)*a else 0)
    (if gk<gj then b0+b1+(degree-q-1)*a+p else 0)

theorem true_false_lt (F : L → (I → Bool) → Bool) (hF : Nested F)
    (j k : L) (x : I → Bool) (hj : F j x=true) (hk : F k x=false) : j<k := by
  by_contra hn
  have he := hF _ _ (le_of_not_gt hn) _ hj
  rw [hk] at he
  contradiction

theorem orientedBits_conditional_card (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj tk uk : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (hj0 : F tj (child x v (!c))=true) (hj1 : F uj (child x v c)=true)
    (hmiss : F tk (child x v (!c))=false ∨ F uk (child x v c)=false)
    (m0 m1 b0 b1 : ℕ) (hm0 : MBound F ti tj tk m0) (hm1 : MBound F ui uj uk m1)
    (hb0 : BBound F ti tk b0) (hb1 : BBound F ui uk b1) :
    (orientedBits F ti ui x v c).card ≤ pairMTarget tj uj tk uk m0 m1 b0 b1 := by
  cases hk0 : F tk (child x v (!c)) <;> cases hk1 : F uk (child x v c)
  · have ht := true_false_lt F hF tj tk _ hj0 hk0
    have hu := true_false_lt F hF uj uk _ hj1 hk1
    have hh := orientedBits_card F ti ui x v c m0 m1 (hm0 _ hj0 hk0) (hm1 _ hj1 hk1)
    exact hh.trans (by unfold pairMTarget; rw [if_pos ⟨ht,hu⟩]; exact le_max_left _ _)
  · have ht := true_false_lt F hF tj tk _ hj0 hk0
    have hh := orientedBits_card F ti ui x v c m0 b1 (hm0 _ hj0 hk0) (hb1 _ hk1)
    exact hh.trans (by unfold pairMTarget; rw [if_pos ht]; exact (le_max_left _ _).trans (le_max_right _ _))
  · have hu := true_false_lt F hF uj uk _ hj1 hk1
    have hh := orientedBits_card F ti ui x v c b0 m1 (hb0 _ hk0) (hm1 _ hj1 hk1)
    exact hh.trans (by unfold pairMTarget; rw [if_pos hu]; exact (le_max_right _ _).trans (le_max_right _ _))
  · rcases hmiss with he | he <;> simp_all

/-- Exact oriented conditional transfer for a middle witness with d guards. -/
theorem oriented_pairM_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (ti ui tj uj tk uk gi gj gk : L)
    (htij : ti ≤ tj) (huij : ui ≤ uj) (hgij : gj ≤ gi) (hgkj : gk ≤ gj)
    (q degree : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool)
    (hj : orientedRow S F tj uj gj q x v c)
    (hcount : (guardFailures S F gj x v).card=q)
    (hk : ¬ orientedRow S F tk uk gk q x v c)
    (hd : (outgoing S v).card=degree)
    (a m0 m1 b0 b1 p : ℕ) (ha : ABound F gj gi a)
    (hm0 : MBound F ti tj tk m0) (hm1 : MBound F ui uj uk m1)
    (hb0 : BBound F ti tk b0) (hb1 : BBound F ui uk b1) (hp : PBound F gk gj gi p) :
    (flipsTo (orientedRowBool S F ti ui gi q v c) false x).card ≤
      pairMCost degree q tj uj tk uk gj gk a m0 m1 b0 b1 p := by
  have hcover := Finset.card_le_card (oriented_down_cover S F hF ti ui tj uj gi gj htij huij hgij q x v c hj)
  have hsplit := hcover.trans (Finset.card_union_le _ _)
  by_cases hmiss : F tk (child x v (!c))=false ∨ F uk (child x v c)=false
  · have hgap : tj<tk ∨ uj<uk := hmiss.elim
      (fun he => Or.inl (true_false_lt F hF tj tk _ hj.1 he))
      (fun he => Or.inr (true_false_lt F hF uj uk _ hj.2.1 he))
    have ht := orientedBits_conditional_card F hF ti ui tj uj tk uk x v c hj.1 hj.2.1
      hmiss m0 m1 b0 b1 hm0 hm1 hb0 hb1
    have hg := ordinaryGuardBits_card_le S F gi gj x v a ha
    rw [hd,hcount] at hg
    exact (hsplit.trans (Nat.add_le_add ht hg)).trans (by
      unfold pairMCost
      rw [if_pos hgap]
      exact le_max_left _ _)
  · have hk0 : F tk (child x v (!c))=true := by cases he : F tk (child x v (!c)) <;> simp_all
    have hk1 : F uk (child x v c)=true := by cases he : F uk (child x v c) <;> simp_all
    have hguard : q < (guardFailures S F gk x v).card := by
      by_contra hn
      exact hk ⟨hk0,hk1,by omega⟩
    have hlt : gk<gj := by
      apply lt_of_le_of_ne hgkj
      intro he
      rw [he,hcount] at hguard
      omega
    have hex : ∃ w ∈ guardFailures S F gk x v, w ∉ guardFailures S F gj x v := by
      by_contra hn
      have hsub : guardFailures S F gk x v ⊆ guardFailures S F gj x v := by
        intro w hw
        by_contra hjw
        exact hn ⟨w,hw,hjw⟩
      have hh := Finset.card_le_card hsub
      omega
    obtain ⟨w,hwk,hwj⟩ := hex
    obtain ⟨hR,hktrue⟩ := (mem_guardFailures S F gk x v w).1 hwk
    have hjfalse : F gj (child x w (S.label v w))=false := by
      cases he : F gj (child x w (S.label v w)) with
      | false => rfl
      | true => exact False.elim (hwj ((mem_guardFailures S F gj x v w).2 ⟨hR,he⟩))
    have hpw := (mem_passingGuards S F gj x v w).2 ⟨hR,hjfalse⟩
    have hg := ordinaryGuardBits_card_special S F gi gj gk x v w a p ha hp hpw hktrue
    rw [hd,hcount] at hg
    have ht := orientedBits_card F ti ui x v c b0 b1 (hb0 _ hk0) (hb1 _ hk1)
    exact (hsplit.trans (Nat.add_le_add ht hg)).trans (by
      unfold pairMCost
      rw [if_pos hlt]
      have he : b0+b1+((degree-q-1)*a+p)=b0+b1+(degree-q-1)*a+p := by omega
      rw [he]
      exact le_max_right _ _)

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.oriented_down_cover
#print axioms ThreeBoundMinmaxTransfer.oriented_pairM_row


