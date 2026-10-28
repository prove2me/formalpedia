-- Prove2me | Definitions.Def_BS2_b3ba934b_WitnessLifting
-- name    : BS2_b3ba934b_WitnessLifting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:36:01.93238+00:00
-- url     : https://prove2.me/theorems/68626467-bbb8-470f-aeca-edf3b3b25b6a
-- title:
--   Sensitivity separation: WitnessLifting (complete source module)
-- statement:
--   Complete Lean source module `WitnessLifting` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/WitnessLifting.lean; original SHA-256 3de5b42744f1a0f912bff6a7825dc8a21c88ce1eeb9e3364123000d6bca68bcc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}

structure Stage (L I V : Type) where
  Adj : V → V → Prop
  loopless : ∀ v, ¬ Adj v v
  label : V → V → Bool
  guard : L → L
  tolerance : L → ℕ
  target : L → ℕ → (I → Bool) → (I → Bool) → Bool

def child (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) : I → Bool :=
  fun i => x ((v,c),i)

noncomputable def failed [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => S.Adj v w ∧ F (S.guard l) (child x w (S.label v w)) = true

noncomputable def parent [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) : Bool := by
  classical
  exact decide (∃ v : V, (failed S F l x v).card ≤ S.tolerance l ∧
    S.target l (failed S F l x v).card (child x v false) (child x v true) = true)

theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤ S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]

theorem parent_false_of_targets_false [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool)
    (h : ∀ v : V,
      S.target l (failed S F l x v).card (child x v false) (child x v true) = false) :
    parent S F l x = false := by
  classical
  simp only [parent, decide_eq_false_iff_not]
  rintro ⟨v, _, hv⟩
  rw [h v] at hv
  contradiction

def replicate (z : I → Bool) : ((V × Bool) × I) → Bool := fun p => z p.2

noncomputable def planted (z p : I → Bool) (v : V) : ((V × Bool) × I) → Bool := by
  classical
  exact fun q => if q.1.1 = v then p q.2 else z q.2

@[simp] theorem child_replicate (z : I → Bool) (v : V) (c : Bool) :
    child (replicate z) v c = z := rfl

@[simp] theorem child_planted_same (z p : I → Bool) (v : V) (c : Bool) :
    child (planted z p v) v c = p := by
  classical
  funext i
  simp [child, planted]

theorem child_planted_other (z p : I → Bool) (v w : V) (c : Bool) (hw : w ≠ v) :
    child (planted z p v) w c = z := by
  classical
  funext i
  simp [child, planted, hw]

theorem planted_failed_empty [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (v : V) (l : L) :
    failed S F l (planted z p v) v = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro w _ hw
  have hwv : w ≠ v := by
    intro he
    subst w
    exact S.loopless v hw.1
  rw [child_planted_other z p v w (S.label v w) hwv, hz] at hw
  exact Bool.noConfusion hw.2

theorem parent_accepts_planted [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (hp : ∀ l, F l p = true)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true) (v : V) (l : L) :
    parent S F l (planted z p v) = true := by
  apply (parent_true_iff S F l _).2
  refine ⟨v, ?_, ?_⟩
  · simp [planted_failed_empty S F z p hz v l]
  · simpa only [planted_failed_empty S F z p hz v l, Finset.card_empty,
      child_planted_same] using haccept l p p hp hp

theorem parent_rejects_replicated [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z : I → Bool)
    (hz : ∀ l, F l z = false)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (l : L) : parent S F l (replicate z) = false := by
  apply parent_false_of_targets_false
  intro v
  exact hreject l _ z z (Or.inl hz)

theorem child_flip_same (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (i : I) :
    child (flip x {((v,c),i)}) v c = flip (child x v c) {i} := by
  classical
  funext a
  simp [child, OAI.Paper320.flip]

theorem child_flip_other (x : ((V × Bool) × I) → Bool)
    (v w : V) (c e : Bool) (i : I) (h : (w,e) ≠ (v,c)) :
    child (flip x {((v,c),i)}) w e = child x w e := by
  classical
  funext a
  have hh : ((w,e),a) ≠ ((v,c),i) := by
    intro he
    exact h (congrArg Prod.fst he)
  simp [child, OAI.Paper320.flip, hh]

theorem parent_rejects_after_planted_flip [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (z p : I → Bool)
    (hz : ∀ l, F l z = false) (i : I) (hi : ∀ l, F l (flip p {i}) = false)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (v : V) (c : Bool) (l : L) :
    parent S F l (flip (planted z p v) {((v,c),i)}) = false := by
  classical
  apply parent_false_of_targets_false
  intro w
  by_cases hw : w = v
  · subst w
    cases c
    · apply hreject
      exact Or.inl (by simpa only [child_flip_same, child_planted_same] using hi)
    · apply hreject
      exact Or.inr (by simpa only [child_flip_same, child_planted_same] using hi)
  · apply hreject
    apply Or.inl
    have hpairs : (w,false) ≠ (v,c) := by
      intro he
      exact hw (congrArg Prod.fst he)
    simpa only [child_flip_other _ v w c false i hpairs,
      child_planted_other z p v w false hw] using hz

/-- The positive common witness doubles its indexed sensitive-bit set. -/
theorem common_positive_lift [Fintype V] {A : Type}
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (z p : I → Bool) (hz : ∀ l, F l z = false) (hp : ∀ l, F l p = true)
    (e : A ↪ I) (he : ∀ a l, F l (flip p {e a}) = false)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (v : V) :
    ∃ (p' : ((V × Bool) × I) → Bool) (e' : (Bool × A) ↪ ((V × Bool) × I)),
      (∀ l, parent S F l p' = true) ∧
      (∀ a l, parent S F l (flip p' {e' a}) = false) := by
  let e' : (Bool × A) ↪ ((V × Bool) × I) :=
    ⟨fun a => ((v,a.1),e a.2), by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun q => q.1.2) h
      · exact e.injective (congrArg Prod.snd h)⟩
  refine ⟨planted z p v, e', ?_, ?_⟩
  · exact fun l => parent_accepts_planted S F z p hz hp haccept v l
  · intro a l
    exact parent_rejects_after_planted_flip S F z p hz (e a.2)
      (he a.2) hreject v a.1 l

noncomputable def pairedBlock (v : V) (B : Finset I) : Finset ((V × Bool) × I) := by
  classical
  exact ((Finset.univ : Finset Bool).product B).map
    ⟨fun q => ((v,q.1),q.2), by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun q => q.1.2) h
      · exact congrArg (fun q => q.2) h⟩

@[simp] theorem mem_pairedBlock (v w : V) (c : Bool) (i : I) (B : Finset I) :
    ((w,c),i) ∈ pairedBlock v B ↔ w = v ∧ i ∈ B := by
  classical
  unfold pairedBlock
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨b,j⟩, hj, heq⟩
    change ((v,b),j) = ((w,c),i) at heq
    cases heq
    exact ⟨rfl, (Finset.mem_product.mp hj).2⟩
  · rintro ⟨rfl, hi⟩
    exact ⟨(c,i), Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

theorem pairedBlock_nonempty (v : V) (B : Finset I) (hB : B.Nonempty) :
    (pairedBlock v B).Nonempty := by
  obtain ⟨i, hi⟩ := hB
  exact ⟨((v,false),i), (mem_pairedBlock v v false i B).2 ⟨rfl,hi⟩⟩

theorem pairedBlock_disjoint {A : Type} (B : A → Finset I)
    (hB : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (v w : V) (a b : A) (h : (v,a) ≠ (w,b)) :
    Disjoint (pairedBlock v (B a)) (pairedBlock w (B b)) := by
  classical
  apply Finset.disjoint_left.mpr
  rintro ⟨⟨u,c⟩,i⟩ hi hj
  obtain ⟨huv, hia⟩ := (mem_pairedBlock v u c i (B a)).1 hi
  obtain ⟨huw, hib⟩ := (mem_pairedBlock w u c i (B b)).1 hj
  have hvw : v = w := huv.symm.trans huw
  have hab : a ≠ b := by
    intro he
    exact h (Prod.ext hvw he)
  exact (Finset.disjoint_left.mp (hB a b hab)) hia hib

theorem flip_replicate_pairedBlock (z : I → Bool) (v : V) (B : Finset I) :
    flip (replicate z) (pairedBlock v B) = planted z (flip z B) v := by
  classical
  funext q
  rcases q with ⟨⟨w,c⟩,i⟩
  by_cases hw : w = v <;> by_cases hi : i ∈ B <;>
    simp [OAI.Paper320.flip, replicate, planted, hw, hi]

/-- The common zero-input block witness multiplies its index set by V. -/
theorem common_blocks_lift [Fintype V] {A : Type}
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (z : I → Bool) (hz : ∀ l, F l z = false)
    (B : A → Finset I) (hne : ∀ a, (B a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hflip : ∀ a l, F l (flip z (B a)) = true)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false) :
    ∃ (z' : ((V × Bool) × I) → Bool) (B' : (V × A) → Finset ((V × Bool) × I)),
      (∀ l, parent S F l z' = false) ∧
      (∀ a, (B' a).Nonempty) ∧
      (∀ a b, a ≠ b → Disjoint (B' a) (B' b)) ∧
      (∀ a l, parent S F l (flip z' (B' a)) = true) := by
  let B' : (V × A) → Finset ((V × Bool) × I) := fun a => pairedBlock a.1 (B a.2)
  refine ⟨replicate z, B', ?_, ?_, ?_, ?_⟩
  · exact fun l => parent_rejects_replicated S F z hz hreject l
  · exact fun a => pairedBlock_nonempty a.1 (B a.2) (hne a.2)
  · exact fun a b h => pairedBlock_disjoint B hdis a.1 b.1 a.2 b.2 h
  · intro a l
    change parent S F l (flip (replicate z) (pairedBlock a.1 (B a.2))) = true
    rw [flip_replicate_pairedBlock]
    exact parent_accepts_planted S F z (flip z (B a.2)) hz (hflip a.2) haccept a.1 l

/-- An injectively indexed family of sensitive coordinates bounds the campaign measure. -/
theorem sensitivity_lower_of_indexed_bits [Fintype I] {A : Type} [Fintype A]
    (f : (I → Bool) → Bool) (x : I → Bool) (e : A ↪ I)
    (he : ∀ a, f (flip x {e a}) ≠ f x) : Fintype.card A ≤ sensitivity f := by
  classical
  have hsub : (Finset.univ.map e) ⊆
      Finset.univ.filter (fun i => f (flip x {i}) ≠ f x) := by
    intro i hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he a⟩
  have hat : Fintype.card A ≤ sensitivityAt f x := by
    simpa only [sensitivityAt, Finset.card_map, Finset.card_univ]
      using Finset.card_le_card hsub
  exact hat.trans (Finset.le_sup (Finset.mem_univ x))

/-- Pairwise disjoint, nonempty sensitive blocks bound the campaign measure. -/
theorem blockSensitivity_lower_of_indexed_blocks [Fintype I] {A : Type} [Fintype A]
    (f : (I → Bool) → Bool) (x : I → Bool) (B : A → Finset I)
    (hne : ∀ a, (B a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hflip : ∀ a, f (flip x (B a)) ≠ f x) :
    Fintype.card A ≤ blockSensitivity f := by
  classical
  have hinj : Function.Injective B := by
    intro a b hab
    by_contra hneab
    obtain ⟨i, hi⟩ := hne a
    have hib : i ∈ B b := by simpa only [hab] using hi
    exact Finset.disjoint_left.mp (hdis a b hneab) hi hib
  let blocks : Finset (Finset I) := Finset.univ.image B
  have hcond : (∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D → Disjoint C D) ∧
      (∀ C ∈ blocks, C.Nonempty ∧ f (flip x C) ≠ f x) := by
    constructor
    · intro C hC D hD hCD
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hD
      exact hdis a b (fun hab => hCD (congrArg B hab))
    · intro C hC
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
      exact ⟨hne a, hflip a⟩
  have hc : blocks.card = Fintype.card A := by
    simp only [blocks, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hat : blocks.card ≤ blockSensitivityAt f x := by
    have hh := Finset.le_sup (f := fun Cs : Finset (Finset I) =>
      if (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) ∧
          (∀ C ∈ Cs, C.Nonempty ∧ f (flip x C) ≠ f x)
      then Cs.card else 0) (Finset.mem_univ blocks)
    calc
      blocks.card = (if (∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D → Disjoint C D) ∧
          (∀ C ∈ blocks, C.Nonempty ∧ f (flip x C) ≠ f x)
        then blocks.card else 0) := (if_pos hcond).symm
      _ ≤ blockSensitivityAt f x := hh
  rw [hc] at hat
  exact hat.trans (Finset.le_sup (Finset.mem_univ x))

theorem parent_sensitivity_lower [Fintype V] [Fintype I] {A : Type} [Fintype A]
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (z p : I → Bool) (hz : ∀ l, F l z = false) (hp : ∀ l, F l p = true)
    (e : A ↪ I) (he : ∀ a l, F l (flip p {e a}) = false)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (v : V) (l : L) :
    2 * Fintype.card A ≤ sensitivity (parent S F l) := by
  obtain ⟨p', e', hp', he'⟩ := common_positive_lift S F z p hz hp e he haccept hreject v
  have h := sensitivity_lower_of_indexed_bits (parent S F l) p' e' (fun a => by
    rw [he' a l, hp' l]
    decide)
  simpa only [Fintype.card_prod, Fintype.card_bool] using h

theorem parent_blockSensitivity_lower [Fintype V] [Fintype I] {A : Type} [Fintype A]
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (z : I → Bool) (hz : ∀ l, F l z = false)
    (B : A → Finset I) (hne : ∀ a, (B a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hflip : ∀ a l, F l (flip z (B a)) = true)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (l : L) :
    Fintype.card V * Fintype.card A ≤ blockSensitivity (parent S F l) := by
  obtain ⟨z', B', hz', hne', hdis', hflip'⟩ :=
    common_blocks_lift S F z hz B hne hdis hflip haccept hreject
  have h := blockSensitivity_lower_of_indexed_blocks (parent S F l) z' B'
    hne' hdis' (fun a => by rw [hflip' a l, hz' l]; decide)
  simpa only [Fintype.card_prod] using h

/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/
def reindex {J : Type} (e : I ≃ J) (f : (I → Bool) → Bool) : (J → Bool) → Bool :=
  fun x => f (fun i => x (e i))

theorem flip_reindex {J : Type} (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => OAI.Paper320.flip x (B.map e.toEmbedding) (e i)) =
      OAI.Paper320.flip (fun i => x (e i)) B := by
  classical
  funext i
  simp [OAI.Paper320.flip]

theorem flip_reindex_singleton {J : Type} (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => OAI.Paper320.flip x {e i} (e a)) =
      OAI.Paper320.flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}

theorem sensitivityAt_reindex {J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  classical
  have hs : (Finset.univ.filter fun j =>
      reindex e f (OAI.Paper320.flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (OAI.Paper320.flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => OAI.Paper320.flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex {J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x _
    rw [sensitivityAt_reindex]
    exact Finset.le_sup (Finset.mem_univ _)
  · apply Finset.sup_le
    intro x _
    have h : sensitivityAt (reindex e f) (fun j => x (e.symm j)) ≤
        sensitivity (reindex e f) := Finset.le_sup (Finset.mem_univ _)
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

end ThreeBoundWitness

#print axioms ThreeBoundWitness.common_positive_lift
#print axioms ThreeBoundWitness.common_blocks_lift
#print axioms ThreeBoundWitness.sensitivity_lower_of_indexed_bits
#print axioms ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks
#print axioms ThreeBoundWitness.parent_sensitivity_lower
#print axioms ThreeBoundWitness.parent_blockSensitivity_lower


