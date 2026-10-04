-- Prove2me | solution 1 for AssumptionsOfPhysics.combined_isPossibility_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:37:44.483473+00:00
-- url     : https://prove2.me/submissions/58a652a4-35ea-4efb-b07e-91b7a31dfef6

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

set_option autoImplicit false

namespace AssumptionsOfPhysics
namespace P95354

universe u

variable {Ω : Type u}

lemma agree {B : Set (Set Ω)} {ω ω' : Ω} (hB : ∀ b ∈ B, (ω ∈ b ↔ ω' ∈ b))
    {s : Set Ω} (hs : NegFinConjCountDisj B s) : (ω ∈ s ↔ ω' ∈ s) := by
  induction hs with
  | basic hb => exact hB _ hb
  | univ => simp
  | compl _ ih => simp only [Set.mem_compl_iff]; exact not_congr ih
  | inter _ _ ih₁ ih₂ => simp only [Set.mem_inter_iff]; exact and_congr ih₁ ih₂
  | iUnion f _ ih => simp only [Set.mem_iUnion]; exact exists_congr ih

lemma nmono {B C : Set (Set Ω)} (h : ∀ s ∈ B, NegFinConjCountDisj C s)
    {s : Set Ω} (hs : NegFinConjCountDisj B s) : NegFinConjCountDisj C s := by
  induction hs with
  | basic hb => exact h _ hb
  | univ => exact .univ
  | compl _ ih => exact .compl ih
  | inter _ _ ih₁ ih₂ => exact .inter ih₁ ih₂
  | iUnion f _ ih => exact .iUnion f ih

lemma ofFin {B : Set (Set Ω)} {s : Set Ω} (hs : FinConjCountDisj B s) :
    NegFinConjCountDisj B s := by
  induction hs with
  | basic hb => exact .basic hb
  | univ => exact .univ
  | empty => simpa using (NegFinConjCountDisj.compl (B := B) NegFinConjCountDisj.univ)
  | inter _ _ ih₁ ih₂ => exact .inter ih₁ ih₂
  | iUnion f _ ih => exact .iUnion f ih

lemma iInter_mem {B : Set (Set Ω)} (f : ℕ → Set Ω) (hf : ∀ n, NegFinConjCountDisj B (f n)) :
    NegFinConjCountDisj B (⋂ n, f n) := by
  have : (⋂ n, f n) = (⋃ n, (f n)ᶜ)ᶜ := by simp
  rw [this]
  exact .compl (.iUnion _ fun n => .compl (hf n))

def atom (D : ExperimentalDomain Ω) (ω : Ω) : Set Ω :=
  {ω' | ∀ s ∈ D.theoretical, ω ∈ s → ω' ∈ s}

lemma mem_atom_iff (D : ExperimentalDomain Ω) (ω ω' : Ω) :
    ω' ∈ atom D ω ↔ ∀ s ∈ D.theoretical, (ω ∈ s ↔ ω' ∈ s) := by
  constructor
  · intro h s hs
    refine ⟨h s hs, fun h' => ?_⟩
    by_contra hc
    have hcs : sᶜ ∈ D.theoretical := NegFinConjCountDisj.compl hs
    exact (h sᶜ hcs hc) h'
  · intro h s hs hω
    exact (h s hs).1 hω

lemma stmts_sub (D : ExperimentalDomain Ω) {s : Set Ω} (hs : s ∈ D.stmts) :
    s ∈ D.theoretical :=
  NegFinConjCountDisj.basic hs

lemma atom_mem (D : ExperimentalDomain Ω) (ω : Ω) : atom D ω ∈ D.theoretical := by
  classical
  obtain ⟨B, hBc, hBsub, hBgen⟩ := D.exists_countable_basis
  let T : Set Ω → Set Ω := fun b => if ω ∈ b then b else bᶜ
  have hTω : ∀ b, ω ∈ T b := by
    intro b
    by_cases hω : ω ∈ b <;> simp [T, hω]
  have hB' : (insert Set.univ B).Countable := hBc.insert _
  obtain ⟨f, hf⟩ := hB'.exists_eq_range (Set.insert_nonempty _ _)
  have hTmem : ∀ n, T (f n) ∈ D.theoretical := by
    intro n
    have hfn : f n ∈ insert Set.univ B := by rw [hf]; exact ⟨n, rfl⟩
    have hth : f n ∈ D.theoretical := by
      rcases hfn with h | h
      · rw [h]; exact NegFinConjCountDisj.univ
      · exact stmts_sub D (hBsub h)
    by_cases hω : ω ∈ f n
    · simp only [T, if_pos hω]; exact hth
    · simp only [T, if_neg hω]; exact NegFinConjCountDisj.compl hth
  have heq : atom D ω = ⋂ n, T (f n) := by
    ext ω'
    simp only [Set.mem_iInter]
    constructor
    · intro h n
      exact h _ (hTmem n) (hTω _)
    · intro h
      rw [mem_atom_iff]
      intro s hs
      have hs' : NegFinConjCountDisj B s :=
        nmono (fun t ht => ofFin (hBgen t ht)) hs
      refine agree (fun b hb => ?_) hs'
      have hbB : b ∈ insert Set.univ B := Set.mem_insert_of_mem _ hb
      rw [hf] at hbB
      obtain ⟨n, hn⟩ := hbB
      have h1 := h n
      rw [hn] at h1
      by_cases hω : ω ∈ b
      · simp only [T, if_pos hω] at h1; exact ⟨fun _ => h1, fun _ => hω⟩
      · simp only [T, if_neg hω, Set.mem_compl_iff] at h1
        exact ⟨fun h2 => absurd h2 hω, fun h2 => absurd h2 h1⟩
  rw [heq]
  exact iInter_mem _ hTmem

lemma isPoss_atom (D : ExperimentalDomain Ω) (ω : Ω) : D.IsPossibility (atom D ω) := by
  refine ⟨atom_mem D ω, ⟨ω, fun s _ h => h⟩, fun s hs => ?_⟩
  by_cases hω : ω ∈ s
  · left
    intro ω' h'
    exact h' s hs hω
  · right
    rw [Set.disjoint_left]
    intro ω' h' hs'
    exact hω (((mem_atom_iff D ω ω').1 h' s hs).2 hs')

lemma eq_atom (D : ExperimentalDomain Ω) {x : Set Ω} (h : D.IsPossibility x) {ω : Ω}
    (hωx : ω ∈ x) : x = atom D ω := by
  ext ω'
  constructor
  · intro hx' s hs hωs
    rcases h.2.2 s hs with hsub | hdisj
    · exact hsub hx'
    · exact (Set.disjoint_left.1 hdisj hωx hωs).elim
  · intro h'
    exact h' x h.1 hωx

lemma comb_theo_sub {ι : Type*} [Countable ι] (Dfam : ι → ExperimentalDomain Ω)
    {s : Set Ω} (hs : s ∈ (ExperimentalDomain.combined Dfam).theoretical) :
    NegFinConjCountDisj (⋃ i, (Dfam i).stmts) s :=
  nmono (fun t ht => ofFin ht) hs

lemma theo_i_sub {ι : Type*} [Countable ι] (Dfam : ι → ExperimentalDomain Ω) (i : ι)
    {s : Set Ω} (hs : s ∈ (Dfam i).theoretical) :
    s ∈ (ExperimentalDomain.combined Dfam).theoretical :=
  nmono (fun t ht => NegFinConjCountDisj.basic
    (show t ∈ (ExperimentalDomain.combined Dfam).stmts from
      FinConjCountDisj.basic (Set.mem_iUnion.2 ⟨i, ht⟩))) hs

lemma atom_comb {ι : Type*} [Countable ι] (Dfam : ι → ExperimentalDomain Ω) (ω : Ω) :
    atom (ExperimentalDomain.combined Dfam) ω = ⋂ i, atom (Dfam i) ω := by
  ext ω'
  simp only [Set.mem_iInter]
  constructor
  · intro h i s hs hω
    exact h s (theo_i_sub Dfam i hs) hω
  · intro h
    rw [mem_atom_iff]
    intro s hs
    refine agree (fun b hb => ?_) (comb_theo_sub Dfam hs)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hb
    exact (mem_atom_iff _ _ _).1 (h i) b (stmts_sub _ hi)

end P95354
end AssumptionsOfPhysics

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} {ι : Type*} [Countable ι]
    (Dfam : ι → ExperimentalDomain Ω) (x : Set Ω) :
    (ExperimentalDomain.combined Dfam).IsPossibility x ↔
      x.Nonempty ∧ ∃ xs : ι → Set Ω, (∀ i, (Dfam i).IsPossibility (xs i)) ∧ x = ⋂ i, xs i := by
  constructor
  · intro h
    obtain ⟨ω, hω⟩ := h.2.1
    refine ⟨h.2.1, fun i => P95354.atom (Dfam i) ω, fun i => P95354.isPoss_atom _ ω, ?_⟩
    rw [P95354.eq_atom _ h hω, P95354.atom_comb]
  · rintro ⟨⟨ω, hω⟩, xs, hxs, rfl⟩
    have e : (⋂ i, xs i) = ⋂ i, P95354.atom (Dfam i) ω :=
      Set.iInter_congr fun i => P95354.eq_atom _ (hxs i) (Set.mem_iInter.1 hω i)
    rw [e, ← P95354.atom_comb]
    exact P95354.isPoss_atom _ ω
