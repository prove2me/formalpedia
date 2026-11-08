-- Prove2me | Definitions.Def_friedmann_parity_lib_valuation
-- name    : friedmann_parity_lib_valuation
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T03:37:29.885706+00:00
-- url     : https://prove2.me/theorems/b2cb0a16-300b-43a7-8df4-636c10a3ef06
-- title:
--   Friedmann parity games: optimal counterstrategies and the strategy-improvement step (proved library)
-- statement:
--   A sorry-free library module for the parity-game model `friedmann_parity`. It contains the valuation theory that the exponential lower-bound construction relies on. It adds no new definitions of mathematical objects beyond small helpers such as the one-step successor `step`, the pointwise merge of two counterstrategies, and the locally minimizing counterstrategy.
--
--   When priorities are injective, the valuation order $\preceq$ on triples $(p,P,\ell)$ is a total preorder (in fact antisymmetric), and it agrees with the count-based order of `friedmann_multiplicity`. Plays unfold one step at a time: if $x$ is not its own cycle leader, the play valuation at $x$ is obtained by prepending $x$ to the valuation at its successor. Two comparison principles hold: a function that is consistent, step by step, with a strategy pair bounds that pair's play valuations.
--
--   The main consequences are the existence of an optimal counterstrategy that minimizes from every start vertex at once (Lemma 3.1), the identification of the selected value with the play valuation of that counterstrategy, and the monotonicity and strictness of an improvement step (Theorem 3.2). The theorem names `counterstrategy_exists_lib` and `improvement_strict_lib` carry the suffix `_lib` so that they do not clash with the corresponding mission theorems.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 7(3:19), 2011, arXiv:1106.0778, §3 (Lemma 3.1, Theorem 3.2)

import Definitions.Def_friedmann_parity
import Definitions.Def_friedmann_multiplicity
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false

namespace FriedmannParity

open FriedmannMultiplicity

/-! ### Part 1: Total Preorder of `FriedmannMultiplicity.ValueLE` and Bridge to `FriedmannParity` -/

lemma reward_injective : Function.Injective reward := by
  intro p q hpq
  unfold reward at hpq
  split_ifs at hpq <;> omega

section GeneralOrder

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_refl (G : Game V) (A : Finset V) : SetEquivalent G A A :=
  fun _ => rfl

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_symm {G : Game V} {A B : Finset V} (h : SetEquivalent G A B) :
    SetEquivalent G B A :=
  fun p => (h p).symm

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_trans {G : Game V} {A B C : Finset V}
    (h1 : SetEquivalent G A B) (h2 : SetEquivalent G B C) :
    SetEquivalent G A C :=
  fun p => (h1 p).trans (h2 p)

omit [Fintype V] [DecidableEq V] in
lemma not_multiplicity_setLT_of_setEquivalent {G : Game V} {A B : Finset V}
    (h : SetEquivalent G A B) : ¬ FriedmannMultiplicity.SetLT G A B := by
  rintro ⟨p, hpne, _, _⟩
  exact hpne (h p)

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_congr_left {G : Game V} {A A' B : Finset V}
    (hA : SetEquivalent G A A') (h : FriedmannMultiplicity.SetLT G A B) :
    FriedmannMultiplicity.SetLT G A' B := by
  rcases h with ⟨p, hpne, hgt, hpar⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← hA p]; exact hpne
  · intro q hq; rw [← hA q]; exact hgt q hq
  · rcases hpar with ⟨he, hlt⟩ | ⟨ho, hlt⟩
    · left; rw [← hA p]; exact ⟨he, hlt⟩
    · right; rw [← hA p]; exact ⟨ho, hlt⟩

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_congr_right {G : Game V} {A B B' : Finset V}
    (hB : SetEquivalent G B B') (h : FriedmannMultiplicity.SetLT G A B) :
    FriedmannMultiplicity.SetLT G A B' := by
  rcases h with ⟨p, hpne, hgt, hpar⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← hB p]; exact hpne
  · intro q hq; rw [← hB q]; exact hgt q hq
  · rcases hpar with ⟨he, hlt⟩ | ⟨ho, hlt⟩
    · left; rw [← hB p]; exact ⟨he, hlt⟩
    · right; rw [← hB p]; exact ⟨ho, hlt⟩

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_asymm {G : Game V} {A B : Finset V}
    (h1 : FriedmannMultiplicity.SetLT G A B) (h2 : FriedmannMultiplicity.SetLT G B A) : False := by
  rcases h1 with ⟨p₁, hpne₁, hgt₁, hpar₁⟩
  rcases h2 with ⟨p₂, hpne₂, hgt₂, hpar₂⟩
  rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
  · exact hpne₂ (hgt₁ p₂ hlt).symm
  · rcases hpar₁ with ⟨he₁, hlt₁⟩ | ⟨ho₁, hlt₁⟩ <;>
    rcases hpar₂ with ⟨he₂, hlt₂⟩ | ⟨ho₂, hlt₂⟩ <;> omega
  · exact hpne₁ (hgt₂ p₁ hgt).symm

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_trans {G : Game V} {A B C : Finset V}
    (h1 : FriedmannMultiplicity.SetLT G A B) (h2 : FriedmannMultiplicity.SetLT G B C) :
    FriedmannMultiplicity.SetLT G A C := by
  rcases h1 with ⟨p₁, hpne₁, hgt₁, hpar₁⟩
  rcases h2 with ⟨p₂, hpne₂, hgt₂, hpar₂⟩
  rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
  · refine ⟨p₂, ?_, ?_, ?_⟩
    · rw [hgt₁ p₂ hlt]; exact hpne₂
    · intro q hq
      exact (hgt₁ q (lt_trans hlt hq)).trans (hgt₂ q hq)
    · rw [hgt₁ p₂ hlt]; exact hpar₂
  · refine ⟨p₁, ?_, ?_, ?_⟩
    · rcases hpar₁ with ⟨_, hlt₁⟩ | ⟨_, hlt₁⟩ <;>
      rcases hpar₂ with ⟨_, hlt₂⟩ | ⟨_, hlt₂⟩ <;> omega
    · intro q hq
      exact (hgt₁ q hq).trans (hgt₂ q hq)
    · rcases hpar₁ with ⟨he₁, hlt₁⟩ | ⟨ho₁, hlt₁⟩ <;>
      rcases hpar₂ with ⟨he₂, hlt₂⟩ | ⟨ho₂, hlt₂⟩
      · left; exact ⟨he₁, by omega⟩
      · omega
      · omega
      · right; exact ⟨ho₁, by omega⟩
  · refine ⟨p₁, ?_, ?_, ?_⟩
    · rw [← hgt₂ p₁ hgt]; exact hpne₁
    · intro q hq
      exact (hgt₁ q hq).trans (hgt₂ q (lt_trans hgt hq))
    · rw [← hgt₂ p₁ hgt]; exact hpar₁

omit [Fintype V] [DecidableEq V] in
lemma count_eq_zero_of_sup_lt {G : Game V} {A : Finset V} {q : ℕ}
    (hq : A.sup G.priority < q) : count G A q = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v hv
  have hle : G.priority v ≤ A.sup G.priority := Finset.le_sup hv
  omega

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_trichotomy_aux (G : Game V) (A B : Finset V) :
    ∀ M : ℕ, (∀ q, M < q → count G A q = count G B q) →
      SetEquivalent G A B ∨ FriedmannMultiplicity.SetLT G A B ∨ FriedmannMultiplicity.SetLT G B A
  | 0, hgt => by
    rcases lt_trichotomy (count G A 0) (count G B 0) with hlt | heq | hgt0
    · right; left
      exact ⟨0, by omega, hgt, Or.inl ⟨rfl, hlt⟩⟩
    · left
      intro q
      rcases Nat.eq_zero_or_pos q with rfl | hpos
      · exact heq
      · exact hgt q hpos
    · right; right
      exact ⟨0, by omega, fun q hq => (hgt q hq).symm, Or.inl ⟨rfl, hgt0⟩⟩
  | M + 1, hgt => by
    rcases lt_trichotomy (count G A (M + 1)) (count G B (M + 1)) with hlt | heq | hgt1
    · right; rcases Nat.mod_two_eq_zero_or_one (M + 1) with hpar | hpar
      · left; exact ⟨M + 1, by omega, hgt, Or.inl ⟨hpar, hlt⟩⟩
      · right; exact ⟨M + 1, by omega, fun q hq => (hgt q hq).symm, Or.inr ⟨hpar, hlt⟩⟩
    · apply multiplicity_setLT_trichotomy_aux G A B M
      intro q hq
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hq) with rfl | hq'
      · exact heq
      · exact hgt q hq'
    · right; rcases Nat.mod_two_eq_zero_or_one (M + 1) with hpar | hpar
      · right; exact ⟨M + 1, by omega, fun q hq => (hgt q hq).symm, Or.inl ⟨hpar, hgt1⟩⟩
      · left; exact ⟨M + 1, by omega, hgt, Or.inr ⟨hpar, hgt1⟩⟩

omit [Fintype V] in
lemma multiplicity_setLT_trichotomy (G : Game V) (A B : Finset V) :
    SetEquivalent G A B ∨ FriedmannMultiplicity.SetLT G A B ∨ FriedmannMultiplicity.SetLT G B A := by
  apply multiplicity_setLT_trichotomy_aux G A B ((A ∪ B).sup G.priority)
  intro q hq
  have hA : A.sup G.priority < q :=
    lt_of_le_of_lt (Finset.sup_mono Finset.subset_union_left) hq
  have hB : B.sup G.priority < q :=
    lt_of_le_of_lt (Finset.sup_mono Finset.subset_union_right) hq
  rw [count_eq_zero_of_sup_lt hA, count_eq_zero_of_sup_lt hB]

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_asymm {G : Game V} {a b : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLT G a b) (h2 : FriedmannMultiplicity.ValueLT G b a) : False := by
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩ <;>
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · omega
  · rw [hp2] at hr1; omega
  · rw [hp2] at hr1; omega
  · rw [hp1] at hr2; omega
  · exact multiplicity_setLT_asymm hs1 hs2
  · exact not_multiplicity_setLT_of_setEquivalent (setEquivalent_symm heq2) hs1
  · rw [hp1] at hr2; omega
  · exact not_multiplicity_setLT_of_setEquivalent (setEquivalent_symm heq1) hs2
  · rcases hl1 with ⟨ho1, hlt1⟩ | ⟨he1, hlt1⟩ <;>
    rcases hl2 with ⟨ho2, hlt2⟩ | ⟨he2, hlt2⟩ <;> omega

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_irrefl (G : Game V) (a : Valuation V) :
    ¬ FriedmannMultiplicity.ValueLT G a a :=
  fun h => multiplicity_valueLT_asymm h h

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLE_refl (G : Game V) (a : Valuation V) :
    FriedmannMultiplicity.ValueLE G a a :=
  multiplicity_valueLT_irrefl G a

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLE_total (G : Game V) (a b : Valuation V) :
    FriedmannMultiplicity.ValueLE G a b ∨ FriedmannMultiplicity.ValueLE G b a := by
  by_cases h : FriedmannMultiplicity.ValueLT G b a
  · right; exact fun h' => multiplicity_valueLT_asymm h h'
  · left; exact h

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_trans {G : Game V} {a b c : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLT G a b) (h2 : FriedmannMultiplicity.ValueLT G b c) :
    FriedmannMultiplicity.ValueLT G a c := by
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩ <;>
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · left; omega
  · left; rw [← hp2]; exact hr1
  · left; rw [← hp2]; exact hr1
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_trans hs1 hs2⟩
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_right heq2 hs1⟩
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_left (setEquivalent_symm heq1) hs2⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans heq1 heq2, ?_⟩
    rw [← hp1] at hl2
    rcases hl1 with ⟨ho1, hlt1⟩ | ⟨he1, hlt1⟩ <;>
    rcases hl2 with ⟨ho2, hlt2⟩ | ⟨he2, hlt2⟩
    · left; exact ⟨ho1, by omega⟩
    · omega
    · omega
    · right; exact ⟨he1, by omega⟩

def ValEq (G : Game V) (a b : Valuation V) : Prop :=
  a.cyclePriority = b.cyclePriority ∧
  SetEquivalent G a.path b.path ∧
  a.length = b.length

omit [Fintype V] in
lemma multiplicity_valueLT_trichotomy (G : Game V) (a b : Valuation V) :
    ValEq G a b ∨ FriedmannMultiplicity.ValueLT G a b ∨ FriedmannMultiplicity.ValueLT G b a := by
  rcases lt_trichotomy (reward a.cyclePriority) (reward b.cyclePriority) with hlt | heq | hgt
  · right; left; exact Or.inl hlt
  · have hp : a.cyclePriority = b.cyclePriority := reward_injective heq
    rcases multiplicity_setLT_trichotomy G a.path b.path with hseq | hslt | hsgt
    · rcases lt_trichotomy a.length b.length with hllt | hleq | hlgt
      · right; rcases Nat.mod_two_eq_zero_or_one a.cyclePriority with hpar | hpar
        · right; exact Or.inr (Or.inr ⟨hp.symm, setEquivalent_symm hseq, Or.inr ⟨hp ▸ hpar, hllt⟩⟩)
        · left; exact Or.inr (Or.inr ⟨hp, hseq, Or.inl ⟨hpar, hllt⟩⟩)
      · left; exact ⟨hp, hseq, hleq⟩
      · right; rcases Nat.mod_two_eq_zero_or_one a.cyclePriority with hpar | hpar
        · left; exact Or.inr (Or.inr ⟨hp, hseq, Or.inr ⟨hpar, hlgt⟩⟩)
        · right; exact Or.inr (Or.inr ⟨hp.symm, setEquivalent_symm hseq, Or.inl ⟨hp ▸ hpar, hlgt⟩⟩)
    · right; left; exact Or.inr (Or.inl ⟨hp, hslt⟩)
    · right; right; exact Or.inr (Or.inl ⟨hp.symm, hsgt⟩)
  · right; right; exact Or.inl hgt

omit [Fintype V] in
lemma multiplicity_valueLE_iff (G : Game V) (a b : Valuation V) :
    FriedmannMultiplicity.ValueLE G a b ↔ ValEq G a b ∨ FriedmannMultiplicity.ValueLT G a b := by
  constructor
  · intro h
    rcases multiplicity_valueLT_trichotomy G a b with heq | hlt | hgt
    · exact Or.inl heq
    · exact Or.inr hlt
    · exact False.elim (h hgt)
  · rintro (⟨hp, hseq, hlen⟩ | hlt) hgt
    · rcases hgt with hr | ⟨_, hslt⟩ | ⟨_, _, hl⟩
      · rw [hp] at hr; omega
      · exact not_multiplicity_setLT_of_setEquivalent (setEquivalent_symm hseq) hslt
      · rcases hl with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
    · exact multiplicity_valueLT_asymm hlt hgt

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_of_valEq_of_valueLT {G : Game V} {a b c : Valuation V}
    (h1 : ValEq G a b) (h2 : FriedmannMultiplicity.ValueLT G b c) :
    FriedmannMultiplicity.ValueLT G a c := by
  rcases h1 with ⟨hp1, hseq1, hlen1⟩
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_left (setEquivalent_symm hseq1) hs2⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans hseq1 heq2, ?_⟩
    rw [hp1, hlen1]; exact hl2

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_of_valueLT_of_valEq {G : Game V} {a b c : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLT G a b) (h2 : ValEq G b c) :
    FriedmannMultiplicity.ValueLT G a c := by
  rcases h2 with ⟨hp2, hseq2, hlen2⟩
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩
  · left; rw [← hp2]; exact hr1
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_right hseq2 hs1⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans heq1 hseq2, ?_⟩
    rw [← hlen2]; exact hl1

omit [Fintype V] [DecidableEq V] in
lemma valEq_trans {G : Game V} {a b c : Valuation V}
    (h1 : ValEq G a b) (h2 : ValEq G b c) : ValEq G a c :=
  ⟨h1.1.trans h2.1, setEquivalent_trans h1.2.1 h2.2.1, h1.2.2.trans h2.2.2⟩

omit [Fintype V] in
lemma multiplicity_valueLE_trans {G : Game V} {a b c : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLE G a b) (h2 : FriedmannMultiplicity.ValueLE G b c) :
    FriedmannMultiplicity.ValueLE G a c := by
  rw [multiplicity_valueLE_iff] at h1 h2 ⊢
  rcases h1 with heq1 | hlt1 <;> rcases h2 with heq2 | hlt2
  · exact Or.inl (valEq_trans heq1 heq2)
  · exact Or.inr (multiplicity_valueLT_of_valEq_of_valueLT heq1 hlt2)
  · exact Or.inr (multiplicity_valueLT_of_valueLT_of_valEq hlt1 heq2)
  · exact Or.inr (multiplicity_valueLT_trans hlt1 hlt2)

/-! #### Injective Priority Bridge between `FriedmannParity` and `FriedmannMultiplicity` -/

omit [Fintype V] [DecidableEq V] in
lemma exists_of_count_pos {G : Game V} {A : Finset V} {p : ℕ}
    (h : 0 < count G A p) : ∃ w ∈ A, G.priority w = p := by
  classical
  unfold count at h
  rcases Finset.card_pos.mp h with ⟨w, hw⟩
  rw [Finset.mem_filter] at hw
  exact ⟨w, hw.1, hw.2⟩

omit [Fintype V] in
lemma count_priority_eq_ite_of_injective {G : Game V} (hinj : Function.Injective G.priority)
    (A : Finset V) (u : V) :
    count G A (G.priority u) = if u ∈ A then 1 else 0 := by
  classical
  unfold count
  have hfilt : A.filter (fun v => G.priority v = G.priority u) = if u ∈ A then {u} else ∅ := by
    ext v
    simp only [Finset.mem_filter, hinj.eq_iff]
    split_ifs with hu
    · simp only [Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hu, h⟩⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro hv rfl
      exact hu hv
  rw [hfilt]
  split_ifs <;> simp

omit [Fintype V] [DecidableEq V] in
lemma count_le_one_of_injective {G : Game V} (hinj : Function.Injective G.priority)
    (A : Finset V) (p : ℕ) : count G A p ≤ 1 := by
  classical
  unfold count
  rw [Finset.card_le_one]
  intro u hu v hv
  rw [Finset.mem_filter] at hu hv
  exact hinj (hu.2.trans hv.2.symm)

omit [Fintype V] in
lemma mem_symmDiff_iff_count_ne {G : Game V} (hinj : Function.Injective G.priority)
    (A B : Finset V) (u : V) :
    u ∈ (A \ B) ∪ (B \ A) ↔ count G A (G.priority u) ≠ count G B (G.priority u) := by
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff,
      count_priority_eq_ite_of_injective hinj A u,
      count_priority_eq_ite_of_injective hinj B u]
  by_cases huA : u ∈ A <;> by_cases huB : u ∈ B <;> simp [huA, huB]

omit [Fintype V] in
lemma setEquivalent_iff_eq {G : Game V} (hinj : Function.Injective G.priority)
    (A B : Finset V) : SetEquivalent G A B ↔ A = B := by
  constructor
  · intro h
    ext u
    have hu := h (G.priority u)
    rw [count_priority_eq_ite_of_injective hinj A u,
        count_priority_eq_ite_of_injective hinj B u] at hu
    by_cases huA : u ∈ A <;> by_cases huB : u ∈ B <;> simp_all
  · rintro rfl
    exact fun _ => rfl

omit [Fintype V] in
lemma setLT_iff_multiplicity_setLT {G : Game V} (hinj : Function.Injective G.priority)
    (A B : Finset V) : SetLT G A B ↔ FriedmannMultiplicity.SetLT G A B := by
  constructor
  · rintro ⟨w, hw_mem, hw_max, hw_par⟩
    refine ⟨G.priority w, (mem_symmDiff_iff_count_ne hinj A B w).mp hw_mem, ?_, ?_⟩
    · intro q hq
      by_contra hne
      have hpos : 0 < count G A q ∨ 0 < count G B q := by omega
      rcases hpos with hA | hB
      · rcases exists_of_count_pos hA with ⟨u, _, rfl⟩
        have hu_mem : u ∈ (A \ B) ∪ (B \ A) :=
          (mem_symmDiff_iff_count_ne hinj A B u).mpr hne
        have hle := hw_max u hu_mem
        omega
      · rcases exists_of_count_pos hB with ⟨u, _, rfl⟩
        have hu_mem : u ∈ (A \ B) ∪ (B \ A) :=
          (mem_symmDiff_iff_count_ne hinj A B u).mpr hne
        have hle := hw_max u hu_mem
        omega
    · rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hw_mem
      rw [count_priority_eq_ite_of_injective hinj A w,
          count_priority_eq_ite_of_injective hinj B w]
      rcases hw_par with ⟨he, hwB⟩ | ⟨ho, hwA⟩
      · left
        have hwA : w ∉ A := by
          rcases hw_mem with ⟨_, hnB⟩ | ⟨_, hnA⟩
          · exact False.elim (hnB hwB)
          · exact hnA
        simp [he, hwA, hwB]
      · right
        have hwB : w ∉ B := by
          rcases hw_mem with ⟨_, hnB⟩ | ⟨_, hnA⟩
          · exact hnB
          · exact False.elim (hnA hwA)
        simp [ho, hwA, hwB]
  · rintro ⟨p, hp_ne, hp_max, hp_par⟩
    have hpos : 0 < count G A p ∨ 0 < count G B p := by omega
    have hex : ∃ w, G.priority w = p := by
      rcases hpos with hA | hB
      · rcases exists_of_count_pos hA with ⟨w, _, hw⟩; exact ⟨w, hw⟩
      · rcases exists_of_count_pos hB with ⟨w, _, hw⟩; exact ⟨w, hw⟩
    rcases hex with ⟨w, rfl⟩
    have hw_mem : w ∈ (A \ B) ∪ (B \ A) :=
      (mem_symmDiff_iff_count_ne hinj A B w).mpr hp_ne
    refine ⟨w, hw_mem, ?_, ?_⟩
    · intro u hu_mem
      have hu_ne := (mem_symmDiff_iff_count_ne hinj A B u).mp hu_mem
      by_contra hlt
      exact hu_ne (hp_max (G.priority u) (by omega))
    · rw [count_priority_eq_ite_of_injective hinj A w,
          count_priority_eq_ite_of_injective hinj B w] at hp_par
      rcases hp_par with ⟨he, hlt⟩ | ⟨ho, hlt⟩
      · left
        refine ⟨he, ?_⟩
        by_cases hwB : w ∈ B
        · exact hwB
        · simp [hwB] at hlt
      · right
        refine ⟨ho, ?_⟩
        by_cases hwA : w ∈ A
        · exact hwA
        · simp [hwA] at hlt

omit [Fintype V] in
lemma valEq_iff_eq {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValEq G a b ↔ a = b := by
  unfold ValEq
  rw [setEquivalent_iff_eq hinj]
  cases a; cases b
  simp

omit [Fintype V] in
lemma valueLT_iff_multiplicity_valueLT {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLT G a b ↔ FriedmannMultiplicity.ValueLT G a b := by
  unfold ValueLT FriedmannMultiplicity.ValueLT
  rw [setLT_iff_multiplicity_setLT hinj, setEquivalent_iff_eq hinj]

omit [Fintype V] in
lemma valueLE_iff_multiplicity_valueLE {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLE G a b ↔ FriedmannMultiplicity.ValueLE G a b := by
  unfold ValueLE
  rw [multiplicity_valueLE_iff, valEq_iff_eq hinj, valueLT_iff_multiplicity_valueLT hinj]

omit [Fintype V] in
lemma valueLT_asymm {G : Game V} (hinj : Function.Injective G.priority)
    {a b : Valuation V} (h1 : ValueLT G a b) (h2 : ValueLT G b a) : False := by
  rw [valueLT_iff_multiplicity_valueLT hinj] at h1 h2
  exact multiplicity_valueLT_asymm h1 h2

omit [Fintype V] in
lemma valueLT_irrefl {G : Game V} (hinj : Function.Injective G.priority)
    (a : Valuation V) : ¬ ValueLT G a a :=
  fun h => valueLT_asymm hinj h h

omit [Fintype V] in
lemma valueLT_trans {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLT G a b) (h2 : ValueLT G b c) : ValueLT G a c := by
  rw [valueLT_iff_multiplicity_valueLT hinj] at h1 h2 ⊢
  exact multiplicity_valueLT_trans h1 h2

omit [Fintype V] in
lemma valueLT_trichotomy {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : a = b ∨ ValueLT G a b ∨ ValueLT G b a := by
  rw [← valEq_iff_eq hinj, valueLT_iff_multiplicity_valueLT hinj,
      valueLT_iff_multiplicity_valueLT hinj]
  exact multiplicity_valueLT_trichotomy G a b

omit [Fintype V] in
lemma valueLE_refl (G : Game V) (a : Valuation V) : ValueLE G a a :=
  Or.inl rfl

omit [Fintype V] in
lemma valueLE_iff_not_valueLT {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLE G a b ↔ ¬ ValueLT G b a := by
  rw [valueLE_iff_multiplicity_valueLE hinj]
  unfold FriedmannMultiplicity.ValueLE
  rw [valueLT_iff_multiplicity_valueLT hinj]

omit [Fintype V] in
lemma valueLE_total {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLE G a b ∨ ValueLE G b a := by
  rw [valueLE_iff_multiplicity_valueLE hinj, valueLE_iff_multiplicity_valueLE hinj]
  exact multiplicity_valueLE_total G a b

omit [Fintype V] in
lemma valueLE_trans {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLE G a b) (h2 : ValueLE G b c) : ValueLE G a c := by
  rw [valueLE_iff_multiplicity_valueLE hinj] at h1 h2 ⊢
  exact multiplicity_valueLE_trans h1 h2

omit [Fintype V] in
lemma valueLE_antisymm {G : Game V} (hinj : Function.Injective G.priority)
    {a b : Valuation V} (h1 : ValueLE G a b) (h2 : ValueLE G b a) : a = b := by
  rcases h1 with rfl | hlt1
  · rfl
  · rcases h2 with rfl | hlt2
    · rfl
    · exact False.elim (valueLT_asymm hinj hlt1 hlt2)

omit [Fintype V] in
lemma valueLT_of_valueLE_of_valueLT {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLE G a b) (h2 : ValueLT G b c) : ValueLT G a c := by
  rcases h1 with rfl | hlt1
  · exact h2
  · exact valueLT_trans hinj hlt1 h2

omit [Fintype V] in
lemma valueLT_of_valueLT_of_valueLE {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLT G a b) (h2 : ValueLE G b c) : ValueLT G a c := by
  rcases h2 with rfl | hlt2
  · exact h1
  · exact valueLT_trans hinj h1 hlt2

end GeneralOrder

/-! ### Part 2: General Finite-Orbit and `playValue` Unfolding Lemmas -/

section GeneralOrbit

variable {V : Type} [Fintype V] [DecidableEq V]

def step (G : Game V) (σ τ : V → V) (w : V) : V :=
  if G.owner w = false then σ w else τ w

omit [Fintype V] [DecidableEq V] in
lemma play_eq_iterate (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    play G σ τ v t = (step G σ τ)^[t] v :=
  rfl

omit [Fintype V] [DecidableEq V] in
lemma play_zero (G : Game V) (σ τ : V → V) (v : V) :
    play G σ τ v 0 = v :=
  rfl

omit [Fintype V] [DecidableEq V] in
lemma play_succ (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    play G σ τ v (t + 1) = play G σ τ (step G σ τ v) t :=
  Function.iterate_succ_apply (step G σ τ) t v

omit [Fintype V] [DecidableEq V] in
lemma play_succ' (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    play G σ τ v (t + 1) = step G σ τ (play G σ τ v t) :=
  Function.iterate_succ_apply' (step G σ τ) t v

omit [Fintype V] [DecidableEq V] in
lemma play_add (G : Game V) (σ τ : V → V) (v : V) (a b : ℕ) :
    play G σ τ v (a + b) = play G σ τ (play G σ τ v a) b := by
  simp only [play_eq_iterate]
  rw [Nat.add_comm, Function.iterate_add_apply]

omit [DecidableEq V] in
lemma mem_recurring_iff {π : ℕ → V} {w : V} :
    w ∈ recurring π ↔ ∀ t, ∃ k, t ≤ k ∧ π k = w := by
  classical
  unfold recurring
  simp

omit [DecidableEq V] in
lemma recurring_step (G : Game V) (σ τ : V → V) (v : V) :
    recurring (play G σ τ (step G σ τ v)) = recurring (play G σ τ v) := by
  ext w
  simp only [mem_recurring_iff]
  constructor
  · intro h t
    rcases h t with ⟨k, htk, hk⟩
    refine ⟨k + 1, by omega, ?_⟩
    rw [play_succ]
    exact hk
  · intro h t
    rcases h (t + 1) with ⟨k, htk, hk⟩
    refine ⟨k - 1, by omega, ?_⟩
    rw [← play_succ]
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1]
    exact hk

omit [DecidableEq V] in
lemma recurring_play (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    recurring (play G σ τ (play G σ τ v t)) = recurring (play G σ τ v) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [play_succ, ih, recurring_step]

omit [DecidableEq V] in
lemma recurring_nonempty (G : Game V) (σ τ : V → V) (v : V) :
    (recurring (play G σ τ v)).Nonempty := by
  classical
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hnot : ∀ w : V, ∃ t, ∀ k, t ≤ k → play G σ τ v k ≠ w := by
    intro w
    have hw : w ∉ recurring (play G σ τ v) := by simp [h]
    rw [mem_recurring_iff] at hw
    simpa using hw
  choose B hB using hnot
  let T := Finset.univ.sup B
  let w := play G σ τ v T
  have hle : B w ≤ T := Finset.le_sup (Finset.mem_univ w)
  exact hB w T hle rfl

omit [DecidableEq V] in
lemma exists_play_eq_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    ∃ k, play G σ τ v k = w := by
  rw [mem_recurring_iff] at hw
  rcases hw 0 with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

omit [DecidableEq V] in
lemma step_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    step G σ τ w ∈ recurring (play G σ τ v) := by
  rw [mem_recurring_iff] at hw ⊢
  intro t
  rcases hw t with ⟨k, htk, hk⟩
  refine ⟨k + 1, by omega, ?_⟩
  rw [play_succ', hk]

omit [DecidableEq V] in
lemma play_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) (s : ℕ) :
    play G σ τ w s ∈ recurring (play G σ τ v) := by
  induction s with
  | zero => exact hw
  | succ s ih =>
    rw [play_succ']
    exact step_mem_recurring ih

omit [DecidableEq V] in
lemma exists_pos_play_eq_self_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    ∃ L > 0, play G σ τ w L = w := by
  rw [mem_recurring_iff] at hw
  rcases hw 0 with ⟨t₀, _, ht₀⟩
  rcases hw (t₀ + 1) with ⟨k, htk, hk⟩
  refine ⟨k - t₀, by omega, ?_⟩
  have hadd : t₀ + (k - t₀) = k := by omega
  rw [← ht₀, ← play_add, hadd, hk, ht₀]

omit [DecidableEq V] in
lemma recurring_eq_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    recurring (play G σ τ w) = recurring (play G σ τ v) := by
  rcases exists_play_eq_of_mem_recurring hw with ⟨t₀, rfl⟩
  exact recurring_play G σ τ v t₀

omit [DecidableEq V] in
lemma exists_recurring_eq_sup (G : Game V) (σ τ : V → V) (v : V) :
    ∃ w, w ∈ recurring (play G σ τ v) ∧
      G.priority w = (recurring (play G σ τ v)).sup G.priority := by
  rcases Finset.exists_mem_eq_sup (recurring (play G σ τ v))
    (recurring_nonempty G σ τ v) G.priority with ⟨w, hw, hp⟩
  exact ⟨w, hw, hp.symm⟩

noncomputable def cycleLeader (G : Game V) (σ τ : V → V) (v : V) : V := by
  classical
  let π := play G σ τ v
  let p := (recurring π).sup G.priority
  exact if h : ∃ w, w ∈ recurring π ∧ G.priority w = p
    then Classical.choose h else v

omit [DecidableEq V] in
lemma cycleLeader_eq_choose (G : Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ v = Classical.choose (exists_recurring_eq_sup G σ τ v) := by
  unfold cycleLeader
  dsimp only
  rw [dif_pos (exists_recurring_eq_sup G σ τ v)]

omit [DecidableEq V] in
lemma cycleLeader_mem_recurring (G : Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ v ∈ recurring (play G σ τ v) := by
  rw [cycleLeader_eq_choose]
  exact (Classical.choose_spec (exists_recurring_eq_sup G σ τ v)).1

omit [DecidableEq V] in
lemma priority_cycleLeader (G : Game V) (σ τ : V → V) (v : V) :
    G.priority (cycleLeader G σ τ v) =
      (recurring (play G σ τ v)).sup G.priority := by
  rw [cycleLeader_eq_choose]
  exact (Classical.choose_spec (exists_recurring_eq_sup G σ τ v)).2

omit [DecidableEq V] in
lemma cycleLeader_step (G : Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ (step G σ τ v) = cycleLeader G σ τ v := by
  rw [cycleLeader_eq_choose, cycleLeader_eq_choose]
  have hrec := recurring_step G σ τ v
  congr! 2
  all_goals rw [hrec]

omit [Fintype V] [DecidableEq V] in
lemma exists_lt_of_play_eq_of_add {G : Game V} {σ τ : V → V} {v w : V} {i j : ℕ}
    (hij : i < j) (heq : play G σ τ v i = play G σ τ v j) :
    ∀ d : ℕ, play G σ τ v (i + d) = w →
      ∃ r < j, play G σ τ v r = w := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hlt : i + d < j
    · exact ⟨i + d, hlt, hd⟩
    · have hlt' : i + d - j < d := by omega
      apply ih (i + d - j) hlt'
      have h1 : j + (i + d - j) = i + d := by omega
      rw [play_add, heq, ← play_add, h1, hd]

omit [DecidableEq V] in
lemma exists_lt_of_play_eq_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v))
    {i j : ℕ} (hij : i < j)
    (heq : play G σ τ v i = play G σ τ v j) :
    ∃ r < j, play G σ τ v r = w := by
  rw [mem_recurring_iff] at hw
  rcases hw i with ⟨k, hik, hk⟩
  have hk' : i + (k - i) = k := by omega
  rw [← hk'] at hk
  exact exists_lt_of_play_eq_of_add hij heq (k - i) hk

omit [DecidableEq V] in
lemma exists_play_eq_cycleLeader (G : Game V) (σ τ : V → V) (v : V) :
    ∃ k : ℕ, play G σ τ v k = cycleLeader G σ τ v :=
  exists_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v)

lemma playValue_cyclePriority (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ v).cyclePriority =
      (recurring (play G σ τ v)).sup G.priority :=
  rfl

lemma playValue_cyclePriority_eq_priority_cycleLeader
    (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ v).cyclePriority = G.priority (cycleLeader G σ τ v) :=
  (priority_cycleLeader G σ τ v).symm

lemma playValue_cyclePriority_step (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ (step G σ τ v)).cyclePriority =
      (playValue G σ τ v).cyclePriority := by
  simp only [playValue_cyclePriority, recurring_step]

lemma playValue_length_eq_find (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ v).length =
      Nat.find (exists_play_eq_cycleLeader G σ τ v) := by
  classical
  change (if h : ∃ k : ℕ, play G σ τ v k = cycleLeader G σ τ v
    then Nat.find h else 0) = _
  rw [dif_pos (exists_play_eq_cycleLeader G σ τ v)]

lemma play_playValue_length (G : Game V) (σ τ : V → V) (v : V) :
    play G σ τ v (playValue G σ τ v).length =
      cycleLeader G σ τ v := by
  rw [playValue_length_eq_find]
  exact Nat.find_spec (exists_play_eq_cycleLeader G σ τ v)

lemma play_ne_cycleLeader_of_lt_length {G : Game V} {σ τ : V → V} {v : V} {t : ℕ}
    (ht : t < (playValue G σ τ v).length) :
    play G σ τ v t ≠ cycleLeader G σ τ v := by
  rw [playValue_length_eq_find] at ht
  exact Nat.find_min (exists_play_eq_cycleLeader G σ τ v) ht

lemma length_le_of_play_eq_cycleLeader (G : Game V) (σ τ : V → V) (v : V) {t : ℕ}
    (ht : play G σ τ v t = cycleLeader G σ τ v) :
    (playValue G σ τ v).length ≤ t := by
  rw [playValue_length_eq_find]
  exact Nat.find_min' (exists_play_eq_cycleLeader G σ τ v) ht

lemma play_injective_of_le_length (G : Game V) (σ τ : V → V) (v : V) {i j : ℕ}
    (hi : i ≤ (playValue G σ τ v).length)
    (hj : j ≤ (playValue G σ τ v).length)
    (heq : play G σ τ v i = play G σ τ v j) :
    i = j := by
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · rcases exists_lt_of_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v) hlt heq with
      ⟨r, hrj, hr⟩
    exact False.elim (play_ne_cycleLeader_of_lt_length (lt_of_lt_of_le hrj hj) hr)
  · rfl
  · rcases exists_lt_of_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v) hgt heq.symm with
      ⟨r, hri, hr⟩
    exact False.elim (play_ne_cycleLeader_of_lt_length (lt_of_lt_of_le hri hi) hr)

lemma mem_playValue_path_iff {G : Game V} {σ τ : V → V} {v u : V} :
    u ∈ (playValue G σ τ v).path ↔
      (∃ t < (playValue G σ τ v).length, play G σ τ v t = u) ∧
      (playValue G σ τ v).cyclePriority < G.priority u := by
  classical
  change u ∈ ((Finset.range (playValue G σ τ v).length).image
    (play G σ τ v)).filter
    (fun w => (playValue G σ τ v).cyclePriority < G.priority w) ↔ _
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]

lemma playValue_path_eq_empty_of_mem_recurring {G : Game V} {σ τ : V → V} {v x : V}
    (hx : x ∈ recurring (play G σ τ v)) :
    (playValue G σ τ x).path = ∅ := by
  ext u
  rw [mem_playValue_path_iff]
  simp only [Finset.notMem_empty, iff_false, not_and]
  rintro ⟨t, _, rfl⟩
  have hmem : play G σ τ x t ∈ recurring (play G σ τ x) :=
    play_mem_recurring (by rw [recurring_eq_of_mem_recurring hx]; exact hx) t
  have hle : G.priority (play G σ τ x t) ≤ (playValue G σ τ x).cyclePriority :=
    Finset.le_sup hmem
  omega

lemma playValue_eq_of_eq_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u = cycleLeader G σ τ u) :
    playValue G σ τ u = ⟨(playValue G σ τ u).cyclePriority, ∅, 0⟩ := by
  have hlen : (playValue G σ τ u).length = 0 := by
    have h0 : (playValue G σ τ u).length ≤ 0 :=
      length_le_of_play_eq_cycleLeader G σ τ u hu
    omega
  have hpath : (playValue G σ τ u).path = ∅ := by
    ext x
    rw [mem_playValue_path_iff, hlen]
    simp
  cases h : playValue G σ τ u
  simp only [h] at hlen hpath ⊢
  subst hlen hpath
  rfl

noncomputable def prepend (G : Game V) (u : V) (a : Valuation V) : Valuation V := by
  classical
  exact ⟨a.cyclePriority,
    if a.cyclePriority < G.priority u then insert u a.path else a.path,
    a.length + 1⟩

lemma playValue_length_eq_succ_of_ne_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    (playValue G σ τ u).length =
      (playValue G σ τ (step G σ τ u)).length + 1 := by
  have hpos : 0 < (playValue G σ τ u).length := by
    by_contra h0
    have hzero : (playValue G σ τ u).length = 0 := by omega
    have hplay := play_playValue_length G σ τ u
    rw [hzero, play_zero] at hplay
    exact hu hplay
  have hle1 : (playValue G σ τ (step G σ τ u)).length ≤
      (playValue G σ τ u).length - 1 := by
    apply length_le_of_play_eq_cycleLeader G σ τ (step G σ τ u)
    rw [cycleLeader_step, ← play_succ]
    have h1 : (playValue G σ τ u).length - 1 + 1 = (playValue G σ τ u).length := by omega
    rw [h1]
    exact play_playValue_length G σ τ u
  have hle2 : (playValue G σ τ u).length ≤
      (playValue G σ τ (step G σ τ u)).length + 1 := by
    apply length_le_of_play_eq_cycleLeader G σ τ u
    rw [play_succ, ← cycleLeader_step]
    exact play_playValue_length G σ τ (step G σ τ u)
  omega

lemma notMem_playValue_step_path_of_ne_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    u ∉ (playValue G σ τ (step G σ τ u)).path := by
  rw [mem_playValue_path_iff]
  rintro ⟨⟨t, ht, hplay⟩, _⟩
  have hlen : (playValue G σ τ u).length =
      (playValue G σ τ (step G σ τ u)).length + 1 :=
    playValue_length_eq_succ_of_ne_cycleLeader hu
  rw [← play_succ] at hplay
  have h0 : play G σ τ u (t + 1) = play G σ τ u 0 := hplay
  have hinj := play_injective_of_le_length G σ τ u (by omega) (by omega) h0
  omega

lemma playValue_eq_prepend_of_ne_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    playValue G σ τ u = prepend G u (playValue G σ τ (step G σ τ u)) := by
  classical
  have hcp := (playValue_cyclePriority_step G σ τ u).symm
  have hlen : (playValue G σ τ u).length =
      (playValue G σ τ (step G σ τ u)).length + 1 :=
    playValue_length_eq_succ_of_ne_cycleLeader hu
  have hpath : (playValue G σ τ u).path =
      if (playValue G σ τ (step G σ τ u)).cyclePriority < G.priority u
      then insert u (playValue G σ τ (step G σ τ u)).path
      else (playValue G σ τ (step G σ τ u)).path := by
    ext x
    rw [mem_playValue_path_iff, hlen, playValue_cyclePriority_step]
    split_ifs with hpu
    · simp only [Finset.mem_insert, mem_playValue_path_iff, playValue_cyclePriority_step]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hpx⟩
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · left; rfl
        · right
          refine ⟨⟨t - 1, by omega, ?_⟩, hpx⟩
          rw [← play_succ]
          have ht1 : t - 1 + 1 = t := by omega
          rw [ht1]
      · rintro (rfl | ⟨⟨t, ht, rfl⟩, hpx⟩)
        · exact ⟨⟨0, by omega, rfl⟩, hpu⟩
        · refine ⟨⟨t + 1, by omega, ?_⟩, hpx⟩
          rw [play_succ]
    · simp only [mem_playValue_path_iff, playValue_cyclePriority_step]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hpx⟩
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exact False.elim (hpu hpx)
        · refine ⟨⟨t - 1, by omega, ?_⟩, hpx⟩
          rw [← play_succ]
          have ht1 : t - 1 + 1 = t := by omega
          rw [ht1]
      · rintro ⟨⟨t, ht, rfl⟩, hpx⟩
        refine ⟨⟨t + 1, by omega, ?_⟩, hpx⟩
        rw [play_succ]
  unfold prepend
  cases hpv : playValue G σ τ u
  cases hpv' : playValue G σ τ (step G σ τ u)
  simp only [hpv, hpv'] at hcp hlen hpath ⊢
  congr!

omit [Fintype V] in
lemma count_insert_of_notMem {G : Game V} {A : Finset V} {u : V}
    (hu : u ∉ A) (q : ℕ) :
    count G (insert u A) q = count G A q + (if G.priority u = q then 1 else 0) := by
  classical
  unfold count
  rw [Finset.filter_insert]
  split_ifs with hq
  · rw [Finset.card_insert_of_notMem]
    simp [hu]
  · omega

omit [Fintype V] in
lemma count_prepend_of_notMem {G : Game V} {a : Valuation V}
    {u : V} (hu : u ∉ a.path) (q : ℕ) :
    count G (prepend G u a).path q =
      count G a.path q + (if a.cyclePriority < G.priority u ∧ G.priority u = q then 1 else 0) := by
  classical
  change count G (if a.cyclePriority < G.priority u then insert u a.path else a.path) q = _
  by_cases h1 : a.cyclePriority < G.priority u
  · rw [if_pos h1, count_insert_of_notMem hu]
    by_cases h2 : G.priority u = q
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), Nat.add_zero]

omit [Fintype V] in
lemma multiplicity_valueLE_prepend {G : Game V} {a b : Valuation V} {u : V}
    (hp : a.cyclePriority = b.cyclePriority) (hua : u ∉ a.path) (hub : u ∉ b.path)
    (hab : FriedmannMultiplicity.ValueLE G a b) :
    FriedmannMultiplicity.ValueLE G (prepend G u a) (prepend G u b) := by
  intro hlt
  apply hab
  have hcnt : ∀ q, count G (prepend G u a).path q =
      count G a.path q + (if a.cyclePriority < G.priority u ∧ G.priority u = q then 1 else 0) :=
    count_prepend_of_notMem hua
  have hcnt' : ∀ q, count G (prepend G u b).path q =
      count G b.path q + (if a.cyclePriority < G.priority u ∧ G.priority u = q then 1 else 0) := by
    intro q
    rw [count_prepend_of_notMem hub q, hp]
  rcases hlt with hr | ⟨_, ⟨p, hpne, hgt, hpar⟩⟩ | ⟨_, hseq, hl⟩
  · left
    exact hr
  · right; left
    refine ⟨hp.symm, p, ?_, ?_, ?_⟩
    · intro heq
      apply hpne
      rw [hcnt p, hcnt' p, heq]
    · intro q hq
      have hq' := hgt q hq
      rw [hcnt q, hcnt' q] at hq'
      omega
    · rcases hpar with ⟨he, hltp⟩ | ⟨ho, hltp⟩
      · left
        rw [hcnt p, hcnt' p] at hltp
        exact ⟨he, by omega⟩
      · right
        rw [hcnt p, hcnt' p] at hltp
        exact ⟨ho, by omega⟩
  · right; right
    refine ⟨hp.symm, ?_, ?_⟩
    · intro q
      have hq := hseq q
      rw [hcnt q, hcnt' q] at hq
      omega
    · change (b.cyclePriority % 2 = 1 ∧ b.length + 1 < a.length + 1) ∨
        (b.cyclePriority % 2 = 0 ∧ a.length + 1 < b.length + 1) at hl
      rcases hl with ⟨ho, hltl⟩ | ⟨he, hltl⟩
      · left; exact ⟨ho, by omega⟩
      · right; exact ⟨he, by omega⟩

lemma count_playValue_step {G : Game V} {σ τ : V → V} {u : V} {q : ℕ}
    (hq : (playValue G σ τ u).cyclePriority < q) :
    count G (playValue G σ τ u).path q =
      count G (playValue G σ τ (step G σ τ u)).path q +
        (if G.priority u = q then 1 else 0) := by
  by_cases hu : u = cycleLeader G σ τ u
  · have hpu : G.priority u = (playValue G σ τ u).cyclePriority := by
      rw [playValue_cyclePriority_eq_priority_cycleLeader, ← hu]
    have hne : G.priority u ≠ q := by omega
    have humem : u ∈ recurring (play G σ τ u) := by
      have hmem := cycleLeader_mem_recurring G σ τ u
      rwa [← hu] at hmem
    have hp1 : (playValue G σ τ u).path = ∅ :=
      playValue_path_eq_empty_of_mem_recurring humem
    have hp2 : (playValue G σ τ (step G σ τ u)).path = ∅ :=
      playValue_path_eq_empty_of_mem_recurring (step_mem_recurring humem)
    rw [hp1, hp2, if_neg hne, Nat.add_zero]
  · rw [playValue_eq_prepend_of_ne_cycleLeader hu,
      count_prepend_of_notMem (notMem_playValue_step_path_of_ne_cycleLeader hu),
      playValue_cyclePriority_step]
    split_ifs with h1 h2 h2
    · rfl
    · exact False.elim (h2 h1.2)
    · exact False.elim (h1 ⟨by omega, h2⟩)
    · rfl

lemma cycleLeader_eq_of_cyclePriority_eq {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp : (playValue G σ₁ τ₁ v₁).cyclePriority = (playValue G σ₂ τ₂ v₂).cyclePriority) :
    cycleLeader G σ₁ τ₁ v₁ = cycleLeader G σ₂ τ₂ v₂ := by
  apply hinj
  rw [← playValue_cyclePriority_eq_priority_cycleLeader,
      ← playValue_cyclePriority_eq_priority_cycleLeader, hcp]

end GeneralOrbit

/-! ### Part 3: Two-Strategy Minimum and Global Optimal Counterstrategy -/

section Counterstrategy

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma le_play_of_le_step_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F (step G σ τ y) ≤ F y) :
    ∀ d : ℕ, ∀ y ∈ recurring (play G σ τ v), F (play G σ τ y d) ≤ F y
  | 0, y, _ => le_rfl
  | d + 1, y, hy => by
    rw [play_succ]
    exact le_trans
      (le_play_of_le_step_on_recurring F hstep d (step G σ τ y) (step_mem_recurring hy))
      (hstep y hy)

omit [DecidableEq V] in
lemma eq_of_le_step_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F (step G σ τ y) ≤ F y)
    {x : V} (hx : x ∈ recurring (play G σ τ v)) :
    F (step G σ τ x) = F x := by
  rcases exists_pos_play_eq_self_of_mem_recurring hx with ⟨L, hL, hplayL⟩
  have hL1 : (L - 1) + 1 = L := by omega
  rw [← hL1, play_succ] at hplayL
  have hle1 := hstep x hx
  have hle2 := le_play_of_le_step_on_recurring F hstep (L - 1)
    (step G σ τ x) (step_mem_recurring hx)
  rw [hplayL] at hle2
  omega

omit [DecidableEq V] in
lemma play_le_of_step_le_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F y ≤ F (step G σ τ y)) :
    ∀ d : ℕ, ∀ y ∈ recurring (play G σ τ v), F y ≤ F (play G σ τ y d)
  | 0, y, _ => le_rfl
  | d + 1, y, hy => by
    rw [play_succ]
    exact le_trans (hstep y hy)
      (play_le_of_step_le_on_recurring F hstep d (step G σ τ y) (step_mem_recurring hy))

omit [DecidableEq V] in
lemma eq_of_step_le_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F y ≤ F (step G σ τ y))
    {x : V} (hx : x ∈ recurring (play G σ τ v)) :
    F (step G σ τ x) = F x := by
  rcases exists_pos_play_eq_self_of_mem_recurring hx with ⟨L, hL, hplayL⟩
  have hL1 : (L - 1) + 1 = L := by omega
  rw [← hL1, play_succ] at hplayL
  have hle1 := hstep x hx
  have hle2 := play_le_of_step_le_on_recurring F hstep (L - 1)
    (step G σ τ x) (step_mem_recurring hx)
  rw [hplayL] at hle2
  omega

omit [Fintype V] [DecidableEq V] in
lemma le_play_int {G : Game V} {σ τ : V → V}
    (F : V → ℤ) (hstep : ∀ y, F (step G σ τ y) ≤ F y) :
    ∀ d : ℕ, ∀ y : V, F (play G σ τ y d) ≤ F y
  | 0, _ => le_rfl
  | d + 1, y => by
    rw [play_succ]
    exact le_trans (le_play_int F hstep d (step G σ τ y)) (hstep y)

omit [DecidableEq V] in
lemma eq_on_recurring_of_le_step_int {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℤ) (hstep : ∀ y, F (step G σ τ y) ≤ F y)
    {x w : V}
    (hx : x ∈ recurring (play G σ τ v))
    (hw : w ∈ recurring (play G σ τ v)) :
    F x = F w := by
  have hwx : w ∈ recurring (play G σ τ x) := by
    rwa [recurring_eq_of_mem_recurring hx]
  have hxw : x ∈ recurring (play G σ τ w) := by
    rwa [recurring_eq_of_mem_recurring hw]
  rcases exists_play_eq_of_mem_recurring hwx with ⟨d₁, hd₁⟩
  rcases exists_play_eq_of_mem_recurring hxw with ⟨d₂, hd₂⟩
  have h1 := le_play_int F hstep d₁ x
  have h2 := le_play_int F hstep d₂ w
  rw [hd₁] at h1
  rw [hd₂] at h2
  omega

omit [Fintype V] [DecidableEq V] in
lemma reward_cyclePriority_le_of_multiplicity_valueLE {G : Game V}
    {a b : Valuation V} (hab : FriedmannMultiplicity.ValueLE G a b) :
    reward a.cyclePriority ≤ reward b.cyclePriority := by
  by_contra hgt
  exact hab (Or.inl (by omega))

omit [Fintype V] in
lemma reward_cyclePriority_le_of_valueLE {G : Game V}
    {a b : Valuation V} (hab : ValueLE G a b) :
    reward a.cyclePriority ≤ reward b.cyclePriority := by
  rcases hab with rfl | hr | ⟨hp, _⟩ | ⟨hp, _⟩
  · exact le_rfl
  · omega
  · rw [hp]
  · rw [hp]

omit [Fintype V] [DecidableEq V] in
lemma count_le_or_ge_of_multiplicity_valueLE {G : Game V}
    {a b : Valuation V} {q : ℕ}
    (hab : FriedmannMultiplicity.ValueLE G a b)
    (hp : a.cyclePriority = b.cyclePriority)
    (hgt : ∀ q', q < q' → count G a.path q' = count G b.path q') :
    (q % 2 = 0 → count G a.path q ≤ count G b.path q) ∧
    (q % 2 = 1 → count G b.path q ≤ count G a.path q) := by
  constructor
  · intro he
    by_contra hlt
    apply hab
    right; left
    refine ⟨hp.symm, q, by omega, fun q' hq' => (hgt q' hq').symm, Or.inl ⟨he, by omega⟩⟩
  · intro ho
    by_contra hlt
    apply hab
    right; left
    refine ⟨hp.symm, q, by omega, fun q' hq' => (hgt q' hq').symm, Or.inr ⟨ho, by omega⟩⟩

omit [Fintype V] [DecidableEq V] in
lemma length_le_of_multiplicity_valueLE_odd {G : Game V}
    {a b : Valuation V}
    (hab : FriedmannMultiplicity.ValueLE G a b)
    (hp : a.cyclePriority = b.cyclePriority)
    (hseq : SetEquivalent G a.path b.path)
    (hodd : a.cyclePriority % 2 = 1) :
    a.length ≤ b.length := by
  by_contra hlt
  apply hab
  right; right
  exact ⟨hp.symm, setEquivalent_symm hseq, Or.inl ⟨hp ▸ hodd, by omega⟩⟩

omit [Fintype V] [DecidableEq V] in
lemma length_ge_of_multiplicity_valueLE_even {G : Game V}
    {a b : Valuation V}
    (hab : FriedmannMultiplicity.ValueLE G a b)
    (hp : a.cyclePriority = b.cyclePriority)
    (hseq : SetEquivalent G a.path b.path)
    (heven : a.cyclePriority % 2 = 0) :
    b.length ≤ a.length := by
  by_contra hlt
  apply hab
  right; right
  exact ⟨hp.symm, setEquivalent_symm hseq, Or.inr ⟨hp ▸ heven, by omega⟩⟩

lemma count_playValue_eq_zero_of_le_cyclePriority
    {G : Game V} {σ τ : V → V} {v : V} {q : ℕ}
    (hq : q ≤ (playValue G σ τ v).cyclePriority) :
    count G (playValue G σ τ v).path q = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu
  rw [mem_playValue_path_iff] at hu
  omega

omit [DecidableEq V] in
lemma count_eq_zero_of_univ_sup_lt {G : Game V} (A : Finset V) {q : ℕ}
    (hq : Finset.univ.sup G.priority < q) : count G A q = 0 :=
  count_eq_zero_of_sup_lt (lt_of_le_of_lt (Finset.sup_mono (Finset.subset_univ A)) hq)

noncomputable def minStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) : V := by
  classical
  exact if FriedmannMultiplicity.ValueLE G (playValue G σ τ₁ x) (playValue G σ τ₂ x)
    then τ₁ x else τ₂ x

noncomputable def minVal (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) : Valuation V := by
  classical
  exact if FriedmannMultiplicity.ValueLE G (playValue G σ τ₁ x) (playValue G σ τ₂ x)
    then playValue G σ τ₁ x else playValue G σ τ₂ x

noncomputable def chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) : V → V := by
  classical
  exact if FriedmannMultiplicity.ValueLE G (playValue G σ τ₁ x) (playValue G σ τ₂ x)
    then τ₁ else τ₂

lemma minStrategy_legal {G : Game V} {σ τ₁ τ₂ : V → V}
    (hτ₁ : Legal G true τ₁) (hτ₂ : Legal G true τ₂) :
    Legal G true (minStrategy G σ τ₁ τ₂) := by
  intro x hx
  unfold minStrategy
  split_ifs
  · exact hτ₁ x hx
  · exact hτ₂ x hx

lemma chosenStrategy_legal {G : Game V} {σ τ₁ τ₂ : V → V}
    (hτ₁ : Legal G true τ₁) (hτ₂ : Legal G true τ₂) (x : V) :
    Legal G true (chosenStrategy G σ τ₁ τ₂ x) := by
  unfold chosenStrategy
  split_ifs
  · exact hτ₁
  · exact hτ₂

lemma minVal_le_left (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    FriedmannMultiplicity.ValueLE G (minVal G σ τ₁ τ₂ x) (playValue G σ τ₁ x) := by
  unfold minVal
  split_ifs with h
  · exact multiplicity_valueLE_refl G _
  · rcases multiplicity_valueLE_total G (playValue G σ τ₁ x) (playValue G σ τ₂ x) with h1 | h2
    · exact False.elim (h h1)
    · exact h2

lemma minVal_le_right (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    FriedmannMultiplicity.ValueLE G (minVal G σ τ₁ τ₂ x) (playValue G σ τ₂ x) := by
  unfold minVal
  split_ifs with h
  · exact h
  · exact multiplicity_valueLE_refl G _

lemma minVal_eq_playValue_chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    minVal G σ τ₁ τ₂ x = playValue G σ (chosenStrategy G σ τ₁ τ₂ x) x := by
  unfold minVal chosenStrategy
  split_ifs <;> rfl

lemma step_minStrategy_eq_chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    step G σ (minStrategy G σ τ₁ τ₂) x = step G σ (chosenStrategy G σ τ₁ τ₂ x) x := by
  unfold step minStrategy chosenStrategy
  split_ifs <;> rfl

lemma minVal_step_le_chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    FriedmannMultiplicity.ValueLE G
      (minVal G σ τ₁ τ₂ (step G σ (minStrategy G σ τ₁ τ₂) x))
      (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ (minStrategy G σ τ₁ τ₂) x)) := by
  unfold chosenStrategy
  split_ifs
  · exact minVal_le_left G σ τ₁ τ₂ _
  · exact minVal_le_right G σ τ₁ τ₂ _

lemma chosenStrategy_step_cyclePriority (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ (minStrategy G σ τ₁ τ₂) x)).cyclePriority =
      (minVal G σ τ₁ τ₂ x).cyclePriority := by
  rw [step_minStrategy_eq_chosenStrategy, playValue_cyclePriority_step,
      ← minVal_eq_playValue_chosenStrategy]

lemma reward_minVal_step_le (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    reward (minVal G σ τ₁ τ₂ (step G σ (minStrategy G σ τ₁ τ₂) x)).cyclePriority ≤
      reward (minVal G σ τ₁ τ₂ x).cyclePriority := by
  have hle := reward_cyclePriority_le_of_multiplicity_valueLE (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
  rwa [chosenStrategy_step_cyclePriority] at hle

lemma minVal_cyclePriority_eq_on_recurring (G : Game V) (σ τ₁ τ₂ : V → V)
    {v x w : V}
    (hx : x ∈ recurring (play G σ (minStrategy G σ τ₁ τ₂) v))
    (hw : w ∈ recurring (play G σ (minStrategy G σ τ₁ τ₂) v)) :
    (minVal G σ τ₁ τ₂ x).cyclePriority = (minVal G σ τ₁ τ₂ w).cyclePriority := by
  apply reward_injective
  exact eq_on_recurring_of_le_step_int
    (fun y => reward (minVal G σ τ₁ τ₂ y).cyclePriority)
    (reward_minVal_step_le G σ τ₁ τ₂) hx hw

lemma count_minVal_eq_above_max (G : Game V) (σ τ₁ τ₂ : V → V) (v : V) :
    let τ₃ := minStrategy G σ τ₁ τ₂
    let m := minVal G σ τ₁ τ₂
    let R₃ := recurring (play G σ τ₃ v)
    let w₃ := cycleLeader G σ τ₃ v
    let p₃ := (playValue G σ τ₃ v).cyclePriority
    let p_star := (m w₃).cyclePriority
    let M := Finset.univ.sup G.priority + max p₃ p_star + 1
    ∀ d : ℕ, ∀ q : ℕ, M - d ≤ q → max p₃ p_star < q →
      ∀ x ∈ R₃,
        count G (m (step G σ τ₃ x)).path q =
          count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q ∧
        count G (m (step G σ τ₃ x)).path q =
          count G (m x).path q := by
  intro τ₃ m R₃ w₃ p₃ p_star M d
  have hw₃ : w₃ ∈ R₃ := cycleLeader_mem_recurring G σ τ₃ v
  induction d with
  | zero =>
    intro q hMq _ x _
    have hsup : Finset.univ.sup G.priority < q := by omega
    rw [count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro q hMq hmaxq
    by_cases hMq' : M - d ≤ q
    · exact ih q hMq' hmaxq
    · have hgt : ∀ x ∈ R₃, ∀ q', q < q' →
          count G (m (step G σ τ₃ x)).path q' =
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q' := by
        intro x hx q' hq'
        exact (ih q' (by omega) (by omega) x hx).1
      have hmx_eq : ∀ x ∈ R₃,
          count G (m x).path q =
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q := by
        intro x hx
        have hpx : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        have hp_lt_q : (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) x).cyclePriority < q := by
          rw [← minVal_eq_playValue_chosenStrategy]
          change (m x).cyclePriority < q
          omega
        have hcnt := count_playValue_step hp_lt_q
        rw [← minVal_eq_playValue_chosenStrategy,
            ← step_minStrategy_eq_chosenStrategy] at hcnt
        have hle_p3 : G.priority x ≤ p₃ := Finset.le_sup hx
        have hne_q : G.priority x ≠ q := by omega
        rw [if_neg hne_q, Nat.add_zero] at hcnt
        exact hcnt
      have hcp_eq : ∀ x ∈ R₃,
          (m (step G σ τ₃ x)).cyclePriority =
            (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).cyclePriority := by
        intro x hx
        have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        rw [h1, chosenStrategy_step_cyclePriority]
        exact h2.symm
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · have hstep_le : ∀ x ∈ R₃,
            count G (m (step G σ τ₃ x)).path q ≤ count G (m x).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
            (hcp_eq x hx) (hgt x hx)).1 hpar
        intro x hx
        have heq := eq_of_le_step_on_recurring
          (fun y => count G (m y).path q) hstep_le hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩
      · have hstep_ge : ∀ x ∈ R₃,
            count G (m x).path q ≤ count G (m (step G σ τ₃ x)).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
            (hcp_eq x hx) (hgt x hx)).2 hpar
        intro x hx
        have heq := eq_of_step_le_on_recurring
          (fun y => count G (m y).path q) hstep_ge hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩

lemma reward_playValue_minStrategy_le (G : Game V) (σ τ₁ τ₂ : V → V) (v : V) :
    reward (playValue G σ (minStrategy G σ τ₁ τ₂) v).cyclePriority ≤
      reward (minVal G σ τ₁ τ₂ (cycleLeader G σ (minStrategy G σ τ₁ τ₂) v)).cyclePriority := by
  let τ₃ := minStrategy G σ τ₁ τ₂
  let m := minVal G σ τ₁ τ₂
  let R₃ := recurring (play G σ τ₃ v)
  let w₃ := cycleLeader G σ τ₃ v
  let p₃ := (playValue G σ τ₃ v).cyclePriority
  let p_star := (m w₃).cyclePriority
  change reward p₃ ≤ reward p_star
  have hw₃ : w₃ ∈ R₃ := cycleLeader_mem_recurring G σ τ₃ v
  have hpw₃ : G.priority w₃ = p₃ :=
    (playValue_cyclePriority_eq_priority_cycleLeader G σ τ₃ v).symm
  have habove : ∀ q : ℕ, max p₃ p_star < q → ∀ x ∈ R₃,
      count G (m (step G σ τ₃ x)).path q =
        count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q := by
    intro q hq x hx
    let M := Finset.univ.sup G.priority + max p₃ p_star + 1
    have hMM : M - M ≤ q := by simp
    exact (count_minVal_eq_above_max G σ τ₁ τ₂ v M q hMM hq x hx).1
  have hcp_eq : ∀ x ∈ R₃,
      (m (step G σ τ₃ x)).cyclePriority =
        (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).cyclePriority := by
    intro x hx
    have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
      minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
    have h2 : (m x).cyclePriority = p_star :=
      minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
    rw [h1, chosenStrategy_step_cyclePriority]
    exact h2.symm
  rcases lt_trichotomy p₃ p_star with hlt | heq | hgt
  · rcases Nat.mod_two_eq_zero_or_one p_star with hpar | hpar
    · unfold reward
      split_ifs <;> omega
    · exfalso
      have hseq : ∀ x ∈ R₃, SetEquivalent G
          (m (step G σ τ₃ x)).path
          (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path := by
        intro x hx q
        by_cases hq : p_star < q
        · exact habove q (by omega) x hx
        · have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
            minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
          have h2 : (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).cyclePriority = p_star :=
            (hcp_eq x hx).symm.trans h1
          have h1' : (playValue G σ
              (chosenStrategy G σ τ₁ τ₂ (step G σ τ₃ x))
              (step G σ τ₃ x)).cyclePriority = p_star := by
            rw [← minVal_eq_playValue_chosenStrategy]
            exact h1
          change count G (minVal G σ τ₁ τ₂ (step G σ τ₃ x)).path q = _
          rw [minVal_eq_playValue_chosenStrategy,
              count_playValue_eq_zero_of_le_cyclePriority (by omega),
              count_playValue_eq_zero_of_le_cyclePriority (by omega)]
      have hlen_step : ∀ x ∈ R₃,
          (m (step G σ τ₃ x)).length ≤
            (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).length ∧
          (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).length + 1 = (m x).length := by
        intro x hx
        have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        have hlen_le := length_le_of_multiplicity_valueLE_odd
          (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
          (hcp_eq x hx) (hseq x hx) (by rw [h1]; exact hpar)
        have hx_ne : x ≠ cycleLeader G σ (chosenStrategy G σ τ₁ τ₂ x) x := by
          intro hcl
          have hpx : G.priority x = p_star := by
            have hpcl := playValue_cyclePriority_eq_priority_cycleLeader
              G σ (chosenStrategy G σ τ₁ τ₂ x) x
            rw [← minVal_eq_playValue_chosenStrategy] at hpcl
            change (m x).cyclePriority = _ at hpcl
            rw [h2, ← hcl] at hpcl
            exact hpcl.symm
          have hpx_le : G.priority x ≤ p₃ := Finset.le_sup hx
          omega
        have hlen_eq := playValue_length_eq_succ_of_ne_cycleLeader hx_ne
        rw [← minVal_eq_playValue_chosenStrategy,
            ← step_minStrategy_eq_chosenStrategy] at hlen_eq
        exact ⟨hlen_le, hlen_eq.symm⟩
      have hstep_le : ∀ x ∈ R₃, (m (step G σ τ₃ x)).length ≤ (m x).length := by
        intro x hx
        have ⟨h1, h2⟩ := hlen_step x hx
        omega
      have heq_w3 := eq_of_le_step_on_recurring (fun y => (m y).length) hstep_le hw₃
      have ⟨h1, h2⟩ := hlen_step w₃ hw₃
      omega
  · rw [heq]
  · rcases Nat.mod_two_eq_zero_or_one p₃ with hpar | hpar
    · exfalso
      have hstep_rel : ∀ x ∈ R₃,
          count G (m (step G σ τ₃ x)).path p₃ ≤
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path p₃ ∧
          count G (m x).path p₃ =
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path p₃ +
              (if G.priority x = p₃ then 1 else 0) := by
        intro x hx
        have hle_cnt := (count_le_or_ge_of_multiplicity_valueLE
          (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
          (hcp_eq x hx)
          (fun q' hq' => habove q' (by omega) x hx)).1 hpar
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        have hp_lt : (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) x).cyclePriority < p₃ := by
          rw [← minVal_eq_playValue_chosenStrategy]
          change (m x).cyclePriority < p₃
          rw [h2]
          exact hgt
        have hcnt := count_playValue_step hp_lt
        rw [← minVal_eq_playValue_chosenStrategy,
            ← step_minStrategy_eq_chosenStrategy] at hcnt
        exact ⟨hle_cnt, hcnt⟩
      have hstep_le : ∀ x ∈ R₃,
          count G (m (step G σ τ₃ x)).path p₃ ≤ count G (m x).path p₃ := by
        intro x hx
        have ⟨h1, h2⟩ := hstep_rel x hx
        omega
      have heq_w3 := eq_of_le_step_on_recurring
        (fun y => count G (m y).path p₃) hstep_le hw₃
      have ⟨h1, h2⟩ := hstep_rel w₃ hw₃
      rw [if_pos hpw₃] at h2
      omega
    · unfold reward
      split_ifs <;> omega

lemma valueLE_playValue_minStrategy {G : Game V} (hinj : Function.Injective G.priority)
    (σ τ₁ τ₂ : V → V) (v : V) :
    FriedmannMultiplicity.ValueLE G
      (playValue G σ (minStrategy G σ τ₁ τ₂) v)
      (minVal G σ τ₁ τ₂ v) := by
  let τ₃ := minStrategy G σ τ₁ τ₂
  let π₃ := play G σ τ₃ v
  let w₃ := cycleLeader G σ τ₃ v
  let p₃ := (playValue G σ τ₃ v).cyclePriority
  let k := (playValue G σ τ₃ v).length
  have hcl_play : ∀ t : ℕ, cycleLeader G σ τ₃ (π₃ t) = w₃ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [π₃] at ih ⊢
      rw [play_succ', cycleLeader_step, ih]
  have hcp_play : ∀ t : ℕ, (playValue G σ τ₃ (π₃ t)).cyclePriority = p₃ := by
    intro t
    rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl_play t,
        ← playValue_cyclePriority_eq_priority_cycleLeader]
  have hbase_w3 : FriedmannMultiplicity.ValueLE G
      (playValue G σ τ₃ w₃) (minVal G σ τ₁ τ₂ w₃) := by
    have hrew : reward p₃ ≤ reward (minVal G σ τ₁ τ₂ w₃).cyclePriority :=
      reward_playValue_minStrategy_le G σ τ₁ τ₂ v
    have hcl_w3 : w₃ = cycleLeader G σ τ₃ w₃ := by
      have h := hcl_play k
      dsimp only [π₃, k] at h
      rw [play_playValue_length] at h
      exact h.symm
    have hcp_w3 : (playValue G σ τ₃ w₃).cyclePriority = p₃ := by
      have h := hcp_play k
      dsimp only [π₃, k] at h
      rw [play_playValue_length] at h
      exact h
    rcases lt_or_eq_of_le hrew with hlt | heq
    · rw [multiplicity_valueLE_iff]
      right; left
      rw [hcp_w3]
      exact hlt
    · have hp_eq : p₃ = (minVal G σ τ₁ τ₂ w₃).cyclePriority := reward_injective heq
      let τ₀ := chosenStrategy G σ τ₁ τ₂ w₃
      have hcp_0 : (playValue G σ τ₃ w₃).cyclePriority =
          (playValue G σ τ₀ w₃).cyclePriority := by
        rw [hcp_w3, ← minVal_eq_playValue_chosenStrategy, hp_eq]
      have hcl_0 : w₃ = cycleLeader G σ τ₀ w₃ :=
        hcl_w3.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_0)
      have hval_3 := playValue_eq_of_eq_cycleLeader hcl_w3
      have hval_0 := playValue_eq_of_eq_cycleLeader hcl_0
      rw [minVal_eq_playValue_chosenStrategy]
      change FriedmannMultiplicity.ValueLE G
        (playValue G σ τ₃ w₃) (playValue G σ τ₀ w₃)
      rw [hval_3, hval_0, hcp_0]
      exact multiplicity_valueLE_refl G _
  have hind : ∀ d : ℕ, d ≤ k →
      FriedmannMultiplicity.ValueLE G
        (playValue G σ τ₃ (π₃ (k - d)))
        (minVal G σ τ₁ τ₂ (π₃ (k - d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hk0 : k - 0 = k := by omega
      rw [hk0]
      dsimp only [π₃, k]
      rw [play_playValue_length]
      exact hbase_w3
    | succ d ih =>
      intro hd
      let t := k - (d + 1)
      have ht_lt : t < k := by omega
      have ht_succ : t + 1 = k - d := by omega
      let x := π₃ t
      let x' := step G σ τ₃ x
      have hx'_eq : x' = π₃ (k - d) := by
        dsimp only [x', x, π₃]
        rw [← play_succ', ht_succ]
      have ih' : FriedmannMultiplicity.ValueLE G
          (playValue G σ τ₃ x') (minVal G σ τ₁ τ₂ x') := by
        rw [hx'_eq]
        exact ih (by omega)
      let τ_i := chosenStrategy G σ τ₁ τ₂ x
      have hm_step : FriedmannMultiplicity.ValueLE G (minVal G σ τ₁ τ₂ x')
          (playValue G σ τ_i (step G σ τ_i x)) := by
        dsimp only [x', τ_i]
        rw [← step_minStrategy_eq_chosenStrategy]
        exact minVal_step_le_chosenStrategy G σ τ₁ τ₂ x
      have hle_step : FriedmannMultiplicity.ValueLE G
          (playValue G σ τ₃ x')
          (playValue G σ τ_i (step G σ τ_i x)) :=
        multiplicity_valueLE_trans ih' hm_step
      have hrew_le : reward (playValue G σ τ₃ x).cyclePriority ≤
          reward (minVal G σ τ₁ τ₂ x).cyclePriority := by
        have h := reward_cyclePriority_le_of_multiplicity_valueLE hle_step
        dsimp only [x', τ_i] at h
        rw [playValue_cyclePriority_step, playValue_cyclePriority_step,
            ← minVal_eq_playValue_chosenStrategy] at h
        exact h
      rcases lt_or_eq_of_le hrew_le with hlt | heq
      · rw [multiplicity_valueLE_iff]
        right; left
        exact hlt
      · have hp_eq : (playValue G σ τ₃ x).cyclePriority =
            (minVal G σ τ₁ τ₂ x).cyclePriority :=
          reward_injective heq
        have hx_ne_w3 : x ≠ cycleLeader G σ τ₃ x := by
          rw [hcl_play t]
          exact play_ne_cycleLeader_of_lt_length ht_lt
        have hx_ne_i : x ≠ cycleLeader G σ τ_i x := by
          intro hcl_i
          have hcp_i : (playValue G σ τ_i x).cyclePriority =
              (playValue G σ τ₃ x).cyclePriority := by
            dsimp only [τ_i]
            rw [← minVal_eq_playValue_chosenStrategy, hp_eq]
          exact hx_ne_w3 (hcl_i.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_i))
        have hval_3 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_w3
        have hnot_3 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_w3
        have hval_i := playValue_eq_prepend_of_ne_cycleLeader hx_ne_i
        have hnot_i := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_i
        change FriedmannMultiplicity.ValueLE G
          (playValue G σ τ₃ x) (minVal G σ τ₁ τ₂ x)
        rw [minVal_eq_playValue_chosenStrategy, hval_3]
        change FriedmannMultiplicity.ValueLE G
          (prepend G x (playValue G σ τ₃ x'))
          (playValue G σ τ_i x)
        rw [hval_i]
        apply multiplicity_valueLE_prepend
        · dsimp only [x', τ_i]
          rw [playValue_cyclePriority_step, playValue_cyclePriority_step,
              ← minVal_eq_playValue_chosenStrategy, hp_eq]
        · exact hnot_3
        · exact hnot_i
        · exact hle_step
  have h0 := hind k le_rfl
  have hkk : k - k = 0 := by omega
  rw [hkk] at h0
  exact h0

noncomputable def defaultStrategy (G : Game V) (hG : WellFormed G) (v : V) : V :=
  Classical.choose (hG.1 v)

omit [Fintype V] [DecidableEq V] in
lemma defaultStrategy_legal {G : Game V} (hG : WellFormed G) (player : Bool) :
    Legal G player (defaultStrategy G hG) := by
  intro v _
  exact Classical.choose_spec (hG.1 v)

lemma exists_counterstrategy_list {G : Game V} (hG : WellFormed G)
    (σ : V → V) (L : List (V → V)) :
    ∃ τ : V → V,
      Legal G true τ ∧
      ∀ τ' ∈ L, Legal G true τ' →
        ∀ v, ValueLE G (playValue G σ τ v) (playValue G σ τ' v) := by
  induction L with
  | nil =>
    refine ⟨defaultStrategy G hG, defaultStrategy_legal hG true, ?_⟩
    intro τ' hmem
    nomatch hmem
  | cons τ₁ L ih =>
    rcases ih with ⟨τ₂, hτ₂, hle₂⟩
    by_cases hτ₁ : Legal G true τ₁
    · refine ⟨minStrategy G σ τ₁ τ₂, minStrategy_legal hτ₁ hτ₂, ?_⟩
      intro τ' hmem hleg v
      have hmin : ValueLE G (playValue G σ (minStrategy G σ τ₁ τ₂) v) (minVal G σ τ₁ τ₂ v) :=
        (valueLE_iff_multiplicity_valueLE hG.2 _ _).mpr
          (valueLE_playValue_minStrategy hG.2 σ τ₁ τ₂ v)
      have hleft : ValueLE G (minVal G σ τ₁ τ₂ v) (playValue G σ τ₁ v) :=
        (valueLE_iff_multiplicity_valueLE hG.2 _ _).mpr
          (minVal_le_left G σ τ₁ τ₂ v)
      have hright : ValueLE G (minVal G σ τ₁ τ₂ v) (playValue G σ τ₂ v) :=
        (valueLE_iff_multiplicity_valueLE hG.2 _ _).mpr
          (minVal_le_right G σ τ₁ τ₂ v)
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq]
        exact valueLE_trans hG.2 hmin hleft
      · exact valueLE_trans hG.2 hmin
          (valueLE_trans hG.2 hright (hle₂ τ' hmem' hleg v))
    · refine ⟨τ₂, hτ₂, ?_⟩
      intro τ' hmem hleg v
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq] at hleg
        exact False.elim (hτ₁ hleg)
      · exact hle₂ τ' hmem' hleg v

lemma exists_optimalCounterstrategy (G : Game V) (hG : WellFormed G) (σ : V → V) :
    ∃ τ, OptimalCounterstrategy G σ τ := by
  rcases exists_counterstrategy_list hG σ (Finset.univ : Finset (V → V)).toList with
    ⟨τ, hτ, hle⟩
  refine ⟨τ, hτ, ?_⟩
  intro v τ' hτ'
  exact hle τ' (Finset.mem_toList.mpr (Finset.mem_univ τ')) hτ' v

lemma isMinimum_playValue_of_optimalCounterstrategy {G : Game V} {σ τ : V → V}
    (hτ : OptimalCounterstrategy G σ τ) (v : V) :
    IsMinimum G σ v (playValue G σ τ v) :=
  ⟨⟨τ, hτ.1, rfl⟩, fun τ' hτ' => hτ.2 v τ' hτ'⟩

lemma isMinimum_unique {G : Game V} (hG : WellFormed G) {σ : V → V} {v : V}
    {a b : Valuation V} (ha : IsMinimum G σ v a) (hb : IsMinimum G σ v b) :
    a = b := by
  rcases ha.1 with ⟨τ₁, hτ₁, rfl⟩
  rcases hb.1 with ⟨τ₂, hτ₂, rfl⟩
  exact valueLE_antisymm hG.2 (ha.2 τ₂ hτ₂) (hb.2 τ₁ hτ₁)

lemma value_eq_of_isMinimum {G : Game V} (hG : WellFormed G) {σ : V → V} {v : V}
    {a : Valuation V} (ha : IsMinimum G σ v a) :
    value G σ v = a := by
  classical
  have hex : ∃ b, IsMinimum G σ v b := ⟨a, ha⟩
  have hval : value G σ v = Classical.choose hex := by
    unfold value
    rw [dif_pos hex]
  rw [hval]
  exact isMinimum_unique hG (Classical.choose_spec hex) ha

lemma value_eq_playValue_of_optimalCounterstrategy {G : Game V} (hG : WellFormed G)
    {σ τ : V → V} (hτ : OptimalCounterstrategy G σ τ) (v : V) :
    value G σ v = playValue G σ τ v :=
  value_eq_of_isMinimum hG (isMinimum_playValue_of_optimalCounterstrategy hτ v)

lemma isMinimum_value {G : Game V} (hG : WellFormed G) (σ : V → V) (v : V) :
    IsMinimum G σ v (value G σ v) := by
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
  rw [value_eq_playValue_of_optimalCounterstrategy hG hτ v]
  exact isMinimum_playValue_of_optimalCounterstrategy hτ v

lemma value_le_playValue {G : Game V} (hG : WellFormed G) (σ : V → V)
    {τ : V → V} (hτ : Legal G true τ) (v : V) :
    ValueLE G (value G σ v) (playValue G σ τ v) :=
  (isMinimum_value hG σ v).2 τ hτ

end Counterstrategy

theorem counterstrategy_exists_lib {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V) (hσ : Legal G false σ) :
    ∃ τ, OptimalCounterstrategy G σ τ ∧ ∀ v, value G σ v = playValue G σ τ v := by
  let _ := hσ
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
  exact ⟨τ, hτ, value_eq_playValue_of_optimalCounterstrategy hG hτ⟩

end FriedmannParity

open FriedmannParity

set_option autoImplicit false

namespace FriedmannParity

open FriedmannMultiplicity

section StepComparison

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Part 1: Right-Step Comparison (`playValue_le_of_step_le`) -/

lemma reward_playValue_step_le_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (x : V) :
    reward (playValue G σ₂ τ₂ (step G σ₁ τ₁ x)).cyclePriority ≤
      reward (playValue G σ₂ τ₂ x).cyclePriority := by
  have hle := reward_cyclePriority_le_of_multiplicity_valueLE (hstep x)
  rwa [playValue_cyclePriority_step] at hle

lemma playValue_cyclePriority_eq_on_recurring_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    {v x w : V}
    (hx : x ∈ recurring (play G σ₁ τ₁ v))
    (hw : w ∈ recurring (play G σ₁ τ₁ v)) :
    (playValue G σ₂ τ₂ x).cyclePriority = (playValue G σ₂ τ₂ w).cyclePriority := by
  apply reward_injective
  exact eq_on_recurring_of_le_step_int
    (fun y => reward (playValue G σ₂ τ₂ y).cyclePriority)
    (reward_playValue_step_le_of_step_le hstep) hx hw

lemma count_playValue_eq_above_max_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    let m := playValue G σ₂ τ₂
    let R₁ := recurring (play G σ₁ τ₁ v)
    let w₁ := cycleLeader G σ₁ τ₁ v
    let p₁ := (playValue G σ₁ τ₁ v).cyclePriority
    let p_star := (m w₁).cyclePriority
    let M := Finset.univ.sup G.priority + max p₁ p_star + 1
    ∀ d : ℕ, ∀ q : ℕ, M - d ≤ q → max p₁ p_star < q →
      ∀ x ∈ R₁,
        count G (m (step G σ₁ τ₁ x)).path q =
          count G (m (step G σ₂ τ₂ x)).path q ∧
        count G (m (step G σ₁ τ₁ x)).path q =
          count G (m x).path q := by
  intro m R₁ w₁ p₁ p_star M d
  have hw₁ : w₁ ∈ R₁ := cycleLeader_mem_recurring G σ₁ τ₁ v
  induction d with
  | zero =>
    intro q hMq _ x _
    have hsup : Finset.univ.sup G.priority < q := by omega
    rw [count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro q hMq hmaxq
    by_cases hMq' : M - d ≤ q
    · exact ih q hMq' hmaxq
    · have hgt : ∀ x ∈ R₁, ∀ q', q < q' →
          count G (m (step G σ₁ τ₁ x)).path q' =
            count G (m (step G σ₂ τ₂ x)).path q' := by
        intro x hx q' hq'
        exact (ih q' (by omega) (by omega) x hx).1
      have hmx_eq : ∀ x ∈ R₁,
          count G (m x).path q =
            count G (m (step G σ₂ τ₂ x)).path q := by
        intro x hx
        have hpx : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        have hp_lt_q : (m x).cyclePriority < q := by omega
        have hcnt := count_playValue_step hp_lt_q
        have hle_p1 : G.priority x ≤ p₁ := Finset.le_sup hx
        have hne_q : G.priority x ≠ q := by omega
        rw [if_neg hne_q, Nat.add_zero] at hcnt
        exact hcnt
      have hcp_eq : ∀ x ∈ R₁,
          (m (step G σ₁ τ₁ x)).cyclePriority =
            (m (step G σ₂ τ₂ x)).cyclePriority := by
        intro x hx
        have h1 : (m (step G σ₁ τ₁ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        rw [h1, playValue_cyclePriority_step]
        exact h2.symm
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · have hstep_le : ∀ x ∈ R₁,
            count G (m (step G σ₁ τ₁ x)).path q ≤ count G (m x).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).1 hpar
        intro x hx
        have heq := eq_of_le_step_on_recurring
          (fun y => count G (m y).path q) hstep_le hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩
      · have hstep_ge : ∀ x ∈ R₁,
            count G (m x).path q ≤ count G (m (step G σ₁ τ₁ x)).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).2 hpar
        intro x hx
        have heq := eq_of_step_le_on_recurring
          (fun y => count G (m y).path q) hstep_ge hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩

lemma reward_playValue_le_of_step_le {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    reward (playValue G σ₁ τ₁ v).cyclePriority ≤
      reward (playValue G σ₂ τ₂ (cycleLeader G σ₁ τ₁ v)).cyclePriority := by
  let m := playValue G σ₂ τ₂
  let R₁ := recurring (play G σ₁ τ₁ v)
  let w₁ := cycleLeader G σ₁ τ₁ v
  let p₁ := (playValue G σ₁ τ₁ v).cyclePriority
  let p_star := (m w₁).cyclePriority
  change reward p₁ ≤ reward p_star
  have hw₁ : w₁ ∈ R₁ := cycleLeader_mem_recurring G σ₁ τ₁ v
  have hpw₁ : G.priority w₁ = p₁ :=
    (playValue_cyclePriority_eq_priority_cycleLeader G σ₁ τ₁ v).symm
  have habove : ∀ q : ℕ, max p₁ p_star < q → ∀ x ∈ R₁,
      count G (m (step G σ₁ τ₁ x)).path q =
        count G (m (step G σ₂ τ₂ x)).path q := by
    intro q hq x hx
    let M := Finset.univ.sup G.priority + max p₁ p_star + 1
    have hMM : M - M ≤ q := by simp
    exact (count_playValue_eq_above_max_of_step_le hstep v M q hMM hq x hx).1
  have hcp_eq : ∀ x ∈ R₁,
      (m (step G σ₁ τ₁ x)).cyclePriority =
        (m (step G σ₂ τ₂ x)).cyclePriority := by
    intro x hx
    have h1 : (m (step G σ₁ τ₁ x)).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
    have h2 : (m x).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
    rw [h1, playValue_cyclePriority_step]
    exact h2.symm
  rcases lt_trichotomy p₁ p_star with hlt | heq | hgt
  · rcases Nat.mod_two_eq_zero_or_one p_star with hpar | hpar
    · unfold reward
      split_ifs <;> omega
    · exfalso
      have hseq : ∀ x ∈ R₁, SetEquivalent G
          (m (step G σ₁ τ₁ x)).path
          (m (step G σ₂ τ₂ x)).path := by
        intro x hx q
        by_cases hq : p_star < q
        · exact habove q (by omega) x hx
        · have h1 : (playValue G σ₂ τ₂ (step G σ₁ τ₁ x)).cyclePriority = p_star :=
            playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
          have h2 : (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)).cyclePriority = p_star :=
            (hcp_eq x hx).symm.trans h1
          change count G (playValue G σ₂ τ₂ (step G σ₁ τ₁ x)).path q =
            count G (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)).path q
          rw [count_playValue_eq_zero_of_le_cyclePriority (by omega),
              count_playValue_eq_zero_of_le_cyclePriority (by omega)]
      have hlen_step : ∀ x ∈ R₁,
          (m (step G σ₁ τ₁ x)).length ≤
            (m (step G σ₂ τ₂ x)).length ∧
          (m (step G σ₂ τ₂ x)).length + 1 = (m x).length := by
        intro x hx
        have h1 : (m (step G σ₁ τ₁ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep (step_mem_recurring hx) hw₁
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        have hlen_le := length_le_of_multiplicity_valueLE_odd
          (hstep x) (hcp_eq x hx) (hseq x hx) (by rw [h1]; exact hpar)
        have hx_ne : x ≠ cycleLeader G σ₂ τ₂ x := by
          intro hcl
          have hpx : G.priority x = p_star := by
            have hpcl := playValue_cyclePriority_eq_priority_cycleLeader G σ₂ τ₂ x
            change (m x).cyclePriority = _ at hpcl
            rw [h2, ← hcl] at hpcl
            exact hpcl.symm
          have hpx_le : G.priority x ≤ p₁ := Finset.le_sup hx
          omega
        have hlen_eq := playValue_length_eq_succ_of_ne_cycleLeader hx_ne
        exact ⟨hlen_le, hlen_eq.symm⟩
      have hstep_le : ∀ x ∈ R₁, (m (step G σ₁ τ₁ x)).length ≤ (m x).length := by
        intro x hx
        have ⟨h1, h2⟩ := hlen_step x hx
        omega
      have heq_w1 := eq_of_le_step_on_recurring (fun y => (m y).length) hstep_le hw₁
      have ⟨h1, h2⟩ := hlen_step w₁ hw₁
      omega
  · rw [heq]
  · rcases Nat.mod_two_eq_zero_or_one p₁ with hpar | hpar
    · exfalso
      have hstep_rel : ∀ x ∈ R₁,
          count G (m (step G σ₁ τ₁ x)).path p₁ ≤
            count G (m (step G σ₂ τ₂ x)).path p₁ ∧
          count G (m x).path p₁ =
            count G (m (step G σ₂ τ₂ x)).path p₁ +
              (if G.priority x = p₁ then 1 else 0) := by
        intro x hx
        have hle_cnt := (count_le_or_ge_of_multiplicity_valueLE
          (hstep x) (hcp_eq x hx)
          (fun q' hq' => habove q' (by omega) x hx)).1 hpar
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_step_le hstep hx hw₁
        have hp_lt : (m x).cyclePriority < p₁ := by
          rw [h2]
          exact hgt
        have hcnt := count_playValue_step hp_lt
        exact ⟨hle_cnt, hcnt⟩
      have hstep_le : ∀ x ∈ R₁,
          count G (m (step G σ₁ τ₁ x)).path p₁ ≤ count G (m x).path p₁ := by
        intro x hx
        have ⟨h1, h2⟩ := hstep_rel x hx
        omega
      have heq_w1 := eq_of_le_step_on_recurring
        (fun y => count G (m y).path p₁) hstep_le hw₁
      have ⟨h1, h2⟩ := hstep_rel w₁ hw₁
      rw [if_pos hpw₁] at h2
      omega
    · unfold reward
      split_ifs <;> omega

lemma multiplicity_playValue_le_of_step_le {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ v)
      (playValue G σ₂ τ₂ v) := by
  let π₁ := play G σ₁ τ₁ v
  let w₁ := cycleLeader G σ₁ τ₁ v
  let p₁ := (playValue G σ₁ τ₁ v).cyclePriority
  let k := (playValue G σ₁ τ₁ v).length
  have hcl_play : ∀ t : ℕ, cycleLeader G σ₁ τ₁ (π₁ t) = w₁ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [π₁] at ih ⊢
      rw [play_succ', cycleLeader_step, ih]
  have hcp_play : ∀ t : ℕ, (playValue G σ₁ τ₁ (π₁ t)).cyclePriority = p₁ := by
    intro t
    rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl_play t,
        ← playValue_cyclePriority_eq_priority_cycleLeader]
  have hbase_w1 : FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ w₁) (playValue G σ₂ τ₂ w₁) := by
    have hrew : reward p₁ ≤ reward (playValue G σ₂ τ₂ w₁).cyclePriority :=
      reward_playValue_le_of_step_le hstep v
    have hcl_w1 : w₁ = cycleLeader G σ₁ τ₁ w₁ := by
      have h := hcl_play k
      dsimp only [π₁, k] at h
      rw [play_playValue_length] at h
      exact h.symm
    have hcp_w1 : (playValue G σ₁ τ₁ w₁).cyclePriority = p₁ := by
      have h := hcp_play k
      dsimp only [π₁, k] at h
      rw [play_playValue_length] at h
      exact h
    rcases lt_or_eq_of_le hrew with hlt | heq
    · rw [multiplicity_valueLE_iff]
      right; left
      rw [hcp_w1]
      exact hlt
    · have hp_eq : p₁ = (playValue G σ₂ τ₂ w₁).cyclePriority := reward_injective heq
      have hcp_0 : (playValue G σ₁ τ₁ w₁).cyclePriority =
          (playValue G σ₂ τ₂ w₁).cyclePriority := by
        rw [hcp_w1, hp_eq]
      have hcl_0 : w₁ = cycleLeader G σ₂ τ₂ w₁ :=
        hcl_w1.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_0)
      have hval_1 := playValue_eq_of_eq_cycleLeader hcl_w1
      have hval_2 := playValue_eq_of_eq_cycleLeader hcl_0
      rw [hval_1, hval_2, hcp_0]
      exact multiplicity_valueLE_refl G _
  have hind : ∀ d : ℕ, d ≤ k →
      FriedmannMultiplicity.ValueLE G
        (playValue G σ₁ τ₁ (π₁ (k - d)))
        (playValue G σ₂ τ₂ (π₁ (k - d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hk0 : k - 0 = k := by omega
      rw [hk0]
      dsimp only [π₁, k]
      rw [play_playValue_length]
      exact hbase_w1
    | succ d ih =>
      intro hd
      let t := k - (d + 1)
      have ht_lt : t < k := by omega
      have ht_succ : t + 1 = k - d := by omega
      let x := π₁ t
      let x' := step G σ₁ τ₁ x
      have hx'_eq : x' = π₁ (k - d) := by
        dsimp only [x', x, π₁]
        rw [← play_succ', ht_succ]
      have ih' : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x') (playValue G σ₂ τ₂ x') := by
        rw [hx'_eq]
        exact ih (by omega)
      have hle_step : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x')
          (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)) :=
        multiplicity_valueLE_trans ih' (hstep x)
      have hrew_le : reward (playValue G σ₁ τ₁ x).cyclePriority ≤
          reward (playValue G σ₂ τ₂ x).cyclePriority := by
        have h := reward_cyclePriority_le_of_multiplicity_valueLE hle_step
        dsimp only [x'] at h
        rw [playValue_cyclePriority_step, playValue_cyclePriority_step] at h
        exact h
      rcases lt_or_eq_of_le hrew_le with hlt | heq
      · rw [multiplicity_valueLE_iff]
        right; left
        exact hlt
      · have hp_eq : (playValue G σ₁ τ₁ x).cyclePriority =
            (playValue G σ₂ τ₂ x).cyclePriority :=
          reward_injective heq
        have hx_ne_w1 : x ≠ cycleLeader G σ₁ τ₁ x := by
          rw [hcl_play t]
          exact play_ne_cycleLeader_of_lt_length ht_lt
        have hx_ne_2 : x ≠ cycleLeader G σ₂ τ₂ x := by
          intro hcl_2
          exact hx_ne_w1 (hcl_2.trans (cycleLeader_eq_of_cyclePriority_eq hinj hp_eq.symm))
        have hval_1 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_w1
        have hnot_1 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_w1
        have hval_2 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_2
        have hnot_2 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_2
        change FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x) (playValue G σ₂ τ₂ x)
        rw [hval_1, hval_2]
        apply multiplicity_valueLE_prepend
        · rw [playValue_cyclePriority_step, playValue_cyclePriority_step, hp_eq]
        · exact hnot_1
        · exact hnot_2
        · exact hle_step
  have h0 := hind k le_rfl
  have hkk : k - k = 0 := by omega
  rw [hkk] at h0
  exact h0

lemma playValue_le_of_step_le {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, ValueLE G
      (playValue G σ₂ τ₂ (step G σ₁ τ₁ x))
      (playValue G σ₂ τ₂ (step G σ₂ τ₂ x)))
    (v : V) :
    ValueLE G (playValue G σ₁ τ₁ v) (playValue G σ₂ τ₂ v) := by
  rw [valueLE_iff_multiplicity_valueLE hinj]
  apply multiplicity_playValue_le_of_step_le hinj
  intro x
  exact (valueLE_iff_multiplicity_valueLE hinj _ _).mp (hstep x)

/-! ### Part 2: Left-Step Comparison (`le_playValue_of_le_step`) -/

lemma reward_playValue_le_step_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (x : V) :
    reward (playValue G σ₁ τ₁ x).cyclePriority ≤
      reward (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)).cyclePriority := by
  have hle := reward_cyclePriority_le_of_multiplicity_valueLE (hstep x)
  rwa [playValue_cyclePriority_step] at hle

lemma playValue_cyclePriority_eq_on_recurring_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    {v x w : V}
    (hx : x ∈ recurring (play G σ₂ τ₂ v))
    (hw : w ∈ recurring (play G σ₂ τ₂ v)) :
    (playValue G σ₁ τ₁ x).cyclePriority = (playValue G σ₁ τ₁ w).cyclePriority := by
  apply reward_injective
  have h := eq_on_recurring_of_le_step_int
    (fun y => -reward (playValue G σ₁ τ₁ y).cyclePriority)
    (fun y => by have := reward_playValue_le_step_of_le_step hstep y; omega) hx hw
  omega

lemma count_playValue_eq_above_max_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    let m := playValue G σ₁ τ₁
    let R₂ := recurring (play G σ₂ τ₂ v)
    let w₂ := cycleLeader G σ₂ τ₂ v
    let p₂ := (playValue G σ₂ τ₂ v).cyclePriority
    let p_star := (m w₂).cyclePriority
    let M := Finset.univ.sup G.priority + max p₂ p_star + 1
    ∀ d : ℕ, ∀ q : ℕ, M - d ≤ q → max p₂ p_star < q →
      ∀ x ∈ R₂,
        count G (m (step G σ₁ τ₁ x)).path q =
          count G (m (step G σ₂ τ₂ x)).path q ∧
        count G (m (step G σ₂ τ₂ x)).path q =
          count G (m x).path q := by
  intro m R₂ w₂ p₂ p_star M d
  have hw₂ : w₂ ∈ R₂ := cycleLeader_mem_recurring G σ₂ τ₂ v
  induction d with
  | zero =>
    intro q hMq _ x _
    have hsup : Finset.univ.sup G.priority < q := by omega
    rw [count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro q hMq hmaxq
    by_cases hMq' : M - d ≤ q
    · exact ih q hMq' hmaxq
    · have hgt : ∀ x ∈ R₂, ∀ q', q < q' →
          count G (m (step G σ₁ τ₁ x)).path q' =
            count G (m (step G σ₂ τ₂ x)).path q' := by
        intro x hx q' hq'
        exact (ih q' (by omega) (by omega) x hx).1
      have hmx_eq : ∀ x ∈ R₂,
          count G (m x).path q =
            count G (m (step G σ₁ τ₁ x)).path q := by
        intro x hx
        have hpx : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        have hp_lt_q : (m x).cyclePriority < q := by omega
        have hcnt := count_playValue_step hp_lt_q
        have hle_p2 : G.priority x ≤ p₂ := Finset.le_sup hx
        have hne_q : G.priority x ≠ q := by omega
        rw [if_neg hne_q, Nat.add_zero] at hcnt
        exact hcnt
      have hcp_eq : ∀ x ∈ R₂,
          (m (step G σ₁ τ₁ x)).cyclePriority =
            (m (step G σ₂ τ₂ x)).cyclePriority := by
        intro x hx
        have h1 : (m (step G σ₂ τ₂ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        rw [playValue_cyclePriority_step, h1, h2]
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · have hstep_ge : ∀ x ∈ R₂,
            count G (m x).path q ≤ count G (m (step G σ₂ τ₂ x)).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).1 hpar
        intro x hx
        have heq := eq_of_step_le_on_recurring
          (fun y => count G (m y).path q) hstep_ge hx
        exact ⟨(hmx_eq x hx).symm.trans heq.symm, heq⟩
      · have hstep_le : ∀ x ∈ R₂,
            count G (m (step G σ₂ τ₂ x)).path q ≤ count G (m x).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (hstep x) (hcp_eq x hx) (hgt x hx)).2 hpar
        intro x hx
        have heq := eq_of_le_step_on_recurring
          (fun y => count G (m y).path q) hstep_le hx
        exact ⟨(hmx_eq x hx).symm.trans heq.symm, heq⟩

lemma reward_le_playValue_of_le_step {G : Game V}
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    reward (playValue G σ₁ τ₁ (cycleLeader G σ₂ τ₂ v)).cyclePriority ≤
      reward (playValue G σ₂ τ₂ v).cyclePriority := by
  let m := playValue G σ₁ τ₁
  let R₂ := recurring (play G σ₂ τ₂ v)
  let w₂ := cycleLeader G σ₂ τ₂ v
  let p₂ := (playValue G σ₂ τ₂ v).cyclePriority
  let p_star := (m w₂).cyclePriority
  change reward p_star ≤ reward p₂
  have hw₂ : w₂ ∈ R₂ := cycleLeader_mem_recurring G σ₂ τ₂ v
  have hpw₂ : G.priority w₂ = p₂ :=
    (playValue_cyclePriority_eq_priority_cycleLeader G σ₂ τ₂ v).symm
  have habove : ∀ q : ℕ, max p₂ p_star < q → ∀ x ∈ R₂,
      count G (m (step G σ₁ τ₁ x)).path q =
        count G (m (step G σ₂ τ₂ x)).path q := by
    intro q hq x hx
    let M := Finset.univ.sup G.priority + max p₂ p_star + 1
    have hMM : M - M ≤ q := by simp
    exact (count_playValue_eq_above_max_of_le_step hstep v M q hMM hq x hx).1
  have hcp_eq : ∀ x ∈ R₂,
      (m (step G σ₁ τ₁ x)).cyclePriority =
        (m (step G σ₂ τ₂ x)).cyclePriority := by
    intro x hx
    have h1 : (m (step G σ₂ τ₂ x)).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
    have h2 : (m x).cyclePriority = p_star :=
      playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
    rw [playValue_cyclePriority_step, h1, h2]
  rcases lt_trichotomy p₂ p_star with hlt | heq | hgt
  · rcases Nat.mod_two_eq_zero_or_one p_star with hpar | hpar
    · exfalso
      have hseq : ∀ x ∈ R₂, SetEquivalent G
          (m (step G σ₁ τ₁ x)).path
          (m (step G σ₂ τ₂ x)).path := by
        intro x hx q
        by_cases hq : p_star < q
        · exact habove q (by omega) x hx
        · have h1 : (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)).cyclePriority = p_star :=
            playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
          have h2 : (playValue G σ₁ τ₁ (step G σ₁ τ₁ x)).cyclePriority = p_star :=
            (hcp_eq x hx).trans h1
          change count G (playValue G σ₁ τ₁ (step G σ₁ τ₁ x)).path q =
            count G (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)).path q
          rw [count_playValue_eq_zero_of_le_cyclePriority (by omega),
              count_playValue_eq_zero_of_le_cyclePriority (by omega)]
      have hlen_step : ∀ x ∈ R₂,
          (m (step G σ₂ τ₂ x)).length ≤
            (m (step G σ₁ τ₁ x)).length ∧
          (m (step G σ₁ τ₁ x)).length + 1 = (m x).length := by
        intro x hx
        have h1 : (m (step G σ₂ τ₂ x)).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep (step_mem_recurring hx) hw₂
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        have hlen_ge := length_ge_of_multiplicity_valueLE_even
          (hstep x) (hcp_eq x hx) (hseq x hx) (by rw [playValue_cyclePriority_step, h2]; exact hpar)
        have hx_ne : x ≠ cycleLeader G σ₁ τ₁ x := by
          intro hcl
          have hpx : G.priority x = p_star := by
            have hpcl := playValue_cyclePriority_eq_priority_cycleLeader G σ₁ τ₁ x
            change (m x).cyclePriority = _ at hpcl
            rw [h2, ← hcl] at hpcl
            exact hpcl.symm
          have hpx_le : G.priority x ≤ p₂ := Finset.le_sup hx
          omega
        have hlen_eq := playValue_length_eq_succ_of_ne_cycleLeader hx_ne
        exact ⟨hlen_ge, hlen_eq.symm⟩
      have hstep_le : ∀ x ∈ R₂, (m (step G σ₂ τ₂ x)).length ≤ (m x).length := by
        intro x hx
        have ⟨h1, h2⟩ := hlen_step x hx
        omega
      have heq_w2 := eq_of_le_step_on_recurring (fun y => (m y).length) hstep_le hw₂
      have ⟨h1, h2⟩ := hlen_step w₂ hw₂
      omega
    · unfold reward
      split_ifs <;> omega
  · rw [heq]
  · rcases Nat.mod_two_eq_zero_or_one p₂ with hpar | hpar
    · unfold reward
      split_ifs <;> omega
    · exfalso
      have hstep_rel : ∀ x ∈ R₂,
          count G (m (step G σ₂ τ₂ x)).path p₂ ≤
            count G (m (step G σ₁ τ₁ x)).path p₂ ∧
          count G (m x).path p₂ =
            count G (m (step G σ₁ τ₁ x)).path p₂ +
              (if G.priority x = p₂ then 1 else 0) := by
        intro x hx
        have hge_cnt := (count_le_or_ge_of_multiplicity_valueLE
          (hstep x) (hcp_eq x hx)
          (fun q' hq' => habove q' (by omega) x hx)).2 hpar
        have h2 : (m x).cyclePriority = p_star :=
          playValue_cyclePriority_eq_on_recurring_of_le_step hstep hx hw₂
        have hp_lt : (m x).cyclePriority < p₂ := by
          rw [h2]
          exact hgt
        have hcnt := count_playValue_step hp_lt
        exact ⟨hge_cnt, hcnt⟩
      have hstep_le : ∀ x ∈ R₂,
          count G (m (step G σ₂ τ₂ x)).path p₂ ≤ count G (m x).path p₂ := by
        intro x hx
        have ⟨h1, h2⟩ := hstep_rel x hx
        omega
      have heq_w2 := eq_of_le_step_on_recurring
        (fun y => count G (m y).path p₂) hstep_le hw₂
      have ⟨h1, h2⟩ := hstep_rel w₂ hw₂
      rw [if_pos hpw₂] at h2
      omega

lemma multiplicity_le_playValue_of_le_step {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ v)
      (playValue G σ₂ τ₂ v) := by
  let π₂ := play G σ₂ τ₂ v
  let w₂ := cycleLeader G σ₂ τ₂ v
  let p₂ := (playValue G σ₂ τ₂ v).cyclePriority
  let k := (playValue G σ₂ τ₂ v).length
  have hcl_play : ∀ t : ℕ, cycleLeader G σ₂ τ₂ (π₂ t) = w₂ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [π₂] at ih ⊢
      rw [play_succ', cycleLeader_step, ih]
  have hcp_play : ∀ t : ℕ, (playValue G σ₂ τ₂ (π₂ t)).cyclePriority = p₂ := by
    intro t
    rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl_play t,
        ← playValue_cyclePriority_eq_priority_cycleLeader]
  have hbase_w2 : FriedmannMultiplicity.ValueLE G
      (playValue G σ₁ τ₁ w₂) (playValue G σ₂ τ₂ w₂) := by
    have hrew : reward (playValue G σ₁ τ₁ w₂).cyclePriority ≤ reward p₂ :=
      reward_le_playValue_of_le_step hstep v
    have hcl_w2 : w₂ = cycleLeader G σ₂ τ₂ w₂ := by
      have h := hcl_play k
      dsimp only [π₂, k] at h
      rw [play_playValue_length] at h
      exact h.symm
    have hcp_w2 : (playValue G σ₂ τ₂ w₂).cyclePriority = p₂ := by
      have h := hcp_play k
      dsimp only [π₂, k] at h
      rw [play_playValue_length] at h
      exact h
    rcases lt_or_eq_of_le hrew with hlt | heq
    · rw [multiplicity_valueLE_iff]
      right; left
      rw [hcp_w2]
      exact hlt
    · have hp_eq : (playValue G σ₁ τ₁ w₂).cyclePriority = p₂ := reward_injective heq
      have hcp_0 : (playValue G σ₁ τ₁ w₂).cyclePriority =
          (playValue G σ₂ τ₂ w₂).cyclePriority := by
        rw [hcp_w2, hp_eq]
      have hcl_1 : w₂ = cycleLeader G σ₁ τ₁ w₂ :=
        hcl_w2.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_0.symm)
      have hval_1 := playValue_eq_of_eq_cycleLeader hcl_1
      have hval_2 := playValue_eq_of_eq_cycleLeader hcl_w2
      rw [hval_1, hval_2, hcp_0]
      exact multiplicity_valueLE_refl G _
  have hind : ∀ d : ℕ, d ≤ k →
      FriedmannMultiplicity.ValueLE G
        (playValue G σ₁ τ₁ (π₂ (k - d)))
        (playValue G σ₂ τ₂ (π₂ (k - d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hk0 : k - 0 = k := by omega
      rw [hk0]
      dsimp only [π₂, k]
      rw [play_playValue_length]
      exact hbase_w2
    | succ d ih =>
      intro hd
      let t := k - (d + 1)
      have ht_lt : t < k := by omega
      have ht_succ : t + 1 = k - d := by omega
      let x := π₂ t
      let x' := step G σ₂ τ₂ x
      have hx'_eq : x' = π₂ (k - d) := by
        dsimp only [x', x, π₂]
        rw [← play_succ', ht_succ]
      have ih' : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x') (playValue G σ₂ τ₂ x') := by
        rw [hx'_eq]
        exact ih (by omega)
      have hle_step : FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
          (playValue G σ₂ τ₂ x') :=
        multiplicity_valueLE_trans (hstep x) ih'
      have hrew_le : reward (playValue G σ₁ τ₁ x).cyclePriority ≤
          reward (playValue G σ₂ τ₂ x).cyclePriority := by
        have h := reward_cyclePriority_le_of_multiplicity_valueLE hle_step
        dsimp only [x'] at h
        rw [playValue_cyclePriority_step, playValue_cyclePriority_step] at h
        exact h
      rcases lt_or_eq_of_le hrew_le with hlt | heq
      · rw [multiplicity_valueLE_iff]
        right; left
        exact hlt
      · have hp_eq : (playValue G σ₁ τ₁ x).cyclePriority =
            (playValue G σ₂ τ₂ x).cyclePriority :=
          reward_injective heq
        have hx_ne_w2 : x ≠ cycleLeader G σ₂ τ₂ x := by
          rw [hcl_play t]
          exact play_ne_cycleLeader_of_lt_length ht_lt
        have hx_ne_1 : x ≠ cycleLeader G σ₁ τ₁ x := by
          intro hcl_1
          exact hx_ne_w2 (hcl_1.trans (cycleLeader_eq_of_cyclePriority_eq hinj hp_eq))
        have hval_1 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_1
        have hnot_1 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_1
        have hval_2 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_w2
        have hnot_2 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_w2
        change FriedmannMultiplicity.ValueLE G
          (playValue G σ₁ τ₁ x) (playValue G σ₂ τ₂ x)
        rw [hval_1, hval_2]
        apply multiplicity_valueLE_prepend
        · rw [playValue_cyclePriority_step, playValue_cyclePriority_step, hp_eq]
        · exact hnot_1
        · exact hnot_2
        · exact hle_step
  have h0 := hind k le_rfl
  have hkk : k - k = 0 := by omega
  rw [hkk] at h0
  exact h0

lemma le_playValue_of_le_step {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V}
    (hstep : ∀ x : V, ValueLE G
      (playValue G σ₁ τ₁ (step G σ₁ τ₁ x))
      (playValue G σ₁ τ₁ (step G σ₂ τ₂ x)))
    (v : V) :
    ValueLE G (playValue G σ₁ τ₁ v) (playValue G σ₂ τ₂ v) := by
  rw [valueLE_iff_multiplicity_valueLE hinj]
  apply multiplicity_le_playValue_of_le_step hinj
  intro x
  exact (valueLE_iff_multiplicity_valueLE hinj _ _).mp (hstep x)

/-! ### Part 3: Locally Minimizing Optimal Counterstrategy and Monotonicity -/

lemma exists_min_neighbor_list {G : Game V} (hG : WellFormed G)
    (σ : V → V) (x : V) (L : List V) :
    ∃ u : V, G.edge x u ∧ ∀ w ∈ L, G.edge x w →
      ValueLE G (value G σ u) (value G σ w) := by
  induction L with
  | nil =>
    rcases hG.1 x with ⟨u, hu⟩
    refine ⟨u, hu, ?_⟩
    intro w hw
    nomatch hw
  | cons w₁ L ih =>
    rcases ih with ⟨u₂, hu₂, hle₂⟩
    by_cases hw₁ : G.edge x w₁
    · rcases valueLE_total hG.2 (value G σ w₁) (value G σ u₂) with h12 | h21
      · refine ⟨w₁, hw₁, ?_⟩
        intro w hmem hwe
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact valueLE_refl G _
        · exact valueLE_trans hG.2 h12 (hle₂ w hmem' hwe)
      · refine ⟨u₂, hu₂, ?_⟩
        intro w hmem hwe
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact h21
        · exact hle₂ w hmem' hwe
    · refine ⟨u₂, hu₂, ?_⟩
      intro w hmem hwe
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact False.elim (hw₁ hwe)
      · exact hle₂ w hmem' hwe

lemma exists_min_neighbor {G : Game V} (hG : WellFormed G) (σ : V → V) (x : V) :
    ∃ u : V, G.edge x u ∧ ∀ w, G.edge x w →
      ValueLE G (value G σ u) (value G σ w) := by
  rcases exists_min_neighbor_list hG σ x (Finset.univ : Finset V).toList with ⟨u, hu, hle⟩
  exact ⟨u, hu, fun w hw => hle w (Finset.mem_toList.mpr (Finset.mem_univ w)) hw⟩

noncomputable def localCounterstrategy (G : Game V) (hG : WellFormed G)
    (σ : V → V) (x : V) : V :=
  Classical.choose (exists_min_neighbor hG σ x)

lemma localCounterstrategy_legal {G : Game V} (hG : WellFormed G) (σ : V → V) :
    Legal G true (localCounterstrategy G hG σ) :=
  fun x _ => (Classical.choose_spec (exists_min_neighbor hG σ x)).1

lemma localCounterstrategy_min {G : Game V} (hG : WellFormed G) (σ : V → V)
    (x w : V) (hw : G.edge x w) :
    ValueLE G (value G σ (localCounterstrategy G hG σ x)) (value G σ w) :=
  (Classical.choose_spec (exists_min_neighbor hG σ x)).2 w hw

lemma playValue_localCounterstrategy_eq_value {G : Game V} (hG : WellFormed G)
    (σ : V → V) (v : V) :
    playValue G σ (localCounterstrategy G hG σ) v = value G σ v := by
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
  have hle1 : ValueLE G
      (playValue G σ (localCounterstrategy G hG σ) v)
      (playValue G σ τ v) := by
    apply playValue_le_of_step_le hG.2
    intro x
    rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ,
        ← value_eq_playValue_of_optimalCounterstrategy hG hτ]
    unfold step
    split_ifs with hx
    · exact valueLE_refl G _
    · exact localCounterstrategy_min hG σ x (τ x)
        (hτ.1 x (Bool.eq_true_of_not_eq_false hx))
  rw [← value_eq_playValue_of_optimalCounterstrategy hG hτ v] at hle1
  have hle2 := value_le_playValue hG σ (localCounterstrategy_legal hG σ) v
  exact valueLE_antisymm hG.2 hle1 hle2

lemma value_le_of_allowed {G : Game V} (hG : WellFormed G)
    {σ σ' : V → V} (hal : Allowed G σ σ') (v : V) :
    ValueLE G (value G σ v) (value G σ' v) := by
  rcases exists_optimalCounterstrategy G hG σ' with ⟨τ', hτ'⟩
  rw [← playValue_localCounterstrategy_eq_value hG σ v,
      value_eq_playValue_of_optimalCounterstrategy hG hτ' v]
  apply le_playValue_of_le_step hG.2
  intro x
  rw [playValue_localCounterstrategy_eq_value hG σ,
      playValue_localCounterstrategy_eq_value hG σ]
  unfold step
  split_ifs with hx
  · exact hal.2 x hx
  · exact localCounterstrategy_min hG σ x (τ' x)
      (hτ'.1 x (Bool.eq_true_of_not_eq_false hx))

omit [Fintype V] in
lemma prepend_injective_of_notMem {G : Game V} (hinj : Function.Injective G.priority)
    {u : V} {a b : Valuation V} (hua : u ∉ a.path) (hub : u ∉ b.path)
    (heq : prepend G u a = prepend G u b) : a = b := by
  rw [← valEq_iff_eq hinj]
  have hcp : a.cyclePriority = b.cyclePriority := by
    have h := congrArg Valuation.cyclePriority heq
    simpa [prepend] using h
  have hlen : a.length = b.length := by
    have h := congrArg Valuation.length heq
    change a.length + 1 = b.length + 1 at h
    omega
  refine ⟨hcp, ?_, hlen⟩
  intro q
  have hq : count G (prepend G u a).path q = count G (prepend G u b).path q := by
    rw [heq]
  rw [count_prepend_of_notMem hua q, count_prepend_of_notMem hub q, hcp] at hq
  omega

lemma value_lt_of_improving_of_priority_ne_cyclePriority
    {G : Game V} (hG : WellFormed G) {σ σ' : V → V} {v : V}
    (hle : ∀ u, ValueLE G (value G σ u) (value G σ' u))
    (hv : G.owner v = false)
    (hlt : ValueLT G (value G σ (σ v)) (value G σ (σ' v)))
    (hpv : G.priority v ≠ (value G σ (σ v)).cyclePriority) :
    ValueLT G (value G σ v) (value G σ' v) := by
  have hlt_step : ValueLT G (value G σ (σ v)) (value G σ' (σ' v)) :=
    valueLT_of_valueLT_of_valueLE hG.2 hlt (hle (σ' v))
  rcases hle v with heq | hlt_v
  · exfalso
    rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
    rcases exists_optimalCounterstrategy G hG σ' with ⟨τ', hτ'⟩
    have hstep1 : step G σ τ v = σ v := by unfold step; rw [if_pos hv]
    have hstep2 : step G σ' τ' v = σ' v := by unfold step; rw [if_pos hv]
    have hval1 := value_eq_playValue_of_optimalCounterstrategy hG hτ v
    have hval2 := value_eq_playValue_of_optimalCounterstrategy hG hτ' v
    have hval1_s := value_eq_playValue_of_optimalCounterstrategy hG hτ (σ v)
    have hval2_s := value_eq_playValue_of_optimalCounterstrategy hG hτ' (σ' v)
    have hne1 : v ≠ cycleLeader G σ τ v := by
      intro hcl
      apply hpv
      rw [hval1_s, ← hstep1, playValue_cyclePriority_step,
          playValue_cyclePriority_eq_priority_cycleLeader, ← hcl]
    have hcp_eq : (playValue G σ τ v).cyclePriority = (playValue G σ' τ' v).cyclePriority := by
      rw [← hval1, ← hval2, heq]
    have hne2 : v ≠ cycleLeader G σ' τ' v := by
      intro hcl2
      exact hne1 (hcl2.trans (cycleLeader_eq_of_cyclePriority_eq hG.2 hcp_eq.symm))
    have hprep1 := playValue_eq_prepend_of_ne_cycleLeader hne1
    have hnot1 := notMem_playValue_step_path_of_ne_cycleLeader hne1
    have hprep2 := playValue_eq_prepend_of_ne_cycleLeader hne2
    have hnot2 := notMem_playValue_step_path_of_ne_cycleLeader hne2
    rw [hstep1, ← hval1_s] at hprep1 hnot1
    rw [hstep2, ← hval2_s] at hprep2 hnot2
    have hprep_eq : prepend G v (value G σ (σ v)) = prepend G v (value G σ' (σ' v)) := by
      rw [← hprep1, ← hval1, heq, hval2, hprep2]
    have hstep_eq := prepend_injective_of_notMem hG.2 hnot1 hnot2 hprep_eq
    rw [hstep_eq] at hlt_step
    exact valueLT_irrefl hG.2 _ hlt_step
  · exact hlt_v

end StepComparison

theorem improvement_strict_lib {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ σ' : V → V)
    (hσ : Legal G false σ) (hi : Improvable G σ) (hs : Improvement G σ σ') :
    (∀ v, ValueLE G (value G σ v) (value G σ' v)) ∧
    ∃ v, G.owner v = false ∧ ValueLT G (value G σ (σ v)) (value G σ' (σ' v)) := by
  let _ := hσ
  have hle : ∀ v, ValueLE G (value G σ v) (value G σ' v) :=
    value_le_of_allowed hG hs.1
  rcases hs.2 hi with ⟨v, hv_owner, hv_lt⟩
  refine ⟨hle, v, hv_owner, ?_⟩
  exact valueLT_of_valueLT_of_valueLE hG.2 hv_lt (hle (σ' v))

end FriedmannParity


