-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Clauses
-- name    : OAI_Probability_RandomSAT_Clauses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:29:37.413596+00:00
-- url     : https://prove2.me/theorems/5427f9cc-62b7-4023-a1a4-21e7b895c8f6
-- title:
--   Proper clauses as signed variable sets, clause counts, frozen coordinates and killing clauses
-- statement:
--   Throughout, an *assignment* on $n$ Boolean variables is a map $\sigma:\{0,\dots,n-1\}\to\{\mathrm{T},\mathrm{F}\}$. A *proper $k$-clause* on $n$ variables is a map $C$ from the variables to $\{\bot,\mathrm{T},\mathrm{F}\}$ that gives a sign to exactly $k$ variables ($\bot$ means the variable is absent). An assignment $\sigma$ satisfies $C$ if $C(i)=\sigma(i)$ for some variable $i$. A formula with $m$ clauses is an $m$-tuple of proper $k$-clauses, and $p_{\mathrm{SAT}}(n,k,m)$ is the fraction of such formulas that are satisfiable. This module develops the basic combinatorics of these objects.
--
--   1. **Support.** The support $\operatorname{supp}C$ of a proper $k$-clause is the set of variables that carry a sign. It has exactly $k$ elements.
--   2. **Signed variable sets and counting.** A signed $k$-set is a pair $(s,\beta)$ consisting of a $k$-element subset $s\subseteq\{0,\dots,n-1\}$ and a sign map $\beta:s\to\{\mathrm{T},\mathrm{F}\}$. The clause built from $(s,\beta)$ gives each $i\in s$ the sign $\beta(i)$ and leaves all other variables absent. Conversely, a clause $C$ is sent to $\operatorname{supp}C$ together with its signs there. These maps form a bijection between proper $k$-clauses and signed $k$-sets, which yields the counts
--   $$
--   \#\{k\text{-subsets}\}=\binom nk,\qquad \#\{\text{proper }k\text{-clauses}\}=\binom nk2^k,\qquad \#\{\text{formulas with }m\text{ clauses}\}=\Big(\binom nk2^k\Big)^m .
--   $$
--   A formula with no clauses is satisfiable, so $p_{\mathrm{SAT}}(n,k,0)=1$ for all $n$ and $k$.
--   3. **Frozen coordinates and killing clauses.** For a set $S$ of assignments and a reference assignment $\sigma_0$, the frozen coordinates are $\operatorname{Fr}(S,\sigma_0)=\{i:\sigma(i)=\sigma_0(i)\text{ for all }\sigma\in S\}$. A clause $C$ *kills* $S$ if no $\sigma\in S$ satisfies $C$. If $\sigma_0\in S$, then $C$ kills $S$ if and only if $\operatorname{supp}C\subseteq\operatorname{Fr}(S,\sigma_0)$ and $C(i)=\neg\sigma_0(i)$ for every $i\in\operatorname{supp}C$.
--   4. **Forced variables.** $\operatorname{Forced}(S)$ is the set of variables $i$ such that $S$ is nonempty and all members of $S$ take the same value at $i$. It is empty for $S=\emptyset$, and it coincides with $\operatorname{Fr}(S,\sigma_0)$ whenever $\sigma_0\in S$.
--   5. **Opposing clauses.** For an assignment $\sigma$ and a $k$-set $s$, the opposing clause gives each $i\in s$ the sign $\neg\sigma(i)$. If $\sigma_0\in S$, then sending a $k$-subset $s\subseteq\operatorname{Fr}(S,\sigma_0)$ to the opposing clause of $\sigma_0$ on $s$ is a bijection onto the proper $k$-clauses that kill $S$. In particular, exactly $\binom{|\operatorname{Fr}(S,\sigma_0)|}{k}$ proper $k$-clauses kill $S$.
--   6. **Uniform and killing probabilities.** For a predicate $P$ on a finite set $A$, $\Pr_A[P]=|\{a\in A:P(a)\}|/|A|$. The killing probability of $S$ is
--   $$
--   \Pr_C\big[S\neq\emptyset\ \text{and}\ C\text{ kills }S\big],
--   $$
--   where $C$ is a uniformly random proper $k$-clause on $n$ variables. It equals $0$ for $S=\emptyset$.
--
--   These are the combinatorial foundations of the clause-by-clause analysis of random proper $k$-SAT. By item 5, a nonempty solution set with $b$ forced variables is killed by a uniform random proper $k$-clause with probability exactly $\binom bk/(\binom nk2^k)$. This is the kill fraction that the replacement estimates study.
--
--   **Formalization Note** A proper clause is a map `Fin n → Option Bool` with exactly $k$ values of the form `some`; `none` encodes an absent variable. `uniformProbability` divides by the cardinality of the type, so by Lean's convention it returns $0$ on an empty type (for example proper $k$-clauses when $n<k$). Two private rewriting lemmas about `ite` are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Clauses.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Clauses.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def clauseSupport {n k : ℕ} (C : ProperClause n k) : Finset (Fin n) :=
  Finset.univ.filter fun i => (C.val i).isSome

@[simp] theorem clauseSupport_card {n k : ℕ} (C : ProperClause n k) :
    (clauseSupport C).card = k := C.property

@[simp] theorem mem_clauseSupport {n k : ℕ} (C : ProperClause n k) (i : Fin n) :
    i ∈ clauseSupport C ↔ (C.val i).isSome := by
  simp [clauseSupport]

abbrev VariableSet (n k : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard k)

abbrev SignedVariableSet (n k : ℕ) := Σ s : VariableSet n k, ↥s.val → Bool

def clauseFromSigns {n k : ℕ} (s : VariableSet n k) (b : ↥s.val → Bool) :
    ProperClause n k :=
  ⟨fun i => if h : i ∈ s.val then some (b ⟨i, h⟩) else none, by
    have hs : (Finset.univ.filter fun i : Fin n =>
        (if h : i ∈ s.val then some (b ⟨i, h⟩) else none).isSome) = s.val := by
      ext i
      by_cases hi : i ∈ s.val <;> simp [hi]
    rw [hs]
    exact (Finset.mem_powersetCard.mp s.property).2⟩

@[simp] theorem clauseSupport_fromSigns {n k : ℕ} (s : VariableSet n k)
    (b : ↥s.val → Bool) : clauseSupport (clauseFromSigns s b) = s.val := by
  ext i
  by_cases hi : i ∈ s.val <;> simp [clauseSupport, clauseFromSigns, hi]

def clauseToSigns {n k : ℕ} (C : ProperClause n k) : SignedVariableSet n k :=
  ⟨⟨clauseSupport C, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, clauseSupport_card C⟩⟩,
    fun i => (C.val i.val).getD false⟩

def properClauseEquiv (n k : ℕ) : ProperClause n k ≃ SignedVariableSet n k where
  toFun := clauseToSigns
  invFun := fun t => clauseFromSigns t.1 t.2
  left_inv C := by
    apply Subtype.ext
    funext i
    dsimp [clauseToSigns, clauseFromSigns]
    by_cases hi : i ∈ clauseSupport C
    · rw [ite_eq_left hi]
      exact Option.getD_of_ne_none (Option.isSome_iff_ne_none.mp
        ((mem_clauseSupport C i).mp hi)) false
    · rw [ite_eq_right hi]
      exact ((Option.not_isSome_iff_eq_none).mp (by simpa using hi)).symm
  right_inv t := by
    rcases t with ⟨s, b⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact clauseSupport_fromSigns s b
    · apply Function.hfunext (by
        change ↥(clauseSupport (clauseFromSigns s b)) = ↥s.val
        rw [clauseSupport_fromSigns])
      intro i j hij
      apply heq_of_eq
      have hv : i.val = j.val := by
        exact (Subtype.heq_iff_coe_eq (fun x => by
          change x ∈ clauseSupport (clauseFromSigns s b) ↔ x ∈ s.val
          rw [clauseSupport_fromSigns])).mp hij
      simp [clauseToSigns, clauseFromSigns, hv, j.property]

@[simp] theorem card_variableSet (n k : ℕ) :
    Fintype.card (VariableSet n k) = n.choose k := by
  simp [VariableSet]

@[simp] theorem card_properClause (n k : ℕ) :
    Fintype.card (ProperClause n k) = n.choose k * 2 ^ k := by
  rw [Fintype.card_congr (properClauseEquiv n k), Fintype.card_sigma]
  have hc (s : VariableSet n k) : Fintype.card (↥s.val → Bool) = 2 ^ k := by
    simp [(Finset.mem_powersetCard.mp s.property).2]
  simp_rw [hc]
  simp

@[simp] theorem card_formula (n k m : ℕ) :
    Fintype.card (Formula n k m) = (n.choose k * 2 ^ k) ^ m := by
  simp [Formula]

theorem satisfiable_empty (n k : ℕ) (F : Formula n k 0) : Satisfiable F := by
  exact ⟨fun _ => false, fun i => Fin.elim0 i⟩

@[simp] theorem properSATProbability_zero (n k : ℕ) : properSATProbability n k 0 = 1 := by
  classical
  simp [properSATProbability, Fintype.card_subtype, satisfiable_empty]

def frozenCoordinates {n : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ σ ∈ S, σ i = σ₀ i

def KillsSolutions {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) : Prop :=
  ∀ σ ∈ S, ¬ SatisfiesClause σ C

theorem kills_iff {n k : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n)
    (hσ₀ : σ₀ ∈ S) (C : ProperClause n k) :
    KillsSolutions S C ↔
      clauseSupport C ⊆ frozenCoordinates S σ₀ ∧
      ∀ i ∈ clauseSupport C, C.val i = some (!(σ₀ i)) := by
  constructor
  · intro h
    have hop (σ : Assignment n) (hσ : σ ∈ S) (i : Fin n)
        (hi : i ∈ clauseSupport C) : C.val i = some (!(σ i)) := by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((mem_clauseSupport C i).mp hi)
      have hne : b ≠ σ i := by
        intro heq
        exact h σ hσ ⟨i, hb.trans (congrArg some heq)⟩
      cases hb' : b <;> cases hv : σ i <;> simp_all
    refine ⟨?_, hop σ₀ hσ₀⟩
    intro i hi
    simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    intro σ hσ
    have heq := (hop σ hσ i hi).symm.trans (hop σ₀ hσ₀ i hi)
    simpa using heq
  · rintro ⟨hsub, hsign⟩ σ hσ ⟨i, hi⟩
    have his : i ∈ clauseSupport C := by
      rw [mem_clauseSupport, hi]
      rfl
    have hf : σ i = σ₀ i := by
      have hf := hsub his
      simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact hf σ hσ
    have heq := hi.symm.trans (hsign i his)
    cases hv : σ₀ i <;> simp_all

def forcedVariables {n : ℕ} (S : Finset (Assignment n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => S.Nonempty ∧ ∃ b : Bool, ∀ σ ∈ S, σ i = b

@[simp] theorem forcedVariables_empty (n : ℕ) :
    forcedVariables (∅ : Finset (Assignment n)) = ∅ := by
  simp [forcedVariables]

def opposingClause {n k : ℕ} (σ : Assignment n) (s : VariableSet n k) :
    ProperClause n k := clauseFromSigns s (fun i => !(σ i.val))

@[simp] theorem support_opposingClause {n k : ℕ} (σ : Assignment n)
    (s : VariableSet n k) : clauseSupport (opposingClause σ s) = s.val :=
  clauseSupport_fromSigns _ _

def killingClauseEquiv {n k : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n)
    (hσ₀ : σ₀ ∈ S) :
    {C : ProperClause n k // KillsSolutions S C} ≃
      ↥((frozenCoordinates S σ₀).powersetCard k) where
  toFun C := ⟨clauseSupport C.val, Finset.mem_powersetCard.mpr
    ⟨((kills_iff S σ₀ hσ₀ C.val).mp C.property).1, clauseSupport_card C.val⟩⟩
  invFun s := ⟨opposingClause σ₀ ⟨s.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp s.property).2⟩⟩, by
    apply (kills_iff S σ₀ hσ₀ _).mpr
    simp only [support_opposingClause]
    refine ⟨(Finset.mem_powersetCard.mp s.property).1, ?_⟩
    intro i hi
    simp [opposingClause, clauseFromSigns, hi]⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (if i ∈ clauseSupport C.val then some (!(σ₀ i)) else none) = C.val.val i
    by_cases hi : i ∈ clauseSupport C.val
    · rw [ite_eq_left hi]
      exact (((kills_iff S σ₀ hσ₀ C.val).mp C.property).2 i hi).symm
    · rw [ite_eq_right hi]
      apply Eq.symm
      apply Option.not_isSome_iff_eq_none.mp
      simpa only [mem_clauseSupport] using hi
  right_inv s := by
    apply Subtype.ext
    exact support_opposingClause _ _

noncomputable def uniformProbability {α : Type*} [Fintype α] (p : α → Prop) : ℝ := by
  classical
  exact (Fintype.card {a : α // p a} : ℝ) / Fintype.card α

noncomputable def killingProbability {n : ℕ} (k : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformProbability (fun C : ProperClause n k => S.Nonempty ∧ KillsSolutions S C)

@[simp] theorem killingProbability_empty (n k : ℕ) :
    killingProbability k (∅ : Finset (Assignment n)) = 0 := by
  classical
  simp [killingProbability, uniformProbability]

end

end FixedClauseThreshold

end OAI


