-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
-- name    : OAI_Probability_SATVariance_RootDisintegration__SATVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:28:49.605003+00:00
-- url     : https://prove2.me/theorems/85347461-cdce-4728-8b48-b70ab7a14b9b
-- title:
--   Splitting a clause into a root pattern on $k$ distinguished variables and a residual clause
-- statement:
--   A $k$-clause on $n$ Boolean variables is a pair $c=(s,\sigma)$ of a $k$-element set $s=\operatorname{supp}c\subseteq[n]=\{0,\dots,n-1\}$ and signs $\sigma:s\to\{\mathrm T,\mathrm F\}$; an assignment $a:[n]\to\{\mathrm T,\mathrm F\}$ satisfies $c$ if $a(v)=\sigma(v)$ for some $v\in s$. Write $\mathcal C_{n,k}$ for the set of $k$-clauses on $n$ variables and $\bot$ for "absent".
--
--   1. **Reading a clause.** $\operatorname{read}_c(v)=\sigma(v)$ if $v\in\operatorname{supp}c$ and $\operatorname{read}_c(v)=\bot$ otherwise. The reading is defined (not $\bot$) exactly on the support, and two $k$-clauses with the same reading at every variable are equal.
--   2. **Root types.** A root type of width $k$ is a map $t:[k]\to\{\bot,\mathrm T,\mathrm F\}$, a partial sign pattern on $k$ root positions. Its support is $\operatorname{supp}t=\{j:t(j)\ne\bot\}$ and its size is $|t|=|\operatorname{supp}t|\le k$. An assignment $a:[k]\to\{\mathrm T,\mathrm F\}$ *root-satisfies* $t$ if $t(j)=a(j)$ for some $j$.
--   3. **Merging.** Fix a bijection $e:[k]\sqcup[u]\to[n]$. Write $e(j)$ for $j\in[k]$ (the root variables) and $e(\bar\jmath)$ for $j\in[u]$ (the remaining variables), where $\bar\jmath$ denotes the copy of $j$ in the second summand. For a root type $t$ and a $(k-|t|)$-clause $c'$ on $u$ variables, $\operatorname{merge}_e(t,c')$ is the $k$-clause on $n$ variables with support $\{e(j):j\in\operatorname{supp}t\}\cup\{e(\bar\jmath):j\in\operatorname{supp}c'\}$, sign $t(j)$ at $e(j)$ and sign $\operatorname{read}_{c'}(j)$ at $e(\bar\jmath)$.
--   4. **Reading back.** For $c\in\mathcal C_{n,k}$, the root type $\operatorname{root}_e(c)(j)=\operatorname{read}_c(e(j))$ records $c$ on the root variables, and $\operatorname{part}_e(c)$ is the clause on $u$ variables with support $\{j\in[u]: e(\bar\jmath)\in\operatorname{supp}c\}$ and the signs of $c$ there; it has length $k-|\operatorname{root}_e(c)|$.
--   5. **Disintegration bijection.** Merging is a bijection
--   $$
--   \bigsqcup_{t:[k]\to\{\bot,\mathrm T,\mathrm F\}}\mathcal C_{u,\,k-|t|}\ \longrightarrow\ \mathcal C_{n,k},\qquad (t,c')\mapsto\operatorname{merge}_e(t,c'),
--   $$
--   whose inverse is $c\mapsto\big(\operatorname{root}_e(c),\operatorname{part}_e(c)\big)$.
--
--   This decomposition describes a uniformly random $k$-clause relative to a fixed set of $k$ root variables: its root type, and, given the root type $t$, a uniformly random clause of length $k-|t|$ on the remaining variables. A merged clause is satisfied exactly when the root part of the assignment root-satisfies $t$ or the remaining part satisfies $c'$. In the analysis of the first unsatisfiability time of random $k$-SAT, the variables of a deleted clause play the role of the roots and every other clause is split into its root and residual parts.
--
--   **Formalization Note** `RootType k` is `Fin k → Option Bool`, with `none` playing the role of $\bot$, and $e$ is an equivalence `Fin k ⊕ Fin u ≃ Fin n`. Signs at absent positions are filled with the unused default `false`. The lemmas `clauseRead_isSome`, `clause_ext`, `rootSize_le`, the membership and reading lemmas for `mergeClause`, `split_support` and `partSupport_card` are the facts behind the bijection `splitClauseEquiv`, whose two halves are `mergeClause_injective` and `mergeClause_surjective`. `RootSatisfies` is the root-satisfaction predicate of item 2.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/RootDisintegration.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/RootDisintegration.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def clauseRead {n k : ℕ} (c : Clause n k) (v : Fin n) : Option Bool :=
  if h : v ∈ c.1.1 then some (c.2 ⟨v,h⟩) else none

lemma clauseRead_isSome {n k : ℕ} (c : Clause n k) (v : Fin n) :
    (clauseRead c v).isSome ↔ v ∈ c.1.1 := by
  simp only [clauseRead]
  split <;> simp_all

lemma clause_ext {n k : ℕ} {c d : Clause n k}
    (h : ∀ v, clauseRead c v = clauseRead d v) : c = d := by
  have hs : c.1 = d.1 := by
    apply Subtype.ext
    ext v
    rw [← clauseRead_isSome, ← clauseRead_isSome, h]
  rcases c with ⟨s,f⟩
  rcases d with ⟨t,g⟩
  dsimp only at hs
  subst t
  have hf : f = g := by
    funext v
    have hh := h v
    simpa [clauseRead, v.property] using hh
  subst g
  rfl

abbrev RootType (k : ℕ) := Fin k → Option Bool

def rootSupport {k : ℕ} (t : RootType k) : Finset (Fin k) :=
  Finset.univ.filter fun j => (t j).isSome

def rootSize {k : ℕ} (t : RootType k) : ℕ := (rootSupport t).card

lemma rootSize_le {k : ℕ} (t : RootType k) : rootSize t ≤ k := by
  simpa [rootSize] using (Finset.card_le_univ (rootSupport t))

def mergeClause {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) : Clause n k :=
  ⟨⟨((rootSupport t).disjSum c.1.1).map e.toEmbedding, by
      rw [Finset.card_map, Finset.card_disjSum, c.1.property]
      exact Nat.add_sub_of_le (rootSize_le t)⟩,
    fun v => match e.symm v with
      | Sum.inl j => (t j).getD false
      | Sum.inr j => (clauseRead c j).getD false⟩

lemma mem_merge_inl {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin k) :
    e (Sum.inl j) ∈ (mergeClause e t c).1.1 ↔ (t j).isSome := by
  simp [mergeClause, rootSupport]

lemma mem_merge_inr {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin u) :
    e (Sum.inr j) ∈ (mergeClause e t c).1.1 ↔ j ∈ c.1.1 := by
  simp [mergeClause]

lemma read_merge_inl {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin k) :
    clauseRead (mergeClause e t c) (e (Sum.inl j)) = t j := by
  have hm := mem_merge_inl e t c j
  unfold clauseRead
  split_ifs with h
  · have ht : (t j).isSome := hm.mp h
    cases hx : t j with
    | none => simp [hx] at ht
    | some b => simp [mergeClause, hx]
  · have ht : ¬(t j).isSome := mt hm.mpr h
    cases hx : t j with
    | none => rfl
    | some b => simp [hx] at ht

lemma read_merge_inr {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin u) :
    clauseRead (mergeClause e t c) (e (Sum.inr j)) = clauseRead c j := by
  have hm := mem_merge_inr e t c j
  by_cases h : j ∈ c.1.1
  · simp [clauseRead, mergeClause, h]
  · simp [clauseRead, mt hm.mp h, h]

lemma mergeClause_injective {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    Function.Injective (fun p : (t : RootType k) × Clause u (k-rootSize t) =>
      mergeClause e p.1 p.2) := by
  rintro ⟨t,c⟩ ⟨s,d⟩ h
  have ht : t = s := by
    funext j
    have hh := congrArg (fun x => clauseRead x (e (Sum.inl j))) h
    simpa only [read_merge_inl] using hh
  subst s
  have hc : c = d := by
    apply clause_ext
    intro j
    have hh := congrArg (fun x => clauseRead x (e (Sum.inr j))) h
    simpa only [read_merge_inr] using hh
  subst d
  rfl

def rootRead {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) : RootType k :=
  fun j => clauseRead c (e (Sum.inl j))

def partSupport {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) : Finset (Fin u) :=
  Finset.univ.filter fun j => e (Sum.inr j) ∈ c.1.1

lemma split_support {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) :
    (rootSupport (rootRead e c)).disjSum (partSupport e c) = c.1.1.map e.symm.toEmbedding := by
  ext z
  cases z <;> simp [rootSupport, rootRead, partSupport, clauseRead_isSome]

lemma partSupport_card {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) :
    (partSupport e c).card = k-rootSize (rootRead e c) := by
  have hh := congrArg Finset.card (split_support e c)
  rw [Finset.card_disjSum, Finset.card_map, c.1.property] at hh
  change rootSize (rootRead e c) + _ = k at hh
  omega

def partRead {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) :
    Clause u (k-rootSize (rootRead e c)) :=
  ⟨⟨partSupport e c, partSupport_card e c⟩,
    fun v => c.2 ⟨e (Sum.inr v), by simpa [partSupport] using v.property⟩⟩

lemma read_partRead {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) (j : Fin u) :
    clauseRead (partRead e c) j = clauseRead c (e (Sum.inr j)) := by
  by_cases h : e (Sum.inr j) ∈ c.1.1
  · simp [clauseRead, partRead, partSupport, h]
  · simp [clauseRead, partRead, partSupport, h]

lemma mergeClause_surjective {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    Function.Surjective (fun p : (t : RootType k) × Clause u (k-rootSize t) =>
      mergeClause e p.1 p.2) := by
  intro c
  refine ⟨⟨rootRead e c, partRead e c⟩, ?_⟩
  apply clause_ext
  intro v
  obtain ⟨z,rfl⟩ := e.surjective v
  cases z with
  | inl j => exact read_merge_inl e _ _ j
  | inr j => rw [read_merge_inr, read_partRead]

def splitClauseEquiv {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    ((t : RootType k) × Clause u (k-rootSize t)) ≃ Clause n k :=
  Equiv.ofBijective _ ⟨mergeClause_injective e, mergeClause_surjective e⟩

def RootSatisfies {k : ℕ} (t : RootType k) (a : Assignment k) : Prop :=
  ∃ j, t j = some (a j)

end RandomKSAT

end

end OAI


