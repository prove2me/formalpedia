-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
-- name    : OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:21:28.638971+00:00
-- url     : https://prove2.me/theorems/cba13db5-7074-4ce7-b338-8ab11632834d
-- title:
--   Frozen variables of a set of assignments and the clauses that kill it
-- statement:
--   Let $[n]=\{0,\dots,n-1\}$. An *assignment* on $n$ Boolean variables is a map $a:[n]\to\{\mathrm T,\mathrm F\}$. A *$k$-clause* on $n$ variables is a pair $c=(s,\sigma)$ consisting of a $k$-element set $s=\operatorname{supp}c\subseteq[n]$ and a sign map $\sigma:s\to\{\mathrm T,\mathrm F\}$; an assignment $a$ *satisfies* $c$ if $a(v)=\sigma(v)$ for at least one $v\in s$. Let $S$ be a finite set of assignments on $n$ variables.
--
--   1. **Frozen variables.** The frozen set of $S$ is the set of variables on which all members of $S$ agree,
--   $$
--   \operatorname{Fr}(S)=\{v\in[n]:\ a(v)=b(v)\ \text{for all } a,b\in S\}.
--   $$
--   If $S$ is empty or a singleton, every variable is frozen.
--   2. **Killing clauses.** A $k$-clause $c$ *kills* $S$ if no assignment in $S$ satisfies $c$. Every clause kills the empty set.
--   3. **Characterization.** If $a_0\in S$, then $c=(s,\sigma)$ kills $S$ if and only if
--   $$
--   s\subseteq\operatorname{Fr}(S)\qquad\text{and}\qquad \sigma(v)=\neg a_0(v)\ \text{ for every } v\in s,
--   $$
--   that is, all variables of $c$ are frozen and every literal of $c$ opposes the common value of $S$ there.
--   4. **Counting bijection.** If $a_0\in S$, sending a killing $k$-clause to its support is a bijection from the $k$-clauses that kill $S$ onto the $k$-element subsets of $\operatorname{Fr}(S)$. The inverse sends $s$ to the clause $(s,\ v\mapsto\neg a_0(v))$. Consequently a nonempty $S$ is killed by exactly $\binom{|\operatorname{Fr}(S)|}{k}$ of the $\binom nk2^k$ possible $k$-clauses.
--
--   These notions describe when one more random clause eliminates every remaining solution: only clauses built from frozen variables with the opposite signs can do so. They underlie the exact formula for the probability that a uniformly random $k$-clause kills a solution set, which feeds the clause-replacement and lifetime estimates in the analysis of the first unsatisfiability time of random $k$-SAT.
--
--   **Formalization Note** A clause is the dependent pair `Clause n k` of a $k$-element `Finset (Fin n)` and a Boolean sign function on it; `frozen` returns a `Finset (Fin n)` and `Kills` is a proposition. The lemma `bool_ne_iff` ($x\ne y$ iff $y=\neg x$ for Booleans) is plumbing; `kills_iff` is item 3 and `killingEquiv` is the bijection of item 4.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/ClauseCombinatorics.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/ClauseCombinatorics.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def frozen {n : ℕ} (S : Finset (Assignment n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∀ a ∈ S, ∀ b ∈ S, a v = b v

def Kills {n k : ℕ} (S : Finset (Assignment n)) (c : Clause n k) : Prop :=
  ∀ a ∈ S, ¬ Satisfies c a

lemma bool_ne_iff (x y : Bool) : x ≠ y ↔ y = !x := by
  cases x <;> cases y <;> decide

lemma kills_iff {n k : ℕ} {S : Finset (Assignment n)} {a₀ : Assignment n}
    (ha₀ : a₀ ∈ S) (c : Clause n k) :
    Kills S c ↔ c.1.1 ⊆ frozen S ∧ ∀ v : c.1.1, c.2 v = !(a₀ v) := by
  classical
  constructor
  · intro h
    have hn : ∀ a ∈ S, ∀ v : c.1.1, a v ≠ c.2 v := by
      intro a ha v he
      exact h a ha ⟨v, he⟩
    refine ⟨?_, fun v => (bool_ne_iff _ _).mp (hn a₀ ha₀ v)⟩
    intro v hv
    simp only [frozen, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha b hb
    have h₁ := (bool_ne_iff _ _).mp (hn a ha ⟨v, hv⟩)
    have h₂ := (bool_ne_iff _ _).mp (hn b hb ⟨v, hv⟩)
    exact Bool.not_injective (h₁.symm.trans h₂)
  · rintro ⟨hs, ht⟩ a ha ⟨v, hv⟩
    have hf := (Finset.mem_filter.mp (hs v.property)).2 a ha a₀ ha₀
    have hne := (bool_ne_iff (a₀ v) (c.2 v)).mpr (ht v)
    exact hne (hf.symm.trans hv)

def killingEquiv {n k : ℕ} {S : Finset (Assignment n)} {a₀ : Assignment n}
    (ha₀ : a₀ ∈ S) :
    {c : Clause n k // Kills S c} ≃
      {s : Finset (Fin n) // s ⊆ frozen S ∧ s.card = k} where
  toFun c := ⟨c.1.1.1, (kills_iff ha₀ c.1).mp c.2 |>.1, c.1.1.2⟩
  invFun s := ⟨⟨⟨s.1, s.2.2⟩, fun v => !(a₀ v)⟩,
    (kills_iff ha₀ _).mpr ⟨s.2.1, fun _ => rfl⟩⟩
  left_inv c := by
    apply Subtype.ext
    rcases c with ⟨⟨s, f⟩, hc⟩
    have hf := (kills_iff ha₀ ⟨s, f⟩).mp hc |>.2
    dsimp
    congr 1
    exact funext fun v => (hf v).symm
  right_inv s := by
    apply Subtype.ext
    rfl

end RandomKSAT

end

end OAI


