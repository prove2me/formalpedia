-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
-- name    : OAI_Probability_SATVariance_ClauseCombinatorics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:13:09.906312+00:00
-- url     : https://prove2.me/theorems/e8c09be3-6dce-4a7d-a5d9-1967d278482f
-- title:
--   Frozen variables of a set of assignments and the clauses that kill it
-- statement:
--   Fix $n$ Boolean variables indexed by $[n]=\{0,1,\dots,n-1\}$. An *assignment* is a map $a:[n]\to\{\mathrm T,\mathrm F\}$. A *clause of width $k$* is a pair $c=(V,\beta)$ consisting of a set $V\subseteq[n]$ of exactly $k$ variables and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$; an assignment $a$ *satisfies* $c$ if $a(v)=\beta(v)$ for at least one $v\in V$. For a finite set $S$ of assignments this module defines the following objects and records their basic combinatorics.
--
--   1. **Frozen variables.** The set of variables on which all members of $S$ agree,
--   $$
--   \operatorname{Fr}(S)=\{v\in[n] : a(v)=a'(v)\ \text{for all } a,a'\in S\}.
--   $$
--   2. **Killing clauses.** A clause $c$ *kills* $S$ if no assignment in $S$ satisfies $c$.
--   3. **Characterization of killing clauses.** If $a_0\in S$, then a clause $c=(V,\beta)$ kills $S$ if and only if
--   $$
--   V\subseteq\operatorname{Fr}(S)\quad\text{and}\quad \beta(v)=\neg a_0(v)\ \text{for every } v\in V .
--   $$
--   4. **Killing clauses versus subsets of frozen variables.** If $a_0\in S$, the map $(V,\beta)\mapsto V$ is a bijection from the width-$k$ clauses that kill $S$ onto the $k$-element subsets of $\operatorname{Fr}(S)$. Its inverse sends $V$ to the clause on $V$ whose signs oppose $a_0$, i.e. $\beta=\neg a_0|_V$.
--
--   By item 4, a nonempty set $S$ is killed by exactly $\binom{|\operatorname{Fr}(S)|}{k}$ of the $\binom nk2^k$ clauses of width $k$. This turns the probability that a uniformly random clause kills a candidate solution set into a function of the single number $|\operatorname{Fr}(S)|$, which is the starting point of the kill-probability estimates for random $k$-SAT built on these definitions.
--
--   **Formalization Note** Assignments are functions from `Fin n` to `Bool`, and a clause is a dependent pair of a `Finset (Fin n)` of cardinality $k$ and a sign function on it. For $S=\emptyset$ every variable is frozen and every clause kills $S$, which is why items 3 and 4 assume a member $a_0\in S$. The lemma `bool_ne_iff` (for Booleans, $x\neq y$ iff $y=\neg x$) is a small helper.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/ClauseCombinatorics.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/ClauseCombinatorics.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATSharpness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATSharpness

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


