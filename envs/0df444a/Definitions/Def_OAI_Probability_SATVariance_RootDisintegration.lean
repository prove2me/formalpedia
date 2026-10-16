-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
-- name    : OAI_Probability_SATVariance_RootDisintegration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:14:59.928869+00:00
-- url     : https://prove2.me/theorems/06327e5e-6fd7-4db0-8833-1f89a05ea204
-- title:
--   Reading a clause as a partial sign pattern, and clause extensionality
-- statement:
--   Let $n,k\in\mathbb N$. A clause of width $k$ on the variables $[n]=\{0,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a set $V\subseteq[n]$ with $|V|=k$ and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$.
--
--   1. **Reading.** The reading of $c$ is the partial sign pattern $\hat c:[n]\to\{\mathrm T,\mathrm F,\bot\}$ given by
--   $$
--   \hat c(v)=\begin{cases}\beta(v), & v\in V,\\ \bot, & v\notin V,\end{cases}
--   $$
--   where $\bot$ records that $v$ does not occur in $c$.
--   2. **Support from the reading.** $\hat c(v)\neq\bot$ if and only if $v\in V$.
--   3. **Extensionality.** If two width-$k$ clauses $c,d$ satisfy $\hat c(v)=\hat d(v)$ for all $v\in[n]$, then $c=d$.
--
--   Thus a clause is the same thing as a sign pattern with exactly $k$ defined entries, and two clauses can be compared variable by variable. Item 3 is the tool for verifying identities between clauses, for instance that renaming the variables of a clause along a bijection and then along its inverse returns the original clause.
--
--   **Formalization Note** `clauseRead c v` has type `Option Bool`, with `none` playing the role of $\bot$. Extensionality is needed because a clause is a dependent pair (an element of a subtype of `Finset (Fin n)` together with a function on it), for which equality is not directly componentwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/RootDisintegration.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/RootDisintegration.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATSharpness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement

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

end RandomKSAT

end

end OAI


