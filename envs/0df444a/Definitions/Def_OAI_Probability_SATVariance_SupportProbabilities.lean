-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities
-- name    : OAI_Probability_SATVariance_SupportProbabilities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:15:55.876547+00:00
-- url     : https://prove2.me/theorems/a75b3637-06ea-4c88-b080-38231c39dbe0
-- title:
--   Renaming the variables of a clause along a bijection
-- statement:
--   Let $n,m,k\in\mathbb N$ and let $e:[n]\to[m]$ be a bijection between the variable sets $[n]=\{0,\dots,n-1\}$ and $[m]=\{0,\dots,m-1\}$. A clause of width $k$ on $[n]$ is a pair $c=(V,\beta)$ with $V\subseteq[n]$, $|V|=k$, and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; its reading $\hat c:[n]\to\{\mathrm T,\mathrm F,\bot\}$ equals $\beta(v)$ for $v\in V$ and $\bot$ for $v\notin V$.
--
--   1. **Renamed clause.** The renaming of $c$ along $e$ is the width-$k$ clause on $[m]$
--   $$
--   e_*c=\big(e(V),\ w\mapsto\beta(e^{-1}(w))\big),
--   $$
--   obtained by moving every literal of $c$ along $e$.
--   2. **Reading of a renamed clause.** For every $w\in[m]$, $\widehat{e_*c}(w)=\hat c\big(e^{-1}(w)\big)$.
--   3. **Renaming bijection.** The map $c\mapsto e_*c$ is a bijection from the width-$k$ clauses on $[n]$ onto the width-$k$ clauses on $[m]$, with inverse $d\mapsto(e^{-1})_*d$.
--
--   Taking $m=n$, item 3 says that every permutation of the variables permutes the clauses of a given width, so the uniform distribution on clauses is invariant under relabelling of the variables. This symmetry is what makes all variables equally likely to occur in a uniformly random clause.
--
--   **Formalization Note** The bijection $e$ is an `Equiv` between `Fin n` and `Fin m`; `renameClauseEquiv e` packages `renameClause e` and `renameClause e.symm` as an `Equiv`, and its inverse laws are checked with clause extensionality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/SupportProbabilities.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/SupportProbabilities.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATSharpness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def renameClause {n m k : ℕ} (e : Fin n ≃ Fin m) (c : Clause n k) : Clause m k :=
  ⟨⟨c.1.1.map e.toEmbedding, by simpa using c.1.2⟩,
    fun v => c.2 ⟨e.symm v, by simpa using v.property⟩⟩

lemma read_renameClause {n m k : ℕ} (e : Fin n ≃ Fin m) (c : Clause n k) (v : Fin m) :
    clauseRead (renameClause e c) v = clauseRead c (e.symm v) := by
  by_cases h : e.symm v ∈ c.1.1 <;> simp [clauseRead, renameClause, h]

def renameClauseEquiv {n m k : ℕ} (e : Fin n ≃ Fin m) : Clause n k ≃ Clause m k where
  toFun := renameClause e
  invFun := renameClause e.symm
  left_inv c := by apply clause_ext; intro v; simp only [read_renameClause, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv c := by apply clause_ext; intro v; simp only [read_renameClause, Equiv.symm_symm, Equiv.apply_symm_apply]

end RandomKSAT

end

end OAI


