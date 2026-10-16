-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
-- name    : OAI_Probability_SATVariance_SupportProbabilities__SATVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:38:14.277993+00:00
-- url     : https://prove2.me/theorems/67e1b5cc-5596-4e0f-9ae5-e0d4a2a4a7fe
-- title:
--   Renaming clause variables, overlaps with a fixed variable set, and the root variables of a split
-- statement:
--   A $k$-clause on $n$ Boolean variables is a pair $c=(s,\sigma)$ of a $k$-element set $s=\operatorname{supp}c\subseteq[n]=\{0,\dots,n-1\}$ and signs $\sigma:s\to\{\mathrm T,\mathrm F\}$. Its reading $\operatorname{read}_c(v)$ is $\sigma(v)$ for $v\in s$ and $\bot$ (absent) otherwise.
--
--   1. **Renaming.** For a bijection $e:[n]\to[m]$, the renamed clause $e_*c$ is the $k$-clause on $m$ variables with support $e(s)$ and sign $\sigma\big(e^{-1}(v)\big)$ at $v\in e(s)$; equivalently $\operatorname{read}_{e_*c}(v)=\operatorname{read}_c\big(e^{-1}(v)\big)$ for all $v\in[m]$. Renaming along $e$ and along $e^{-1}$ are mutually inverse, so $c\mapsto e_*c$ is a bijection between the $k$-clauses on $n$ variables and those on $m$ variables.
--   2. **Overlap.** For $R\subseteq[n]$, $\operatorname{ov}_R(c)=|R\cap\operatorname{supp}c|$.
--   3. **Root variables.** For a bijection $e:[k]\sqcup[u]\to[n]$, the root variables are $\operatorname{Root}(e)=\{e(j):\ j\in[k]\}$, the images of the first summand; this set has exactly $k$ elements.
--
--   Renaming shows that the uniform law on clauses is invariant under permutations of the variables, so the probability that the support of a uniformly random $k$-clause contains a given variable, or a given pair of distinct variables, does not depend on the choice. This leads to the estimates
--   $$
--   n\,\mathbb P\big[\operatorname{ov}_R(c)\ne0\big]\le|R|\,k,\qquad n^2\,\mathbb P\big[\operatorname{ov}_R(c)\ge2\big]\le2|R|^2k^2
--   $$
--   for a uniformly random $k$-clause $c$, valid for $k\le n$ (and, for the second, also $k\ge1$ and $n\ge2$). With $R=\operatorname{Root}(e)$, the overlap of a merged clause is the number of root positions it uses, so the probabilities that a uniformly random root datum is incident or colliding are at most $k^2/n$ and $2k^4/n^2$. For $M\le Bn$ clauses this feeds the second-moment bound for the effect of deleting one clause on the first unsatisfiability time.
--
--   **Formalization Note** `renameClause` maps the support along the embedding given by `e` and reads signs through `e.symm`; `read_renameClause` is the reading formula and `renameClauseEquiv` the bijection of item 1. `clauseOverlap` is a natural number and `rootVariables` a `Finset (Fin n)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/SupportProbabilities.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/SupportProbabilities.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments

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

def clauseOverlap {n k : ℕ} (R : Finset (Fin n)) (c : Clause n k) : ℕ :=
  (R ∩ c.1.1).card

def rootVariables {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) : Finset (Fin n) :=
  Finset.univ.image (fun j => e (Sum.inl j))

end RandomKSAT

end

end OAI


