-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
-- name    : OAI_Probability_SATVariance_FiniteVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:25:52.752971+00:00
-- url     : https://prove2.me/theorems/b36de120-ed3d-4291-b498-caa2ead679ef
-- title:
--   Uniform variance and truncated satisfiability times of a clause word, with one clause omitted
-- statement:
--   For a real function $f$ on a finite set $A$ write $\operatorname{avg}_A f=\frac1{|A|}\sum_{x\in A}f(x)$. A $k$-clause on $n$ Boolean variables is a set of $k$ distinct variables in $[n]=\{0,\dots,n-1\}$ with a sign $\mathrm T$ or $\mathrm F$ for each; an assignment $a:[n]\to\{\mathrm T,\mathrm F\}$ satisfies it if it agrees with at least one of these signs. Let $L\in\mathbb N$ and let $\mathbf c=(c_0,\dots,c_{L-1})$ be a word of $k$-clauses.
--
--   1. **Uniform variance.** $\operatorname{Var}_A f=\operatorname{avg}_A(f^2)-(\operatorname{avg}_A f)^2$, the variance of $f(X)$ for $X$ uniform on $A$.
--   2. **Prefix satisfiability.** $\mathrm{SAT}(\mathbf c,m)$ holds when some assignment satisfies every $c_j$ with $j<m$ (for $m\ge L$ this means the whole word).
--   3. **Truncated failure time.**
--   $$
--   \tau(\mathbf c)=\#\big\{m\in\{0,\dots,L-1\}:\ \mathrm{SAT}(\mathbf c,m)\big\}.
--   $$
--   Since satisfiability of prefixes is inherited by shorter prefixes, $\tau(\mathbf c)=\min(F,L)$, where $F$ is the length of the shortest unsatisfiable prefix ($F=\infty$ if the whole word is satisfiable).
--   4. **Time with clause $i$ omitted.** For $i\in\{0,\dots,L-1\}$,
--   $$
--   \tau_{-i}(\mathbf c)=\#\big\{m\in\{0,\dots,L-1\}:\ \text{some assignment satisfies every } c_j \text{ with } j<m,\ j\ne i\big\}.
--   $$
--   It does not depend on the clause $c_i$.
--
--   Take $L=\lfloor Bn\rfloor$ for a real $B$ and let $\mathbf c$ consist of the first $L$ clauses of a stream of independent uniformly random $k$-clauses; then $\tau(\mathbf c)$ is the first unsatisfiability time truncated at $\lfloor Bn\rfloor$. These definitions express an Efron-Stein type bound: for $k\le n$, the variance of the truncated time is at most $\sum_{i<L}\mathbb E\big[(\tau_{-i}(\mathbf c)-\tau(\mathbf c))^2\big]$. This reduces the variance upper bound to controlling the effect of deleting a single clause.
--
--   **Formalization Note** `fvariance` is defined through `favg`, which divides by the cardinality and so returns $0$ on an empty type. `finiteTime` and `omittedTime` are real-valued sums over `Fin L` of indicator values of the corresponding satisfiability statements.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiniteVariance.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiniteVariance.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def fvariance.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ) : ℝ :=
  favg (fun a => (f a)^2) - (favg f)^2

def finiteSAT {n k L : ℕ} (cs : Fin L → Clause n k) (m : ℕ) : Prop :=
  ∃ a : Assignment n, ∀ j : Fin L, j.val < m → Satisfies (cs j) a

def finiteTime {n k L : ℕ} (cs : Fin L → Clause n k) : ℝ :=
  ∑ m : Fin L, if finiteSAT cs m.val then 1 else 0

def omittedTime {n k L : ℕ} (i : Fin L) (cs : Fin L → Clause n k) : ℝ :=
  ∑ m : Fin L, if (∃ a : Assignment n,
    ∀ j : Fin L, j.val < m.val → j ≠ i → Satisfies (cs j) a) then 1 else 0

end RandomKSAT

end

end OAI


