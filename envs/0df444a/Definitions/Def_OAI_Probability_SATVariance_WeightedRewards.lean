-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
-- name    : OAI_Probability_SATVariance_WeightedRewards
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:34:14.237871+00:00
-- url     : https://prove2.me/theorems/f54c893b-3f0a-4e10-8675-33a6a1ab1fc8
-- title:
--   Incidence and collision sets of root data, the deletion weight, and the logarithmic duration factor
-- statement:
--   Let $u,k,M\in\mathbb N$. A root datum is a pair $p=(t,c)$ of a root type $t:[k]\to\{\bot,\mathrm T,\mathrm F\}$ and a residual clause $c$ of length $k-|t|$ on $u$ Boolean variables, where $|t|=\#\{j:t(j)\ne\bot\}$ is the number of root variables the datum touches (a clause being a set of distinct variables with a sign for each). Let $(p_i)_{i<M}=\big((t_i,c_i)\big)_{i<M}$ be a word of root data.
--
--   1. **Incident and collision indices.**
--   $$
--   \mathcal I=\{i<M:\ |t_i|\ne0\},\qquad \mathcal V=\{i<M:\ |t_i|\ge2\}.
--   $$
--   An incident datum meets the root variables, a colliding one meets at least two of them.
--   2. **Deletion weight.** For $k,d\in\mathbb N$,
--   $$
--   Q_k(d)=(C_k+1)\,d^{\beta_k},\qquad \beta_k=\frac k{k-1},\quad C_k=4\big(2K_k\big)^{1/(k-1)},\quad K_k=\big(2^k(k-1)\big)^{k-1}.
--   $$
--   3. **Duration factor.**
--   $$
--   \lambda_k(M)=\begin{cases}1+\log(M+1)&\text{if } k=3,\\1&\text{if } k\ne3.\end{cases}
--   $$
--
--   These quantities organize the second-moment bound for the effect of deleting one clause on the first unsatisfiability time of random $k$-SAT. With $k=r+1$, $2\le r$, $r+1\le u$, $Z=|\mathcal I|$, $V=|\mathcal V|$ and $Q=Q_k(\max(1,Z))$, the mean square over the refresh noise of the forced-reward sum along the root data is at most $8Q^2\lambda_k(M)+2MQV+M^2V(V-1)$. The factor $\lambda_3$ produces the logarithm in the $k=3$ variance bound, and $Q_k(\max(1,Z))\le(C_k+1)(1+Z)^2$ for $k\ge3$.
--
--   **Formalization Note** In `lifetimeBeta` and `lifetimeC`, $k-1$ is natural-number subtraction and the reciprocal is taken in $\mathbb R$ with $1/0=0$; $d^{\beta_k}$ is the real power. `incidentSet` and `collisionSet` are `Finset (Fin M)`, and the logarithm in `durationLog` is the natural logarithm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/WeightedRewards.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/WeightedRewards.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def incidentSet {u k M : ℕ} (env : Fin M → RootData u k) : Finset (Fin M) :=
  Finset.univ.filter fun i => rootSize (env i).1 ≠ 0

def collisionSet {u k M : ℕ} (env : Fin M → RootData u k) : Finset (Fin M) :=
  Finset.univ.filter fun i => 2 ≤ rootSize (env i).1

def deletionQ (k d : ℕ) : ℝ := (lifetimeC k+1)*(d : ℝ)^(lifetimeBeta k)

def durationLog (k M : ℕ) : ℝ := if k = 3 then 1+Real.log (M+1) else 1

end RandomKSAT

end

end OAI


