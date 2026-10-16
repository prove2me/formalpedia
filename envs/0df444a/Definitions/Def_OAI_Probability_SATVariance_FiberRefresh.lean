-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
-- name    : OAI_Probability_SATVariance_FiberRefresh
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:30:10.376069+00:00
-- url     : https://prove2.me/theorems/02f0ddc3-2c5d-46e9-b2e8-b35814267e60
-- title:
--   Refreshing the residual part of a split clause, path rewards, and uniform-noise Markov operators
-- statement:
--   Assignments on $m$ Boolean variables are maps $[m]\to\{\mathrm T,\mathrm F\}$, $[m]=\{0,\dots,m-1\}$, and $\mathcal C_{u,s}$ is the set of $s$-clauses on $u$ variables (sets of $s$ distinct variables with a sign for each). A root type of width $k$ is a map $t:[k]\to\{\bot,\mathrm T,\mathrm F\}$ with size $|t|=\#\{j:t(j)\ne\bot\}$, and a root assignment $a:[k]\to\{\mathrm T,\mathrm F\}$ root-satisfies $t$ if $t(j)=a(j)$ for some $j$. A $k$-clause split along $k$ root variables is described by a root type $t$ together with a residual clause in $\mathcal C_{u,k-|t|}$.
--
--   1. **Refresh noise.** $\mathcal Z_{u,k}=\mathcal C_{u,k}\times(\mathcal C_{u,k-1})^{[k]}$. A noise value $z=(z_1,z_2)$ consists of one fresh $k$-clause $z_1$ and, for each root position $j\in[k]$, a fresh $(k-1)$-clause $z_2(j)$.
--   2. **True root.** If $a$ root-satisfies $t$, then $j^*(t,a)$ denotes a chosen position $j$ with $t(j)=a(j)$.
--   3. **Refreshing the residual part.** For a root type $t$, a root assignment $a$, a residual clause $c\in\mathcal C_{u,k-|t|}$ and noise $z=(z_1,z_2)$,
--   $$
--   \operatorname{refresh}(t,a,c,z)=\begin{cases} z_1 & \text{if } |t|=0,\\ z_2\big(j^*(t,a)\big) & \text{if } |t|=1 \text{ and } a \text{ root-satisfies } t,\\ c & \text{otherwise.}\end{cases}
--   $$
--   The residual part is thus resampled exactly when the clause has no root variable, or has a single root literal that $a$ satisfies; in the latter case the residual part is irrelevant for assignments whose root part is $a$.
--   4. **Path reward.** Let $X$ be a set, $\alpha$ a set of noise values, $\mathrm{step}_i:\alpha\times X\to X$ for $i\ge0$, and $f:X\to\mathbb R$. For a noise word $z=(z_0,\dots,z_{m-1})\in\alpha^m$ and $x\in X$,
--   $$
--   \operatorname{PR}_m(z,x)=\sum_{i=0}^{m-1}f(x_i),\qquad x_0=x,\quad x_{i+1}=\mathrm{step}_i(z_i,x_i).
--   $$
--   5. **Uniform-noise operator.** For finite $\alpha$, $(U_if)(x)=\frac1{|\alpha|}\sum_{z\in\alpha}f\big(\mathrm{step}_i(z,x)\big)$, the transition operator of applying $\mathrm{step}_i$ with uniformly random noise.
--
--   For $k\le u$, refreshing preserves the uniform law: averaging a function of $\operatorname{refresh}(t,a,c,z)$ over a uniform residual clause $c$ and uniform noise $z$ gives its average over a uniform residual clause. The average of the path reward over a uniform noise word equals the cumulative reward $\sum_{i<m}U_0\cdots U_{i-1}f$ of the operators $U_i$, and the mean square of path rewards can be controlled through a potential function. Together these allow the clauses surrounding a deleted clause to be partially resampled without changing their joint law, which turns the effect of the deletion on the first unsatisfiability time into the reward of an explicit Markov evolution.
--
--   **Formalization Note** `clauseCastEquiv` identifies $s$-clauses with $t$-clauses when $s=t$; it is needed because the residual length $k-|t|$ is part of the type, and `refreshPart` uses it to view $z_1$ and $z_2(j)$ as clauses of length $k-0$ and $k-1$. `trueRoot` is defined by choice; when $|t|=1$ the chosen position is the unique root position. `RefreshNoise u k` is the product type of item 1.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiberRefresh.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiberRefresh.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def clauseCastEquiv {u s t : ℕ} (h : s = t) : Clause u s ≃ Clause u t :=
  Equiv.cast (congrArg (Clause u) h)

abbrev RefreshNoise (u k : ℕ) := Clause u k × (Fin k → Clause u (k-1))

def trueRoot {k : ℕ} (t : RootType k) (a : Assignment k) (h : RootSatisfies t a) : Fin k :=
  h.choose

def refreshPart {u k : ℕ} (t : RootType k) (a : Assignment k)
    (c : Clause u (k-rootSize t)) (z : RefreshNoise u k) : Clause u (k-rootSize t) :=
  if h : rootSize t = 0 then clauseCastEquiv (by omega) z.1
  else if h' : rootSize t = 1 ∧ RootSatisfies t a then
    clauseCastEquiv (by omega) (z.2 (trueRoot t a h'.2))
  else c

def pathReward.{u_1, u_2} {X : Type u_1} {α : Type u_2} (step : ℕ → α → X → X) (f : X → ℝ) :
    (m : ℕ) → (Fin m → α) → X → ℝ
  | 0, _, _ => 0
  | m+1, z, x => f x + pathReward (fun i => step (i+1)) f m (Fin.tail z) (step 0 (z 0) x)

def uniformStep.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] (step : ℕ → α → X → X)
    (i : ℕ) (f : X → ℝ) (x : X) : ℝ := favg (fun a => f (step i a x))

end RandomKSAT

end

end OAI


