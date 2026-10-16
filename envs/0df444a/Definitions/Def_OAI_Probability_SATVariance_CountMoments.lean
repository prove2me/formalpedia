-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_CountMoments
-- name    : OAI_Probability_SATVariance_CountMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:35:48.531029+00:00
-- url     : https://prove2.me/theorems/ae75f546-a5e0-4803-a843-743a27854bfc
-- title:
--   Hit counts in random words and the moment constant for deletion rewards
-- statement:
--   Let $\alpha$ be a set, $M\in\mathbb N$ and $w=(w_0,\dots,w_{M-1})\in\alpha^M$ a word.
--
--   1. **Extension of a word.** If $\alpha$ is nonempty, $\bar w(i)=w_i$ for $i<M$ and $\bar w(i)=\alpha_0$ for $i\ge M$, where $\alpha_0$ is a fixed but arbitrary element of $\alpha$; this turns a finite word into an infinite sequence.
--   2. **Hit count.** For a predicate $p$ on $\alpha$, $N_p(w)=\#\{i<M:\ p(w_i)\}$.
--   3. **Hit probability.** For finite $\alpha$, $\pi(p)=\#\{x\in\alpha:p(x)\}/|\alpha|$, the probability that a uniformly random element of $\alpha$ satisfies $p$.
--   4. **Incidence and collision predicates.** A root datum $(t,c)$ consists of a root type $t:[k]\to\{\bot,\mathrm T,\mathrm F\}$ and a residual clause $c$ of length $k-|t|$ on $u$ Boolean variables, where $|t|=\#\{j:t(j)\ne\bot\}$. It is *incident* if $|t|\ne0$ and *colliding* if $|t|\ge2$.
--   5. **Moment constant.** For $k\in\mathbb N$ and $A,D\in\mathbb R$,
--   $$
--   \mathsf M_k(A,D)=48e\,(C_k+1)^2e^{(e-1)A}+4e^2(C_k+1)\,D\,e^{(e-1)A}+D^2,
--   $$
--   where $C_k=4(2K_k)^{1/(k-1)}$ is the lifetime constant and $K_k=\big(2^k(k-1)\big)^{k-1}$.
--
--   For a uniformly random word over a finite nonempty $\alpha$, $N_p$ is a binomial count with mean $M\pi(p)$ and $\mathbb E\,e^{N_p}\le e^{M(e-1)\pi(p)}$. Such bounds on counts of incident and colliding data, combined with the conditional second-moment estimate for the effect of deleting one clause, give the following: for $k=r+1$ with $2\le r$ and $r+1\le u$, if $M\pi(\text{incident})\le A$ and $M^2\pi(\text{colliding})\le D$, the mean square of the forced-reward sum over $M$ independent uniform root data is at most $\mathsf M_k(A,D)\,\lambda_k(M)$, where $\lambda_k(M)=1+\log(M+1)$ for $k=3$ and $\lambda_k(M)=1$ otherwise.
--
--   **Formalization Note** `extendWord` uses `Classical.choice` for the default element. `wordCount` and `hitProbability` are real numbers; `hitProbability` is the uniform average of an indicator and so is $0$ on an empty type. In `lifetimeC`, $k-1$ is natural-number subtraction and $1/0=0$ in $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/CountMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/CountMoments.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def extendWord.{u_1} {α : Type u_1} [Nonempty α] {M : ℕ} (w : Fin M → α) (i : ℕ) : α :=
  if h : i < M then w ⟨i,h⟩ else Classical.choice ‹Nonempty α›

def wordCount.{u_1} {α : Type u_1} {M : ℕ} (p : α → Prop) (w : Fin M → α) : ℝ :=
  ∑ i, if p (w i) then 1 else 0

def hitProbability.{u_1} {α : Type u_1} [Fintype α] (p : α → Prop) : ℝ :=
  favg (fun x => if p x then 1 else 0)

def rootIncident {u k : ℕ} (p : RootData u k) : Prop := rootSize p.1 ≠ 0

def rootCollision {u k : ℕ} (p : RootData u k) : Prop := 2 ≤ rootSize p.1

def deletionMomentC (k : ℕ) (A D : ℝ) : ℝ :=
  48*Real.exp 1*(lifetimeC k+1)^2*Real.exp ((Real.exp 1-1)*A) +
  4*(Real.exp 1)^2*(lifetimeC k+1)*D*Real.exp ((Real.exp 1-1)*A)+D^2

end RandomKSAT

end

end OAI


