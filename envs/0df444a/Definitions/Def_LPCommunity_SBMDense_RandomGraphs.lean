-- Prove2me | Definitions.Def_LPCommunity_SBMDense_RandomGraphs
-- name    : LPCommunity_SBMDense_RandomGraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:44.642873+00:00
-- url     : https://prove2.me/theorems/3d0295a9-4f8c-4c69-add6-9fe8bc9a64ba
-- title:
--   §4, pp. 13–14 — the graph-level laws of $\mathcal G_{n,p}$ and $\mathcal G_{n,p,q}$ (bisection marginalised out) and the dense scaling (20)
-- statement:
--   For an edge probability $p$, the **Erdős–Rényi model** $\mathcal G_{n,p}$ draws a graph on $V=\{1,\dots,n\}$ in which each of the $\binom n2$ pairs is an edge independently with probability $p$; the probability of a graph $G$ is
--
--   $$
--   \mathbb P_{\mathcal G_{n,p}}(G)=\prod_{1\le i<j\le n} p^{a_{ij}}(1-p)^{1-a_{ij}}.
--   $$
--
--   The **stochastic block model** $\mathcal G_{n,p,q}$, for an even number $n$ of nodes, first chooses a bisection $V_1,V_2$ of $V$ uniformly at random, then draws an edge between each pair $i,j$ on the same side with probability $p$ and between each pair $i\in V_1$, $j\in V_2$ with probability $q$, all edges independently. The **law of the graph alone** under $\mathcal G_{n,p,q}$ is the average, over the bisections, of the probability of $G$ given the bisection:
--
--   $$
--   \mathbb P_{\mathcal G_{n,p,q}}(G)=\frac{1}{\#\{\text{bisections}\}}\sum_{V_1}\ \prod_{1\le i<j\le n} r_{ij}^{a_{ij}}(1-r_{ij})^{1-a_{ij}},\qquad r_{ij}=\begin{cases}p & i,j\text{ on the same side},\\ q&\text{otherwise.}\end{cases}
--   $$
--
--   The **dense scaling** (20) is $p=\alpha n^{-\omega}$, $q=\beta n^{-\omega}$; for $\omega=0$ it is the very dense regime with constant $p=\alpha$, $q=\beta$.
--
--   These graph-level laws are the marginals of the coupling of Proposition 11; the dense scaling is the parameter family of Theorem 7 and Propositions 12, 14, 17, 18.
--
--   **Formalization Note** The edge-product weight `edgeWeight`, the bisections, and the event probabilities `erProb`, `sbmProb` come from the shared module `LPCommunity.SBMRecovery.Setting`; `sameSide` from `LPCommunity.MinBisect.Setting`. Each edge probability is clamped into $[0,1]$ there, because $\alpha n^{-\omega}$ can exceed $1$ for small $n$; for the parameters of this mission the clamp changes only finitely many $n$. Bisections are recorded by their side $V_1$, so $V_1$ and $V_1^{\mathrm c}$ are listed separately, which does not change the uniform law of the unordered partition; for odd $n$ there is no bisection and the SBM weight is $0$. The power $n^{-\omega}$ is the real power, with $n^{0}=1$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 13–14, §4 (ER model, SBM, (20)); p. 28, Proposition 11 (marginal laws)

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Setting

namespace LPCommunity.SBMDense

open Finset
open scoped Classical

/-- The probability of the graph `G` under the Erdős–Rényi law `G_{n,p}`, so that
`erProb n p E = ∑ G, erWeight n p G * [E G]`. -/
noncomputable def erWeight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  LPCommunity.SBMRecovery.edgeWeight G (fun _ _ => p)

/-- The probability of the graph `G` alone under the stochastic block model `G_{n,p,q}`, the
planted bisection being marginalised out: the average over the bisections `V1` of the
probability of `G` given `V1` (pairs on the same side have probability `p`, pairs across `q`). -/
noncomputable def sbmWeight (n : ℕ) (p q : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  (1 / ((LPCommunity.SBMRecovery.bisections n).card : ℝ)) *
    ∑ V1 ∈ LPCommunity.SBMRecovery.bisections n,
      LPCommunity.SBMRecovery.edgeWeight G
        (fun i j => if LPCommunity.MinBisect.sameSide V1 i j then p else q)

/-- The dense scaling (20): the edge probability `α n^{-ω}` on `n` nodes (real power; at `ω = 0`
this is the constant `α`). -/
noncomputable def denseRegime (α ω : ℝ) (n : ℕ) : ℝ := α * (n : ℝ) ^ (-ω)

end LPCommunity.SBMDense


