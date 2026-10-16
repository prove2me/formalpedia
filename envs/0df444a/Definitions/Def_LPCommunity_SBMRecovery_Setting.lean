-- Prove2me | Definitions.Def_LPCommunity_SBMRecovery_Setting
-- name    : LPCommunity_SBMRecovery_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:11.752459+00:00
-- url     : https://prove2.me/theorems/02594d7f-161a-44e0-b869-eb0ec372c4d3
-- title:
--   §4, pp. 13–14 — the Erdős–Rényi law G_{n,p} and the stochastic block model G_{n,p,q} as finite probability laws on graphs
-- statement:
--   Let $V=\{1,\dots,n\}$ and let $G$ range over the simple graphs on $V$.
--
--   1. **Independent edges.** Given a number $r_{ij}$ for each pair $i<j$, the probability of the graph $G$ when each pair $\{i,j\}$ is an edge independently with probability $r_{ij}$ is
--   $$w_r(G)=\prod_{1\le i<j\le n}\begin{cases} r_{ij} & \text{if } \{i,j\}\in E(G),\\ 1-r_{ij} & \text{otherwise.}\end{cases}$$
--   2. **Erdős–Rényi law.** $G_{n,p}$ draws every pair as an edge independently with probability $p$; for an event $A$ on graphs, $\mathbb P_{G\sim G_{n,p}}[A]=\sum_G w_p(G)\,\mathbf 1_A(G)$.
--   3. **Stochastic block model.** For even $n$, $G_{n,p,q}$ first chooses a bisection $V_1,V_2$ of $V$ uniformly at random, then draws each pair with both ends in $V_1$ or both in $V_2$ as an edge with probability $p$, and each pair with one end in each set with probability $q$, all independently. For an event $A$ that may depend on the planted bisection and on the graph,
--   $$\mathbb P_{G\sim G_{n,p,q}}[A]=\frac{1}{\#\{\text{bisections}\}}\sum_{V_1}\ \sum_G w^{V_1}_{p,q}(G)\,\mathbf 1_A(V_1,G),$$
--   where $w^{V_1}_{p,q}$ uses $r_{ij}=p$ when $i,j$ are on the same side of $V_1$ and $r_{ij}=q$ otherwise.
--
--   These laws are the probabilistic setting of §4: statements such as "the LP relaxation recovers the planted bisection with high probability" are limits of these probabilities as $n\to\infty$ (Theorems 6–8 and the propositions they use).
--
--   **Formalization Note** Vertices are `Fin n` (0-based); a bisection is recorded by its side $V_1$ with $2|V_1|=n$ (companion definition of §2). Each edge probability is clamped into $[0,1]$ (`max 0 (min 1 p)`), so the laws are probability laws for every real parameter; this is the identity on $[0,1]$ and matters only for small $n$, where parameters such as $\alpha n^{-\omega}$ or $\alpha\log n/n$ may exceed $1$. The SBM law carries no assumption $p>q$ (the paper's standing assumption of §4 is stated in each theorem that uses it), because some results apply it with $p=0$. For odd $n$ there is no bisection and the formula gives $0$; the SBM is only used for even $n$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 13–14, §4 (the ER model G_{n,p}; the SBM G_{n,p,q}: uniformly random bisection, then independent edges with probabilities p inside and q across)

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_MinBisect_Setting

open Finset
open scoped Classical

namespace LPCommunity.SBMRecovery

/-! §4 of Del Pia, Khajavirad, Kunisky, *Linear Programming and Community Detection*
(arXiv:2006.03213v2): the random-graph laws of pp. 13–14, the Erdős–Rényi law `G_{n,p}` and the
stochastic block model `G_{n,p,q}` (a uniformly random bisection, then independent edges).
Bisections and `sameSide` come from `LPCommunity.MinBisect`; the metric relaxation (LP-P) and LP
recovery from `LPCommunity.LPRecovery`. Vertices are `Fin n` (the paper's {1,…,n}, shifted to
0-based). -/

/-- A real number clamped into `[0, 1]`, used as an edge probability. -/
noncomputable def clamp01 (p : ℝ) : ℝ := max 0 (min 1 p)

/-- The unordered pairs `{i, j}` of `Fin n`, listed as `(i, j)` with `i < j`. -/
noncomputable def pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter fun p : Fin n × Fin n => p.1 < p.2

/-- Probability of the graph `G` when each pair `{i, j}` (`i < j`) is an edge independently with
probability `r i j` (clamped into `[0, 1]`). -/
noncomputable def edgeWeight {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) : ℝ :=
  ∏ p ∈ pairs n, if G.Adj p.1 p.2 then clamp01 (r p.1 p.2) else 1 - clamp01 (r p.1 p.2)

/-- `ℙ_{G ∼ G_{n,p}}[E(G)]`: the probability of the event `E` under the Erdős–Rényi law `G_{n,p}`
(every pair is an edge independently with probability `p`). -/
noncomputable def erProb (n : ℕ) (p : ℝ) (E : SimpleGraph (Fin n) → Prop) : ℝ :=
  ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if E G then 1 else 0)

/-- The bisections of `Fin n`, each recorded by its side `V1`. -/
noncomputable def bisections (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter fun S : Finset (Fin n) => LPCommunity.MinBisect.IsBisection n S

/-- `ℙ_{G ∼ G_{n,p,q}}[E(V1, G)]` (p. 13): choose a bisection `V1, V1ᶜ` uniformly at random, then
draw each pair inside a side with probability `p` and each pair across with probability `q`,
independently. The event may depend on the drawn planted side `V1` and on the graph `G`. -/
noncomputable def sbmProb (n : ℕ) (p q : ℝ) (E : Finset (Fin n) → SimpleGraph (Fin n) → Prop) : ℝ :=
  (1 / ((bisections n).card : ℝ)) *
    ∑ V1 ∈ bisections n, ∑ G : SimpleGraph (Fin n),
      edgeWeight G (fun i j => if LPCommunity.MinBisect.sameSide V1 i j then p else q) * (if E V1 G then 1 else 0)

end LPCommunity.SBMRecovery


