-- Prove2me | Definitions.Def_DiaconisStroock_OddPaths_Iota
-- name    : DiaconisStroock_OddPaths_Iota
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:05:58.253706+00:00
-- url     : https://prove2.me/theorems/013d45a6-0027-4cef-bd7c-8b1d61adbb10
-- title:
--   §1C, p. 40 — the smallest eigenvalue β_min, systems Σ of odd closed paths, and ι(Σ) of (1.7)
-- statement:
--   Let $P$ be a transition matrix on a finite set $X$, $\pi$ a stationary distribution, and $Q(x,y)=\pi(x)P(x,y)$. Three objects of §1C are defined.
--
--   1. The **smallest eigenvalue** $\beta_{\min}=\beta_{m-1}$ of $P$, defined as the infimum of the real numbers $\beta$ for which $P\varphi=\beta\varphi$ has a nonzero real solution $\varphi$. For a stochastic $P$ on a nonempty finite state space this is a finite nonempty set contained in $[-1,1]$, so the infimum is the least eigenvalue.
--   2. An **odd closed path** at $x$: a walk $\sigma_x$ from $x$ back to $x$ along edges with $Q>0$ (self-loops allowed), with an odd number of edges, which traverses no directed edge twice. A **system of odd paths** $\Sigma=(\sigma_x)_{x\in X}$ chooses one such path for every $x$.
--   3. The geometric quantity (1.7),
--   $$
--   \iota=\iota(\Sigma)=\max_e\sum_{\sigma_x\ni e}|\sigma_x|_Q\,\pi(x),
--   $$
--   where the maximum runs over the directed edges $e$ of the graph (ordered pairs with $Q(e)>0$, self-loops included), the sum runs over the points $x$ whose path $\sigma_x$ traverses $e$, and $|\sigma_x|_Q=\sum_{e\in\sigma_x}Q(e)^{-1}$ is the length (1.4).
--
--   $\iota$ measures how much weight the odd paths load onto a single edge; Proposition 2 bounds $\beta_{\min}$ from below by $-1+2/\iota$.
--
--   **Formalization Note** The paper defines $|\sigma_x|_Q$ "by analogy with (1.4)", whose paths may not repeat an edge. §1C's graph has directed edges ("an edge from $x$ to $y$ if $Q(x,y)>0$"), and the rule is read for directed edges: an edge may be traversed once in each direction. Under the unordered-edge reading a vertex of degree one has no odd closed path, contradicting the page's "Such paths always exist for irreducible aperiodic chains". The maximum over edges is a real supremum over a finite index set; it equals $0$ when the chain has no edge, which a system of odd paths on a nonempty set excludes. $\beta_{\min}$ has Lean's default value $0$ when $P$ has no real eigenvalue, as can occur for an empty state space or a nonstochastic real matrix; the mission's Markov-chain hypotheses exclude this case.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 36, §1A (eigenvalues β_0 > β_1 ≥ ⋯ ≥ β_{m−1}); p. 40, §1C and (1.7), https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_Poincare_Paths

namespace DiaconisStroock.OddPaths

open MarkovMixing

/-- The smallest eigenvalue `β_min = β_{m-1}` of `P` (Diaconis and Stroock, Geometric bounds for
eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1A, p. 36, and §1C, p. 40): the
infimum of the real eigenvalues of `P`. For a stochastic `P` on a nonempty finite set this set is
finite, nonempty (it contains `1`) and bounded below by `-1`, so the infimum is the minimum. -/
noncomputable def betaMin {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) : ℝ :=
  sInf {β : ℝ | IsEigenvalue P β}

/-- `p` is an odd closed path at `x` in the graph of §1C (p. 40): a walk from `x` to `x` along edges
with `Q(z, w) > 0` (self-loops `(z, z)` with `Q(z, z) > 0` included), with an odd number of edges,
in which no directed edge `(z, w)` is traversed twice. The graph of §1C has "an edge from `x` to `y`
if `Q(x, y) > 0`"; §1B's rule "a given edge appears at most once in a given path" is read for these
directed edges. -/
def IsOddPath {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ) (x : V)
    (p : List V) : Prop :=
  DiaconisStroock.Poincare.IsWalk P π x x p ∧ (DiaconisStroock.Poincare.pathEdges p).Nodup ∧ Odd (DiaconisStroock.Poincare.pathEdges p).length

/-- A system `Σ = (σ_x)_{x ∈ X}` of odd closed paths, one for each `x` (§1C, p. 40). -/
def IsOddPathSystem {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (S : V → List V) : Prop :=
  ∀ x : V, IsOddPath P π x (S x)

/-- The geometric quantity (1.7), p. 40: `ι(Σ) = max_e ∑_{σ_x ∋ e} |σ_x|_Q π(x)`, the maximum over
directed edges `e = (e⁻, e⁺)` with `Q(e) > 0` of the sum over the points `x` whose path `σ_x`
traverses `e`. -/
noncomputable def iota {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (S : V → List V) : ℝ :=
  ⨆ e : {e : V × V // 0 < edgeMeasure P π e.1 e.2},
    ∑ x, if e.1 ∈ DiaconisStroock.Poincare.pathEdges (S x) then DiaconisStroock.Poincare.qLength P π (S x) * π x else 0

end DiaconisStroock.OddPaths


