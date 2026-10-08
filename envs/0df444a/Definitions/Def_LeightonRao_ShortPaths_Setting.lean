-- Prove2me | Definitions.Def_LeightonRao_ShortPaths_Setting
-- name    : LeightonRao_ShortPaths_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:51.355401+00:00
-- url     : https://prove2.me/theorems/da002b2c-8e8a-4032-9d03-a427053a48d5
-- title:
--   §2.2 and §2.5 — short-path flow, restricted distance, capacity and radius
-- statement:
--   Let $N$ be a finite undirected capacitated network. Its **total capacity** is $C=\sum_{e}C(e)$, and $C_{\max}$ is the largest sum of capacities incident to one vertex. A **distance function** assigns a nonnegative symmetric length $d(u,v)$ to each pair; its **total weight** is $W=\sum_e C(e)d(e)$. The length of a walk is the sum of its edge lengths.
--
--   For a real hop budget $B$, let $d_B(u,v)$ be the infimum of the $d$-lengths of walks from $u$ to $v$ using at most $B$ edges. If no such walk exists, $d_B(u,v)=\infty$. For a vertex set $T$, $d_B(T,u)=\inf_{t\in T}d_B(t,u)$. The restricted uniform dual constraint is
--
--   $$\frac12\sum_{u,v\in V}d_L(u,v)\ge 1.$$
--
--   A **short concurrent flow** routes a common fraction $\lambda$ of every commodity using at most $L$ edges per path, with joint undirected edge loads no greater than capacity. Its maximum is the supremum of feasible nonnegative $\lambda$. A component has **edge radius** at most $\rho_e$ and **distance radius** at most $\rho_d$ if each vertex can be reached from one center by a walk inside the component satisfying both bounds at once. The capacity crossing a partition counts each edge between distinct components once.
--
--   **Formalization Note** The short flow is represented by nonnegative arc flow indexed by commodity and hop. Flow enters at hop zero, is conserved at later hops, stops at its destination and vanishes after hop $L$; this is equivalent to a nonnegative path flow supported on walks of at most $L$ edges. Restricted distances use extended nonnegative reals, preserving the paper's infinite value when no allowed walk exists. The maximum is bounded and attainable for the positive-demand uniform problem on a finite network.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 796, 808–809, §2.2, §2.5, Eqs. (4)–(5), Theorem 18, Lemmas 19 and 21

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Network

namespace LeightonRao.ShortPaths

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def totalCap (N : Network V) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, N.C u v

/-- Largest total capacity incident to one vertex. The empty-type default is irrelevant to results. -/
noncomputable def cmax (N : Network V) : ℝ :=
  sSup (Set.range fun v : V => ∑ u, N.C v u)

def IsDistanceFunction (d : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ d u v) ∧ (∀ u v, d u v = d v u)

noncomputable def totalWeight (N : Network V) (d : V → V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, N.C u v * d u v

def walkLen {N : Network V} (d : V → V → ℝ) {u v : V} (p : N.graph.Walk u v) : ℝ :=
  (p.darts.map fun a => d a.fst a.snd).sum

/-- Infimum of lengths of walks using at most `B` edges. An empty walk family gives `⊤`. -/
noncomputable def distL (N : Network V) (d : V → V → ℝ) (B : ℝ) (u v : V) : ENNReal :=
  ⨅ (p : N.graph.Walk u v) (_ : (p.length : ℝ) ≤ B), ENNReal.ofReal (walkLen d p)

noncomputable def distFromL (N : Network V) (d : V → V → ℝ) (B : ℝ)
    (T : Finset V) (u : V) : ENNReal :=
  ⨅ t ∈ T, distL N d B t u

def SatisfiesShortConstraint (N : Network V) (d : V → V → ℝ) (L : ℕ) : Prop :=
  1 ≤ (1 / 2 : ENNReal) * ∑ u, ∑ v, distL N d (L : ℝ) u v

/-- One walk within the component witnesses both the hop radius and the distance radius. -/
def HasRadii (N : Network V) (d : V → V → ℝ) (S : Finset V) (ρe ρd : ℝ) : Prop :=
  ∃ c ∈ S, ∀ y ∈ S, ∃ p : N.graph.Walk c y,
    (∀ x ∈ p.support, x ∈ S) ∧ (p.length : ℝ) ≤ ρe ∧ walkLen d p ≤ ρd

noncomputable def crossCap (N : Network V) (P : Finpartition (Finset.univ : Finset V)) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, if P.part u = P.part v then 0 else N.C u v

/-- Hop-indexed concurrent flow. `f s t h i j` is commodity `s,t` on `i → j` at hop `h+1`.
The equations inject flow at hop zero, conserve it at each later hop, absorb it at the sink,
and forbid flow after hop `L`; hence every routed path has at most `L` edges. -/
def IsShortConcurrentFlow (N : Network V) (D : V → V → ℝ) (L : ℕ)
    (f : V → V → ℕ → V → V → ℝ) (lam : ℝ) : Prop :=
  (∀ s t h i j, 0 ≤ f s t h i j) ∧
  (∀ s t h i j, L ≤ h → f s t h i j = 0) ∧
  (∀ s h i j, f s s h i j = 0) ∧
  (∀ s t, s ≠ t → ∀ v, ∑ j, f s t 0 v j = if v = s then lam * D s t else 0) ∧
  (∀ s t h, s ≠ t → h + 1 < L → ∀ v,
    ∑ j, f s t (h + 1) v j = if v = t then 0 else ∑ i, f s t h i v) ∧
  (∀ s t h, s ≠ t → h < L → ∑ j, f s t h t j = 0) ∧
  (∀ s t h, s ≠ t → h + 1 = L → ∀ v, v ≠ t → ∑ i, f s t h i v = 0) ∧
  (∀ s t, s ≠ t → ∑ h ∈ Finset.range L, ∑ i, f s t h i t = lam * D s t) ∧
  (∀ i j, ∑ s, ∑ t, ∑ h ∈ Finset.range L,
    (f s t h i j + f s t h j i) ≤ N.C i j)

/-- Concurrent short-path max-flow, as a supremum of feasible values. -/
noncomputable def maxShortFlow (N : Network V) (D : V → V → ℝ) (L : ℕ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsShortConcurrentFlow N D L f lam}

end LeightonRao.ShortPaths


