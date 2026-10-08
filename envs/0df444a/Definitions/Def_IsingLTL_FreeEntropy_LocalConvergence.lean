-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_LocalConvergence
-- name    : IsingLTL_FreeEntropy_LocalConvergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:16.587996+00:00
-- url     : https://prove2.me/theorems/7287e5b6-3b36-4a00-bcc6-2b225ca058fe
-- title:
--   Balls $B_i(t)$, rooted isomorphism $\simeq$, local convergence to $T(P,\rho,\infty)$ and uniform sparsity (Definitions 2.1, 2.2)
-- statement:
--   Let $G_n=(V_n=[n],E_n)$ be a sequence of graphs. For $i\in V_n$, the **ball** $B_i(t)$ is the subgraph of $G_n$ induced by the vertices at graph distance at most $t$ from $i$, rooted at $i$, and $|\partial i|$ is the degree of $i$. Two rooted graphs are **isomorphic**, $T_1\simeq T_2$, when a graph isomorphism maps the root of one to the root of the other (for trees this is the paper's identification after breadth-first relabeling).
--
--   **Definition 2.1 (local convergence).** Let $\mathbb P_n$ be the law of the ball $B_i(t)$ around a uniformly random vertex $i\in[n]$. The sequence $\{G_n\}$ **converges locally** to $T(P,\rho,\infty)$ if for every $t$ and every rooted tree $T$ with $t$ generations
--   $$\lim_{n\to\infty}\mathbb P_n\{B_i(t)\simeq T\}=\mathbb P\{T(P,\rho,t)\simeq T\}.$$
--
--   **Definition 2.2 (uniform sparsity).** The sequence $\{G_n\}$ is **uniformly sparse** if
--   $$\lim_{l\to\infty}\limsup_{n\to\infty}\frac1n\sum_{i\in V_n}|\partial i|\,\mathbb I(|\partial i|\ge l)=0.$$
--
--   These are the hypotheses on the graph sequence in Theorem 2.4 and Lemma 6.4.
--
--   **Formalization Note** $G_n$ is a graph on `Fin n`. Distances are extended-valued, so unreachable vertices are not in any ball. The rooted trees with $t$ generations are represented by the trees $T(t)$ of all offspring functions. The averages in (2.4) are computed in $[0,\infty]$, so the $\limsup$ of an unbounded sequence is $\infty$ and not a junk value.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 4, Definition 2.1 (2.3), Definition 2.2 (2.4), and the definitions of $B_i(t)$ and $\simeq$

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_UlamHarrisTree
import Definitions.Def_IsingLTL_FreeEntropy_DegreeDist

namespace IsingLTL.FreeEntropy

open MeasureTheory Filter Topology

/-- **Rooted isomorphism** `T₁ ≃ T₂` (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*,
arXiv:0804.4726v3, p. 4: two trees are identified "when vertices are relabeled from 1 to
`|T₁| = |T₂|`, in a breadth first fashion, and following lexicographic order among siblings"):
there is a graph isomorphism `G ≃g H` mapping the root `r` to the root `s`.

Formalization Note: the paper's canonical relabeling identifies rooted trees up to
root-preserving isomorphism (siblings unordered); this is that relation, stated for arbitrary
rooted graphs (a ball `B_i(t)` that is not a tree is isomorphic to no tree). -/
def RootedIso {V W : Type*} (G : SimpleGraph V) (r : V) (H : SimpleGraph W) (s : W) : Prop :=
  ∃ e : G ≃g H, e r = s

/-- The vertex set of the ball `B_i(t)` (p. 4): the vertices at graph distance at most `t` from
`i`. Unreachable vertices have extended distance `⊤` and are excluded. -/
noncomputable def ballSet {V : Type*} [Fintype V] (G : SimpleGraph V) (i : V) (t : ℕ) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun j => G.edist i j ≤ t)

theorem mem_ballSet_self {V : Type*} [Fintype V] (G : SimpleGraph V) (i : V) (t : ℕ) :
    i ∈ (ballSet G i t : Set V) := by
  classical
  simp [ballSet]

/-- The ball `B_i(t)` as the subgraph of `G` induced by the vertices at distance `≤ t` from `i`
(p. 4), rooted at `i` (`ballRoot`). -/
abbrev ballGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (i : V) (t : ℕ) :=
  G.induce (ballSet G i t : Set V)

/-- The root `i` of the ball `B_i(t)`. -/
def ballRoot {V : Type*} [Fintype V] (G : SimpleGraph V) (i : V) (t : ℕ) :
    (ballSet G i t : Set V) :=
  ⟨i, mem_ballSet_self G i t⟩

theorem nil_mem_ballTree (ω : List ℕ → ℕ) (t : ℕ) : [] ∈ (ballTree ω t : Set (List ℕ)) := by
  simp only [Finset.mem_coe, ballTree, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨0, Nat.succ_pos t, by simp [gen]⟩

/-- The rooted tree `T(t)` of the first `t` generations of the tree with offspring function `ω`,
as a graph (rooted at `ø = []`, `treeRoot`). -/
abbrev treeBallGraph (ω : List ℕ → ℕ) (t : ℕ) :=
  treeGraph.induce (ballTree ω t : Set (List ℕ))

/-- The root `ø = []` of `T(t)`. -/
def treeRoot (ω : List ℕ → ℕ) (t : ℕ) : (ballTree ω t : Set (List ℕ)) :=
  ⟨[], nil_mem_ballTree ω t⟩

/-- **Local convergence** (Definition 2.1, p. 4). A sequence of graphs `G_n` on `[n]`
converges locally to `T(P, ρ, ∞)` if for every `t` and every rooted tree `T` with `t`
generations,
`lim_{n→∞} P_n{B_i(t) ≃ T} = P{T(P, ρ, t) ≃ T}` (2.3),
where `P_n` is the law of the ball `B_i(t)` around a uniformly random vertex `i ∈ [n]`, so
`P_n{B_i(t) ≃ T} = #{i : B_i(t) ≃ T} / n`.

Formalization Note: `G_n` is a graph on `Fin n`. The rooted trees with (at most) `t` generations
are exactly, up to rooted isomorphism, the trees `T(t)` of offspring functions `τ`, so the
condition is quantified over all `τ : List ℕ → ℕ`. The probability on the right is the
`gwTree` measure of the event (a function of finitely many offspring numbers). -/
def ConvergesLocally (G : ∀ n : ℕ, SimpleGraph (Fin n)) (D : DegreeDist) : Prop :=
  ∀ (t : ℕ) (τ : List ℕ → ℕ),
    Tendsto
      (fun n : ℕ =>
        (Nat.card {i : Fin n //
          RootedIso (ballGraph (G n) i t) (ballRoot (G n) i t) (treeBallGraph τ t) (treeRoot τ t)} : ℝ)
          / n)
      atTop
      (𝓝 (D.gwTree {ω | RootedIso (treeBallGraph ω t) (treeRoot ω t)
        (treeBallGraph τ t) (treeRoot τ t)}).toReal)

/-- **Uniform sparsity** (Definition 2.2, p. 4):
`lim_{l→∞} limsup_{n→∞} (1/n) ∑_{i ∈ V_n} |∂i| 𝕀(|∂i| ≥ l) = 0` (2.4).

Formalization Note: the averages are computed in `ℝ≥0∞`, so the `limsup` is the true one (an
unbounded sequence has `limsup = ∞`, not the junk value `0` of a real `limsup`). -/
def UniformlySparse (G : ∀ n : ℕ, SimpleGraph (Fin n)) [∀ n, DecidableRel (G n).Adj] : Prop :=
  Tendsto
    (fun l : ℕ => limsup
      (fun n : ℕ => (n : ENNReal)⁻¹ *
        ∑ i : Fin n, if l ≤ (G n).degree i then ((G n).degree i : ENNReal) else 0)
      atTop)
    atTop (𝓝 0)

end IsingLTL.FreeEntropy


