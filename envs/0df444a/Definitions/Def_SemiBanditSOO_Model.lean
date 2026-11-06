-- Prove2me | Definitions.Def_SemiBanditSOO_Model
-- name    : SemiBanditSOO_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:59.113663+00:00
-- url     : https://prove2.me/theorems/2f0f3899-8681-4c0b-b601-486c9c91661a
-- title:
--   Stochastic online optimization on a decision tree: problems, policies, $f(\sigma\mid D)$ and $\mathrm{OPT}(D)$
-- statement:
--   There are $n$ coordinates; coordinate $i$ takes values in a known domain $\mathrm{dom}(i)\subseteq[0,1]$, and the coordinates $X_1,\dots,X_n$ are independent with distributions $D_1,\dots,D_n$; $D=\prod_iD_i$.
--
--   A **problem** is a finite rooted decision structure with root $r$ and children $\mathrm{ch}(u)$, with observation sets $\mathrm{obs}(u)\subseteq[n]$ (the coordinates observed on reaching $u$), feasible actions and leaf rewards. Every edge $(u,v)$ is either a *revelation edge*, which reveals one new coordinate $i\notin\mathrm{obs}(u)$ with $\mathrm{obs}(v)=\mathrm{obs}(u)\cup\{i\}$, or a *stopping edge*, which leads to a leaf with $\mathrm{obs}(v)=\mathrm{obs}(u)$. At a non-leaf node $u$ with observations $x_{\mathrm{obs}(u)}$ the feasible actions form a nonempty set $\mathcal A_u(x_{\mathrm{obs}(u)})\subseteq\mathrm{ch}(u)$, and a leaf $\ell$ has reward $f_\ell(x_{\mathrm{obs}(\ell)})\in[0,1]$. Rewards and feasibility are measurable.
--
--   A **deterministic policy** $\sigma$ chooses a feasible action $\sigma_u(x_{\mathrm{obs}(u)})\in\mathcal A_u(x_{\mathrm{obs}(u)})$ at every non-leaf node, measurably. For a realization $x$, $f(\sigma,x)$ is the reward of the leaf reached, and
--   $$f(\sigma\mid D)=\mathbb E_{X\sim D}[f(\sigma,X)],\qquad \mathrm{OPT}(D)=\sup_\sigma f(\sigma\mid D).$$
--
--   This is the model of the paper; it covers stochastic Boolean function evaluation, secretary and optimal-stopping problems, scheduling and overbooking.
--
--   **Formalization Note.** The decision structure is a finite rooted DAG (every node reachable from the root and a height function strictly decreasing along edges); footnote 1 (p.6) says the analysis applies to such DAGs, and trees are the special case. Observations are full vectors, and every quantity attached to node $u$ depends only on the coordinates in $\mathrm{obs}(u)$. Distributions are probability measures on the subtypes $\mathrm{dom}(i)$. The supremum defining $\mathrm{OPT}$ ranges over measurable deterministic policies; randomized policies, as averages of deterministic ones, give the same supremum. The leaf reached is the node after $\mathrm{height}(r)$ steps of the execution.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, §2.1, pp.6–7 and footnote 1, p.6

import Mathlib

open MeasureTheory

namespace SemiBanditSOO

/-- **Observation vectors** (§2.1, p.6). Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic
Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, §2.1, p.6.

Coordinate `i : Fin n` takes values in its domain `dom i ⊆ [0, 1]`; an observation vector assigns
a value of its domain to every coordinate.

**Formalization Note.** The paper carries the partial vector `x_obs(u) = (x_i)_{i ∈ obs(u)}`. Here
every quantity attached to a node `u` takes a full vector `x` and is required (or shown) to depend
only on the coordinates in `obs(u)` (`DependsOn`). Values live in the subtype `dom i`, with the
subspace σ-algebra, so no measurability of `dom i ⊆ ℝ` is assumed. -/
abbrev Obs {n : ℕ} (dom : Fin n → Set ℝ) : Type := (i : Fin n) → dom i

/-- `F` depends only on the coordinates in `S`: two vectors agreeing on `S` have the same image.
This encodes "`F` is a function of `x_S`" (§2.1, p.6). -/
def DependsOn {n : ℕ} {dom : Fin n → Set ℝ} {α : Type*} (S : Finset (Fin n))
    (F : Obs dom → α) : Prop :=
  ∀ x y : Obs dom, (∀ i ∈ S, x i = y i) → F x = F y

/-- **A problem** (§2.1, pp.6–7, and footnote 1, p.6). Harada, Kawase, Sumita, arXiv:2611.02739v1,
§2.1, pp.6–7.

A problem on `n` coordinates with domains `dom i ⊆ [0, 1]` consists of a finite rooted decision
structure on the node type `V` (root `root`, children `children u`), the observation sets
`obs u ⊆ [n]`, the feasible actions `feasible u x ⊆ children u` (nonempty at every non-leaf) and the
leaf rewards `reward ℓ x ∈ [0, 1]`. Every edge `u → v` is either a revelation edge, which reveals one
new coordinate `i ∉ obs u` with `obs v = obs u ∪ {i}` (`edgeCoord u v = some i`), or a stopping edge,
which leads to a leaf with `obs v = obs u` (`edgeCoord u v = none`). Feasibility and rewards depend
only on the observed coordinates and are measurable (p.7).

**Formalization Note.**
* The decision structure is a finite rooted directed acyclic graph: every node is reachable from
  the root, and `height` strictly decreases along every edge (this is acyclicity). A tree is the
  special case with unique parents; footnote 1 (p.6) states that the analysis applies to such
  DAGs, because `obs` is a function of the node (all root paths to a node reveal the same
  coordinates). A leaf is a node without children.
* `edgeCoord` labels each edge by the coordinate it reveals; its values off the edges are unused.
* Rewards are only constrained at leaves; `reward` at a non-leaf node is never used. -/
structure Problem (n : ℕ) (dom : Fin n → Set ℝ) (V : Type) where
  /-- Every domain is a subset of `[0, 1]`. -/
  dom_subset : ∀ i, dom i ⊆ Set.Icc 0 1
  /-- The root `r`. -/
  root : V
  /-- The children `ch(u)`. -/
  children : V → Finset V
  /-- The observation sets `obs(u) ⊆ [n]`. -/
  obs : V → Finset (Fin n)
  /-- The coordinate revealed by an edge (`none` for a stopping edge). -/
  edgeCoord : V → V → Option (Fin n)
  reveal_spec : ∀ u, ∀ v ∈ children u, ∀ i, edgeCoord u v = some i →
    i ∉ obs u ∧ obs v = insert i (obs u)
  stop_spec : ∀ u, ∀ v ∈ children u, edgeCoord u v = none →
    obs v = obs u ∧ children v = ∅
  /-- A height function strictly decreasing along edges (acyclicity). -/
  height : V → ℕ
  height_lt : ∀ u, ∀ v ∈ children u, height v < height u
  /-- Every node is reachable from the root. -/
  reachable : ∀ u, Relation.ReflTransGen (fun a b => b ∈ children a) root u
  /-- The feasible actions `𝒜_u(x_obs(u))`. -/
  feasible : V → Obs dom → Finset V
  feasible_subset : ∀ u x, feasible u x ⊆ children u
  feasible_nonempty : ∀ u x, children u ≠ ∅ → (feasible u x).Nonempty
  feasible_dependsOn : ∀ u, DependsOn (obs u) (feasible u)
  feasible_measurable : ∀ u v, MeasurableSet {x : Obs dom | v ∈ feasible u x}
  /-- The leaf rewards `f_ℓ(x_obs(ℓ))`. -/
  reward : V → Obs dom → ℝ
  reward_mem : ∀ u, children u = ∅ → ∀ x, reward u x ∈ Set.Icc (0 : ℝ) 1
  reward_dependsOn : ∀ u, children u = ∅ → DependsOn (obs u) (reward u)
  reward_measurable : ∀ u, children u = ∅ → Measurable (reward u)

namespace Problem

variable {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V)

open Classical in
/-- One step of the execution of a selection rule `σ` on the vector `x`: stay at a leaf,
otherwise move to `σ u x`. -/
noncomputable def step (σ : V → Obs dom → V) (x : Obs dom) (u : V) : V :=
  if Pb.children u = ∅ then u else σ u x

/-- The node reached after `k` steps of the execution of `σ` on `x`, started at the root. -/
noncomputable def reach (σ : V → Obs dom → V) (x : Obs dom) (k : ℕ) : V :=
  (Pb.step σ x)^[k] Pb.root

/-- The node at which the execution of `σ` on `x` ends: the node reached after `height root` steps.
Since `height` strictly decreases along edges, every root path has at most `height root` edges, so
for a policy (`IsPolicy`) this node is the leaf `ℓ` reached by `σ` on `x`. -/
noncomputable def leafOf (σ : V → Obs dom → V) (x : Obs dom) : V :=
  Pb.reach σ x (Pb.height Pb.root)

/-- The reward `f(σ, x)` of the deterministic rule `σ` on the realization `x` (§2.1, p.7). -/
noncomputable def payoff (σ : V → Obs dom → V) (x : Obs dom) : ℝ :=
  Pb.reward (Pb.leafOf σ x) x

/-- **Deterministic policies** (§2.1, p.7): at every non-leaf node `u`, `σ u x ∈ 𝒜_u(x_obs(u))`;
`σ u` depends only on `x_obs(u)`; and `σ` is measurable. -/
structure IsPolicy (σ : V → Obs dom → V) : Prop where
  mem_feasible : ∀ u x, Pb.children u ≠ ∅ → σ u x ∈ Pb.feasible u x
  dependsOn : ∀ u, DependsOn (Pb.obs u) (σ u)
  measurable : ∀ u v, MeasurableSet {x : Obs dom | σ u x = v}

end Problem

/-- The product distribution `D = ∏ᵢ Dᵢ` on observation vectors (§2.1, p.6). -/
noncomputable def prodDist {n : ℕ} {dom : Fin n → Set ℝ} (D : ∀ i, ProbabilityMeasure (dom i)) :
    Measure (Obs dom) :=
  Measure.pi fun i => (D i : Measure (dom i))

namespace Problem

variable {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V)

/-- `f(σ | D) = 𝔼_{X∼D}[f(σ, X)]` (§2.1, p.7). -/
noncomputable def value (D : ∀ i, ProbabilityMeasure (dom i)) (σ : V → Obs dom → V) : ℝ :=
  ∫ x, Pb.payoff σ x ∂(prodDist D)

/-- **The benchmark** `OPT(D) = sup_σ f(σ | D)` (§2.1, p.7).

**Formalization Note.** The supremum ranges over measurable deterministic policies (`IsPolicy`).
The paper's supremum also ranges over randomized policies (distributions over deterministic ones);
their values are averages of deterministic values, so the supremum is the same. -/
noncomputable def OPT (D : ∀ i, ProbabilityMeasure (dom i)) : ℝ :=
  sSup ((fun σ => Pb.value D σ) '' {σ | Pb.IsPolicy σ})

end Problem

end SemiBanditSOO


