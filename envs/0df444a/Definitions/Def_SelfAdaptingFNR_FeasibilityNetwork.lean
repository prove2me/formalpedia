-- Prove2me | Definitions.Def_SelfAdaptingFNR_FeasibilityNetwork
-- name    : SelfAdaptingFNR_FeasibilityNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:53.134012+00:00
-- url     : https://prove2.me/theorems/272fc19a-76de-4874-84b8-ec2357f6f6c2
-- title:
--   Layered networks, their paths, and feasibility networks of $\mathscr F_t$
-- statement:
--   A **layered network** $\mathcal N_t=(\mathcal V_t,\mathcal E_t)$ for period $t$ of a WDP has $J+1$ finite layers $\mathcal V_{t,1},\dots,\mathcal V_{t,J+1}$, where the first layer consists of a single root. An arc $(v_j,s_j,a_j,v_{j+1})$ goes from a node $v_j\in\mathcal V_{t,j}$ to a node $v_{j+1}\in\mathcal V_{t,j+1}$ and is labelled by a component state–action pair $(s_j,a_j)$ with $s_j\in\mathcal S_{t,j}$, $a_j\in\mathcal A_{t,j}(s_j)$; a node–state–action triple $(v_j,s_j,a_j)$ carries at most one arc.
--
--   A **path** is a sequence of $J$ arcs $((v_j,s_j,a_j,v_{j+1}),\ j\in\mathcal J)$ that starts at the root (layer 1) and ends in layer $J+1$; $\mathcal P_t$ is the (finite) set of paths. A path represents the WDP state–action pair $(s,a)=((s_1,\dots,s_J),(a_1,\dots,a_J))$ formed by its labels.
--
--   $\mathcal N_t$ is a **feasibility network** of $\mathscr F_t$ when its paths represent the feasible state–action pairs and vice versa: the map sending a path to its pair is a bijection from $\mathcal P_t$ onto $\mathscr F_t$.
--
--   Feasibility networks encode the linking constraints exactly; the slack network and the minimal network of the paper are examples, and the relaxation FNR is built on any of them.
--
--   **Formalization Note** Layers are `Fin (J+1)`, 0-based; the arcs of component $j$ go from layer `j.castSucc` to layer `j.succ`. Arcs are a partial successor map $(j,v,s_j,a_j)\mapsto v'$ (an `Option`), reflecting p.17's "each node-state-action triple is unique". The single root is the paper's $|\mathcal V_{t,1}|=1$ (p.ec8). A path is recorded by its nodes and labels.
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §1, p.3 (feasibility network); §3.1, p.12 (layers, arcs, paths $\mathcal P_t$); §4.1, pp.16–17 (node–state–action triples); EC.4, Lemma EC.2, p.ec8 (single root)

import Mathlib
import Definitions.Def_SelfAdaptingFNR_WDP

open scoped Classical

namespace SelfAdaptingFNR

variable {J K T : ℕ}

/-- A **layered network for period `t`** of a WDP (Nadarajah & Cire, *Self-Adapting Network
Relaxations for Weakly Coupled MDPs*, SSRN 4081430, Aug. 2023, §3.1, p.12, and §4.1, pp.16–17):
`J + 1` finite layers `𝒱_{t,1}, …, 𝒱_{t,J+1}`, a single root forming the first layer, and arcs
`(vⱼ, sⱼ, aⱼ, vⱼ₊₁)` from layer `j` to layer `j + 1`, each labelled by a component state–action
pair `(sⱼ, aⱼ)` with `aⱼ ∈ 𝒜_{t,j}(sⱼ)`.

**Formalization Note.** Layers are indexed by `Fin (J + 1)` (the paper's layer `j` is the index
`+ 1`); the arcs of component `j : Fin J` go from layer `j.castSucc` to layer `j.succ`. Arcs are
given by the partial successor map `succ j v s a : Option (V j.succ)`: a node–state–action triple
`(v, sⱼ, aⱼ)` carries at most one arc, as p.17 states ("each node-state-action triple is unique"),
and the FNR variables `y_{t,j}(v, sⱼ, aⱼ)` are indexed by such triples. The single root is the
paper's `|𝒱_{t,1}| = 1` (p.ec8). -/
structure LayeredNetwork (M : WDP J K T) (t : ℕ) where
  /-- The node layers `𝒱_{t,1}, …, 𝒱_{t,J+1}`. -/
  V : Fin (J + 1) → Type
  instFintypeV : ∀ i, Fintype (V i)
  /-- The root, the unique node of the first layer. -/
  root : V 0
  root_unique : ∀ v : V 0, v = root
  /-- `succ j v s a = some v'` iff `(v, s, a, v')` is an arc of component `j`. -/
  succ : (j : Fin J) → V j.castSucc → M.S t j → M.Act t j → Option (V j.succ)
  /-- Arc labels are component-feasible state–action pairs. -/
  succ_feasible : ∀ (j : Fin J) (v : V j.castSucc) (s : M.S t j) (a : M.Act t j) (v' : V j.succ),
    succ j v s a = some v' → a ∈ M.A t j s

attribute [instance] LayeredNetwork.instFintypeV

/-- A **path** of a layered network: a sequence of `J` arcs `((vⱼ, sⱼ, aⱼ, vⱼ₊₁), j ∈ 𝒥)` starting
at the root (layer 1) and ending at layer `J + 1` (p.12). It is recorded by its nodes
`node i` (one per layer) and its labels `(st j, act j)`. -/
def LayeredNetwork.Path {M : WDP J K T} {t : ℕ} (N : LayeredNetwork M t) : Type :=
  {q : ((i : Fin (J + 1)) → N.V i) × ((j : Fin J) → M.S t j) × ((j : Fin J) → M.Act t j) //
    q.1 0 = N.root ∧ ∀ j : Fin J, N.succ j (q.1 j.castSucc) (q.2.1 j) (q.2.2 j) = some (q.1 j.succ)}

noncomputable instance LayeredNetwork.instFintypePath {M : WDP J K T} {t : ℕ}
    (N : LayeredNetwork M t) : Fintype N.Path := by
  unfold LayeredNetwork.Path; infer_instance

/-- The nodes of a path, one per layer. -/
def LayeredNetwork.Path.node {M : WDP J K T} {t : ℕ} {N : LayeredNetwork M t} (p : N.Path) :
    (i : Fin (J + 1)) → N.V i := p.1.1

/-- The component states of a path's labels. -/
def LayeredNetwork.Path.st {M : WDP J K T} {t : ℕ} {N : LayeredNetwork M t} (p : N.Path) :
    (j : Fin J) → M.S t j := p.1.2.1

/-- The component actions of a path's labels. -/
def LayeredNetwork.Path.act {M : WDP J K T} {t : ℕ} {N : LayeredNetwork M t} (p : N.Path) :
    (j : Fin J) → M.Act t j := p.1.2.2

/-- The **state–action pair represented by a path**: the sequence of its arc labels
`((s₁,a₁), …, (s_J,a_J))`, read as the WDP pair `(s, a)`. -/
def LayeredNetwork.Path.labels {M : WDP J K T} {t : ℕ} {N : LayeredNetwork M t} (p : N.Path) :
    ((j : Fin J) → M.S t j) × ((j : Fin J) → M.Act t j) := (p.st, p.act)

/-- **Feasibility network of `𝓕_t`** (pp.3, 12, 16): a layered network whose paths represent the
feasible state–action pairs of the WDP and vice versa (p.3: "each of its paths represents a
feasible state–action pair of the WDP and vice versa"), i.e. the map sending a path to its labels
is a bijection from the path set `𝒫_t` onto `𝓕_t`. -/
def LayeredNetwork.IsFeasibilityNetwork {M : WDP J K T} {t : ℕ} (N : LayeredNetwork M t) : Prop :=
  Function.Injective (fun p : N.Path => p.labels) ∧
    Set.range (fun p : N.Path => p.labels) = M.feasiblePairs t

end SelfAdaptingFNR


