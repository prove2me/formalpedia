-- Prove2me | Definitions.Def_TwoConnSS_Structured
-- name    : TwoConnSS_Structured
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:56.869105+00:00
-- url     : https://prove2.me/theorems/b012127e-8d89-4c0a-a46e-55a3927e8c88
-- title:
--   $(\alpha,\eta)$-structured graphs
-- statement:
--   Let $\alpha, \eta > 0$. A graph $G$ is **$(\alpha, \eta)$-structured** if:
--
--   1. $G$ is 2-vertex-connected and has at least $8/\eta$ vertices;
--   2. no edge $uv$ is **irrelevant**, i.e. $\{u, v\}$ is never a vertex cut;
--   3. there is no **non-isolating 2-vertex cut** (a 2-vertex cut whose deletion does not leave exactly two components, one of them a single vertex);
--   4. every $\alpha$-contractible subgraph has more than $8/\eta$ vertices;
--   5. no 3-vertex cut has a side partition with both sides of size at least $\lceil 2/(\alpha - 1)\rceil - 1$, and no 4-vertex cut has one with both sides of size at least $\lceil 6/(\alpha-1)\rceil - 1$.
--
--   For $11/9 \le \alpha < 5/4$ the cut thresholds are $8$ and at most $26$. The reduction of Lemma 8.2 allows the approximation algorithms to assume these properties.
--
--   **Formalization Note** This is the list of properties the paper records for the structured graphs of [20, Definition 1]; [20] may impose further conditions, which only shrink its class.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1, pp.31–32 (Definition 8.1)

import Mathlib
import Definitions.Def_TwoConnSS_HasThreeMatching
import Definitions.Def_TwoConnSS_IsContractible

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- The 2-vertex cut `{u, v}` is isolating (p.31): deleting it leaves exactly two components, one a
single vertex `w`. -/
def IsIsolatingCut (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ w, w ≠ u ∧ w ≠ v ∧ (∀ x, G.Adj w x → x = u ∨ x = v) ∧
    (G.induce ({u, v, w} : Set V)ᶜ).Connected

/-- `{u, v}` is a non-isolating 2-vertex cut (p.31). -/
def IsNonIsolatingTwoCut (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ IsVertexCut G {u, v} ∧ ¬ IsIsolatingCut G u v

/-- `T` is a `k`-vertex cut with a side partition whose two sides both have at least `t`
vertices (Definition 8.1, p.31). -/
def IsLargeCut (G : SimpleGraph V) (k t : ℕ) (T : Finset V) : Prop :=
  T.card = k ∧ ∃ U W, IsSidePartition G T U W ∧ t ≤ U.card ∧ t ≤ W.card

/-- The size threshold `⌈2/(α − 1)⌉ − 1` of the excluded 3-vertex cuts (p.32). -/
noncomputable def thr3 (α : ℝ) : ℕ := ⌈2 / (α - 1)⌉₊ - 1

/-- The size threshold `⌈6/(α − 1)⌉ − 1` of the excluded 4-vertex cuts (p.32). -/
noncomputable def thr4 (α : ℝ) : ℕ := ⌈6 / (α - 1)⌉₊ - 1

/-- **(α, η)-structured graph.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1, p.32: "the structured graphs
supplied by this reduction are simple and 2VC, have at least 8/η vertices, and exclude irrelevant
edges, non-isolating 2-vertex cuts, α-contractible subgraphs on at most 8/η vertices (Definition
6.8), and the large 3- and 4-vertex cuts defined above; see [20, Definition 1]"; p.31: "An edge uv
is irrelevant if {u, v} is a vertex cut"; p.32: "Preprocessing excludes these separators. In the
stated range of α, its size thresholds are ⌈2/(α − 1)⌉ − 1 = 8 for 3-vertex cuts and
⌈6/(α − 1)⌉ − 1 ≤ 26 for 4-vertex cuts."

`Structured α η G` says: `G` is 2VC; `|V| ≥ 8/η`; no edge `uv` has `{u, v}` a vertex cut; no
non-isolating 2-vertex cut; every α-contractible subgraph has more than `8/η` vertices; no 3-vertex
cut with both sides of size at least `⌈2/(α − 1)⌉ − 1`; no 4-vertex cut with both sides of size at
least `⌈6/(α − 1)⌉ − 1`.

**Formalization Note.** Simplicity is built into `SimpleGraph`. The class is the p.32 list (the
paper's reading of [20, Definition 1], which may impose further conditions; those only shrink
[20]'s class). The cut thresholds are the preprocessing thresholds written on p.32; for
`11/9 ≤ α < 5/4` they are `8` and at most `26`, so every excluded cut of Definition 8.1 is excluded
here. -/
def Structured (α η : ℝ) (G : SimpleGraph V) : Prop :=
  IsTwoVC G ∧ 8 / η ≤ (Fintype.card V : ℝ) ∧
  (∀ u v, G.Adj u v → ¬ IsVertexCut G {u, v}) ∧
  (∀ u v, ¬ IsNonIsolatingTwoCut G u v) ∧
  (∀ X EH, IsContractible G α X EH → 8 / η < (X.card : ℝ)) ∧
  (∀ T, ¬ IsLargeCut G 3 (thr3 α) T) ∧ (∀ T, ¬ IsLargeCut G 4 (thr4 α) T)

end TwoConnSS


