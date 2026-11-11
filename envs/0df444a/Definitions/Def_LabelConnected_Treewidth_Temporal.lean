-- Prove2me | Definitions.Def_LabelConnected_Treewidth_Temporal
-- name    : LabelConnected_Treewidth_Temporal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:27:15.881079+00:00
-- url     : https://prove2.me/theorems/b11a38fa-6998-4952-8eff-a34a37203bd2
-- title:
--   Temporal labelings, strict temporal paths, temporal connectivity and Gossiping (label-connected multigraphs)
-- statement:
--   A **temporal labeling** of a multigraph $G = (V, E)$ assigns one positive integer $\lambda(e)$ to each edge $e$; different edges may receive equal labels. A **strict temporal path** from $u$ to $w$ is a path $u = v_0, e_1, v_1, \dots, e_\ell, v_\ell = w$ (no repeated vertex; $\ell = 0$ is allowed when $u = w$) whose labels strictly increase,
--   $$\lambda(e_1) < \lambda(e_2) < \cdots < \lambda(e_\ell).$$
--   The temporal graph $(G, \lambda)$ is **temporally connected** if a strict temporal path exists from $u$ to $w$ for every ordered pair $(u, w)$ of vertices; a graph with at most one vertex is temporally connected. **Gossiping** asks whether some labeling makes $(G, \lambda)$ temporally connected; a yes-instance is called **label-connected**.
--
--   Equal labels never chain: two edges with the same label cannot both lie on one strict temporal path.
--
--   **Formalization Note.** Labels are `ℕ`-valued with `0 < lab e` (`IsTemporalLabeling`); `HasStrictTemporalPath`, `TemporallyConnected`, `IsLabelConnected`.
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), §1, p. 2, Gossiping; §2, p. 6, Temporal Connectivity

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph

open Classical

namespace LabelConnected.Treewidth

/-! # Temporal labelings, strict temporal paths, temporal connectivity and Gossiping

Klasing, Mertzios, Molter, Morawietz, Spirakis, *Recognizing Label-Connected Graphs*,
arXiv:2611.05144 (PDF sha256 8dde27a5…), §2, p. 6, "Temporal Connectivity.": "A temporal labeling
of a multigraph G = (V, E) is a function λ: E → N assigning one positive integer to each edge. A
strict temporal path traverses edges e1, . . . , eℓ with λ(e1) < · · · < λ(eℓ). The temporal graph
(G, λ) is temporally connected if a strict temporal path exists from u to v for every ordered pair
u, v ∈ V. Paths of length zero are allowed, so a graph with at most one vertex is temporally
connected." §1, p. 2: "Gossiping. Input: An undirected multigraph G = (V, E). Question: Is there a
labeling λ: E → N such that (G, λ) is temporally connected? […] we call a multigraph
label-connected if it is a yes-instance of Gossiping."

**Formalization Note.** Labels are natural numbers, and a temporal labeling requires every label to
be at least `1`. A strict temporal path from `u` to `w` is a path (no repeated vertex, length `0`
allowed) `v₀ = u, …, v_ℓ = w` with edges `e₁, …, e_ℓ`, `eᵢ` joining `v_{i−1}` and `vᵢ`, and strictly
increasing labels. -/

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- `lab` is a **temporal labeling**: one positive integer per edge (equal labels allowed). -/
def IsTemporalLabeling (lab : E → ℕ) : Prop := ∀ e, 0 < lab e

/-- A **strict temporal path** from `u` to `w` under `lab`: vertices `v 0 = u, …, v ℓ = w`, pairwise
distinct, edges `e i` joining `v i` and `v (i + 1)`, labels strictly increasing along the path. -/
def HasStrictTemporalPath (ends : E → Fin n × Fin n) (lab : E → ℕ) (u w : Fin n) : Prop :=
  ∃ (ℓ : ℕ) (v : Fin (ℓ + 1) → Fin n) (e : Fin ℓ → E),
    Function.Injective v ∧ v 0 = u ∧ v (Fin.last ℓ) = w ∧
    (∀ i : Fin ℓ, Joins ends (e i) (v i.castSucc) (v i.succ)) ∧
    StrictMono fun i => lab (e i)

/-- `(G, λ)` is **temporally connected**: a strict temporal path from `u` to `w` for every ordered
pair `(u, w)`. -/
def TemporallyConnected (ends : E → Fin n × Fin n) (lab : E → ℕ) : Prop :=
  ∀ u w : Fin n, HasStrictTemporalPath ends lab u w

/-- `G` is **label-connected**, i.e. a yes-instance of **Gossiping**: some temporal labeling makes
`(G, λ)` temporally connected. -/
def IsLabelConnected (ends : E → Fin n × Fin n) : Prop :=
  ∃ lab : E → ℕ, IsTemporalLabeling lab ∧ TemporallyConnected ends lab

end LabelConnected.Treewidth


