-- Prove2me | Definitions.Def_STCSublinear1377_Main_Supplement_Terminal
-- name    : STCSublinear1377_Main_Supplement_Terminal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:18:54.007296+00:00
-- url     : https://prove2.me/theorems/95913def-bcef-4c97-834a-c748c7149524
-- title:
--   Terminal partitions, maximum and total boundary, and the connected multiway-cut optimum
-- statement:
--   Let $F$ be a finite weighted graph and $\Gamma\subseteq V(F)$ a set of $t$ prescribed terminals. A **one-terminal partition** assigns to every vertex $v$ a terminal $\lambda(v)\in\Gamma$, with $\lambda(s)=s$ for each $s\in\Gamma$; its parts $A_s=\{v:\lambda(v)=s\}$ partition $V(F)$ and each contains exactly one terminal. The parts need not be connected. The partition is **connected** if every part induces a connected subgraph. With $b_F(A)$ the total weight of edges leaving $A$, put
--
--   $$B(\lambda)=\max_{s\in\Gamma} b_F(A_s),\qquad S(\lambda)=\sum_{s\in\Gamma} b_F(A_s),\qquad \mathrm{OPT}(F,\Gamma)=\min_{\lambda\ \text{connected}} B(\lambda).$$
--
--   $\mathrm{OPT}$ is the optimum of the min-max connected multiway cut problem of §1 (p.3). A labelling is encoded by listing, in name order, the binary label of every vertex.
--
--   **Formalization Note** Partitions are labellings `Fin n → Fin n`; the minimum is attained over the finite set of labellings and is explicitly zero when no connected one-terminal partition exists (never the case when every connected component contains a terminal). The maximum over an empty terminal set is zero.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, §1 Min-max connected multiway cut (p.3) and Theorem B.1 (p.19), PDF/printed pp.3, 19

import Definitions.Def_STCSublinear1377_Main_DataMachine
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- A one-terminal partition of the vertex set, given by labels: every vertex is labelled by one
prescribed terminal and every terminal by itself. Parts may be disconnected. -/
def IsTerminalLabeling {n : ℕ} (f : WeightedGraph n) (terms : Finset (Fin n))
    (lab : Fin n → Fin n) : Prop :=
  terms ⊆ f.vertices ∧ (∀ v ∈ f.vertices, lab v ∈ terms) ∧ ∀ s ∈ terms, lab s = s

/-- The part of the terminal (or label) `s`. -/
noncomputable def part {n : ℕ} (f : WeightedGraph n) (lab : Fin n → Fin n)
    (s : Fin n) : Finset (Fin n) := by
  classical
  exact f.vertices.filter (fun v => lab v = s)

/-- A connected one-terminal partition: every part induces a connected subgraph. -/
def IsConnectedLabeling {n : ℕ} (f : WeightedGraph n) (terms : Finset (Fin n))
    (lab : Fin n → Fin n) : Prop :=
  IsTerminalLabeling f terms lab ∧ ∀ s ∈ terms, f.connectedSet (part f lab s)

/-- Maximum boundary of the parts (zero for an empty terminal set). -/
noncomputable def maxBoundary {n : ℕ} (f : WeightedGraph n) (terms : Finset (Fin n))
    (lab : Fin n → Fin n) : ℝ :=
  terms.fold max 0 (fun s => f.boundary (part f lab s))

/-- Total boundary `S` of the parts. -/
noncomputable def sumBoundary {n : ℕ} (f : WeightedGraph n) (terms : Finset (Fin n))
    (lab : Fin n → Fin n) : ℝ :=
  ∑ s ∈ terms, f.boundary (part f lab s)

/-- The min-max connected multiway cut optimum: an attained minimum over the finite set of
connected one-terminal partitions; explicitly zero when there is none. -/
noncomputable def opt {n : ℕ} (f : WeightedGraph n) (terms : Finset (Fin n)) : ℝ := by
  classical
  let values := ((Finset.univ : Finset (Fin n → Fin n)).filter
    (IsConnectedLabeling f terms)).image (maxBoundary f terms)
  exact if h : values.Nonempty then values.min' h else 0

/-- Binary encoding of a labelling: the label of every vertex in name order. -/
def labelBits {n : ℕ} (lab : Fin n → Fin n) : List Bool :=
  (List.finRange n).flatMap (fun v => natBits (lab v).val)

end STCSublinear1377.Main.Supplement


