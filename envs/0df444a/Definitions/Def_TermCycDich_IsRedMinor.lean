-- Prove2me | Definitions.Def_TermCycDich_IsRedMinor
-- name    : TermCycDich_IsRedMinor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:38.845205+00:00
-- url     : https://prove2.me/theorems/9c870096-429a-4e78-8fbf-9aafadbde42b
-- title:
--   Red-minor $(H,B) \preceq (G,R)$
-- statement:
--   An annotated graph $(H, B)$ is a **red-minor** of an annotated graph $(G, R)$ if there is a minor model of $H$ in $G$ in which every vertex of $B$ is represented by a branch set containing a red vertex: there are vertex sets $G_w \subseteq V(G)$, $w \in V(H)$, such that
--
--   1. each $G_w$ is nonempty and induces a connected subgraph of $G$;
--   2. the $G_w$ are pairwise disjoint;
--   3. for every edge $ab$ of $H$ some vertex of $G_a$ is adjacent in $G$ to some vertex of $G_b$;
--   4. $R \cap G_w \neq \emptyset$ for every $w \in B$.
--
--   Equivalently, $(H,B)$ arises from $(G,R)$ by edge deletions, vertex deletions, edge contractions (the new vertex is red iff an endpoint was red) and colour erasures.
--
--   **Formalization Note** The branch-set form of the minor model (the paper's simplified model, p.15); its first three clauses are those of the public `RobertsonSeymour1986.GM5.IsMinor`, restated so that the red clause refers to the same branch sets. $H$ lives on its own vertex type, which builds in "isomorphic to".
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.1, p.16 (PDF 18); operational form p.2 (PDF 4); minor models p.15 (PDF 17)

import Mathlib

namespace TermCycDich

/-- `(H, B)` is a **red-minor** of `(G, R)`: there is a minor model of `H` in `G` (branch sets)
in which the branch set of every vertex of `B` contains a red vertex of `R`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.1, p.16 (PDF 18): "An annotated graph (H, B) is a red-minor of an annotated
graph (G, R) if there exists a minor-model {G_v}_{v∈V(H)} of H in G such that R ∩ V(G_v) ≠ ∅ for
all v ∈ B." (Operational form on p.2 (PDF 4): edge deletions, vertex deletions, contractions
keeping red if an endpoint was red, and colour erasures.)

**Formalization Note** The minor model is the branch-set model of p.15 (PDF 17), which the paper
uses "most of the time": nonempty, pairwise disjoint vertex sets `β w`, each inducing a connected
subgraph of `G`, and for every edge `ab` of `H` an edge of `G` between `β a` and `β b`. Its three
clauses are those of the public `RobertsonSeymour1986.GM5.IsMinor`, restated inline because the
red condition must refer to the same `β`. The model with explicit edge paths `G_e` gives the same
relation (contract each `G_e` minus one end into a branch set; this keeps red vertices).
Quantifying `H` on its own vertex type `W` builds in "isomorphic to". -/
def IsRedMinor {W V : Type} (H : SimpleGraph W) (B : Set W) (G : SimpleGraph V) (R : Set V) :
    Prop :=
  ∃ β : W → Set V,
    (∀ w, (β w).Nonempty ∧ (G.induce (β w)).Connected) ∧
    Pairwise (fun a b => Disjoint (β a) (β b)) ∧
    (∀ a b, H.Adj a b → ∃ x ∈ β a, ∃ y ∈ β b, G.Adj x y) ∧
    ∀ w ∈ B, (β w ∩ R).Nonempty

end TermCycDich


