-- Prove2me | Definitions.Def_ClawFreeChoosable_IsElementary
-- name    : ClawFreeChoosable_IsElementary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:00.802208+00:00
-- url     : https://prove2.me/theorems/176cc571-7cab-4717-a335-82421fa72bdf
-- title:
--   Elementary graph
-- statement:
--   A graph $G$ is **elementary** if it admits an edge two-colouring in which the two edges of every induced three-vertex path have different colours. An induced three-vertex path is a triple $a, b, d$ with $ab, bd \in E(G)$, $a \ne d$ and $ad \notin E(G)$.
--
--   By Chvátal–Sbihi every claw-free perfect atom is elementary or peculiar; elementary graphs are, by Maffray–Reed, augmentations of line graphs of bipartite multigraphs.
--
--   **Formalization Note** The two-colouring is a map from unordered pairs of vertices to $\{\mathrm{true}, \mathrm{false}\}$; its values on non-edges are never used.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §1 p.1, "elementary graph"

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Elementary graph** (arXiv:2611.01068v1, §1 p.1): `G` admits an edge two-colouring in which
the two edges of every induced three-vertex path have different colours. An induced path
`a – b – d` is given by `G.Adj a b`, `G.Adj b d`, `a ≠ d` and `¬ G.Adj a d`.

**Formalization Note.** The two-colouring is a map `c : Sym2 V → Bool` (two colours); its values
on non-edges are never used. -/
def IsElementary {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ c : Sym2 V → Bool, ∀ a b d : V, G.Adj a b → G.Adj b d → a ≠ d → ¬ G.Adj a d →
    c s(a, b) ≠ c s(b, d)

end ClawFreeChoosable


