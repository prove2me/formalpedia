-- Prove2me | Definitions.Def_TermCycDich_AnnotatedGraph
-- name    : TermCycDich_AnnotatedGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:35.05443+00:00
-- url     : https://prove2.me/theorems/8ada6626-7b69-42a6-b826-5b818a66d201
-- title:
--   Annotated graph $(G,R)$
-- statement:
--   An **annotated graph** is a pair $(G, R)$ of a finite simple graph $G$ and a set $R \subseteq V(G)$ of red vertices. A class of annotated graphs is a set of such pairs.
--
--   **Formalization Note** The vertex set is $\{0,\dots,n-1\}$ (`Fin n`, $n = |G|$) and $R$ is a finite set of vertices. All classes in the mission are red-minor-closed, hence closed under isomorphism, so the fixed vertex set loses nothing.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1, p.1 (PDF 3)

import Mathlib

namespace TermCycDich

/-- An **annotated graph** `(G, R)`: a finite simple graph `G` with a set `R ⊆ V(G)` of red
vertices (terminals). This is the type that a *class* of annotated graphs is a subset of.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1, p.1 (PDF 3): "We call the pair (G, R) an annotated graph"; graphs are finite
(Section 2.1, p.15 (PDF 17): "|G| = |V(G)|").

**Formalization Note** The vertex set is `Fin n` (`n = |G|`) and `R` is a `Finset (Fin n)`.
Every class used in this mission is closed under red-minors, hence under isomorphism (an
isomorphic copy is a red-minor), so fixing the vertex set to `Fin n` loses nothing. -/
structure AnnotatedGraph where
  /-- the number of vertices `|G|` -/
  n : ℕ
  /-- the graph `G` on the vertex set `Fin n` -/
  G : SimpleGraph (Fin n)
  /-- the red vertices (terminals) `R ⊆ V(G)` -/
  R : Finset (Fin n)

end TermCycDich


