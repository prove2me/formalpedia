-- Prove2me | Definitions.Def_TermCycDich_IsAnnotatedPlanar
-- name    : TermCycDich_IsAnnotatedPlanar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:29.215282+00:00
-- url     : https://prove2.me/theorems/7be2dcf5-7674-4087-8765-49ed9bcc075e
-- title:
--   Annotated planar graph
-- statement:
--   An annotated graph $(G, R)$ is an **annotated planar graph** if $G$ is planar; the red set $R \subseteq V(G)$ is arbitrary.
--
--   "A class contains all annotated planar graphs" therefore means it contains $(G,R)$ for every planar $G$ and every $R$.
--
--   **Formalization Note** Planarity is the public `RobertsonSeymour1986.GM5.IsPlanar`: a crossing-free drawing of $G$ in the plane by simple arcs.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_TermCycDich_AnnotatedGraph

namespace TermCycDich

/-- An **annotated planar graph**: an annotated graph `(G, R)` whose graph `G` is planar; the
red set `R` is arbitrary.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.1, p.2 (PDF 4): "If R does not contain all annotated planar graphs [...]"; the
discussion after it (p.2) uses "all planar annotated graphs of the form (G, V(G))" as a special
case, so `R` ranges over all subsets.

**Formalization Note** Planarity is the public `RobertsonSeymour1986.GM5.IsPlanar` (a
crossing-free drawing in `ℝ × ℝ` by simple arcs). -/
def IsAnnotatedPlanar (x : AnnotatedGraph) : Prop :=
  RobertsonSeymour1986.GM5.IsPlanar x.G

end TermCycDich


