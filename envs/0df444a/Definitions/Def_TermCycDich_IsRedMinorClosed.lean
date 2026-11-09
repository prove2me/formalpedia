-- Prove2me | Definitions.Def_TermCycDich_IsRedMinorClosed
-- name    : TermCycDich_IsRedMinorClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:53.531362+00:00
-- url     : https://prove2.me/theorems/48aff454-60d5-4d4b-9c56-010e91f8c148
-- title:
--   Red-minor-closed class
-- statement:
--   A class $\mathcal C$ of annotated graphs is **red-minor-closed** if every red-minor of a member of $\mathcal C$ belongs to $\mathcal C$.
--
--   Theorem 1.1 classifies the complexity of Terminal Cyclability on every such class.
--
--   **Formalization Note** No decidability, nonemptiness or other condition is imposed on the class.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_TermCycDich_IsRedMinor
import Definitions.Def_TermCycDich_AnnotatedGraph

namespace TermCycDich

/-- A class `C` of annotated graphs is **red-minor-closed**: every red-minor of a member of `C`
is a member of `C`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.1, p.2 (PDF 4): "Let R be a red-minor-closed class of annotated graphs."

**Formalization Note** A class is an arbitrary set of `AnnotatedGraph`s; no decidability,
nonemptiness or isomorphism closure is assumed (the last follows from red-minor closure). -/
def IsRedMinorClosed (C : Set AnnotatedGraph) : Prop :=
  ∀ x ∈ C, ∀ y : AnnotatedGraph, IsRedMinor y.G (↑y.R : Set (Fin y.n)) x.G (↑x.R : Set (Fin x.n)) →
    y ∈ C

end TermCycDich


