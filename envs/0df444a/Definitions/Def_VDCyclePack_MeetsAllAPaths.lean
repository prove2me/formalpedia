-- Prove2me | Definitions.Def_VDCyclePack_MeetsAllAPaths
-- name    : VDCyclePack_MeetsAllAPaths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:09.451194+00:00
-- url     : https://prove2.me/theorems/146bdf01-0e76-410e-980b-41ba888a65ce
-- title:
--   A vertex set meeting every $A$-path
-- statement:
--   A set $X$ of vertices **meets every $A$-path** of $F$ if every $A$-path of $F$ has a vertex (possibly an end) in $X$.
--
--   This is the second alternative of Gallai's theorem (Lemma 3.1), used in Lemma 6.4.
--
--   **Formalization Note** "Meets" means sharing a vertex, ends included.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 3.1, p.10

import Mathlib
import Definitions.Def_VDCyclePack_IsAPath

namespace VDCyclePack

/-- **A vertex set meeting every A-path.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 3.1, p.10: "some set of at most 2M − 2 vertices meets every A-path in F".

`MeetsAllAPaths F A X` says every A-path of `F` has a vertex in `X`.

**Formalization Note.** "Meets" means sharing a vertex, ends included. -/
def MeetsAllAPaths {V : Type*} (F : SimpleGraph V) (A : Set V) (X : Finset V) : Prop :=
  ∀ (u v : V) (p : F.Walk u v), IsAPath F A p → ∃ w ∈ p.support, w ∈ X

end VDCyclePack


