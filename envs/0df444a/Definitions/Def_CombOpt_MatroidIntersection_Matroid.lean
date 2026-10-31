-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_Matroid
-- name    : CombOpt_MatroidIntersection_Matroid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:39.108591+00:00
-- url     : https://prove2.me/theorems/2a12ca57-1979-4b51-99a4-49deffa526c8
-- title:
--   Matroid on a finite set
-- statement:
--   A **matroid** $M=(S,\mathcal I)$ consists of a finite set $S$ and a family $\mathcal I$ of subsets of $S$, the **independent sets**, satisfying the axioms (M0)–(M2). Two matroids $M_1=(S,\mathcal I_1)$, $M_2=(S,\mathcal I_2)$ **on** $S$ share the ground set $S$; a set in $\mathcal I_1\cap\mathcal I_2$ is a **common independent set**.
--
--   **Formalization Note** The ground set is a finite type `S`, all of which is the ground set; `M.Indep` is the family of independent `Finset S`s, bundled with a proof of (M0)–(M2). This is the book's definition, distinct from Mathlib's `_root_.Matroid`, which allows infinite ground sets inside a larger type; on finite ground sets the two describe the same objects.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, pp. 274–275 (PDF pp. 281–282)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_IsMatroid

namespace CombOpt.MatroidIntersection

/-- **A matroid on a finite set `S`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1,
pp. 274–275 (PDF pp. 281–282): a matroid `M = (S, I)` is a finite set `S` together with a family
`I` of subsets of `S` (the independent sets) satisfying (M0)–(M2).

`M : Matroid S` consists of the family `M.Indep` of independent subsets of the finite type `S`
and a proof that it satisfies (M0)–(M2) (`IsMatroid`).

**Formalization Note.** The ground set `S` is a finite type (`[Fintype S]`) and is the whole
type; "matroids `M₁, M₂` on `S`" are two terms of `Matroid S`. This is the book's axiomatic
definition, in the namespace `CombOpt.MatroidIntersection`; it is not Mathlib's
`_root_.Matroid` (which allows infinite ground sets inside a larger type). For a finite ground
set the two notions describe the same objects. -/
structure Matroid (S : Type*) [Fintype S] [DecidableEq S] where
  /-- The family of independent sets. -/
  Indep : Finset S → Prop
  /-- The independent sets satisfy (M0), (M1), (M2). -/
  isMatroid : IsMatroid Indep

end CombOpt.MatroidIntersection


