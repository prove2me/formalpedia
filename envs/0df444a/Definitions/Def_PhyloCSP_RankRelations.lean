-- Prove2me | Definitions.Def_PhyloCSP_RankRelations
-- name    : PhyloCSP_RankRelations
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:51.851529+00:00
-- url     : https://prove2.me/theorems/22370334-3bf6-42b0-8859-fd78e36f13e1
-- title:
--   The relations $\sim$ and $\prec$ of an order on $Z$
-- statement:
--   Let $<$ be a linear order on $Z$ and $C$ the relation of the Fraïssé limit. Define $x\sim x$, and for distinct $x,y$,
--   $$
--   x\sim y\iff\bigl(a<x\Leftrightarrow a<y\bigr)\ \text{for every }a\text{ with }a\mid_C xy, \tag{9}
--   $$
--   so $x\sim y$ when no outgroup of $\{x,y\}$ in the input lies between them. Further, $x\prec y$ iff $x<y$ and $x\not\sim y$.
--
--   For a random invariant order, $\sim$ is almost surely an equivalence relation whose classes are intervals (Lemma 9.2) and $\prec$ orders the classes; the ranks of Lemma 9.4 realize this preorder by real numbers.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 9.1, eq. (9), p.26 (PDF p.28); p.27 (PDF p.29)

import Mathlib
import Definitions.Def_PhyloCSP_fraisseRel

set_option autoImplicit false

namespace PhyloCSP

/-- **The relations `∼` and `≺` of a linear order on `Z` (Section 9.1, eq. (9)).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 9.1, p.26 (PDF p.28): "We define a random relation ∼
as follows. Let x ∼ x. For distinct x, y, let x ∼ y if a < x if and only if a < y for every a with
a |C xy. (9)" Here `C = fraisseRel` and `lt` is the (realized) order `<`. -/
def simRel (lt : Z → Z → Bool) (x y : Z) : Prop :=
  x = y ∨ ∀ a : Z, fraisseRel a x y = true → (lt a x = true ↔ lt a y = true)

/-- p.27 (PDF p.29): "Let us say that x ≺ y if x < y and x ≁ y." -/
def precRel (lt : Z → Z → Bool) (x y : Z) : Prop :=
  lt x y = true ∧ ¬ simRel lt x y

end PhyloCSP


