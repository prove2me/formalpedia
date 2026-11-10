-- Prove2me | Definitions.Def_EvasivePatterns_Rigid
-- name    : EvasivePatterns_Rigid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:13.586728+00:00
-- url     : https://prove2.me/theorems/a51538e4-7922-4014-8fd8-9f118ef00509
-- title:
--   Homometrically rigid finite integer set
-- statement:
--   A finite set $A \subseteq \mathbb Z$ is **(homometrically) rigid** when every set homometric to $A$ is a translate of $A$ or a translate of its reflection: whenever $\mathcal D(T) = \mathcal D(A)$ there is an integer $a$ with
--   $$
--   T = A + a \qquad\text{or}\qquad T = a - A .
--   $$
--   Rigidity of period supports is the geometric input of the mission: it forbids alternative "spectral factors" of the signed period polynomial.
--
--   **Formalization Note** Homometric sets range over nonempty finite sets of integers. A finite real set homometric to an integer set is an integer set after translating its minimum to $0$ (every point is then a distance), so integers lose nothing. Excluding the empty set only matters for singletons, which are then rigid.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §2, p.2 (PDF p.3), lines 68–71

import Mathlib
import Definitions.Def_EvasivePatterns_distMultiset

namespace EvasivePatterns

/-- **Homometric rigidity.** A finite integer set `A` is rigid when every set homometric to `A`
(same distance multiset) is a translate of `A` or a translate of its reflection: `T = A + a` or
`T = a − A` for some integer `a`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §2, printed p. 2 (PDF p. 3), lines 68–70: "Two sets are homometric
when they have the same distance multiset. We say that A is rigid when every homometric set is a
translate of A or a translate of its reflection."

**Formalization Note** Homometric sets range over nonempty finite sets of integers. Integers lose
nothing: a finite real set homometric to an integer set becomes an integer set after translating its
minimum to `0`, since every point is then a distance (the paper's own remark, lines 70–71).
Nonemptiness only removes the empty set, which is homometric to every singleton (no distances);
with it, singletons are rigid, and for `|A| ≥ 2` every homometric set is nonempty anyway. -/
def Rigid (A : Finset ℤ) : Prop :=
  ∀ T : Finset ℤ, T.Nonempty → distMultiset T = distMultiset A →
    ∃ a : ℤ, T = A.image (fun x => x + a) ∨ T = A.image (fun x => a - x)

end EvasivePatterns


