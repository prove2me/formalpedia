-- Prove2me | Definitions.Def_LocallyConvex_SchwartzSpace
-- name    : LocallyConvex_SchwartzSpace
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:20:28.623177+00:00
-- url     : https://prove2.me/theorems/8e55df02-d37a-4a29-9528-663556f0eeef
-- title:
--   Schwartz spaces in the sense of Grothendieck: locally convex spaces in which every continuous seminorm $p$ has a $0$-neighbourhood that is precompact for $p$
-- statement:
--   This file defines **Schwartz spaces in the sense of Grothendieck**, a class of locally convex spaces. (They are not the spaces of rapidly decreasing functions, which are also named after Schwartz.)
--
--   Let $E$ be a complex vector space with a topology. The predicate `MasulloGRH.IsSchwartzLCS E` says that
--
--   1. the topology of $E$ is a locally convex vector space topology, i.e. it is defined by a family of seminorms (`MasulloGRH.IsLocallyConvexTopology`), and
--   2. for every continuous seminorm $p$ on $E$ there is a neighbourhood $V$ of $0$ in $E$ which is *precompact for $p$*: for every $\varepsilon>0$ there are finitely many points $y_1,\dots,y_r\in E$ with
--   $$V\ \subset\ \bigcup_{i=1}^{r}\{x\in E:\ p(x-y_i)<\varepsilon\}.$$
--
--   The source words the definition as follows: for every closed convex circled $0$-neighbourhood $U\subset E$ there is a $0$-neighbourhood $V\subset E$ whose image in the normed space $E_U=E/p_U^{-1}(0)$ (normed by the gauge $p_U$ of $U$) is precompact, i.e. has compact closure in the Banach space completion $\widehat{E_U}$. The continuous seminorms on $E$ are exactly the gauges of the closed convex circled $0$-neighbourhoods ($p$ is the gauge of $\{p\le 1\}$), and a subset of a normed space is precompact if and only if it is totally bounded, so the two formulations agree.
--
--   Schwartz spaces are the class singled out by Grothendieck for which quotient maps of Fréchet spaces lift bounded sets; nuclear spaces are Schwartz spaces (Example C.1.5.10 of the source), which is how the source applies the lifting theorem in Theorem C.1.5.11 and Corollary C.1.5.13. A normed space is a Schwartz space only if it is finite-dimensional. The converse implication "Schwartz implies nuclear", asserted in passing on p. 668 of the source, is false.
--
--   **Formalization Note.** As in `Def_MasulloGRH_LocallyConvex`, the predicate is a property of the topology carried by `E`; only `[TopologicalSpace E]` is assumed and local convexity is part of the predicate. No Hausdorff condition is imposed (the source imposes none). The centres $y_i$ are arbitrary points of $E$; requiring them to lie in $V$ gives an equivalent condition (replace $\varepsilon$ by $\varepsilon/2$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 667-668, §C.1.5 (definition of Schwartz spaces, between Definition C.1.5.9 and Example C.1.5.10); classical reference: A. Grothendieck, Sur les espaces (F) et (DF), Summa Brasil. Math. 3 (1954), pp. 57-123, II.4, Définition 5, p. 117 (as cited by the paper)

import Definitions.Def_MasulloGRH_LocallyConvex

/-!
# Schwartz spaces in the sense of Grothendieck

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix C, §C.1.5,
pp. 667–668 (the paragraphs between Definition C.1.5.9 and Example C.1.5.10), which quotes
A. Grothendieck, *Sur les espaces (F) et (DF)*, Summa Brasil. Math. 3 (1954), II.4, Définition 5.

These are *locally convex spaces* with a compactness property of their `0`-neighbourhoods; they are
unrelated to the function spaces of rapidly decreasing functions (`SchwartzMap` in Mathlib).

All vector spaces are over `ℂ`, and, as in `Def_MasulloGRH_LocallyConvex`, a property of a space `E`
is a property of the topology carried by `E`: no instance beyond `TopologicalSpace E` is assumed.
-/

namespace MasulloGRH

open Topology

universe u

/-- `E` is a *Schwartz space* in the sense of Grothendieck: `E` is a locally convex space and for
every continuous seminorm `p` on `E` there is a `0`-neighbourhood `V` which is precompact for `p`,
i.e. for every `ε > 0` the set `V` is covered by finitely many open `p`-balls
`{x | p (x - y) < ε}` of radius `ε`.

Every continuous seminorm `p` is the gauge of the closed convex circled `0`-neighbourhood
`U = {p ≤ 1}`, and the condition says exactly that the image of `V` in the normed space
`E_U = E / p⁻¹(0)` is precompact.  No Hausdorff condition is imposed. -/
def IsSchwartzLCS (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  IsLocallyConvexTopology E ‹TopologicalSpace E› ∧
    ∀ p : Seminorm ℂ E, Continuous p → ∃ V ∈ 𝓝 (0 : E), ∀ ε : ℝ, 0 < ε →
      ∃ S : Finset E, V ⊆ ⋃ y ∈ S, {x : E | p (x - y) < ε}

end MasulloGRH


