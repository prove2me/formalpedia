-- Prove2me | Definitions.Def_Garrido_Foelner
-- name    : Garrido_Foelner
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-23T19:06:35.126279+00:00
-- url     : https://prove2.me/theorems/11052593-b704-4eb8-8a31-0a763ed8edbd
-- title:
--   The Følner condition and Følner sequences
-- statement:
--   Two notions for a discrete group $G$.
--
--   **`SatisfiesFoelnerCondition G` (Definition 3.1).** p. 8: “A discrete group $G$ satisfies the *Følner condition* if for every finite subset $A \subseteq G$ and every $\varepsilon > 0$ there exists a finite nonempty subset $F \subseteq G$ such that for each $a \in A$ we have $\frac{|aF \,\triangle\, F|}{|F|} \le \varepsilon$.” `SatisfiesFoelnerCondition G` is this condition, with $\varepsilon$ real and $\triangle$ the symmetric difference. Note the inequality is non-strict, matching the
--   source, and that $A$ is permitted to be empty, in which case the condition on $F$ is vacuous
--   and any finite nonempty $F$ serves.
--
--   **`HasFoelnerSequence G` (Definition 3.3).** p. 8: “For a discrete and countable (resp. locally compact) group $G$, a *Følner sequence* is a sequence $\{F_n\}$ of nonempty finite (resp. compact) subsets of $G$ such that $\frac{|gF_n \,\triangle\, F_n|}{|F_n|} \to 0$ (resp. $\frac{\mu(gF_n \,\triangle\, F_n)}{\mu(F_n)} \to 0$) for every $g \in G$.” `HasFoelnerSequence G` says that a Følner sequence in the discrete sense exists: a sequence $F : \mathbb{N} \to \mathcal{P}(G)$ with every
--   $F_n$ finite and nonempty, such that for every $g \in G$ the ratio $|gF_n \,\triangle\, F_n| / |F_n|$ tends to $0$ as $n \to \infty$. The predicate is stated for every group, the countability being supplied where it is used (Lemma 3.4 assumes $G$ countable, and Example 3.5 concerns $\mathbb{Z}$).
--
--   Note what the second definition does **not** require, following the source exactly: the $F_n$
--   need not be nested, their sizes need not tend to infinity, and they need not exhaust $G$. Some
--   texts build one or more of these into "Følner sequence"; Definition 3.3 asks only for finite,
--   nonempty sets whose translation ratios vanish. The sequence is also chosen before $g$, so only
--   the rate of convergence may depend on $g$.
--
--   In both definitions $aF$ and $gF_n$ are the **left** translates $\{ax : x \in F\}$, matching the
--   source. Cardinalities are `Set.ncard`, so no `DecidableEq` instance enters; on a finite set this
--   is the ordinary cardinality, and it is $0$ on an infinite one, which the finiteness hypotheses
--   exclude. The quotient is real division and $|F| \ge 1$, so no division-by-zero junk value
--   arises. This is the discrete, countably-indexed form; for uncountable groups the source only names
--   Følner nets (“we define a *Følner net* in the obvious way”), and they are not formalised here.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 8, Definitions 3.1 and 3.3. The source's locally compact clause of Definition 3.1 reads "A is a compact subgroup", where a compact subset is meant; only the discrete case is formalised here; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib

namespace Garrido

open scoped Pointwise symmDiff

def SatisfiesFoelnerCondition (G : Type*) [Group G] : Prop :=
  ∀ A : Set G, A.Finite → ∀ ε : ℝ, 0 < ε →
    ∃ F : Set G, F.Finite ∧ F.Nonempty ∧
      ∀ a ∈ A, (((a • F) ∆ F).ncard : ℝ) / (F.ncard : ℝ) ≤ ε

def HasFoelnerSequence (G : Type*) [Group G] : Prop :=
  ∃ F : ℕ → Set G, (∀ n, (F n).Finite ∧ (F n).Nonempty) ∧
    ∀ g : G, Filter.Tendsto
      (fun n => (((g • F n) ∆ F n).ncard : ℝ) / ((F n).ncard : ℝ))
      Filter.atTop (nhds 0)

end Garrido


