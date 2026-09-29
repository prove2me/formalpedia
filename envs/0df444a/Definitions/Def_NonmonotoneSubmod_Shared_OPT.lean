-- Prove2me | Definitions.Def_NonmonotoneSubmod_Shared_OPT
-- name    : NonmonotoneSubmod_Shared_OPT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:57:37.988985+00:00
-- url     : https://prove2.me/theorems/14604aad-8ee3-44fa-993d-019ab373d377
-- title:
--   The optimum $OPT = \max_{S \subseteq X} f(S)$
-- statement:
--   For a set function $f : 2^X \to \mathbb{R}$ on a finite ground set $X$, the **optimum** is
--
--   $$OPT = \max_{S \subseteq X} f(S),$$
--
--   the largest value of $f$ over all $2^{|X|}$ subsets of $X$ (including $\emptyset$ and $X$). It is the benchmark against which the approximation guarantees of the paper are measured.
--
--   Used by all five missions of this paper: 01-random-set (Theorem 2.1, p. 1137), 02-nonadaptive (Theorem 2.1, p. 1137, used in Theorem 2.6, p. 1139), 03-local-search (proof of Theorem 3.4, p. 1141), 04-smooth-local-search (Theorem 2.1, p. 1137, used in Theorem 3.6, p. 1142) and 05-query-lower-bound (the problem max{f(S) : S ⊆ X} of §1, p. 1133, used in Theorem 4.5, p. 1149).
--
--   **Formalization Note** The maximum is `Finset.univ.sup' Finset.univ_nonempty f` over the finite, always nonempty family `Finset (Finset X)` (it contains $\emptyset$), so it is attained and there is no default value, also when $X$ is empty.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Theorem 2.1 (OPT = max_{S⊆X} f(S))

import Mathlib

namespace NonmonotoneSubmod.Shared

/-- The optimum `OPT = max_{S ⊆ X} f(S)` (Feige–Mirrokni–Vondrák 2011, Theorem 2.1, p. 1137):
the maximum of `f` over all `2^|X|` subsets of the finite ground set `X`. The family of subsets
always contains `∅`, so the maximum is taken over a nonempty finite family. -/
def OPT {X : Type} [Fintype X] (f : Finset X → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

end NonmonotoneSubmod.Shared


