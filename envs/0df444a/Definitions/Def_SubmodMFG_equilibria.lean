-- Prove2me | Definitions.Def_SubmodMFG_equilibria
-- name    : SubmodMFG_equilibria
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:36.927347+00:00
-- url     : https://prove2.me/theorems/c9c65271-b75f-44a5-91a3-2af7926147cc
-- title:
--   The set $M$ of mean field game equilibria
-- statement:
--   A distribution $\mu\in L$ is a **mean field game equilibrium** if $\mu\in R(\mu)$, i.e. $\mu$ is a fixed point of the best-response map. The set of all equilibria is
--   $$
--   M=\{\mu\in L:\ \mu\in R(\mu)\}.
--   $$
--
--   Theorem 2.6 is about the structure of $M$: its least and greatest elements and how to reach them.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.1, Definition 2.2, p.6; the set M is named in Theorem 2.6, p.7

import Mathlib
import Definitions.Def_SubmodMFG_bestResponse

namespace SubmodMFG

/-- **The set `M` of mean field game equilibria.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.1, Definition 2.2, p.6: "We say that µ ∈ L is a mean field game
equilibrium if µ ∈ R(µ), i.e. µ is a fixed point of the best-response-map." The set of all
equilibria is called `M` in Theorem 2.6, p.7.

**Formalization Note.** `equilibria p J = {µ | µ ∈ R(µ)}` with `R = bestResponse p J`. -/
def equilibria {E L : Type*} (p : E → L) (J : E → L → ℝ) : Set L :=
  {μ | μ ∈ bestResponse p J μ}

end SubmodMFG


