-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_DownwardClosure
-- name    : TarskiBootstrap_Dimensional_DownwardClosure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:23.622733+00:00
-- url     : https://prove2.me/theorems/166f231c-3549-44c7-af3a-d6373c851cbc
-- title:
--   Downward closure in a partial order
-- statement:
--   For a subset $A$ of an arbitrary partially ordered set $L$, define its **downward closure** by
--
--   $$D=\{y\in L:\exists a\in A,\ y\le a\}.$$
--
--   Neither finiteness nor the antichain property is built into the definition. This is shared by the general order lemma and the grid padding construction.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 3.2, PDF/printed pp. 11–12; equation (3.1), PDF/printed p. 11, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Mathlib

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Downward closure in an arbitrary partial order, Lemma 3.2, pp. 11–12. -/
def downwardClosure {L : Type*} [PartialOrder L] (A : Set L) : Set L :=
  {y | ∃ a ∈ A, y ≤ a}

end TarskiBootstrap.Dimensional


