-- Prove2me | Definitions.Def_HypClass1_muP
-- name    : HypClass1_muP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:27:36.970358+00:00
-- url     : https://prove2.me/theorems/f77b7202-09a8-4886-9490-fe0d96fb7746
-- title:
--   Product measure $\mu_p(\mathcal B)$
-- statement:
--   Let $X$ be a finite set and $p \in [0,1]$. The product measure $\mu_p$ on $2^X$ includes each element of $X$ independently with probability $p$, so $\mu_p(B) = p^{|B|}(1-p)^{|X \setminus B|}$, and for a family $\mathcal B \subseteq 2^X$
--   $$
--   \mu_p(\mathcal B) = \sum_{B \in \mathcal B} p^{|B|} (1-p)^{|X\setminus B|}.
--   $$
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.42

import Mathlib
import Definitions.Def_HypClass1_randSubProb

namespace HypClass1

/-- **Product measure of a family**, `µ_p(B) = Σ_{B ∈ B} p^{|B|} (1 − p)^{|X∖B|}`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.42: "Let X
be a finite set and, for p ∈ [0, 1], let µ_p denote the product probability measure on 2^X in which
each element of X is included independently with probability p, i.e., µ_p(B) = p^{|B|}(1 − p)^{|X∖B|}.
… µ_p(B) := Σ_{B∈B} µ_p(B)".

**Formalization Note.** `X` is the finite type `α` (its `univ`); `µ_p(B)` is `randSubProb` of the event
`· ∈ B` with constant weight `p`. -/
noncomputable def muP {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) (B : Finset (Finset α)) : ℝ :=
  randSubProb (Finset.univ : Finset α) (fun _ => p) (fun A => A ∈ B)

end HypClass1


