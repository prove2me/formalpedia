-- Prove2me | Definitions.Def_TeschlODE_Shared_tentRepellor
-- name    : TeschlODE_Shared_tentRepellor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:03:26.086993+00:00
-- url     : https://prove2.me/theorems/ba55b439-5fbe-4cfa-8e0a-1488e9789c12
-- title:
--   The invariant set $\Lambda$ of the tent map: points whose orbit stays in $[0,1]$ (11.16)–(11.18)
-- statement:
--   For the tent map $T_\mu$, let
--   $$\Lambda = \{\, x \in \mathbb{R} \;:\; T_\mu^n(x) \in [0,1] \text{ for all } n \in \mathbb{N}_0 \,\}$$
--   be the set of points whose forward orbit never leaves $[0,1]$.
--
--   For $\mu > 2$ the book constructs $\Lambda$ as $\bigcap_{n} \Lambda_n$ (11.18), where $\Lambda_0 = [0,1]$ and $\Lambda_n = \mu^{-1}\Lambda_{n-1} \cup (1 - \mu^{-1}\Lambda_{n-1})$ is the set of points staying in $[0,1]$ for $n$ iterations (p. 299); the intersection is exactly the set above. For $\mu = 2$ it is $[0,1]$ (as the book notes in the proof of Theorem 11.20, p. 310). This is the set called the repellor of the tent map in Theorem 11.20.
--
--   This one definition serves chunk 09-interval-maps (Lemma 11.4, p. 299; Theorem 11.5, p. 301; Theorem 11.20, p. 309) and chunk 11-horseshoe (Lemma 11.4, p. 299; Theorem 11.5, p. 301; the invariant set $\Lambda = \Lambda(T_{1/\lambda}) \times \Lambda(T_\mu)$ of the horseshoe, Eq. (13.8), p. 332), where it was called `tentSet`.
--
--   **Formalization Note.** The set is defined dynamically, uniformly in $\mu$, rather than by the recursion (11.16)–(11.17); for $\mu \ge 2$ the two agree.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), pp. 298–299, §11.4, Eqs. (11.16)–(11.18)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap

namespace TeschlODE.Shared

/-- Teschl, §11.4, pp. 298–299, (11.16)–(11.18): the set `Λ` of points whose forward orbit under
the tent map `T_µ` stays in `[0, 1]` for all iterations, `Λ = {x ∈ ℝ | T_µⁿ(x) ∈ [0, 1] ∀ n ≥ 0}`.
For `µ > 2` this is the book's `Λ = ⋂ₙ Λₙ` (11.18), `Λₙ` being the points that stay in `[0, 1]`
for `n` iterations; for `µ = 2` it is `[0, 1]` (p. 310). -/
def tentRepellor (μ : ℝ) : Set ℝ :=
  {x | ∀ n : ℕ, (tentMap μ)^[n] x ∈ Set.Icc (0 : ℝ) 1}

end TeschlODE.Shared


