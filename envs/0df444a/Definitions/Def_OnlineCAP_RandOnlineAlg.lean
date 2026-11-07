-- Prove2me | Definitions.Def_OnlineCAP_RandOnlineAlg
-- name    : OnlineCAP_RandOnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:29.8872+00:00
-- url     : https://prove2.me/theorems/204775fb-0eeb-4ed5-aec2-b38a24d31d3f
-- title:
--   Randomized online algorithm for online hitting set
-- statement:
--   A **randomized online algorithm** for an online hitting-set problem with elements of a type $U$ and requests of a type $\mathcal R$ consists of
--
--   1. a probability space $(\Omega,\mu)$ of coins;
--   2. for every outcome $\omega\in\Omega$ and every list $s=(r_1,\dots,r_t)$ of revealed requests, a finite set $F_\omega(s)\subseteq U$, the elements purchased after the $t$-th request,
--
--   such that nothing is purchased before the first request ($F_\omega(\emptyset)=\emptyset$), purchases are irrevocable ($F_\omega(s)\subseteq F_\omega(s\,r)$ for every further request $r$), and every event $\{\omega : e\in F_\omega(s)\}$ is measurable.
--
--   The algorithm is *online* because $F_\omega(s)$ depends only on the coins and on the requests revealed so far. This is the algorithm model of every competitive statement of the mission; a deterministic algorithm is the case of a one-point $\Omega$.
--
--   **Formalization Note** Feasibility, staying inside a ground set, and the competitive or rounding guarantee are imposed by `IsCompetitive` and `IsRounding`. Measurability makes costs and purchase probabilities genuine random variables.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2.2, p.10; Problem 2.4, p.9

import Mathlib

namespace OnlineCAP

open MeasureTheory

/-- **Randomized online algorithm for an online hitting-set problem.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2.2 "Online
Hitting Set and Competitive Analysis", p.10 (PDF p.10), and Problem 2.4, p.9: "At each time step
t, we must maintain an integral hitting set Ht ⊆ U such that … and Ht ⊇ Ht−1"; randomized
algorithms are evaluated "against an oblivious adversary, which has knowledge of the algorithm
but cannot adapt to its random coin flips".

The algorithm draws its coins `ω` from a probability space `(Ω, μ)` and, after the requests
`s = [r₁, …, r_t]` have been revealed, holds the purchased set `buy ω s : Finset U`. It is online
because `buy ω s` depends only on the coins and the revealed prefix `s`; purchases are
irrevocable (`mono`); nothing is bought before the first request (`init`).

**Formalization Note.** `U` is the type of elements that can be bought and `Req` the type of
requests. Measurability of every event `{ω | e ∈ buy ω s}` makes costs and purchase probabilities
genuine random variables (no junk integrals). A deterministic algorithm is the case `Ω = Unit`.
The oblivious adversary is expressed by quantifying the request list outside the integral in
`IsCompetitive` and `IsRounding`. Whether the purchased set stays inside a ground set and is
feasible is problem-specific and is imposed by those predicates. -/
structure RandOnlineAlg (U Req : Type) where
  /-- the sample space of the coins -/
  Ω : Type
  /-- the σ-algebra on the sample space -/
  [mΩ : MeasurableSpace Ω]
  /-- the law of the coins -/
  μ : Measure Ω
  /-- the law of the coins is a probability measure -/
  [prob : IsProbabilityMeasure μ]
  /-- `buy ω s`: the set purchased after the requests `s` have been revealed, on coins `ω` -/
  buy : Ω → List Req → Finset U
  /-- nothing is purchased before the first request -/
  init : ∀ ω, buy ω [] = ∅
  /-- purchases are irrevocable -/
  mono : ∀ ω (s : List Req) (r : Req), buy ω s ⊆ buy ω (s ++ [r])
  /-- every purchase event is measurable -/
  meas : ∀ (s : List Req) (e : U), MeasurableSet {ω | e ∈ buy ω s}

attribute [instance] RandOnlineAlg.mΩ RandOnlineAlg.prob

end OnlineCAP


