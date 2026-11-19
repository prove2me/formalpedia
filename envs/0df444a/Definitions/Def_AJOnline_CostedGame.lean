-- Prove2me | Definitions.Def_AJOnline_CostedGame
-- name    : AJOnline_CostedGame
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:29:31.032701+00:00
-- url     : https://prove2.me/theorems/64891a06-e796-4b6c-b2f2-d2bf252fa091
-- title:
--   Costed games, competitive and randomised-competitive strategies
-- statement:
--   A **costed game** $C$ is an AJ game $C.G$ together with two functions on finite plays, both with values in $[0,\infty]$:
--
--   - $\mathrm{alg}(s)$, the cost paid by the algorithm (Player) along $s$;
--   - $\mathrm{opt}(s)$, the offline optimum for the requests in $s$.
--
--   The file defines three notions.
--
--   1. A deterministic strategy $\sigma$ is **$(\rho,b)$-competitive** if $\mathrm{alg}(s)\le\rho\,\mathrm{opt}(s)+b$ for every $s\in\sigma$.
--   2. The **tensor** $C\otimes D$ is the costed game on $C.G\otimes D.G$ with
--   $$\mathrm{alg}(s)=\mathrm{alg}_C(s{\restriction}C)+\mathrm{alg}_D(s{\restriction}D),\qquad \mathrm{opt}(s)=\mathrm{opt}_C(s{\restriction}C)+\mathrm{opt}_D(s{\restriction}D).$$
--   3. For a behaviour strategy $\beta$ and a script $r$, $\mathbb E[\mathrm{alg}]$ and $\mathbb E[\mathrm{opt}]$ are the expectations over the play-out of $\beta$ from the empty play against $r$. $\beta$ is **$(\rho,b)$-randomised-competitive** if, for every script $r$,
--   $$\mathbb E[\mathrm{alg}]\le\rho\,\mathbb E[\mathrm{opt}]+b .$$
--
--   **Formalization Note** Offline optima add over the components of a tensor: the two problems are independent instances. A strategy that stops at once has expected cost $0$, so existence statements in this mission also require the strategy never to stop.
-- source:
--   A. Borodin, R. El-Yaniv, Online Computation and Competitive Analysis, CUP 1998, Definition 1.1 (competitive ratio against an oblivious adversary), on the games of S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057

import Mathlib
import Definitions.Def_AJGames_Behaviour

/-!
# Online problems as Abramsky–Jagadeesan games

An online problem is read as an AJ game in which Opponent issues requests and Player serves them.
A *costed game* attaches to every finite play `s` the cost `alg s` that Player has paid along `s`,
and the offline optimum `opt s` for the requests that occur in `s`. A Player strategy is
`(ρ, β)`-competitive when every play it allows satisfies `alg s ≤ ρ · opt s + β` (Borodin and
El-Yaniv, *Online Computation and Competitive Analysis*, CUP 1998, Definition 1.1, for an oblivious
adversary; here the adversary's moves are the Opponent moves of the game).

**Formalization Note.** Costs are `ℝ≥0∞`-valued functions of finite plays, so the finite-play
(safety) fragment of AJ games suffices. In the tensor `A ⊗ B` the two problems run side by side and
Opponent decides which one receives the next request (AJ: only Opponent switches component).
Costs and offline optima add over the components: the two instances are independent.
-/

namespace AJOnline

open AJGames
open scoped ENNReal NNReal

universe u

/-- An online problem as an AJ game with costs on finite plays. -/
structure CostedGame where
  G : AJGames.Game.{u}
  alg : List G.M → ℝ≥0∞
  opt : List G.M → ℝ≥0∞

/-- `σ` is `(ρ, β)`-competitive: on every finite play it allows, its cost is at most
`ρ` times the offline optimum plus `β`. -/
def Competitive (C : CostedGame.{u}) (σ : Strategy C.G) (ρ β : ℝ≥0) : Prop :=
  ∀ s ∈ σ.carrier, C.alg s ≤ (ρ : ℝ≥0∞) * C.opt s + β

/-- Two independent online problems side by side: the AJ tensor of the games, with costs and
offline optima added over the components. -/
def CostedGame.tensor (C D : CostedGame.{u}) : CostedGame.{u} where
  G := AJGames.Game.tensor C.G D.G
  alg s := C.alg (projL s) + D.alg (projR s)
  opt s := C.opt (projL s) + D.opt (projR s)

/-- Expected cost to Player of the behaviour strategy `β` against the oblivious script `rs`
(stop-counts semantics, `AJGames.playOut`). -/
noncomputable def expAlg (C : CostedGame.{u}) (β : BehStrategy C.G) (rs : List C.G.M) : ℝ≥0∞ :=
  ∑' s, playOut β [] rs s * C.alg s

/-- Expected offline optimum over the same outcomes. -/
noncomputable def expOpt (C : CostedGame.{u}) (β : BehStrategy C.G) (rs : List C.G.M) : ℝ≥0∞ :=
  ∑' s, playOut β [] rs s * C.opt s

/-- `β` is `(ρ, b)`-competitive against oblivious adversaries: for every script,
`E[alg] ≤ ρ · E[opt] + b`. -/
def RandCompetitive (C : CostedGame.{u}) (β : BehStrategy C.G) (ρ b : ℝ≥0) : Prop :=
  ∀ rs : List C.G.M, expAlg C β rs ≤ (ρ : ℝ≥0∞) * expOpt C β rs + b

end AJOnline


