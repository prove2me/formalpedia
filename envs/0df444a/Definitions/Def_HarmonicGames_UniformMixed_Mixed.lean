-- Prove2me | Definitions.Def_HarmonicGames_UniformMixed_Mixed
-- name    : HarmonicGames_UniformMixed_Mixed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:45:46.230028+00:00
-- url     : https://prove2.me/theorems/51e51bad-3d2d-4959-b07d-963fa03cbf81
-- title:
--   Pure-versus-mixed payoffs (35), mixed Nash equilibria (Definition 5.1.1) and the uniformly mixed strategy profile (Definition 5.2)
-- statement:
--   Fix a finite set of players $\mathcal M$ and, for each player $m$, a finite nonempty strategy set $E^m$ with $h_m = |E^m|$ elements; $E = \prod_m E^m$ is the set of strategy profiles and $u = (u^m)_m$ the utilities. A **mixed strategy** of player $m$ is a probability vector $x^m \in \Delta E^m$ ($x^m(q^m) \ge 0$, $\sum_{q^m} x^m(q^m) = 1$), and a **mixed strategy profile** is $x = \{x^m\}_m \in \prod_m \Delta E^m$. The mixed extension of $u^m$ is
--
--   $$
--   u^m(x) = \sum_{p \in E} u^m(p) \prod_{k \in \mathcal M} x^k(p^k) \qquad (34).
--   $$
--
--   1. **Pure deviation payoff (35).** If player $m$ plays the pure strategy $q^m$ and the others play $x^{-m}$, the payoff of $m$ is
--
--   $$
--   u^m(q^m, x^{-m}) = \sum_{p^{-m} \in E^{-m}} u^m(q^m, p^{-m}) \prod_{k \ne m} x^k(p^k).
--   $$
--
--   2. **Definition 5.1.1 (mixed Nash equilibrium).** A mixed strategy profile $x \in \prod_m \Delta E^m$ is a mixed Nash equilibrium if $u^m(x^m, x^{-m}) \ge u^m(p^m, x^{-m})$ for all $m \in \mathcal M$ and all $p^m \in E^m$.
--   3. **Definition 5.2 (uniformly mixed strategy profile).** The uniformly mixed strategy of player $m$ plays every $q^m \in E^m$ with probability $1/h_m$; the uniformly mixed strategy profile is the profile in which every player uses its uniformly mixed strategy.
--
--   These are the solution concepts of the mission's goal (Theorem 5.4) and of Corollary 5.2.
--
--   **Formalization Note** Mixed strategies and the mixed extension (34) come from the referenced `agt_games` bundle (`AGT.IsLottery`, `AGT.IsMixedProfile`, `AGT.expectedPayoff`). The payoff (35) is defined as the mixed extension evaluated at the profile in which $x^m$ is replaced by the point mass at $q^m$; the product then vanishes unless $p^m = q^m$, which leaves exactly the sum (35). The equilibrium condition uses deviations to pure strategies, as printed (the `agt_games` notion `AGT.IsMixedNash` uses mixed deviations and is not used). The uniform profile is $1/h_m$ with $h_m$ the cardinality of $E^m$; it is a probability vector because every $E^m$ is nonempty, which the theorems of the mission assume.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 24, (34), (35), Definition 5.1.1 (pp. 24–25); p. 27, Definition 5.2

import Mathlib
import Definitions.Def_agt_games

/-!
Mixed strategies in a finite game (Section 5.2.2 of Candogan, Menache, Ozdaglar, Parrilo):
the payoff (35) of a pure strategy against the opponents' mixed strategies, mixed Nash
equilibria with pure deviations (Definition 5.1.1), and the uniformly mixed strategy profile
(Definition 5.2).  The mixed extension (34) is `AGT.expectedPayoff`, mixed strategies are
`AGT.IsLottery` / `AGT.IsMixedProfile`, and correlated equilibria (Definition 5.1.2) are
`HartSchmeidler.Finite.IsCorrelatedEq`.
-/

noncomputable section

namespace HarmonicGames.UniformMixed

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type} [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

/-- The pure strategy `a ∈ E^m` as a mixed strategy of player `m`: the point mass at `a`. -/
def pureLottery {m : ι} (a : E m) : E m → ℝ := fun b => if b = a then 1 else 0

/-- The payoff (35) of player `m` when `m` plays the pure strategy `a = q^m` and the other
players use the mixed strategies `x^{-m}`:
`u^m(q^m, x^{-m}) = ∑_{p^{-m} ∈ E^{-m}} u^m(q^m, p^{-m}) ∏_{k ≠ m} x^k(p^k)`.
It is the mixed extension (34) (`AGT.expectedPayoff`) evaluated at the profile in which the
mixed strategy of player `m` is replaced by the point mass at `a`; the product over all players
then vanishes unless `p^m = a`, which leaves exactly the sum (35). -/
def mixedVsPure (u : ι → (∀ k, E k) → ℝ) (x : ∀ k, E k → ℝ) (m : ι) (a : E m) : ℝ :=
  AGT.expectedPayoff u (Function.update x m (pureLottery a)) m

/-- **Definition 5.1.1** (mixed Nash equilibrium): a mixed strategy profile
`x = {x^m}_m ∈ ∏_m ΔE^m` is a mixed Nash equilibrium if for all players `m` and all pure
strategies `p^m ∈ E^m`, `u^m(x^m, x^{-m}) ≥ u^m(p^m, x^{-m})`, where `u^m(x)` is the mixed
extension (34) and `u^m(p^m, x^{-m})` is (35).  Deviations are to pure strategies, as printed. -/
def IsMixedNashEquilibrium (u : ι → (∀ k, E k) → ℝ) (x : ∀ k, E k → ℝ) : Prop :=
  AGT.IsMixedProfile x ∧ ∀ (m : ι) (a : E m), mixedVsPure u x m a ≤ AGT.expectedPayoff u x m

/-- **Definition 5.2** (uniformly mixed strategy profile): every player `m` plays each of its
`h_m = |E^m|` strategies with probability `1 / h_m`.  It is a mixed strategy profile when every
`E^m` is nonempty (with `E^m = ∅` the value `1/0 = 0` would not be a lottery). -/
def uniformProfile (E : ι → Type) [∀ m, Fintype (E m)] : ∀ m, E m → ℝ :=
  fun m _ => 1 / (Fintype.card (E m) : ℝ)

end HarmonicGames.UniformMixed

end


