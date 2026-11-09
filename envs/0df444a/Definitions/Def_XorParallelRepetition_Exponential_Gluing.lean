-- Prove2me | Definitions.Def_XorParallelRepetition_Exponential_Gluing
-- name    : XorParallelRepetition_Exponential_Gluing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:20.438854+00:00
-- url     : https://prove2.me/theorems/54407bdd-e327-49ec-afec-af6cdb348147
-- title:
--   §3.1 — gluing a generalized XOR game over a set of players
-- statement:
--   Let $\Psi$ be a generalized XOR game with law $\mu$, and let $I$ be a set of players. The game $\Psi_{\mathrm{glue}(I)}$ is played as follows:
--
--   1. sample a challenge $(x,t)\sim\mu$;
--   2. sample a challenge $(x',t')\sim\mu$ conditioned on $x'_i=x_i$ for all $i\in I$;
--   3. for each $i\notin I$, send $x_i$ to player $i$ and $x'_i$ to a new player $i'$, and accept exactly when
--
--   $$
--   \sum_{i\notin I}(a_i+a'_i)=t-t'.
--   $$
--
--   The second sample has the conditional law of $\mu$ given the questions of $I$ in the first sample. This is not $\mu\times\mu$ conditioned on agreement, which would change the law of the first sample. The source uses the operation for non-empty $I$; the game has $2(k-|I|)$ players.
--
--   The operation carries one Cauchy–Schwarz step (Lemma 3.1) and lowers $H_N$ (Lemma 3.3). Since it changes the player set, a sequence of gluings is a sequence of games packaged with their player types.
--
--   **Formalization Note** The new players are $\{i\mid i\notin I\}\times\mathrm{Bool}$, with $(i,\mathrm{false})$ for $i$ and $(i,\mathrm{true})$ for $i'$. The law is built with `PMF.bindOnSupport` and `PMF.filter`: the conditional law is only ever formed at a supported first challenge, whose fiber contains it and so has positive mass, and no fallback value occurs.
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), §3.1, printed pp. 10–11, PDF pp. 10–11

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames

/-!
# The gluing operation

Source: Braverman and Minzer, STOC 2027 submission #195, §3.1 (printed/PDF pp. 10–11).
-/

namespace XorParallelRepetition.Exponential

universe u

variable {p : ℕ} {ι : Type}

namespace GeneralizedXorGame

/-- The fiber of a challenge `ω` over the players of `I`: the challenges that give each player of
`I` the same question as `ω`. -/
def fiber (Ψ : GeneralizedXorGame.{u} p ι) (I : Finset ι) (ω : (∀ i, Ψ.Q i) × ZMod p) :
    Set ((∀ i, Ψ.Q i) × ZMod p) :=
  {ω' | ∀ i ∈ I, ω'.1 i = ω.1 i}

/-- The law of the second challenge given the first: `μ` conditioned on the fiber of `ω`.  It is
defined for a supported `ω`, whose fiber has positive mass because it contains `ω`. -/
noncomputable def conditional (Ψ : GeneralizedXorGame.{u} p ι) (I : Finset ι)
    (ω : (∀ i, Ψ.Q i) × ZMod p) (hω : ω ∈ Ψ.μ.support) : PMF ((∀ i, Ψ.Q i) × ZMod p) :=
  Ψ.μ.filter (Ψ.fiber I ω) ⟨ω, fun _ _ => rfl, hω⟩

/-- The challenge of the glued game built from two challenges of `Ψ`.  A remaining player
`(i, false)` is the first copy of `i` and gets its question from the first challenge; `(i, true)`
is the primed copy `i′` and gets its question from the second one.  The right hand side is
`t - t′`. -/
def glueChallenge (Ψ : GeneralizedXorGame.{u} p ι) (I : Finset ι)
    (ω ω' : (∀ i, Ψ.Q i) × ZMod p) :
    (∀ s : {i // i ∉ I} × Bool, Ψ.Q s.1.1) × ZMod p :=
  (fun s => if s.2 then ω'.1 s.1.1 else ω.1 s.1.1, ω.2 - ω'.2)

/-- The game `Ψ_{glue(I)}` (§3.1): sample `(x, t) ∼ μ`, then sample `(x′, t′) ∼ μ` conditioned on
`x′_i = x_i` for all `i ∈ I`.  The players of `I` are removed, every other player `i` is doubled
into `i` and `i′`, which receive `x_i` and `x′_i`, and the right hand side is `t - t′`. -/
noncomputable def glue (Ψ : GeneralizedXorGame.{u} p ι) (I : Finset ι) :
    GeneralizedXorGame.{u} p ({i // i ∉ I} × Bool) where
  Q s := Ψ.Q s.1.1
  μ := Ψ.μ.bindOnSupport fun ω hω => (Ψ.conditional I ω hω).map (Ψ.glueChallenge I ω)

end GeneralizedXorGame

/-- A generalized XOR game packaged with its finite player type, so that a sequence of games can
change the player set from one term to the next. -/
structure PackedGame (p : ℕ) where
  /-- The player set. -/
  Player : Type
  /-- The player set is finite. -/
  [fintype : Fintype Player]
  /-- The player set has decidable equality. -/
  [decEq : DecidableEq Player]
  /-- The game. -/
  game : GeneralizedXorGame.{u} p Player

attribute [instance] PackedGame.fintype PackedGame.decEq

/-- Gluing a packaged game over a set of its players. -/
noncomputable def PackedGame.glue (G : PackedGame.{u} p) (I : Finset G.Player) :
    PackedGame.{u} p where
  Player := {i // i ∉ I} × Bool
  game := G.game.glue I

end XorParallelRepetition.Exponential


