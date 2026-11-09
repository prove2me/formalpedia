-- Prove2me | Definitions.Def_XorParallelRepetition_Exponential_Games
-- name    : XorParallelRepetition_Exponential_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:00:16.957004+00:00
-- url     : https://prove2.me/theorems/e892bfc3-0765-4a2a-8e88-068a4afa942f
-- title:
--   §1 — one-round games, value and $n$-fold repetition
-- statement:
--   A one-round game with player set $\iota$ consists of a question set $\Sigma_i$ and an answer set $A_i$ for each player, a discrete joint law of the question tuple $(x_i)_{i\in\iota}$ and of a private verifier coin $c$, and a verifier predicate $V(x,c,a)$. The verifier samples $(x,c)$, sends only $x_i$ to player $i$, receives $a_i$, and accepts exactly when $V(x,c,a)$ holds. The games of §1 of the source have a trivial coin; the coin carries the sampled right hand side of Definition 2.1.
--
--   A deterministic local strategy is a family of arbitrary functions $S_i:\Sigma_i\to A_i$. Its winning probability is the probability that the verifier accepts, and the value is
--
--   $$
--   \operatorname{val}(G)=\sup_{S}\ \Pr_{(x,c)}\bigl[V\bigl(x,c,(S_i(x_i))_i\bigr)\bigr],
--   $$
--
--   the supremum running over **all** such strategies.
--
--   The $n$-fold repeated game $G^{\otimes n}$ draws $n$ independent samples of the joint law, keeping every correlation between players inside one sample. Player $i$ receives its whole block $x_i\in\Sigma_i^n$ and answers with a block in $A_i^n$, which may depend on the whole block. The verifier accepts exactly when $V$ holds in every coordinate. For $n=0$ the verifier always accepts.
--
--   These objects are the common interface of every statement of the mission: the value of a repeated game is the value of an honest game, not a product of single-copy values.
--
--   **Formalization Note** `iidPMF μ n` is built by recursion from `PMF.bind`. The supremum is taken in $[0,\infty]$, where every term is at most $1$, and then read as a real number, so no default value of a real supremum arises.
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), §1, printed pp. 1–2, PDF pp. 1–2

import Mathlib

open scoped ENNReal

/-!
# One-round multi-player games, their value and their parallel repetition

Source: Braverman and Minzer, *Parallel Repetition for k-Player XOR Games*, STOC 2027 submission
#195, §1, printed/PDF pp. 1–2.

A game has a finite-or-not player set `ι`, question types, answer types, a discrete joint law on
question tuples and a verifier predicate.  The law also samples a private verifier coin, which no
player sees; the games of §1 are the case of a trivial coin, and the generalized XOR games of
Definition 2.1 use the coin for the sampled right hand side.
-/

namespace XorParallelRepetition.Exponential

universe u v w

/-- `iidPMF μ n` is the law of `n` independent samples of `μ`, as a function `Fin n → α`:
the first coordinate is drawn from `μ` and the others from `iidPMF μ (n - 1)`, independently.
For `n = 0` it is the point mass on the unique empty tuple. -/
noncomputable def iidPMF {α : Type u} (μ : PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure Fin.elim0
  | n + 1 => μ.bind fun a => (iidPMF μ n).map fun s => Fin.cons a s

/-- A one-round game with players `ι` (§1, p. 1): question types `Question i`, answer types
`Answer i`, a joint law of the question tuple and of a private verifier coin, and the verifier's
acceptance predicate on questions, coin and answers. -/
structure Game (ι : Type) where
  /-- The question set of each player. -/
  Question : ι → Type u
  /-- The answer set of each player. -/
  Answer : ι → Type v
  /-- The private verifier randomness, sampled jointly with the questions. -/
  Coin : Type w
  /-- The joint law of the questions and the coin. -/
  law : PMF ((∀ i, Question i) × Coin)
  /-- The verifier's predicate. -/
  accepts : (∀ i, Question i) → Coin → (∀ i, Answer i) → Prop

namespace Game

variable {ι : Type}

/-- A deterministic local strategy: each player answers as a function of its own question only. -/
abbrev Strategy (G : Game.{u, v, w} ι) : Type (max u v) :=
  ∀ i, G.Question i → G.Answer i

/-- The probability that the verifier accepts when the players use the strategy `S`. -/
noncomputable def winProb (G : Game.{u, v, w} ι) (S : G.Strategy) : ℝ≥0∞ :=
  G.law.toOuterMeasure {ω | G.accepts ω.1 ω.2 fun i => S i (ω.1 i)}

/-- The value `val(G)`: the supremum of the acceptance probability over **all** deterministic
local strategies.  The supremum is taken in `[0, ∞]`, where each term is at most `1`, and then
read as a real number. -/
noncomputable def val (G : Game.{u, v, w} ι) : ℝ :=
  (⨆ S : G.Strategy, G.winProb S).toReal

/-- The `n`-fold repeated game `G^{⊗n}` (§1, p. 2).  The verifier draws `n` independent samples
of the joint law, keeping every correlation inside one sample; player `i` receives its whole
block of `n` questions and answers with a block of `n` answers, which may depend on the whole
block; the verifier accepts exactly when the predicate of `G` holds in **every** coordinate. -/
noncomputable def rep (G : Game.{u, v, w} ι) (n : ℕ) : Game.{u, v, w} ι where
  Question i := Fin n → G.Question i
  Answer i := Fin n → G.Answer i
  Coin := Fin n → G.Coin
  law := (iidPMF G.law n).map fun s => (fun i j => (s j).1 i, fun j => (s j).2)
  accepts x c a := ∀ j, G.accepts (fun i => x i j) (c j) (fun i => a i j)

end Game

end XorParallelRepetition.Exponential


