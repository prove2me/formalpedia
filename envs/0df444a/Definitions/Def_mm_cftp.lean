-- Prove2me | Definitions.Def_mm_cftp
-- name    : mm_cftp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T17:45:06.387596+00:00
-- url     : https://prove2.me/theorems/d92c93c3-5007-4a2f-83a2-aaf7f05c6512
-- title:
--   Random maps and coupling from the past
-- statement:
--   This file formalizes the ingredients of coupling from the past, following Chapter 22 of Levin–Peres–Wilmer (and §1.2 for the random mapping representation).
--
--   **Random mapping representations.** A **random map** for a chain $P$ on a finite state space $V$ is a probability distribution $\nu$ on update functions $f:V\to V$ that reproduces the transition probabilities in one step:
--   $$\nu\{f:\ f(x)=y\}\;=\;P(x,y)\qquad\text{for all }x,y.$$
--   Drawing $f\sim\nu$ and applying it to the current state performs one $P$-step — simultaneously from every possible current state, which is what lets CFTP drive all trajectories with the same randomness.
--
--   **Composition from the past.** CFTP uses i.i.d. maps $f_{-1},f_{-2},\dots$ indexed by past times, composed forward from the past up to time zero:
--   $$F^0_{-t}\;=\;f_{-1}\circ f_{-2}\circ\cdots\circ f_{-t}.$$
--   The composition is encoded by a tuple $F$ of $t$ maps with $F(i)$ the map used at time $-(i+1)$, folded so that the last entry applies first — deepening the horizon prepends new randomness inside the composition while the maps near time $0$ stay fixed, the asymmetry that distinguishes running from the past from running into the future.
--
--   **Coalescence and output.** The composition has **coalesced** when $F^0_{-t}$ is a constant map — every starting state has been funneled to one common value. Two finite sums over the $t$-tuples of maps, weighted by $\prod_i\nu(F(i))$, record the algorithm's behaviour at horizon $t$: the probability that the composition has *not* yet coalesced, and the probability that it has coalesced with common value a given state $y$ (the algorithm's output law). The Propp–Wilson theorem — the goal of this mission — asserts that as $t\to\infty$ the latter tends exactly to $\pi(y)$.
--
--   **Conventions.** All randomness is finite: distributions on the finite set of update maps and products over finite tuples; the limits in the theorems are limits of explicit real sequences, with no measure-theoretic infrastructure.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 22, Sections 22.1-22.3 (and Section 1.2), pp. 287-292

import Definitions.Def_mm_mixing

/-!
Coupling from the past, following Levin–Peres–Wilmer, *Markov Chains and
Mixing Times*, Chapter 22.

The randomizing operation is a **random map**: a distribution `ν` on update
functions `f : V → V` whose one-step action reproduces the transition
matrix (`P(x,y) = ν{f : f(x) = y}`, the random mapping representation of
LPW §1.2).  CFTP runs i.i.d. maps `f_{-1}, f_{-2}, …` from the past and
outputs the common value of the composition
`F⁰_{-t} = f_{-1} ∘ f_{-2} ∘ ⋯ ∘ f_{-t}` once it is a constant map; the
composition is encoded by a tuple `F : Fin t → (V → V)` with `F i` the map
used at time `-(i+1)`.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `ν` is a **random mapping representation** of `P` (LPW §1.2 and §22.3):
a distribution on update functions with `ν{f : f(x) = y} = P(x,y)`. -/
def IsRandomMapRep (P : Matrix V V ℝ) (ν : (V → V) → ℝ) : Prop :=
  IsDist ν ∧
  ∀ x y : V, ∑ f ∈ Finset.univ.filter (fun f : V → V => f x = y), ν f = P x y

/-- The composition `F⁰_{-t} = f_{-1} ∘ ⋯ ∘ f_{-t}` of the maps used at
times `-1, …, -t` (`F i` is the map at time `-(i+1)`, so the *last* map in
the tuple is applied first; LPW §22.3). -/
def cftpCompose {t : ℕ} (F : Fin t → (V → V)) : V → V :=
  fun x => (List.ofFn F).foldr (fun f v => f v) x

/-- The probability that the CFTP composition of `t` i.i.d. maps has *not*
yet coalesced to a constant map. -/
def cftpNotCoalescedProb (ν : (V → V) → ℝ) (t : ℕ) : ℝ :=
  ∑ F : Fin t → (V → V),
    if ¬∀ x y : V, cftpCompose F x = cftpCompose F y then ∏ i, ν (F i) else 0

/-- The probability that the CFTP composition of `t` i.i.d. maps has
coalesced with common value `y`. -/
def cftpOutputProb (ν : (V → V) → ℝ) (t : ℕ) (y : V) : ℝ :=
  ∑ F : Fin t → (V → V),
    if ∀ x : V, cftpCompose F x = y then ∏ i, ν (F i) else 0

end

end MarkovMixing


