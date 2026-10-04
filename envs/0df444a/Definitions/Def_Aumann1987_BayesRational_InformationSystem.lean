-- Prove2me | Definitions.Def_Aumann1987_BayesRational_InformationSystem
-- name    : Aumann1987_BayesRational_InformationSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:39:45.422962+00:00
-- url     : https://prove2.me/theorems/87301b59-4e31-421d-9a29-b14ffd229331
-- title:
--   Information systems, conditional expectation given a partition, and Bayes rationality at a state
-- statement:
--   Fix an $n$-person game with action sets $S^i$ and payoffs $h^i$. An **information system** consists of
--
--   1. a finite set $\Omega$ of states of the world;
--   2. a common prior $p$, a probability vector on $\Omega$ (the Common Prior Assumption: all players' priors coincide);
--   3. for each player $i$, an information partition $\mathcal P^i$ of $\Omega$;
--   4. action functions $\mathbf s^i:\Omega\to S^i$, with $\mathbf s(\omega)=(\mathbf s^1(\omega),\dots,\mathbf s^n(\omega))$, such that each $\mathbf s^i$ is measurable with respect to $\mathcal P^i$, i.e. constant on every element of $\mathcal P^i$ (each player knows which action he chooses).
--
--   For a random variable $x$ on $\Omega$, $E(x\mid\mathcal P^i)(\omega)=E(x\mid P)$ where $P\in\mathcal P^i$ is the element containing $\omega$:
--   $$
--   E(x\mid\mathcal P^i)(\omega)=\frac{\sum_{\omega'\in P}p(\omega')\,x(\omega')}{\sum_{\omega'\in P}p(\omega')}.
--   $$
--   Player $i$ is **Bayes rational at $\omega$** if for every action $a\in S^i$
--   $$
--   E\big(h^i(\mathbf s)\mid\mathcal P^i\big)(\omega)\ \ge\ E\big(h^i(\mathbf s^{-i},a)\mid\mathcal P^i\big)(\omega),
--   $$
--   where $(\mathbf s^{-i},a)$ is the random $n$-tuple $\omega'\mapsto\mathbf s(\omega')$ with player $i$'s coordinate replaced by $a$: he chooses an action maximizing his expected payoff given his information.
--
--   This is the hypothesis side of Aumann's Main Theorem.
--
--   **Formalization Note.** A partition is an equivalence relation (`Setoid`) on $\Omega$. The prior need not have full support. When the cell of $\omega$ has probability $0$ the paper leaves $E(x\mid P)$ undefined; in Lean the quotient is $0/0=0$, so Bayes rationality at such a state holds vacuously — the paper's argument never uses such states. The comparison is required for every $a$, including $a=\mathbf s^i(\omega)$, where both sides agree by measurability.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, pp. 6-7 (PDF pp. 7-8), Sect. 3 items (i)-(iv), Common Prior Assumption, footnotes 7-8, Bayes rationality; p. 10 (PDF p. 11), Sect. 4d, information system

import Mathlib
import Definitions.Def_agt_games

/-!
# Aumann (1987), Sect. 3: information systems and Bayes rationality

R. J. Aumann, *Correlated Equilibrium as an Expression of Bayesian Rationality*, Econometrica 55
(1987), no. 1, 1–18, Sect. 3, pp. 6–7 (PDF pp. 7–8), and Sect. 4d, p. 10 (PDF p. 11).

Given an `n`-person game with action sets `S i` and payoffs `h : ι → (∀ i, S i) → ℝ`, the model of
Sect. 3 consists of a finite set `Ω` of states of the world, a prior on `Ω`, an information
partition `𝒫ⁱ` of `Ω` for each player, and the action functions `sⁱ : Ω → Sⁱ`, each measurable with
respect to its player's partition. Under the Common Prior Assumption (p. 7, "We will use the
following assumption") the priors coincide; the paper calls the system `(Ω, p, (𝒫ⁱ), s)` an
*information system* (Sect. 4d, p. 10). This bundle defines information systems, the conditional
expectation given a player's information, and Bayes rationality at a state.

**Formalization Note.** A partition of `Ω` is encoded as an equivalence relation (`Setoid Ω`); the
element of `𝒫ⁱ` containing `ω` is `{ω' | (P i).r ω ω'}`. The Common Prior Assumption is built in:
an information system carries a single prior `p`, shared by all players.
-/

namespace Aumann1987.BayesRational

open Finset

variable {ι : Type*} {S : ι → Type*}

/-- **Information system** (Aumann 1987, Sect. 3, items (i)–(iii) and (iv), pp. 6–7, PDF pp. 7–8,
under the Common Prior Assumption, p. 7; the name is the paper's, Sect. 4d, p. 10, PDF p. 11:
"the system consisting of `Ω`, `p`, the `𝒫ⁱ`, and `s`").

On a finite set `Ω` of states of the world (item (i); finiteness is the `[Fintype Ω]` parameter):
* `p` is the common prior, a probability vector on `Ω` (item (ii) with the Common Prior Assumption
  `p¹ = ⋯ = pⁿ = p`);
* `P i` is the information partition `𝒫ⁱ` of player `i` (item (iii));
* `s ω` is the action `n`-tuple `s(ω) = (s¹(ω), …, sⁿ(ω))` chosen at `ω` (item (iv));
* `measurable`: "each player `i` knows which action he chooses, i.e., `sⁱ` is measurable w.r.t.
  `𝒫ⁱ`" (p. 7), i.e. constant on each element of `𝒫ⁱ` (footnote 7).

**Formalization Note.** The prior is a real weight vector (`AGT.IsLottery`: nonnegative, summing
to `1`). It is not required to have full support, as the paper does not require it. -/
structure InformationSystem (Ω : Type*) [Fintype Ω] (S : ι → Type*) where
  /-- The common prior `p` on `Ω`. -/
  p : Ω → ℝ
  /-- `p` is a probability vector. -/
  isProb : AGT.IsLottery p
  /-- The information partition `𝒫ⁱ` of player `i`, as an equivalence relation on `Ω`. -/
  P : ι → Setoid Ω
  /-- The action `n`-tuple `s(ω)` chosen at the state `ω`. -/
  s : Ω → ∀ i, S i
  /-- Each `sⁱ` is measurable w.r.t. `𝒫ⁱ`: constant on each element of `𝒫ⁱ`. -/
  measurable : ∀ (i : ι) (ω ω' : Ω), (P i).r ω ω' → s ω i = s ω' i

/-- **Conditional expectation given a partition** (Aumann 1987, footnote 8, p. 7, PDF p. 8):
"if `x` is a random variable, then `E(x|𝒫ⁱ)` is defined as the r.v. whose value at a specific `ω` is
`E(x|P)`, where `P` is the event in `𝒫ⁱ` that contains `ω`." With the prior `p` and the cell
`P = {ω' | ω' ~ ω}`,
`E(x|𝒫)(ω) = (∑_{ω' ∈ P} p(ω') x(ω')) / (∑_{ω' ∈ P} p(ω'))`.

**Formalization Note.** When the cell has probability `0` the paper leaves `E(x|P)` undefined;
here Lean's convention `a / 0 = 0` makes the value `0`. Consequently every comparison of two
conditional expectations at a state of a null cell reads `0 ≤ 0` and holds, so Bayes rationality
(`IsBayesRationalAt`) imposes nothing at such states. This matches the paper, whose proof of the
Main Theorem multiplies each cell inequality by `Prob P`, so null cells never matter. Membership in
the cell uses classical decidability. -/
noncomputable def condExp {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (P : Setoid Ω) (x : Ω → ℝ)
    (ω : Ω) : ℝ :=
  open Classical in
  (∑ ω' ∈ univ.filter (fun ω' => P.r ω ω'), p ω' * x ω') /
    (∑ ω' ∈ univ.filter (fun ω' => P.r ω ω'), p ω')

/-- **Bayes rational at `ω`** (Aumann 1987, Sect. 3, p. 7, PDF p. 8): player `i` is Bayes rational
at `ω` if his expected payoff given his information, `E(hⁱ(s)|𝒫ⁱ)(ω)`, is at least as great as the
amount `E(hⁱ(s⁻ⁱ, sⁱ)|𝒫ⁱ)(ω)` that it would have been had he chosen any other action `sⁱ ∈ Sⁱ`;
here `(s⁻ⁱ, sⁱ)` is the random `n`-tuple `ω' ↦ s(ω')` with `i`'s coordinate replaced by the fixed
action `sⁱ`.

**Formalization Note.** The data are the common prior `p`, the partitions `P`, and the action
`n`-tuple `s` (for an information system `I`: `I.p`, `I.P`, `I.s`). The comparison is required for
every `a : S i`, including `a = sⁱ(ω)`; for that `a` both sides agree whenever `sⁱ` is constant on
the cell of `ω`, so this is the paper's "other than the action `sⁱ(ω)`". For the convention at
states whose cell has probability `0`, see `condExp`. -/
def IsBayesRationalAt [DecidableEq ι] {Ω : Type*} [Fintype Ω] (h : ι → (∀ i, S i) → ℝ)
    (p : Ω → ℝ) (P : ι → Setoid Ω) (s : Ω → ∀ i, S i) (i : ι) (ω : Ω) : Prop :=
  ∀ a : S i,
    condExp p (P i) (fun ω' => h i (Function.update (s ω') i a)) ω ≤
      condExp p (P i) (fun ω' => h i (s ω')) ω

end Aumann1987.BayesRational


