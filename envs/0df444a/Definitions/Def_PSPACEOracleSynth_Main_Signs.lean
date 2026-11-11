-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Signs
-- name    : PSPACEOracleSynth_Main_Signs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:34.565658+00:00
-- url     : https://prove2.me/theorems/c891534f-3f7d-4c6c-a226-3386d27aad0e
-- title:
--   $k$-wise independent unbiased signs
-- statement:
--   Finitely many random signs $(\xi_i)_{i\in I}$, $\xi_i\in\{+1,-1\}$, are described by their joint law $p$, a probability distribution on the sign patterns $\omega\in\{0,1\}^I$ with $\xi_i=(-1)^{\omega_i}$. They are **$k$-wise independent and unbiased** if every set of at most $k$ of them is uniformly distributed:
--   $$\Pr\bigl[\omega_i=a_i\text{ for all }i\in T\bigr]=2^{-|T|}\qquad\text{for all }T\subseteq I,\ |T|\le k,\ a\in\{0,1\}^I.$$
--   This is weaker than full independence; it is what makes seeds of polynomial length suffice in the proof of Lemma 3.3.
--
--   **Formalization Note.** The expectation of $F$ is $\sum_\omega p(\omega)F(\omega)$; `sgn b` is $-1$ for `true` and $+1$ for `false`.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §3.2, p. 17 (statement of Lemma 3.4)

import Mathlib

namespace PSPACEOracleSynth.Main

/-!
# `k`-wise independent unbiased signs

Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission #1740 (October 2026),
§3.2, p. 17 (Lemma 3.4).

Finitely many random signs `(ξ_i)_{i ∈ I}` are given by their joint law, a probability distribution
`p` on the sign patterns `ω : I → Bool` (`ξ_i(ω) = −1` if `ω i`, and `+1` otherwise). They are
**`k`-wise independent and unbiased** if every set of at most `k` of them is uniformly distributed:
for every `T ⊆ I` with `|T| ≤ k` and every prescribed pattern on `T`, the probability of that pattern
is `2^{−|T|}`. This is weaker than full independence when `k < |I|`.
-/

/-- The sign `ξ = (−1)^b ∈ {+1, −1}` of a bit `b`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- `p` is the joint law of `k`-wise independent unbiased signs indexed by the finite set `I`:
a probability distribution on `I → Bool` whose marginal on every set of at most `k` coordinates is
uniform. -/
def IsKWiseUniform {I : Type} [Fintype I] [DecidableEq I] (k : ℕ) (p : (I → Bool) → ℝ) : Prop :=
  (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω = 1) ∧
    ∀ T : Finset I, T.card ≤ k → ∀ a : I → Bool,
      ∑ ω ∈ Finset.univ.filter (fun ω : I → Bool => ∀ i ∈ T, ω i = a i), p ω = (1 / 2 : ℝ) ^ T.card

end PSPACEOracleSynth.Main


