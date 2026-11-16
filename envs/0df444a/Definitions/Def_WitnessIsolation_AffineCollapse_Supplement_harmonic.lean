-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_harmonic
-- name    : WitnessIsolation_AffineCollapse_Supplement_harmonic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:05.691306+00:00
-- url     : https://prove2.me/theorems/dec93215-4c0f-4c8a-9c07-d4bc73b29f12
-- title:
--   The harmonic subset law
-- statement:
--   For $M\ge1$ let $H_M=\sum_{k=1}^M 1/k$ be the $M$-th harmonic number (Mathlib's `harmonic`, cast to $\mathbb R$). The **harmonic subset law** on subsets $A\subseteq[M]$ draws a size $k\in\{1,\dots,M\}$ with probability $1/(kH_M)$ and then a uniform $k$-subset. It gives each nonempty $A$ with $|A|=k$ the mass
--   $$\frac{1}{k\,H_M\binom{M}{k}},$$
--   and the empty set mass $0$.
--
--   This is the private-set distribution of the harmonic pool in Lemma 4.1 and the proof of Theorem 1.3. The definition records only the raw masses; that they sum to $1$ is part of the theorem `harmonic_equalizer`.
--
--   **Formalization Note** $[M]$ is represented by `Fin M` (zero-based). No samplability restriction is imposed.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 8, PDF p. 9, Lemma 4.1 (the two-stage distribution); harmonic number H_M defined on p. 2, PDF p. 3

import Definitions.Def_WitnessIsolation_AffineCollapse_probability

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- The two-stage harmonic law of Lemma 4.1 (printed p. 8 / PDF p. 9), as raw masses:
a nonempty `A ⊆ [M]` of size `k` gets `1/(k · H_M · (M choose k))`, the empty set gets `0`.
`H_M` is Mathlib's `harmonic M = ∑_{k=1}^M 1/k`, cast to `ℝ`. Normalization is a theorem
clause of `harmonic_equalizer`, not an assumption stored here. -/
def harmonicMass (M : ℕ) (A : Finset (Fin M)) : ℝ :=
  if A.card = 0 then 0 else
    1 / ((A.card : ℝ) * (harmonic M : ℝ) * (Nat.choose M A.card : ℝ))

end WitnessIsolation.AffineCollapse.Supplement


