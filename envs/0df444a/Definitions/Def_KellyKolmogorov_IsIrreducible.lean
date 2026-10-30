-- Prove2me | Definitions.Def_KellyKolmogorov_IsIrreducible
-- name    : KellyKolmogorov_IsIrreducible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:31.386366+00:00
-- url     : https://prove2.me/theorems/5ef37ae0-e542-4cd1-a838-ffff708cffb7
-- title:
--   Irreducible process
-- statement:
--   A process $X(t)$, $t\in\mathbb R$, with values in a countable set $\mathcal S$ is **irreducible** if every state can be reached from every other state: for all states $j\ne k$ there are a time $s$ and a step $\tau>0$ with
--   $$
--   \mathbb P\bigl(X(s)=j,\ X(s+\tau)=k\bigr)>0 .
--   $$
--
--   **Formalization Note** "$k$ can be reached from $j$" is read as a positive probability of being in $j$ at some time and in $k$ a positive time later.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, pp. 1–2 (PDF pp. 4–5), definition of an irreducible Markov process

import Mathlib

open MeasureTheory

namespace KellyKolmogorov

/-- **Irreducibility.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, pp. 1–2: a Markov process "is
irreducible if every state in `𝒮` can be reached from every other state."

For all distinct states `j ≠ k` there are a time `s` and a step `τ > 0` with
`P(X(s) = j, X(s + τ) = k) > 0`.

**Formalization Note.** "`k` can be reached from `j`" is read as: the process is in `j` at some
time and in `k` a positive time later with positive probability. -/
def IsIrreducible {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮) : Prop :=
  ∀ j k : 𝒮, j ≠ k → ∃ s τ : ℝ, 0 < τ ∧ μ ({ω | X s ω = j} ∩ {ω | X (s + τ) ω = k}) ≠ 0

end KellyKolmogorov


