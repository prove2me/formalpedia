-- Prove2me | Definitions.Def_FairShares_pickValue
-- name    : FairShares_pickValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:16.162301+00:00
-- url     : https://prove2.me/theorems/3ed28743-0dec-4746-b199-437843ac1d19
-- title:
--   $x_k$: the value agent $k$ can ensure under a picking order
-- statement:
--   A **picking order** for $m$ goods and $n$ agents is a list $\omega_1,\dots,\omega_m$ with $\omega_j\in[n]$; $\omega_j$ is the agent who picks at step $j$. For a valuation $v$ and an agent $k$, $x_k$ is the maximum value that agent $k$ with valuation $v$ can ensure when the picking order is $\omega$, facing an adversary that makes all the picks $\omega_j\ne k$ to minimize her value. It is the value of the picking game (`FairShares.gameVal`) started with all goods available and $k$ holding nothing.
--
--   **Formalization Note** A picking order is `ω : Fin m → Fin n`; agents are numbered from 0.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §4.1, p.15

import Mathlib
import Definitions.Def_FairShares_gameVal

namespace FairShares

/-- **`x_k`: what agent `k` can ensure under the picking order `ω`.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §4.1, p.15: "For a setting with n agents and a set M or size m, a picking order ω is a list
ω1, ω2, . . . , ωm, with ωj ∈ [n] for each j ∈ [m]. The value ωj determines which agent picks an
item at the j-th step in the picking sequence. Fix a valuation v and a picking order ω. Let xk be
the maximum value that agent k ∈ [n] with valuation v can ensure she gets when the picking order
is ω."

A picking order is `ω : Fin m → Fin n` (`ω j` picks at step `j`); `pickValue ω v k` is the value of
the picking game (`FairShares.gameVal`) started with all items available and `k` holding nothing.

**Formalization Note.** Agents are `Fin n` (numbered from 0), steps `Fin m`; the list of pickers is
`List.ofFn ω`, which has length `m`, so every item is picked. -/
noncomputable def pickValue {m n : ℕ} (ω : Fin m → Fin n) (v : Finset (Fin m) → ℝ)
    (k : Fin n) : ℝ :=
  gameVal v k (List.ofFn ω) Finset.univ ∅

end FairShares


