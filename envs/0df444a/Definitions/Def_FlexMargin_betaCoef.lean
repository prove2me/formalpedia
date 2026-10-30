-- Prove2me | Definitions.Def_FlexMargin_betaCoef
-- name    : FlexMargin_betaCoef
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:37:48.312697+00:00
-- url     : https://prove2.me/theorems/addfd305-8ef4-41b4-a970-5266db0e4d28
-- title:
--   Margin differences $\beta_{tr}=P_t-P_r$
-- statement:
--   For margins $P_1<\dots<P_T$ and the convention $P_0\equiv0$, set
--
--   $$
--   \beta_{tr}=P_t-P_r,\qquad 1\le t\le T,\ 0\le r\le t .
--   $$
--
--   So $\beta_{t0}=P_t$ and $\beta_{tt}=0$. By Lemma 1 these are the values an optimal product price $y_i$ of a product with margin $P_t$ can take; they are the coefficients of the DMGI (4).
--
--   **Formalization Note** Categories are 0-based: the Lean category $t$ is the paper's $t+1$, and the level $r$ is a natural number with $P_0=0$; levels beyond $T$ never occur.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.1, p. 17

import Mathlib

namespace FlexMargin

/-- **The margin differences `β_{tr} = P_t − P_r` (with `P_0 ≡ 0`).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.1, p. 17: "For each 1 ≤ t ≤ T, define βtr := Pt − Pr for each 0 ≤ r ≤ t, where P0 ≡ 0."

The margins are `P : Fin T → ℝ`, 0-based: the paper's `P_t` (`t = 1, …, T`) is `P ⟨t-1, _⟩`. The
paper's level `r ∈ {0, …, t}` is kept as a natural number. `betaCoef P t r` is `P t − P̂ r`, where
`P̂ 0 = 0` and `P̂ r = P ⟨r-1, _⟩` for `1 ≤ r ≤ T`. So for the 0-based category `t` (the paper's
`t + 1`), `betaCoef P t 0 = P t` is the paper's `β_{t+1,0}`, `betaCoef P t r` (`1 ≤ r ≤ t + 1`) is the
paper's `β_{t+1,r} = P_{t+1} − P_r`, and `betaCoef P t (t+1) = 0` is the paper's `β_{tt} = 0`.

**Formalization Note.** For `r > T` the definition uses `P̂ r = 0`; such levels never occur,
because every user restricts the level of a product of category `t` to `r ≤ t + 1 ≤ T`.
For two categories `P = ![P_L, P_H]`: `β_{10} = P_L`, `β_{20} = P_H`, `β_{21} = P_H − P_L` are
`betaCoef P 0 0`, `betaCoef P 1 0`, `betaCoef P 1 1` (checked in the verification file). -/
def betaCoef {T : ℕ} (P : Fin T → ℝ) (t : Fin T) (r : ℕ) : ℝ :=
  P t - if h : 0 < r ∧ r ≤ T then P ⟨r - 1, by omega⟩ else 0

end FlexMargin


