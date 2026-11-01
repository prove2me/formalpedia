-- Prove2me | Definitions.Def_RecoveringBandits_F
-- name    : RecoveringBandits_F
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:26.066666+00:00
-- url     : https://prove2.me/theorems/d1c08a21-4d72-4815-a958-6450c164af34
-- title:
--   Per-arm values $F_{i,T}(x)$ (problem (2)) and $F_i(x)=\limsup_T F_{i,T}(x)$
-- statement:
--   For one arm with recovery function $r$, a horizon $T\ge1$ and a pull budget $x$, let
--
--   $$F_{i,T}(x)=\max\ \frac1T\sum_{j=1}^{J}r(s_j-s_{j-1})\quad\text{s.t. } J\le xT,\ 0=s_0<s_1<\dots<s_J\le T,$$
--
--   the optimal average reward when the arm is pulled at most $xT$ times (problem (2)). The **long-run value** of the arm is
--
--   $$F_i(x)=\limsup_{T\to\infty}F_{i,T}(x).$$
--
--   These per-arm values are the building blocks of the upper bound $\mathrm{UB}_R[K]$.
--
--   **Formalization Note** The limsup is taken over $T\ge1$. For an admissible arm and $x\ge0$, every $F_{i,T}(x)$ lies in $[0,R_{\max}]$, so the sequence is bounded and Lean's `Filter.limsup` is the real limsup. $F_i$ is defined by the optimization, never by the closed form of Lemma 1. Applied to the concave envelope $R^{cc}_i$, $F_{i,T}$ is the value $F^{cc}_{i,T}$ of problem (EC.1).
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.1, problem (2), p.11; (EC.1), p.ec1 (PDF p.33)

import Mathlib
import Definitions.Def_RecoveringBandits_schedReward

namespace RecoveringBandits

/-- **`F_{i,T}(x)`, the value of problem (2)** (arXiv:2106.14813v2, §4.1, (2), p.11):
`max (1/T) ∑_{j=1}^J r(s_j − s_{j−1})` subject to `J ≤ x·T` and `0 = s_0 < s_1 < ⋯ < s_J ≤ T`,
i.e. the optimal average reward of one arm pulled at most `x·T` times in `[1, T]`.

**Formalization Note.** The pull times are the finite set `S ⊆ [1, T]` and `J = #S`. For `x ≥ 0`
the feasible set is finite and contains `S = ∅`, so this `sSup` is the maximum. Every statement
using `FT` takes `T ≥ 1` (the paper's `T ≥ 1`), so the division by `T` never divides by `0`.
Applied to the concave envelope `Rcc r` it is the paper's `F^cc_{i,T}` of (EC.1), p.ec1. -/
noncomputable def FT (r : ℕ → ℝ) (T : ℕ) (x : ℝ) : ℝ :=
  sSup ((fun S : Finset ℕ => schedReward r S / T) ''
    {S | S ⊆ Finset.Icc 1 T ∧ (S.card : ℝ) ≤ x * T})

/-- **`F_i(x) = limsup_T F_{i,T}(x)`** (arXiv:2106.14813v2, §4.1, p.11), "the point-wise long-run
optimal average reward of pulling arm `i` under `x`".

**Formalization Note.** The limsup is taken over `T ≥ 1` (the sequence `T ↦ F_{i,T+1}(x)`), so
`T = 0` never enters. For an admissible arm (`ArmAdmissible r Rmax`) and `x ≥ 0`, every
`F_{i,T}(x)` lies in `[0, Rmax]` (each gap earns at most `Rmax` and there are at most `T` pulls),
so the sequence is bounded and `Filter.limsup` is the real limsup. `F` is never replaced by the
closed form of Lemma 1. -/
noncomputable def F (r : ℕ → ℝ) (x : ℝ) : ℝ :=
  Filter.limsup (fun T : ℕ => FT r (T + 1) x) Filter.atTop

end RecoveringBandits


