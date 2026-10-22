-- Prove2me | Definitions.Def_KMNewsvendor_kmSurv
-- name    : KMNewsvendor_kmSurv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T02:04:50.170027+00:00
-- url     : https://prove2.me/theorems/a151d1f3-f0d0-48a7-bb8e-8718a8070fe3
-- title:
--   Kaplan–Meier product-limit estimator of $P[D>d]$ from censored observations
-- statement:
--   Suppose $n$ observations $(Z_1,\delta_1),\dots,(Z_n,\delta_n)$ have been made, where $Z_i=\min\{D_i,Y_i\}$ is the observed sales in period $i$ and $\delta_i=\mathbf 1[D_i\le Y_i]$ is the **censoring indicator** ($\delta_i=1$: the demand was observed exactly; $\delta_i=0$: only $D_i>Y_i$ is known). The **Kaplan–Meier estimator** of $\bar F(d)=P[D>d]$, for an integer $d\ge0$, is
--   $$\bar F_n(d)=\prod_{k=0}^{d}\left(1-\frac{\#\{i\le n: Z_i=k,\ \delta_i=1\}}{\#\{i\le n: Z_i\ge k\}}\right),$$
--   where a factor whose denominator is $0$ is read as $1$.
--
--   This is the product-limit formula of Kaplan and Meier (1958), Eq. (2) of the source, written with the observations grouped by value. The source orders the observations by $Z$, placing uncensored observations before censored ones at equal values, and sets $\bar F_n(d)=\prod_{t: Z_{(t)}\le d}\big((n-t)/(n-t+1)\big)^{\delta_{(t)}}$ for $d\le Z_{(n)}$. Under that tie-break the $m$ uncensored observations at a value $k$ occupy consecutive positions and their factors multiply to $1-m/\#\{Z\ge k\}$, which is the grouped factor above. It is the estimator from which the KM-myopic policy computes its order.
--
--   **Formalization Note** The observations are indexed from $0$ in Lean: `kmSurv n z δ d` uses `z 0, …, z (n-1)` and `δ 0, …, δ (n-1)`, with `δ i = true` meaning uncensored. The sales `z` are real numbers, so the definition also covers real censoring levels; only integer values $k\le d$ can produce a factor different from $1$. Division by zero returns $0$ in Lean, so an empty risk set gives the factor $1$, matching Eq. (2), which has no factor there. For $d>Z_{(n)}$ the grouped product is constant, equal to its value at $Z_{(n)}$; Eq. (2) is stated only for $d\le Z_{(n)}$, and this constant continuation is the one the policy's infimum uses.
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 932, §3, Eq. (2) and the tie-breaking rule above it; grouped form as in the proof of Lemma 2, p. 935

import Mathlib

namespace KMNewsvendor

open Finset

/-- The Kaplan–Meier product-limit estimator `F̄_n(d)` of `P[D > d]` (Eq. (2), p. 932), built from
the first `n` observations `(z i, δ i)`, `i < n`, where `z i` is the observed sales
`Z = min {D, Y}` and `δ i = true` means the observation is uncensored (`D ≤ Y`). It is written in
the product-limit form grouped by value: for each integer `k ≤ d`, the factor is
`1 - #{i < n : z i = k, δ i} / #{i < n : z i ≥ k}`. With the paper's tie-break (uncensored before
censored at equal values) this equals Eq. (2) for `d ≤ Z_(n)`, and it continues Eq. (2) as a
constant beyond `Z_(n)`. When `#{z ≥ k} = 0` the factor is `1 - 0/0 = 1`. -/
noncomputable def kmSurv (n : ℕ) (z : ℕ → ℝ) (δ : ℕ → Bool) (d : ℕ) : ℝ :=
  ∏ k ∈ range (d + 1),
    (1 - (((range n).filter (fun i => z i = (k : ℝ) ∧ δ i = true)).card : ℝ) /
      (((range n).filter (fun i => (k : ℝ) ≤ z i)).card : ℝ))

end KMNewsvendor


