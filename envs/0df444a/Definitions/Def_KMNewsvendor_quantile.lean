-- Prove2me | Definitions.Def_KMNewsvendor_quantile
-- name    : KMNewsvendor_quantile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T01:47:16.09149+00:00
-- url     : https://prove2.me/theorems/edb1599b-627f-49a7-98c5-5e8b57286e6d
-- title:
--   Survival function, critical ratio, newsvendor quantile $\psi(r)$ and upper quantile $\tilde\psi(r)$
-- statement:
--   Let $D$ be a nonnegative integer-valued random variable on a probability space $(\Omega,\mathcal F,\mu)$. Its **complementary CDF** (survival function) is
--   $$\bar F(d)=P[D>d],\qquad d\in\mathbb N .$$
--   For a per-unit overage cost $h>0$ and a per-unit lost-sales penalty $b>0$ the **critical ratio** is $r^*=b/(b+h)\in(0,1)$.
--
--   For $r\in(0,1)$ the **$r$-quantile** and the **upper $r$-quantile** of $D$ are
--   $$\psi(r)=\inf\{d:\bar F(d)\le 1-r\},\qquad \tilde\psi(r)=\inf\{d:\bar F(d)<1-r\}.$$
--   The **newsvendor quantile** is $\psi^*=\psi(r^*)$, and $\tilde\psi^*=\tilde\psi(r^*)$. Ordering $\psi^*$ units minimises the expected newsvendor cost $h\,E(y-D)^+ + b\,E(D-y)^+$; when $\bar F(\psi^*)=1-r^*$ every integer in $[\psi^*,\tilde\psi^*]$ is optimal as well. Every statement of this mission is about convergence of an adaptive policy to $\psi^*$ or to the set $\{\psi^*,\tilde\psi^*\}$.
--
--   **Formalization Note** `survival μ X d` is $\mu\{X>d\}$ converted to a real number. Since $D$ is integer-valued, $\bar F$ is constant on each $[k,k+1)$, so the infimum over real $d$ is attained at an integer and equals the least natural number with the property; the Lean definitions use `sInf` on $\mathbb N$. For $r<1$ and a probability measure the set is nonempty because $\bar F(d)\to0$; the junk value `sInf ∅ = 0` is reached only for $r\ge1$, which no statement of the mission uses ($r^*=b/(b+h)$ with $b,h>0$).
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 931, Eq. (1) (psi, r* = b/(b+h), F-bar); p. 935 (upper r-quantile)

import Mathlib

namespace KMNewsvendor

open MeasureTheory

/-- The complementary CDF (CCDF) of a nonnegative integer-valued random variable `X` under `μ`:
`survival μ X d = F̄(d) = P[X > d]` (Huh et al. 2011, p. 931). -/
noncomputable def survival {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ)
    (d : ℕ) : ℝ :=
  (μ {ω | d < X ω}).toReal

/-- The critical ratio `r* = b / (b + h)` of the newsvendor problem with per-unit lost-sales
penalty `b` and per-unit overage cost `h` (p. 931). -/
noncomputable def critRatio (b h : ℝ) : ℝ :=
  b / (b + h)

/-- The `r`-quantile `ψ(r) = inf {d : F̄(d) ≤ 1 - r}` of Eq. (1), p. 931. For an `ℕ`-valued `X`
the CCDF is constant on `[k, k+1)`, so the infimum over real `d` is the least natural number with
the property. For `r < 1` and a probability measure the set is nonempty (`F̄(d) → 0`); `sInf ∅ = 0`
is only reached outside that range. -/
noncomputable def quantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ)
    (r : ℝ) : ℕ :=
  sInf {d : ℕ | survival μ X d ≤ 1 - r}

/-- The upper `r`-quantile `ψ̃(r) = inf {d : F̄(d) < 1 - r}` (p. 935), the least natural number
with the property; the set is nonempty for `r < 1` under a probability measure. -/
noncomputable def upperQuantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ)
    (r : ℝ) : ℕ :=
  sInf {d : ℕ | survival μ X d < 1 - r}

end KMNewsvendor


