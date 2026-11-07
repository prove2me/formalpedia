-- Prove2me | Definitions.Def_FixedPriceTrade_IsHardPair
-- name    : FixedPriceTrade_IsHardPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:46.389311+00:00
-- url     : https://prove2.me/theorems/beb18350-a8c9-43bf-8096-cf48a6c7d85c
-- title:
--   The bounded hard pair of Lemma 9.2
-- statement:
--   Let $d>0$ and $H:[0,1]\to[0,1]$ with $\eta=H(1)>0$, and $R_\eta=1+d/\eta$. Put
--   $$
--   L(s)=d+\int_s^1H(u)\,du,\qquad T(s)=\int_0^sL(u)^{-2}du,\qquad F_s(s)=d\big(L(s)^{-1}-H(s)T(s)\big)\quad(0\le s<1).
--   $$
--   A pair of laws $(\mu_s,\mu_b)$ is the **hard pair** of $(d,H)$ when
--
--   1. the buyer is almost surely nonnegative with survival function $\Pr(V_b>s)=H(s)$ on $[0,1]$, $=\eta$ on $[1,R_\eta)$, and $=0$ at and above $R_\eta$ (so it has an atom $1-H(0)$ at zero and an atom $\eta$ at $R_\eta$);
--   2. the seller is almost surely nonnegative with CDF $F_s$ on $[0,1)$ and all its mass in $[0,1]$ (the remaining mass is an atom at one).
--
--   These pairs approach the welfare constant (Lemma 9.2, Theorem A).
--
--   **Formalization Note** A probability law on $\mathbb R$ is determined by its CDF, so the predicate pins both laws; measures take values in $[0,\infty]$, hence the conversions of the real values. The hypotheses of Lemma 9.2 on $H$ are stated in the theorems that use it.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 9.2, (42), p.21

import Mathlib

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- The tail integral `L(s) = d + ∫_s^1 H(u) du` ((42), p.21). -/
noncomputable def hardL (d : ℝ) (H : ℝ → ℝ) (s : ℝ) : ℝ := d + ∫ u in s..(1 : ℝ), H u

/-- The auxiliary integral `T(s) = ∫_0^s L(u)^{−2} du` ((42), p.21). -/
noncomputable def hardT (d : ℝ) (H : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, 1 / hardL d H u ^ 2

/-- The seller CDF `F_s(s) = d (L(s)^{−1} − H(s) T(s))` on `0 ≤ s < 1` ((42), p.21). -/
noncomputable def hardFs (d : ℝ) (H : ℝ → ℝ) (s : ℝ) : ℝ :=
  d * (1 / hardL d H s - H s * hardT d H s)

/-- `R_η = 1 + d/η` (Lemma 9.2, p.21). -/
noncomputable def Reta (d η : ℝ) : ℝ := 1 + d / η

/-- **The bounded hard pair of Lemma 9.2** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
Lemma 9.2, (42), p.21. With `η = H(1)` and `R_η = 1 + d/η`, `μb` and `μs` are the probability laws
on `ℝ` such that

1. the buyer is a.s. nonnegative and has survival function `μb(V_b > s) = H(s)` on `[0, 1]`,
   `= η` on `[1, R_η)`, and `= 0` at and above `R_η` (so an atom `1 − H(0)` at zero and an atom
   `η` at `R_η`);
2. the seller is a.s. nonnegative, has CDF `F_s(s) = d(L(s)^{−1} − H(s)T(s))` on `[0, 1)`, and
   `μs(V_s ≤ 1) = 1` (the completion by an atom at one).

**Formalization Note.** A probability measure on `ℝ` is determined by its CDF, so these
conditions pin `μs`, `μb` uniquely; the predicate has no freedom. Measures take values in
`ℝ≥0∞`, hence the `ENNReal.ofReal`. The hypotheses on `H` (continuous, nonincreasing, values in
`[0,1]`, `H(1) > 0`) are the lemma's and are stated where it is used. -/
def IsHardPair (d : ℝ) (H : ℝ → ℝ) (μs μb : Measure ℝ) : Prop :=
  IsProbabilityMeasure μs ∧ IsProbabilityMeasure μb ∧
    μb (Iio 0) = 0 ∧
    (∀ s ∈ Icc (0 : ℝ) 1, μb (Ioi s) = ENNReal.ofReal (H s)) ∧
    (∀ s, 1 ≤ s → s < Reta d (H 1) → μb (Ioi s) = ENNReal.ofReal (H 1)) ∧
    (∀ s, Reta d (H 1) ≤ s → μb (Ioi s) = 0) ∧
    μs (Iio 0) = 0 ∧
    (∀ s ∈ Ico (0 : ℝ) 1, μs (Iic s) = ENNReal.ofReal (hardFs d H s)) ∧
    μs (Iic 1) = 1

end FixedPriceTrade


