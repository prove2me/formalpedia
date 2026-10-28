-- Prove2me | Definitions.Def_ValuePersPricing_Deviation_Model
-- name    : ValuePersPricing_Deviation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:44.855411+00:00
-- url     : https://prove2.me/theorems/7c76d2a3-302e-4b0d-91c9-89f68658e27d
-- title:
--   §2–§3.2, App. A — valuation law, single-price and personalized profit, scale, margin, coefficient of deviation, Lambert W₋₁, δL, δM, δH and the three bounds
-- statement:
--   The model of Elmachtoub, Gupta and Hamilton, *The Value of Personalized Pricing* (§2, pp. 7–8; §3, p. 8; Lemma 1, p. 9; §3.2, p. 12; Theorem 2, p. 13; Appendix A, p. ec1).
--
--   A monopolist sells a product with per-unit cost $c$. A random customer's valuation is a random variable $V\sim F$ with mean $\mu=\mathbb E[V]$. The **standing assumptions** of §2 are bundled as a market $(F,c)$: $F$ is a probability law on $\mathbb R$, $c\ge 0$, $V\ge c$ almost surely, and $\mathbb E|V|<\infty$. The purchase probability at price $p$ is
--   $$\bar F(p)=\mathbb P(V\ge p),$$
--   which includes the atom $\mathbb P(V=p)$ (footnote 1, p. 7). The optimal **single-pricing profit** and the **idealized personalized-pricing profit** are
--   $$\mathcal R_{SP}(F,c)=\sup_{p\in\mathbb R}\,(p-c)\bar F(p),\qquad \mathcal R_{PP}(F,c)=\mu-c .$$
--
--   The three statistics of §3 are the **scale** $S=\inf\{k\mid F(k)=1\}/\mu$, where $F$ is the CDF (so $S\mu$ is the essential supremum of $V$, and $S=\infty$ for unbounded support), the **margin** $M=1-c/\mu$, and the **coefficient of deviation** $D=\mathbb E|V-\mu|/(2\mu)$. The **standardized law** $F_c$ is the law of $V_c=(V-c)/(\mu-c)$, and $S_c=(S+M-1)/M$ is its scale.
--
--   $W_{-1}$ is the negative real branch of the Lambert $W$ function: for $x\in[-1/e,0)$, $W_{-1}(x)$ is the solution $w\le -1$ of $we^w=x$. The regime thresholds (p. 12) are
--   $$\delta_L=-\frac{M\log\frac{S+M-1}{M}}{W_{-1}\!\Big(\frac{-1}{e\frac{S+M-1}{M}}\Big)},\qquad \delta_M=\frac{M\log\frac{S+M-1}{M}}{1+\log\frac{S+M-1}{M}},\qquad \delta_H=\frac{M(S-1)}{S+M-1},$$
--   and the three bounds of Theorem 2 (p. 13) are
--   $$\frac{-W_{-1}\big(\frac{D/M-1}{e}\big)}{1-D/M}\ \text{(low)},\qquad \frac{M\log\frac{S+M-1}{M}}{D}\ \text{(medium)},\qquad -W_{-1}\Big(\frac{-1}{e\frac{S+M-1}{M}(1-\frac DM)}\Big)\ \text{(high)}.$$
--
--   These objects carry every statement of the mission: Theorem 2 bounds $\mathcal R_{PP}/\mathcal R_{SP}$ by the regime's bound and shows each bound is attained.
--
--   **Formalization Note** The valuation law is a measure `ν : Measure ℝ`; `Market ν c` holds the four standing assumptions. $\bar F(p)$ is `(ν (Ici p)).toReal`. $\mathcal R_{SP}$ is the real `sSup` of the profits over all real prices; it is not assumed attained, and under `Market` the set of profits is bounded above by $\mu-c$, so the supremum is the true one. The scale is the predicate `IsScale ν S`: $\nu((S\mu,\infty))=0$ and $\nu((k,\infty))>0$ for every $k<S\mu$; `Unbounded ν` is the case $S=\infty$. `lambertWm1` is defined by choice and takes the junk value $0$ outside $[-1/e,0)$; no statement of the mission evaluates it there under its hypotheses. Divisions follow Lean's $x/0=0$; the theorems add the hypotheses ($c<\mu$) under which no division by zero occurs.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), pp. 7–9, 12–13 (PDF 7–9, 12–13), §2, §3, Lemma 1, §3.2, Theorem 2; App. A, p. ec1 (PDF 33)

import Mathlib

namespace ValuePersPricing.Deviation

open MeasureTheory Set

/-- §2 standing assumptions (Elmachtoub–Gupta–Hamilton, p. 7) on the valuation law `ν` of a random
customer's valuation `V` and the per-unit cost `c`: `ν` is a probability law on `ℝ`, the cost is
nonnegative, `V ≥ c` almost surely, and `V` has a finite mean. -/
structure Market (ν : Measure ℝ) (c : ℝ) : Prop where
  isProb : IsProbabilityMeasure ν
  cost_nonneg : 0 ≤ c
  ge_cost : ∀ᵐ v ∂ν, c ≤ v
  integrable : Integrable (fun v : ℝ => v) ν

/-- The mean valuation `µ = E[V]` (p. 7). -/
noncomputable def mean (ν : Measure ℝ) : ℝ := ∫ v, v ∂ν

/-- `F̄(p) = P(V ≥ p)` (p. 7 and footnote 1): the purchase probability at price `p`, which
includes the atom `P(V = p)`. -/
noncomputable def tail (ν : Measure ℝ) (p : ℝ) : ℝ := (ν (Ici p)).toReal

/-- `R_SP(F, c) = max_p (p − c) F̄(p)` (p. 7), as the supremum over all real prices `p`. -/
noncomputable def spProfit (ν : Measure ℝ) (c : ℝ) : ℝ :=
  sSup (range fun p : ℝ => (p - c) * tail ν p)

/-- `R_PP(F, c) = µ − c` (p. 8). -/
noncomputable def ppProfit (ν : Measure ℝ) (c : ℝ) : ℝ := mean ν - c

/-- The margin `M = 1 − c/µ` (§3, p. 8). -/
noncomputable def margin (ν : Measure ℝ) (c : ℝ) : ℝ := 1 - c / mean ν

/-- The coefficient of deviation `D = E|V − µ| / (2µ)` (§3, p. 8). -/
noncomputable def coefDev (ν : Measure ℝ) : ℝ := (∫ v, |v - mean ν| ∂ν) / (2 * mean ν)

/-- `S` is the scale of `ν` (§3, p. 8): `S µ = inf {k | F(k) = 1}`, where `F` is the CDF, i.e.
`S µ` is the essential supremum of `V`: `P(V > S µ) = 0` and `P(V > k) > 0` for every `k < S µ`. -/
def IsScale (ν : Measure ℝ) (S : ℝ) : Prop :=
  ν (Ioi (S * mean ν)) = 0 ∧ ∀ k < S * mean ν, 0 < ν (Ioi k)

/-- Unbounded support, the case `S = ∞` (p. 8): `P(V > k) > 0` for every `k`. -/
def Unbounded (ν : Measure ℝ) : Prop := ∀ k : ℝ, 0 < ν (Ioi k)

/-- The standardized law `F_c` of `V_c = (V − c)/(µ − c)` (Lemma 1, p. 9). -/
noncomputable def standardize (ν : Measure ℝ) (c : ℝ) : Measure ℝ :=
  ν.map (fun v : ℝ => (v - c) / (mean ν - c))

/-- The negative real branch `W₋₁` of the Lambert W function (App. A, p. ec1): for
`x ∈ [−1/e, 0)`, the unique `w ≤ −1` with `w e^w = x`. Outside `[−1/e, 0)` there is no such `w`
and the value is the junk value `0`. -/
noncomputable def lambertWm1 (x : ℝ) : ℝ :=
  haveI := Classical.propDecidable (∃ w : ℝ, w ≤ -1 ∧ w * Real.exp w = x)
  if h : ∃ w : ℝ, w ≤ -1 ∧ w * Real.exp w = x then Classical.choose h else 0

/-- The standardized scale `S_c = (S + M − 1)/M` (Lemma 1, p. 9). -/
noncomputable def sc (M S : ℝ) : ℝ := (S + M - 1) / M

/-- `δ_L = −M log((S+M−1)/M) / W₋₁(−1/(e (S+M−1)/M))` (§3.2, p. 12). -/
noncomputable def deltaL (M S : ℝ) : ℝ :=
  -(M * Real.log (sc M S)) / lambertWm1 (-1 / (Real.exp 1 * sc M S))

/-- `δ_M = M log((S+M−1)/M) / (1 + log((S+M−1)/M))` (§3.2, p. 12). -/
noncomputable def deltaM (M S : ℝ) : ℝ :=
  M * Real.log (sc M S) / (1 + Real.log (sc M S))

/-- `δ_H = M(S − 1)/(S + M − 1)` (§3.2, p. 12). -/
noncomputable def deltaH (M S : ℝ) : ℝ := M * (S - 1) / (S + M - 1)

/-- The Low Heterogeneity bound `−W₋₁((D/M − 1)/e) / (1 − D/M)` (Theorem 2(a), p. 13). -/
noncomputable def lowBound (M D : ℝ) : ℝ :=
  -lambertWm1 ((D / M - 1) / Real.exp 1) / (1 - D / M)

/-- The Medium Heterogeneity bound `M log((S+M−1)/M) / D` (Theorem 2(b), p. 13). -/
noncomputable def medBound (M S D : ℝ) : ℝ := M * Real.log (sc M S) / D

/-- The High Heterogeneity bound `−W₋₁(−1/(e ((S+M−1)/M)(1 − D/M)))` (Theorem 2(c), p. 13). -/
noncomputable def highBound (M S D : ℝ) : ℝ :=
  -lambertWm1 (-1 / (Real.exp 1 * sc M S * (1 - D / M)))

end ValuePersPricing.Deviation


