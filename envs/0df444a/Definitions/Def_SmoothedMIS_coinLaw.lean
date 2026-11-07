-- Prove2me | Definitions.Def_SmoothedMIS_coinLaw
-- name    : SmoothedMIS_coinLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:41.720231+00:00
-- url     : https://prove2.me/theorems/cad6ed82-62b4-4a4b-8133-b3ce786810ce
-- title:
--   Independent Bernoulli coins on a finite index set
-- statement:
--   For a finite set $\alpha$ and a number $q$, the law $\mathrm{Coin}_\alpha(q)$ is the product measure on $\{\text{true},\text{false}\}^\alpha$ under which the coins $(\omega_x)_{x\in\alpha}$ are independent and each equals true with probability $q$.
--
--   It models the random edges of the smoothing (each vertex pair independently with probability $p$), the Erdős–Rényi graph $G(N,q)$, the mark coins $\kappa_{uv}$ of the analysis (p.25), and the random sample of Lemma 3.5.
--
--   **Formalization Note** The probability is clamped to $[0,1]$, i.e. $\max(0,\min(1,q))$ is used, so the law is a probability measure for every real $q$; for $q\in[0,1]$ the clamp does nothing.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §2, p.9 (random edges) and p.10 ($G(N,q)$); §4.2.1, p.25 (coins $\kappa_{uv}$) (PDF pp.11, 12, 27)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SmoothedMIS

/-- A real number clamped to `[0, 1]`, as a point of `unitInterval`. -/
noncomputable def clampProb (q : ℝ) : unitInterval :=
  ⟨max 0 (min 1 q), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- **Independent Bernoulli coins.** `coinLaw α q` is the law of a family `(ω x)_{x ∈ α}` of
independent coins with `P[ω x = true] = q`, the product measure on `α → Bool` (Dey, Dufoulon,
Moses Jr., Pandurangan, *Smoothed Analysis for Distributed MIS* (manuscript, sha256
dc2131db…), §2, p.9 and p.10: "every pair of vertices is an edge independently with
probability q"; p.25: the mark coins `κ_uv`).

**Formalization Note** The success probability is clamped to `[0, 1]`
(`clampProb q = max 0 (min 1 q)`), so the law is a probability measure for every real `q`;
for `q ∈ [0, 1]` the clamp is the identity. `true` is the outcome of probability `q`. -/
noncomputable def coinLaw (α : Type) [Fintype α] (q : ℝ) : Measure (α → Bool) :=
  Measure.pi fun _ => bernoulliMeasure true false (clampProb q)

end SmoothedMIS


