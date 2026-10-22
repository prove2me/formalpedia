-- Prove2me | Definitions.Def_KellyStochasticNetworks_EffectiveBandwidth_model
-- name    : KellyStochasticNetworks_EffectiveBandwidth_model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:09.983497+00:00
-- url     : https://prove2.me/theorems/5e15eba0-2eee-44ff-b080-1cbb91374c54
-- title:
--   Infinite-past workload and extended logarithmic queue rates
-- statement:
--   Let $P$ be a probability measure on a measurable space $\Omega$, let $J$ be a finite set of source classes, and let $X_{ji}[a,b](\omega)$ be the real workload from source $i$ of class $j$ over an interval. For natural multiplicities $n_j$, natural scale $N$, and real capacity $C$ and buffer level $B$, define
--   $$S^N[a,b]=\sum_{j\in J}\sum_{i=0}^{n_jN-1}X_{ji}[a,b],\qquad Q^N(0)=\sup_{t\ge0}\{S^N[-t,0]-CNt\},\qquad L_N=P\{Q^N(0)>BN\}.$$
--   The workload supremum takes values in the extended reals; its measurability is required when defining the overflow probability. The representative increments $X_{j0}[0,t]$ are required to be measurable when defining the rate. With $M_j(s,t)=\log\int e^{sX_{j0}[0,t]}\,dP$, define
--   $$R=\sup_{t\ge0}\inf_{s\ge0}\left\{\sum_{j\in J}n_jM_j(s,t)-s(B+Ct)\right\}.$$
--   The helper $\operatorname{scaledLog}(N,p)$ is $\log(p)/(N+1)$. The exponential integral is the nonnegative Lebesgue integral, allowing $+\infty$, and the logarithm takes zero to $-\infty$ and infinity to $+\infty$.
--
--   These definitions give the actual infinite-past queue and the candidate many-sources rate. The aggregate and workload constructions accept arbitrary real interval data. The overflow and rate definitions require a probability measure and the stated measurability; independence, stationarity, and workload structure belong to the theorem.
--
--   **Formalization Note** Source indices start at zero. Time and tilt range over nonnegative real subtypes. The product $st\alpha_j(s,t)$ is represented directly by $M_j(s,t)$, including at $s=0$ or $t=0$, so no singular division is used. With a probability measure and zero-length increments equal to zero, both boundary log MGFs vanish. The definitions do not assert stationarity, independence, or nonnegative additive increments; the goal states these explicitly. Zero multiplicities contribute zero even when a log MGF is infinite.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 134–136, 143–145 (PDF pp. 142–144, 151–153), Sections 6.1 and 6.3, Eqs. (6.4)–(6.5); DOI https://doi.org/10.1017/CBO9781139565363

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KellyStochasticNetworks.EffectiveBandwidth

noncomputable def scaledLog (N : ℕ) (p : ℝ≥0∞) : EReal :=
  (((N + 1 : ℕ) : ℝ)⁻¹ : EReal) * ENNReal.log p

noncomputable def sourceTotal {Ω J : Type*} [Fintype J]
    (X : J → ℕ → ℝ → ℝ → Ω → ℝ) (n : J → ℕ)
    (N : ℕ) (a b : ℝ) (ω : Ω) : ℝ :=
  ∑ j, ∑ i ∈ Finset.range (n j * N), X j i a b ω

noncomputable def workload {Ω J : Type*} [Fintype J]
    (X : J → ℕ → ℝ → ℝ → Ω → ℝ) (n : J → ℕ)
    (C : ℝ) (N : ℕ) (ω : Ω) : EReal :=
  ⨆ t : {t : ℝ // 0 ≤ t},
    ((sourceTotal X n N (-t.val) 0 ω - (C * N) * t.val : ℝ) : EReal)

noncomputable def overflow {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : J → ℕ → ℝ → ℝ → Ω → ℝ) (n : J → ℕ)
    (C B : ℝ) (N : ℕ) (_hQ : Measurable (workload X n C N)) : ℝ≥0∞ :=
  P {ω | ((B * N : ℝ) : EReal) < workload X n C N ω}

noncomputable def queueRate {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : J → ℕ → ℝ → ℝ → Ω → ℝ) (n : J → ℕ) (C B : ℝ)
    (_hX : ∀ j t, Measurable (X j 0 0 t)) : EReal :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ⨅ s : {s : ℝ // 0 ≤ s},
    (∑ j, (n j : EReal) * ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (s.val * X j 0 0 t.val ω)) ∂P)) -
      ((s.val * (B + C * t.val) : ℝ) : EReal)

end KellyStochasticNetworks.EffectiveBandwidth


