-- Prove2me | Definitions.Def_MaxObjBandit_ucbIndex
-- name    : MaxObjBandit_ucbIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:58.703877+00:00
-- url     : https://prove2.me/theorems/a58973a3-edce-4c7b-af2a-3c48351cd6ca
-- title:
--   ADA-ETC's $\tau$, frozen mean, $\mathrm{UCB}$ (2), $\mathrm{LCB}$ (3) and the index deficit $\Delta$
-- statement:
--   Fix $K$ arms and a horizon $T$, and let
--   $$
--   \tau=\Big\lceil \frac{T^{2/3}}{K^{2/3}}\Big\rceil .
--   $$
--   For a reward sequence $U_1,U_2,\dots$ of one arm and $n\ge1$, the **frozen empirical mean** is $\bar\mu_n=\frac1{\min\{n,\tau\}}\sum_{s=1}^{\min\{n,\tau\}}U_s$; it does not change after $\tau$ pulls. The indices (2) and (3) are
--   $$
--   \mathrm{UCB}_n=\bar\mu_n+\sqrt{\frac4n\log\Big(\frac{T}{Kn^{3/2}}\Big)}\;\mathbb 1_{\{n<\tau\}},\qquad
--   \mathrm{LCB}_n=\bar\mu_n-\bar\mu_n\mathbb 1_{\{n<\tau\}} .
--   $$
--   For an arm with mean $\mu$, the **index deficit** of the proof of Theorem 4 is
--   $$
--   \Delta=\Big(\mu-\min_{n\le\tau}\Big(\bar\mu_n+\sqrt{\frac4n\log\Big(\frac{T}{Kn^{3/2}}\Big)}\;\mathbb 1_{\{n<\tau\}}\Big)\Big)^+ ,
--   $$
--   the largest amount by which the arm's upper confidence index falls below its mean during its first $\tau$ pulls.
--
--   These indices drive ADA-ETC, and $\Delta$ (for arm 1) is the random variable that controls its regret.
--
--   **Formalization Note** $\tau$ is written $\lceil (T/K)^{2/3}\rceil$. Reward sequences are 0-indexed (`U s` is $U_{s+1}$). For $1\le n<\tau$ the logarithm's argument exceeds $1$, so no $\log^+$ is needed in the bonus. The minimum over $n=1,\dots,\tau$ is an infimum over `Fin τ`, nonempty when $1\le K<T$.
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Algorithm 1, Eqs. (2)–(3), p.20; Appendix C.1, definition of ∆, p.72

import Mathlib
import Definitions.Def_MaxObjBandit_BanditInstance

namespace MaxObjBandit

/-- The exploration length `τ = ⌈T^{2/3}/K^{2/3}⌉` of ADA-ETC (arXiv:2006.06853v6, Algorithm 1,
line 2, p.20).

**Formalization Note** Written as `⌈(T/K)^{2/3}⌉₊`; `(T/K)^{2/3} = T^{2/3}/K^{2/3}` for `K, T > 0`. -/
noncomputable def tau (K T : ℕ) : ℕ := ⌈((T : ℝ) / K) ^ ((2 : ℝ) / 3)⌉₊

/-- The exploration bonus `√((4/n) log(T/(K n^{3/2}))) · 𝟙{n < τ}` of (2) (arXiv:2006.06853v6,
Algorithm 1, Eq. (2), p.20). The indicator multiplies the whole square root.

**Formalization Note** For `1 ≤ n < τ` one has `n^{3/2} < T/K`, so the logarithm is positive and
equals `log⁺` of its argument; no `log⁺` is used here, as on the page. -/
noncomputable def bonus (K T n : ℕ) : ℝ :=
  if n < tau K T then
    Real.sqrt (4 / (n : ℝ) * Real.log ((T : ℝ) / ((K : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2))))
  else 0

/-- The frozen empirical mean `µ̄ₙ = (1/min{n,τ}) ∑_{s=1}^{min{n,τ}} U_s` of a reward sequence after
`n ≥ 1` pulls; it stays fixed after `τ` pulls (arXiv:2006.06853v6, Algorithm 1, line 2, p.20).

**Formalization Note** The sequence is `0`-indexed: `U s` is the paper's `U_{s+1}`. -/
noncomputable def frozenMean (K T : ℕ) (U : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ s ∈ Finset.range (min n (tau K T)), U s) / ((min n (tau K T) : ℕ) : ℝ)

/-- `UCBₙ = µ̄ₙ + √((4/n) log(T/(K n^{3/2}))) 𝟙{n<τ}` of (2) (arXiv:2006.06853v6, Eq. (2), p.20). -/
noncomputable def ucbIndex (K T : ℕ) (U : ℕ → ℝ) (n : ℕ) : ℝ :=
  frozenMean K T U n + bonus K T n

/-- `LCBₙ = µ̄ₙ − µ̄ₙ 𝟙{n<τ}` of (3) (arXiv:2006.06853v6, Eq. (3), p.20). -/
noncomputable def lcbIndex (K T : ℕ) (U : ℕ → ℝ) (n : ℕ) : ℝ :=
  frozenMean K T U n - frozenMean K T U n * (if n < tau K T then 1 else 0)

/-- The index deficit `∆ = (µ − min_{n≤τ} (µ̄ₙ + √((4/n) log(T/(K n^{3/2}))) 𝟙{n<τ}))⁺` of the
proof of Theorem 4 (arXiv:2006.06853v6, Appendix C.1, p.72), for an arm with mean `µ` and reward
sequence `U` (the paper applies it to arm 1).

**Formalization Note** The minimum over `n = 1, …, τ` is `⨅ n : Fin τ` at `n + 1`; for
`1 ≤ K < T` one has `τ ≥ 1`, so it is a minimum over a nonempty finite set. -/
noncomputable def indexDeficit (K T : ℕ) (μ : ℝ) (U : ℕ → ℝ) : ℝ :=
  max 0 (μ - ⨅ n : Fin (tau K T), ucbIndex K T U ((n : ℕ) + 1))

end MaxObjBandit


