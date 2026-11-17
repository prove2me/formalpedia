-- Prove2me | Definitions.Def_MultitaskContracts_Supplement_clippedContract
-- name    : MultitaskContracts_Supplement_clippedContract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:05:23.88966+00:00
-- url     : https://prove2.me/theorems/d9525fa2-6013-45af-a2f5-0a072d674757
-- title:
--   The clipped contract $\hat t$ of eq. (23), with $\mu$, $\sigma$, $L$
-- statement:
--   Let $I$ be an instance of the multitask model on a finite task set $K$ with parameters $0\le q_k<p_k\le1$ and costs $c_k>0$, and let $t_{\mathrm{Sep}}(Y)=\sum_{k\in Y}c_k/(p_k-q_k)$ be the separable contract of Lemma 15. Put
--   $$\mu=\sum_{k\in K}p_k\frac{c_k}{p_k-q_k},\qquad \sigma=\Bigl(\sum_{k\in K}\Bigl(\frac{c_k}{p_k-q_k}\Bigr)^2p_k(1-p_k)\Bigr)^{1/2},$$
--   $$L=\max\Bigl\{c(K),\ \max_{k\in K}\frac{c_k}{p_k-q_k},\ 2\sigma\Bigr\}.$$
--   For independent tasks, $\mu$ and $\sigma^2$ are the mean and the variance of $t_{\mathrm{Sep}}(Y)$ under full effort. The **clipped contract** is
--   $$\hat t(Y)\;=\;\frac54\,\min\Bigl\{8L,\ \max\Bigl\{0,\ t_{\mathrm{Sep}}(Y)-\mu+\tfrac{11}{2}L\Bigr\}\Bigr\}.\tag{23}$$
--   It pays nothing below the window $[\mu-\tfrac{11}{2}L,\ \mu+\tfrac52L]$, $10L$ above it, and $\tfrac54t_{\mathrm{Sep}}$ plus a constant inside it.
--
--   The contract is the explicit witness of Theorem 6, the $10$-approximation for Min-Budget. Every ingredient is a single sum over the tasks, so $\hat t$ is computed and evaluated in one pass.
--
--   **Formalization Note** $\mu$, $\sigma$ and $L$ are the helper definitions `clipMean`, `clipSigma` and `clipL`. The inner maximum over tasks is the real `⨆ k`, a true maximum over the finite task set; for $K=\emptyset$ it is $0$, which does not change $L$ because $c(K)\ge0$.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), proof of Theorem 6: µ, σ², L on p.36 (PDF p.38), eq. (23) on p.37 (PDF p.39)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_Instance_tSep

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `µ := ∑_k p_k c_k/(p_k − q_k)`, the mean of `t_Sep(Y)` under full effort for independent
tasks (proof of Theorem 6, p.36, PDF 38). -/
noncomputable def clipMean (I : Instance K) : ℝ :=
  ∑ k, I.p k * (I.c k / (I.p k - I.q k))

/-- `σ := √(∑_k (c_k/(p_k − q_k))² p_k(1 − p_k))`, the standard deviation of `t_Sep(Y)` under full
effort for independent tasks (proof of Theorem 6, p.36, PDF 38). -/
noncomputable def clipSigma (I : Instance K) : ℝ :=
  Real.sqrt (∑ k, (I.c k / (I.p k - I.q k)) ^ 2 * (I.p k * (1 - I.p k)))

/-- `L := max{c(K), max_k c_k/(p_k − q_k), 2σ}` (proof of Theorem 6, p.36, PDF 38).

**Formalization Note.** `max_k` is the real `⨆ k`, the maximum over the finite set of tasks; for
`K = ∅` it is `0`, which leaves `L` unchanged because `c(K) ≥ 0`. -/
noncomputable def clipL (I : Instance K) : ℝ :=
  max (I.cost Finset.univ) (max (⨆ k, I.c k / (I.p k - I.q k)) (2 * clipSigma I))

/-- **The clipped contract `ˆt` of Eq. (23)** (proof of Theorem 6, p.37, PDF 39): the separable
contract `t_Sep` clipped to the window `[µ − 11L/2, µ + 5L/2]` and scaled by `5/4`,
`ˆt(Y) = (5/4)·min{8L, max{0, t_Sep(Y) − µ + 11L/2}}`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), proof of Theorem 6, eq. (23), p.37
(PDF 39), with `µ`, `σ`, `L` from p.36 (PDF 38).

**Formalization Note.** `t_Sep` is the published `Instance.tSep`
(`t_Sep(Y) = ∑_{k∈Y} c_k/(p_k − q_k)`). `µ`, `σ`, `L` are the helpers `clipMean`, `clipSigma`,
`clipL`, computed from the parameters `p, q, c` by single sums over the tasks, as on p.36. -/
noncomputable def clippedContract (I : Instance K) (Y : Finset K) : ℝ :=
  (5 / 4 : ℝ) * min (8 * clipL I) (max 0 (I.tSep Y - clipMean I + 11 / 2 * clipL I))

end MultitaskContracts.Supplement


