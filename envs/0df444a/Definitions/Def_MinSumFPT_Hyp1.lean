-- Prove2me | Definitions.Def_MinSumFPT_Hyp1
-- name    : MinSumFPT_Hyp1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:54.727806+00:00
-- url     : https://prove2.me/theorems/542b09d9-23b6-4280-8e46-bcc7d6413d84
-- title:
--   Hypothesis 1: the estimates of Stages 2–3
-- statement:
--   Let $\sigma$ be a clustering of $A$ into clusters $C_0,\dots,C_{k-1}$ and let $\varepsilon,\alpha,\gamma>0$. **Hypothesis 1** holds for estimates $(\hat\mu_{C_i},\widehat{|C_i|},\widehat{\Delta}_{C_i})_i$ and $\widehat{\mathrm{OPT}}$ if, for every cluster $C_i$:
--
--   1. $\hat\mu_{C_i}\in A$ is an $(\varepsilon,\alpha)$-approximate center of $C_i$, i.e. satisfies (1) with $\mathrm{OPT}=\mathrm{OPT}_k(d)$;
--   2. $\widehat{|C_i|}$ $\gamma$-approximates $|C_i|$ (2);
--   3. $\widehat{\Delta}_{C_i}$ $\gamma$-approximates $\Delta_{C_i}$ (4);
--
--   and $\widehat{\mathrm{OPT}}$ $\gamma$-approximates $\mathrm{OPT}_k(d)$ (3).
--
--   Stages 2 and 3 of the algorithm enumerate such estimates. The analysis of those stages (Lemmas 13, 15, 23, 24) assumes the hypothesis holds for the enumerated values.
--
--   **Formalization Note** The estimates form a record `Estimates` indexed by the labels. The statements that use the hypothesis assume every cluster is nonempty, since (13) divides by $\widehat{|C_i|}$ and $\Delta_{C_i}$ divides by $|C_i|$.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Hypothesis 1, p.10

import Mathlib
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_IsCovered
import Definitions.Def_MinSumFPT_ApproxDelta

namespace MinSumFPT

/-!
# Hypothesis 1

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Hypothesis 1, p.10: for every C ∈ 𝒞 an approximate center µ̂_C satisfying (1), an
approximation |Ĉ| of |C| satisfying (2), an approximation Δ̂_C of Δ_C satisfying (4), and an
approximate value ÔPT satisfying (3).

This module bundles the estimate record `Estimates` and `Hyp1`.

**Formalization Note.** The clustering is a labelling `σ : Fin n → Fin k`; the data are functions
of the label: `muHat i : Fin n` (a point of A), `chat i` (|Ĉ_i|), `deltaHat i` (Δ̂_{C_i}), and the
real `optHat` (ÔPT). OPT is `optCost d k`, the optimum of the instance, and (1) is used with the
parameter `α` (the paper uses α = 5 from §2.4 on). The statements using `Hyp1` assume every cluster
nonempty (µ_C, Δ_C and the threshold (13) divide by |C| and |Ĉ|). -/

/-- The estimates of Stages 2–3 for a clustering into `k` clusters: for every label `i` an
approximate center `muHat i ∈ A` (µ̂_{C_i}), a size estimate `chat i` (|Ĉ_i|), a cost-parameter
estimate `deltaHat i` (Δ̂_{C_i}), and an estimate `optHat` (ÔPT) of OPT. -/
structure Estimates (n k : ℕ) where
  /-- µ̂_{C_i}, a point of `A`. -/
  muHat : Fin k → Fin n
  /-- |Ĉ_i|. -/
  chat : Fin k → ℝ
  /-- Δ̂_{C_i}. -/
  deltaHat : Fin k → ℝ
  /-- ÔPT. -/
  optHat : ℝ

/-- Hypothesis 1 for the labelling `σ` with parameters `ε, α, γ` and the estimates `E`. -/
def Hyp1 {n k : ℕ} (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) (ε α γ : ℝ)
    (E : Estimates n k) : Prop :=
  (∀ i, IsApproxCenter d (optCost d k) k ε α (clusterOf σ i) (E.muHat i) ∧
      GammaApprox γ (E.chat i) ((clusterOf σ i).card : ℝ) ∧
      ApproxDelta γ k (optCost d k) ((clusterOf σ i).card : ℝ) (E.deltaHat i)
        (Delta d (clusterOf σ i))) ∧
    GammaApprox γ E.optHat (optCost d k)

end MinSumFPT


