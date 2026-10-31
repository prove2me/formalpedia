-- Prove2me | Definitions.Def_ReviewProvision_Params
-- name    : ReviewProvision_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:40.844017+00:00
-- url     : https://prove2.me/theorems/17fb58f8-2fa4-47c7-aaec-f4529ea7f930
-- title:
--   Model parameters $\tau,\eta,\zeta,\theta,h,m$
-- statement:
--   The model is described by six real parameters:
--
--   1. $\tau>0$, the precision of the prior of the unknown quality;
--   2. $\eta>0$, the precision of the cluster preferences;
--   3. $\zeta>0$, the precision of an individual quality perception;
--   4. $\theta\in(0,1]$, the proportion of first-period buyers who leave a rating;
--   5. $h>0$, the price sensitivity of demand;
--   6. $m>0$, the mass of the second batch of customers in each cluster.
--
--   They are common knowledge and are shared by every statement of the mission.
--
--   **Formalization Note** The number $N$ of clusters is not a field: clusters are `Fin N`, and $N\ge2$ is an explicit hypothesis where it matters. The prior mean $q_p=1$ of p.9 is built into `prior`.
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), §3 and Table 1, pp.9–13

import Mathlib

namespace ReviewProvision

/-- **Model parameters** of the review-provision game. Xiao, Chen, Tang, *Customer Review Provision
Policies with Heterogeneous Cluster Preferences*, SSRN 3403322 (manuscript of 2021-05-24), §3 and
Table 1, pp.9–13 (PDF 9–13).

* `tau` is `τ`, the precision of the prior of the quality `q` (p.9);
* `eta` is `η`, the precision of the cluster preferences `t_n` (p.10);
* `zeta` is `ζ`, the precision of an individual quality perception (p.10);
* `theta` is `θ ∈ (0, 1]`, the proportion of first-period users that leave a rating (p.11);
* `h` is the price sensitivity, `h > 0` (p.10);
* `m` is the mass of the second batch of customers in each cluster, `m > 0` (p.10).

**Formalization Note.** The number of clusters is not a field: it is the implicit `N` of `Fin N`,
and `N ≥ 2` (p.9) is an explicit hypothesis wherever it matters. The prior mean `q_p = 1` (p.9,
"Without loss of generality") is built into `prior`. -/
structure Params where
  /-- precision `τ` of the prior of the quality -/
  tau : ℝ
  /-- precision `η` of the cluster preferences -/
  eta : ℝ
  /-- precision `ζ` of an individual quality perception -/
  zeta : ℝ
  /-- proportion `θ` of first-period users that leave a rating -/
  theta : ℝ
  /-- price sensitivity `h` -/
  h : ℝ
  /-- mass `m` of the second batch of customers in each cluster -/
  m : ℝ
  tau_pos : 0 < tau
  eta_pos : 0 < eta
  zeta_pos : 0 < zeta
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  h_pos : 0 < h
  m_pos : 0 < m

end ReviewProvision


