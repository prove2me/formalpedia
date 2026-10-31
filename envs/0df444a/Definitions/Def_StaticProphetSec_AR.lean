-- Prove2me | Definitions.Def_StaticProphetSec_AR
-- name    : StaticProphetSec_AR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:58.136984+00:00
-- url     : https://prove2.me/theorems/43823f0c-cfc9-4820-9447-babe6c4e13fd
-- title:
--   Acceptance rate $\mathrm{AR}_k(d)=\min(1,k/(d+1))$
-- statement:
--   For $k\ge1$ and $d\in\mathbb N_0$,
--
--   $$\mathrm{AR}_k(d)=\min\left(1,\frac{k}{d+1}\right).$$
--
--   Because applicants arrive in random order, an applicant who competes with $d$ others for $k$ items is accepted with probability $\mathrm{AR}_k(d)$. It measures the risk of allocating items too quickly.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (6), p.16

import Mathlib

namespace StaticProphetSec

/-- The acceptance-rate function `AR_k(d) = min(1, k/(d+1))`, equation (6) (Arnosti & Ma,
arXiv:2108.12893v2, (6), p.16): the probability that an applicant who competes with `d` others
for `k` items is accepted under a uniformly random arrival order. -/
noncomputable def AR (k d : ℕ) : ℝ :=
  min 1 ((k : ℝ) / ((d : ℝ) + 1))

end StaticProphetSec


