-- Prove2me | Definitions.Def_MaxCompForest_Supplement_optReal
-- name    : MaxCompForest_Supplement_optReal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:07:58.825503+00:00
-- url     : https://prove2.me/theorems/1fd61e1d-4fe7-4655-942d-307a8fa236b4
-- title:
--   Real-center weighted clustering optimum $\mathrm{OPT}^{\mathrm{real}}_m$
-- statement:
--   For a finite indexed family $x=(x_v)_{v\in V}$ of points of $\mathbb R^d$, positive weights $w_v$ and a center budget $m\ge1$, the **real-center optimum** is
--
--   $$\mathrm{OPT}^{\mathrm{real}}_m(x)=\inf_{a_1,\dots,a_m\in\mathbb R^d}\ \sum_{v\in V} w_v\min_{j\le m}\|x_v-a_j\|^2 .$$
--
--   The centers are arbitrary points (not necessarily input rows), and unused centers and empty clusters are allowed. It is the benchmark against which the sharpness results (Theorem 2.1, Theorem B.1) are stated "even allowing arbitrary real centers"; with degree weights it is $\mathrm{OPT}^{\mathrm{real}}_b(\Phi;D)$.
--
--   **Formalization Note** Both minima are infima; the inner one over the finite index set is a minimum when $m\ge1$, and the outer one is the infimum of a set bounded below by $0$. At $m=0$ the inner infimum over the empty index set is the junk value $0$; every statement uses $m=2q\ge2$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §2.1, p.7 (PDF p.9); Appendix B, p.33 (PDF p.35)

import Mathlib
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V : Type*} [Fintype V]

/-- **The real-center optimum** `OPTreal_m(x) = min_{a_1,…,a_m} ∑_v w_v min_{j ≤ m} ‖x_v − a_j‖²`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §2.1, p.7 (and Appendix B, p.33, with `w = d`).

**Formalization Note.** Both minima are infima (`⨅`): the inner one over the finite index set `Fin m`, the outer
one over all center tuples. The summands are nonnegative for nonnegative weights, so the outer infimum is a
genuine infimum of a set bounded below; for `m ≥ 1` the inner infimum is a minimum. At `m = 0` the inner `⨅`
over the empty type is the junk value `0`; every statement uses `m = 2q ≥ 2`. -/
noncomputable def optReal {d : ℕ} (W : V → ℝ) (x : V → EuclideanSpace ℝ (Fin d)) (m : ℕ) : ℝ :=
  ⨅ a : Fin m → EuclideanSpace ℝ (Fin d), ∑ v, W v * ⨅ j : Fin m, ‖x v - a j‖ ^ 2

end MaxCompForest.Supplement


