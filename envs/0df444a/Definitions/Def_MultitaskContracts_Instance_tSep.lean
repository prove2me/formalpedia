-- Prove2me | Definitions.Def_MultitaskContracts_Instance_tSep
-- name    : MultitaskContracts_Instance_tSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:27.861649+00:00
-- url     : https://prove2.me/theorems/97d92ac3-255a-4c95-9fcc-552934dd1ac6
-- title:
--   The separable contract $t_{\mathrm{Sep}}$ of Lemma 15
-- statement:
--   The separable contract $t_{\mathrm{Sep}}$ pays $c_k/(p_k-q_k)$ on the success of each task $k$ and nothing on its failure, with no fixed payment:
--   $$t_{\mathrm{Sep}}(Y)=\sum_{k\in Y}\frac{c_k}{p_k-q_k}.$$
--   By Lemma 15 it is an optimal separable contract for Min-Pay, Min-Budget and Budgeted Min-Pay simultaneously; its expected payment under full effort is the sum of the stand-alone payments.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Lemma 15, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- The separable contract `t_Sep` of Lemma 15 (App. C, p.55, PDF 57): it pays `c_k/(p_k − q_k)` on
the success of each task `k` and nothing on its failure, `t_Sep(Y) = ∑_{k∈Y} c_k/(p_k − q_k)`
(fixed payment `t₀ = 0`). E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Lemma 15, p.55. -/
noncomputable def Instance.tSep {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K)
    (Y : Finset K) : ℝ :=
  ∑ k ∈ Y, I.c k / (I.p k - I.q k)

end MultitaskContracts


