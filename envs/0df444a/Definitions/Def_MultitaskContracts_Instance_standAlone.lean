-- Prove2me | Definitions.Def_MultitaskContracts_Instance_standAlone
-- name    : MultitaskContracts_Instance_standAlone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:32.256789+00:00
-- url     : https://prove2.me/theorems/1c48cb8b-93c8-4f41-acb1-b857159c235b
-- title:
--   Stand-alone payment $c_k/(1-q_k/p_k)$ (Definition 4)
-- statement:
--   The **stand-alone payment** of a task $k$ is
--   $$\frac{c_k}{1-q_k/p_k}.$$
--   It is the least expected payment that implements effort on $k$ when $k$ is the only task (by Lemma 15), and it bounds $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}$ from below for independent tasks (proof of Theorem 2).
--
--   **Formalization Note** Real division; $p_k>q_k\ge0$ makes both denominators positive.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Definition 4, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **Stand-alone payment** (Definition 4, p.14, PDF 16) of task `k`: `c_k / (1 − q_k/p_k)`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Definition 4, p.14.

**Formalization Note.** Real division; `p_k > q_k ≥ 0` makes both denominators positive. -/
noncomputable def Instance.standAlone {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K)
    (k : K) : ℝ :=
  I.c k / (1 - I.q k / I.p k)

end MultitaskContracts


