-- Prove2me | Definitions.Def_BilatMatch_FB
-- name    : BilatMatch_FB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:03.471634+00:00
-- url     : https://prove2.me/theorems/f706fd8b-170d-471c-92d8-52068f89d767
-- title:
--   First-best benchmark $\mathrm{FB}=\mathbb E[\sup_{M\in\mathcal F}\sum_{(i,j)\in M}(v_i-c_j)_+]$
-- statement:
--   The **first-best benchmark** of a market is
--   $$\mathrm{FB}=\mathbb E\Big[\sup_{M\in\mathcal F}\sum_{(i,j)\in M}(v_i-c_j)_+\Big],\qquad (w)_+=\max\{w,0\}.$$
--   It is the expected value of the best total gains from trade over feasible matchings when types are public.
--
--   **Formalization Note** Positive parts, the (possibly infinite) sum over a matching and the expectation are taken in $[0,\infty]$ (a `lintegral`), so $\mathrm{FB}$ is always defined. The paper's standing assumption $\mathrm{FB}<\infty$ is a hypothesis of the theorems that need it.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §2, p.6 (pdf p.8)

import Mathlib
import Definitions.Def_BilatMatch_Market

open MeasureTheory

namespace BilatMatch

variable {B S : Type*}

/-- The first-best benchmark (Liu, Qin, Wang, arXiv:2609.30702, held version, sha256 ff1490ad…,
§2, p.6 (pdf p.8)):
`FB = E[ sup_{M ∈ F} ∑_{(i,j) ∈ M} (v_i − c_j)_+ ]`.

**Formalization Note** The positive parts are taken in `ℝ≥0∞` (`ENNReal.ofReal`), the sum over a
possibly infinite matching is `tsum` in `ℝ≥0∞`, and the expectation is a `lintegral`, so `FB` is
always defined, possibly `⊤`. The paper's standing assumption `FB < ∞` is a hypothesis of the
theorems that need it. -/
noncomputable def FB (I : Market B S) : ENNReal :=
  ∫⁻ θ, ⨆ M ∈ I.family, ∑' e : M, ENNReal.ofReal (θ.1 e.1.1 - θ.2 e.1.2) ∂typeMeasure I

end BilatMatch


