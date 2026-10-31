-- Prove2me | Definitions.Def_LearnManip_vk
-- name    : LearnManip_vk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:05.746168+00:00
-- url     : https://prove2.me/theorems/06386d78-d754-458c-8f50-1383f9961a48
-- title:
--   Finite-stage iteration $v_k$
-- statement:
--   The $k$-stage dynamic program: $v_0=0$ and
--   $$v_{k+1}(\mu,s,c)=\sup_{q\ge0}\Bigl\{-cq+\gamma\log E_{\mu,s}\Bigl[\exp\Bigl(\frac{\mu^q+\alpha v_k(\mu^q,\frac{s}{1+sq},c\eta)}{\gamma}\Bigr)\Bigr]\Bigr\}.$$
--
--   **Formalization Note.** The supremum is a real supremum of a set that is nonempty and bounded above; the milestone (EC.16) states that it is a least upper bound.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), proof of Lemma EC.3, p.ec9 (PDF 48)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_dissemObjective

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The `k`-stage DP iteration of the proof of Lemma EC.3, p.ec9 (PDF 48), of Keppo, Kim, Zhang (SSRN
3465030, 2021-09-04): `v₀ = 0` and `v_k` is the right side of (13) with `v_{k−1}` on the right.

**Formalization Note.** The paper's `max` is a real `sSup`. The set is nonempty and bounded above;
`eq_EC_16` states that the value is its least upper bound, so no junk value is used. -/
noncomputable def vk (P : Params) : ℕ → ℝ → ℝ≥0 → ℝ≥0 → ℝ
  | 0, _, _, _ => 0
  | k + 1, μ, s, c => sSup (Set.range (dissemObjective P (vk P k) μ s c))

end LearnManip


