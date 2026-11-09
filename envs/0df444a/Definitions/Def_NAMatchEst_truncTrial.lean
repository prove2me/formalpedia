-- Prove2me | Definitions.Def_NAMatchEst_truncTrial
-- name    : NAMatchEst_truncTrial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:57:31.939201+00:00
-- url     : https://prove2.me/theorems/5ed6d81c-b7fd-4d6a-bc1a-e9588fd40e24
-- title:
--   One truncated trial
-- statement:
--   One **truncated trial** (§3.9): the large-scale trial when $k>\alpha^2$ and the small-scale trial otherwise, aborted with output No (and no queries) when one of its two Bernoulli samples $S$, with inclusion probability $p$, has
--
--   $$
--   |S|>\lceil 2np+100L\rceil . \qquad (24)
--   $$
--
--   The abort decision is a function of the internal randomness only.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.9, display (24), p.29 (PDF 33), and proof of Lemma 3.1, p.31 (PDF 35)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_guard
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_Delta
import Definitions.Def_NAMatchEst_largeTrial
import Definitions.Def_NAMatchEst_smallTrial

namespace NAMatchEst

/-- One **truncated trial** (§3.9): the large-scale trial when `k > α²` and the small-scale trial
otherwise, aborted with output No (`false`) and no queries when one of its two Bernoulli samples
`S` (inclusion probability `p`) has `|S| > ⌈2np + 100L⌉` (24).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.9, p.29 (PDF 33): "For either Bernoulli sample S with inclusion probability p, abort the
trial and output No if |S| > ⌈2np + 100L⌉. (24) Both vertex sets and this abort decision are
generated before issuing any queries for the trial." Proof of Lemma 3.1, p.31 (PDF 35): "Use the
large-scale trial when k > α² and the small-scale trial otherwise, with the caps just described."

**Formalization Note** The abort decision reads only the two Bernoulli components of the seed
(`ω.2.2.2.1`, `ω.2.2.2.2.1` in the large-scale trial; `ω.2.1`, `ω.2.2` in the small-scale trial);
`p` is the inclusion probability of that sample, (14) resp. (23). -/
noncomputable def truncTrial (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) : RandAlg n Bool :=
  open Classical in
  if α ^ 2 < k then
    (largeTrial n α k).guard
      (fun ω =>
        let e : (Fin n → Bool) × (Fin n → Bool) ×
            (Fin n → Fin ⌈cc * Delta k α * L n / α⌉₊ → Fin (Delta k α)) := ω.2.2.2
        ((Finset.univ.filter fun v => e.1 v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n / Real.sqrt (k * α)) + 100 * L n⌉₊ ∧
          ((Finset.univ.filter fun v => e.2.1 v = true).card : ℝ) ≤
            ⌈2 * n * Real.sqrt (α / k) + 100 * L n⌉₊)
      false
  else
    (smallTrial n α k).guard
      (fun ω =>
        let e : (Fin n → Bool) × (Fin n → Bool) := ω.2
        ((Finset.univ.filter fun v => e.1 v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n * Real.sqrt α / k) + 100 * L n⌉₊ ∧
          ((Finset.univ.filter fun v => e.2 v = true).card : ℝ) ≤
            ⌈2 * n * (1 / Real.sqrt α) + 100 * L n⌉₊)
      false

end NAMatchEst


