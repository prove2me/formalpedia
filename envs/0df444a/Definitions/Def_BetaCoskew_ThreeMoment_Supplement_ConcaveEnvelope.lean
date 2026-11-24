-- Prove2me | Definitions.Def_BetaCoskew_ThreeMoment_Supplement_ConcaveEnvelope
-- name    : BetaCoskew_ThreeMoment_Supplement_ConcaveEnvelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:37:20.238956+00:00
-- url     : https://prove2.me/theorems/c62ca577-168f-4aa4-97b3-fb93d7b52717
-- title:
--   Theorem 1, p. 10 — least concave majorant and its right derivative
-- statement:
--   For a real function $g$ on $[0,1]$, define its least concave majorant by
--
--   $$
--   \widehat g(q)=\inf\{h(q):h\text{ is concave on }[0,1],\ h(t)\ge g(t)\text{ for every }t\in[0,1]\}.
--   $$
--   The envelope used in Theorem 1 is $\widehat N$. Its slope is the right derivative $\widehat N'_+(q)$ for $0<q<1$, with no smoothness or strict-concavity requirement on the envelope. In particular, linear segments are allowed.
--
--   **Formalization Note** The infimum is initially an extended-real infimum. For the source function $N$, the family is nonempty, since the zero function is a majorant, and its values at each $q\in[0,1]$ are bounded below by $N(q)$. The real conversion is therefore finite on the entire source domain. The right derivative uses differentiation within $[q,\infty)$; at the endpoints its unused value is assigned one. Those endpoints are null in the payoff construction and absent from the all-multiplier integrals. For an arbitrary function without a concave majorant the extended infimum is $+\infty$ before conversion; no theorem applies this conversion to such a function.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), p. 10, Theorem 1, definition of N̂ and N̂′

import Mathlib

namespace BetaCoskew.ThreeMoment.Supplement

open Set

/-- A genuine extended infimum over all concave majorants on [0,1].
No selected envelope is supplied as free data. -/
noncomputable def concaveEnvelopeE (g : ℝ → ℝ) (q : ℝ) : EReal :=
  sInf {v : EReal | ∃ h : ℝ → ℝ, ConcaveOn ℝ (Icc 0 1) h ∧
    (∀ t ∈ Icc (0 : ℝ) 1, g t ≤ h t) ∧ v = (h q : EReal)}

/-- Real value of the envelope. For the source N on [0,1], the family is
nonempty (the zero majorant) and is bounded below by N(q), so no infinite value
is converted. For general g, an empty family gives +∞ before conversion. -/
noncomputable def concaveEnvelope (g : ℝ → ℝ) (q : ℝ) : ℝ :=
  (concaveEnvelopeE g q).toReal

/-- The right derivative in the interior, without any global C¹ assumption.
Endpoint values are assigned 1 and occur only on null sets in Theorem 1. -/
noncomputable def rightSlope (g : ℝ → ℝ) (q : ℝ) : ℝ :=
  if q ∈ Ioo (0 : ℝ) 1 then
    derivWithin (concaveEnvelope g) (Ici q) q
  else 1

end BetaCoskew.ThreeMoment.Supplement


