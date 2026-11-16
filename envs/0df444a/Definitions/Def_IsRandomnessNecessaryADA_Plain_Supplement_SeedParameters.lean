-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedParameters
-- name    : IsRandomnessNecessaryADA_Plain_Supplement_SeedParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:05.051208+00:00
-- url     : https://prove2.me/theorems/250febe6-ec07-4ce1-a94c-53a13c83ae80
-- title:
--   Finite witness parameters for limited private randomness
-- statement:
--   For the proof of Theorem 1.4, put $N=20n$, let $b$ be the private bit budget, and use the published density factor $D=(N+1)2^N$. Define
--
--   $$k=\left\lceil\frac{\log(2^bN^n)}{\log(10/9)}\right\rceil+1,\qquad M=2^{b+1}N^n(100kN2^ND^k)^2,\qquad d=NM.$$
--
--   The horizon computation also accepts a general row count $N$; the column and domain counts use $N=20n$. In the intended regime $n>2$, all logarithm arguments and counts are positive. The ceiling on the printed expression for $M$ is redundant because the product is integral. These are operational witness computations, not assumptions about a successful attack or proofs of their asymptotic bounds. The new seed-aware names leave the published $b=0$ parameters unchanged. Outside the intended regime the functions remain total, with Lean's real logarithm and natural ceiling conventions.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, Is Randomness Necessary for Adaptive Data Analysis?, STOC 2027 submission #267 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf, §4.5, p.15 (PDF p.15); Definitions 2.1–2.2, pp.7–8; supporting conventions §§3–4.4, pp.8–14.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Supplement

/-- Section 4.5, p.15: logarithm of the number of sample-seed pairs, base 10/9.
The intended witness uses n > 2 and N = 20n, so both log arguments are positive. -/
noncomputable def seedAttackHorizon (n N b : ℕ) : ℕ :=
  Nat.ceil (Real.log ((2 : ℝ) ^ b * (N : ℝ) ^ n) / Real.log (10 / 9 : ℝ)) + 1

/-- Section 4.5, p.15. The printed ceiling is redundant: the product is integral. -/
noncomputable def seedColumnCount (n b : ℕ) : ℕ :=
  let N := 20 * n
  let k := seedAttackHorizon n N b
  2 ^ (b + 1) * N ^ n * (100 * k * N * 2 ^ N * densityFactor N ^ k) ^ 2

/-- Cardinality of the proof's product domain [20n] × [M]. -/
noncomputable def seedDomainSize (n b : ℕ) : ℕ :=
  (20 * n) * seedColumnCount n b

end IsRandomnessNecessaryADA.Plain.Supplement


