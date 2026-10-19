-- Prove2me | Definitions.Def_FBAComp_AmazonGain_ClosedForms
-- name    : FBAComp_AmazonGain_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:05.763183+00:00
-- url     : https://prove2.me/theorems/a401af6e-6870-4a5e-89d1-10cf7d7b871c
-- title:
--   Lemmas A.1–A.2 and Proposition 1 (i) — closed forms
-- statement:
--   This file gives the six printed closed-form decisions: wholesale and both retail prices in the no-FBA equilibrium and in the FBA subgame at fee $T$. It also gives the seller's maximum willingness-to-pay threshold:
--
--   $$\bar T=c+\frac{(1-r)(s_A-s_S)[8\alpha-(3+r)\alpha\beta^2-6\beta\eta+(2+r)\beta^3\eta]}{(1-\beta^2)[8-(3+r)\beta^2]}.$$
--
--   Lemmas A.1–A.2 assert that the candidate decisions are the unique respective outcomes. The denominators are positive under $0<r,\beta<1$.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 34, Lemmas A.1–A.2; p. 18, Proposition 1 (i)

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

namespace FBAComp.AmazonGain

/-- `w*N` in Lemma A.1, p. 34. -/
noncomputable def wN_star (P : Params) (η : ℝ) : ℝ :=
  (P.g * P.β + P.QA * (2 - P.r * P.β ^ 2) +
    P.QS * (P.β - P.r * P.β) - P.c * (2 - P.β - P.β ^ 2) +
    P.sA * (2 * P.α - P.β * η - P.r * P.α * P.β ^ 2 + P.r * P.β * η) +
    P.sS * (P.α * P.β - P.r * P.α * P.β - 2 * η + P.r * P.β ^ 2 * η)) /
    (2 * (2 - P.β ^ 2)) + P.c0 / 2

/-- `p*A,N` in Lemma A.1, p. 34. -/
noncomputable def pAN_star (P : Params) (η : ℝ) : ℝ :=
  (P.g * P.β * (3 + P.r - P.β ^ 2 - P.r * P.β ^ 2) +
    P.c * ((1 - P.r) * (2 - P.β) * (1 + P.β) +
      (1 + P.r) * P.β * (2 - P.β ^ 2)) +
    P.c0 * (1 - P.r) * (2 - P.β ^ 2) +
    P.QA * (1 - P.r) * (6 - (2 + P.r) * P.β ^ 2) +
    P.QS * P.β * (3 - 2 * P.r - P.β ^ 2 - P.r ^ 2 + P.r ^ 2 * P.β ^ 2) +
    P.sA * (1 - P.r) *
      (P.α * (6 - (2 + P.r) * P.β ^ 2) -
        P.β * (3 + P.r - (1 + P.r) * P.β ^ 2) * η) +
    P.sS * (1 - P.r) *
      (P.α * P.β * (3 + P.r - (1 + P.r) * P.β ^ 2) -
        6 * η + (2 + P.r) * P.β ^ 2 * η)) /
    ((1 - P.r) * (4 - (1 + P.r) * P.β ^ 2) * (2 - P.β ^ 2))

/-- `p*S,N` in Lemma A.1, p. 34. -/
noncomputable def pSN_star (P : Params) (η : ℝ) : ℝ :=
  (P.g * (8 - (3 + P.r) * P.β ^ 2) +
    P.c * (8 + 2 * (1 - P.r) * P.β - (3 + P.r) * P.β ^ 2 -
      (1 - P.r) * P.β ^ 3) +
    P.c0 * P.β * (1 - P.r) * (2 - P.β ^ 2) +
    P.QA * (1 - P.r) * P.β * (6 - (2 + P.r) * P.β ^ 2) +
    P.QS * (1 - P.r) * (8 - (3 + P.r) * P.β ^ 2) +
    P.sA * (1 - P.r) *
      (6 * P.α * P.β - (2 + P.r) * P.α * P.β ^ 3 - 8 * η +
        (3 + P.r) * P.β ^ 2 * η) +
    P.sS * (1 - P.r) *
      (8 * P.α - (3 + P.r) * P.α * P.β ^ 2 - 6 * P.β * η +
        (2 + P.r) * P.β ^ 3 * η)) /
    (2 * (1 - P.r) * (4 - (1 + P.r) * P.β ^ 2) * (2 - P.β ^ 2))

/-- `w*F` in Lemma A.2, p. 34. -/
noncomputable def wF_star (P : Params) (η T : ℝ) : ℝ :=
  (P.g * P.β + P.QA * (2 - P.r * P.β ^ 2) +
    P.QS * (1 - P.r) * P.β -
    P.c * (2 - 2 * P.β - P.β ^ 2 + P.β ^ 3) -
    T * (P.β - P.β ^ 3) +
    P.sA * (2 + (1 - P.r) * P.β - P.r * P.β ^ 2) * (P.α - η)) /
    (2 * (2 - P.β ^ 2)) + P.c0 / 2

/-- `p*A,F` in Lemma A.2, p. 34. -/
noncomputable def pAF_star (P : Params) (η T : ℝ) : ℝ :=
  (P.g * P.β * (3 + P.r - P.β ^ 2 - P.r * P.β ^ 2) +
    P.c0 * (1 - P.r) * (2 - P.β ^ 2) +
    P.c * (1 - P.r) * (1 - P.β) * (2 - P.β ^ 2) +
    P.sA * (P.α - η) * (1 - P.r) *
      (6 + P.β * (1 - P.β) * (3 + P.β) +
        P.r * P.β * (1 - P.β - P.β ^ 2)) +
    P.QA * (1 - P.r) * (6 - (2 + P.r) * P.β ^ 2) +
    P.QS * (1 - P.r) * P.β * (3 + P.r - P.β ^ 2 - P.r * P.β ^ 2) +
    T * P.β * (5 - P.r - 2 * P.β ^ 2)) /
    ((1 - P.r) * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2))

/-- `p*S,F` in Lemma A.2, p. 34. -/
noncomputable def pSF_star (P : Params) (η T : ℝ) : ℝ :=
  (P.g * (8 - (3 + P.r) * P.β ^ 2) +
    P.sA * (P.α - η) * (1 - P.r) *
      (8 + (6 * P.β - P.β ^ 2 * (3 + P.r + (2 + P.r) * P.β))) +
    P.c * (1 - P.r) * P.β * (2 - 2 * P.β - P.β ^ 2 + P.β ^ 3) +
    P.QA * (1 - P.r) * (6 - (2 + P.r) * P.β ^ 2) * P.β +
    P.QS * (1 - P.r) * (8 - (3 + P.r) * P.β ^ 2) +
    P.c0 * P.β * (1 - P.r) * (2 - P.β ^ 2) +
    T * (8 - (1 + 3 * P.r) * P.β ^ 2 - (1 - P.r) * P.β ^ 4)) /
    (2 * (1 - P.r) * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2))

/-- Seller's willingness-to-pay threshold `T̄`, Proposition 1 (i), p. 18. -/
noncomputable def Tbar (P : Params) (η : ℝ) : ℝ :=
  P.c + (1 - P.r) * (P.sA - P.sS) *
    (8 * P.α - (3 + P.r) * P.α * P.β ^ 2 - 6 * P.β * η +
      (2 + P.r) * P.β ^ 3 * η) /
    ((1 - P.β ^ 2) * (8 - (3 + P.r) * P.β ^ 2))

end FBAComp.AmazonGain


