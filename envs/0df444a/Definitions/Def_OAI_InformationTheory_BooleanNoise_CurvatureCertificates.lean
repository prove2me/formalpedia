-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
-- name    : OAI_InformationTheory_BooleanNoise_CurvatureCertificates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:17:03.379469+00:00
-- url     : https://prove2.me/theorems/da601ba7-975c-4439-a2d2-c68c1b71579f
-- title:
--   Polynomial curvature certificates in Bernstein form
-- statement:
--   The file fixes explicit polynomials and Bernstein coefficient lists used as numerical certificates.
--
--   1. **Bernstein sums.** For $d\in\mathbb{N}$ and coefficients $B_0,\dots,B_d$,
--   $$
--   \mathcal B_d(B)(t)=\sum_{i=0}^dB_i\binom{d}{i}t^i(1-t)^{d-i}.
--   $$
--   2. **Curvature polynomials.**
--   $$
--   T(z)=1+\tfrac z3+\tfrac{z^2}5+\tfrac{z^3}7+\tfrac{z^4}9+\tfrac{z^5}{11},\qquad P(z)=\tfrac{347}{500}-\tfrac z2-\tfrac{z^2}{12}-\tfrac{z^3}{30}-\tfrac{z^4}{56}-\tfrac{z^5}{90},
--   $$
--   $$
--   N(z)=(1-z)\Bigl(\tfrac43+\tfrac8{15}z+\tfrac{12}{35}z^2+\tfrac{16}{63}z^3+\tfrac{20}{99}z^4\Bigr)+\tfrac{24}{143}z^5,
--   $$
--   and $\mathcal C(z)=2(1-z)^3T(z)^3-3P(z)^2N(z)$, with an explicit list of $19$ positive rational Bernstein coefficients for it.
--   3. **The $\lambda$ polynomial.**
--   $$
--   \Lambda(b)=4-\tfrac52b-5b^2-\tfrac74b^3+\tfrac{56}{15}b^4+b^5+\tfrac{15}{14}b^6+\tfrac38b^7+\tfrac8{15}b^8,
--   $$
--   with two lists of $9$ positive rational Bernstein coefficients, for a low and a high subinterval.
--
--   Positive Bernstein coefficients certify positivity of a polynomial on an interval. These certificates verify the analytic inequalities (convexity and curvature bounds) needed in the proof of the information bound by finite exact arithmetic.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CurvatureCertificates.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CurvatureCertificates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def bernsteinSum (d : ℕ) (B : Fin (d + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, B i * (d.choose i.val : ℝ) * t ^ i.val * (1 - t) ^ (d - i.val)

def curvatureT (z : ℝ) : ℝ :=
  1 + z / 3 + z ^ 2 / 5 + z ^ 3 / 7 + z ^ 4 / 9 + z ^ 5 / 11

def curvatureP (z : ℝ) : ℝ :=
  347 / 500 - z / 2 - z ^ 2 / 12 - z ^ 3 / 30 - z ^ 4 / 56 - z ^ 5 / 90

def curvatureN (z : ℝ) : ℝ :=
  (1 - z) * (4 / 3 + (8 / 15) * z + (12 / 35) * z ^ 2 +
    (16 / 63) * z ^ 3 + (20 / 99) * z ^ 4) + (24 / 143) * z ^ 5

def curvaturePolynomial (z : ℝ) : ℝ :=
  2 * (1 - z) ^ 3 * curvatureT z ^ 3 - 3 * curvatureP z ^ 2 * curvatureN z

 def curvatureBernstein : Fin 19 → ℝ :=
  ![(4591 / 62500 : ℝ),
    (49876 / 703125 : ℝ),
    (616620509 / 9036562500 : ℝ),
    (425343109 / 6506325000 : ℝ),
    (1239780551 / 19880437500 : ℝ),
    (8677345901149 / 146538704812500 : ℝ),
    (243668974553 / 4355288437500 : ℝ),
    (9012669336346771 / 171450284630625000 : ℝ),
    (1633213857973883 / 33281525840062500 : ℝ),
    (270017981574109469 / 5940752362451156250 : ℝ),
    (49027630438590434159 / 1176268967765328937500 : ℝ),
    (363078011510202773129 / 9624018827170873125000 : ℝ),
    (10171907529149910232987 / 303156593055882503437500 : ℝ),
    (4117638512237582389 / 141331745014397437500 : ℝ),
    (29341211329970780039 / 1199300807693601112500 : ℝ),
    (7749647417493214337891 / 395769266538888367125000 : ℝ),
    (14423931694547701552427 / 989423166347220917812500 : ℝ),
    (140069602865401114033 / 14550340681576778203125 : ℝ),
    (2753371080520712929 / 554298692631496312500 : ℝ)]

def lambdaPolynomial (b : ℝ) : ℝ :=
  4 - (5 / 2) * b - 5 * b ^ 2 - (7 / 4) * b ^ 3 + (56 / 15) * b ^ 4 +
    b ^ 5 + (15 / 14) * b ^ 6 + (3 / 8) * b ^ 7 + (8 / 15) * b ^ 8

 def lambdaBernsteinLow : Fin 9 → ℝ :=
  ![4,
    (241 / 64 : ℝ),
    (1537 / 448 : ℝ),
    (42755 / 14336 : ℝ),
    (217187 / 89600 : ℝ),
    (510487 / 286720 : ℝ),
    (8901163 / 8028160 : ℝ),
    (19161827 / 36700160 : ℝ),
    (1316227 / 4587520 : ℝ)]

 def lambdaBernsteinHigh : Fin 9 → ℝ :=
  ![(1316227 / 4587520 : ℝ),
    (7652479 / 36700160 : ℝ),
    (5432143 / 32112640 : ℝ),
    (2869523 / 16056320 : ℝ),
    (3747241 / 15052800 : ℝ),
    (1185781 / 3010560 : ℝ),
    (79071 / 125440 : ℝ),
    (5261 / 5376 : ℝ),
    (1229 / 840 : ℝ)]

end LeanBlast.CourtadeKumar

end

end OAI


