-- Prove2me | Definitions.Def_Freiman_lowerJModel
-- name    : Freiman_lowerJModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:20:54.213027+00:00
-- url     : https://prove2.me/theorems/c7f96d4f-7c90-48f8-9d1f-5acdef9ad350
-- title:
--   Freiman repeated-three width proof: lowerJModel
-- statement:
--   Exact report J-family scalar recurrences,28 signs,two contact and two p81 width polynomials, and actual inner/fork endpoints.
-- source:
--   Freiman report j_family.tex and j_certificates.tex; uniform_certificate.json and p81 product bounds.

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerSourceCover
namespace Freiman
attribute [local instance] Classical.propDecidable
noncomputable def lowerJPhi (x : ℝ) : ℝ := 1/(3+x)
noncomputable def lowerJIter (k : ℕ) (x : ℝ) : ℝ := prefixEval (List.replicate k 3) x
noncomputable def lowerJTau (k : ℕ) : ℝ := finiteCF (List.replicate k (3:ℕ+))
noncomputable def lowerJA : ℝ := lowerTheta 3
noncomputable def lowerJA2 : ℝ := lowerTheta 25
noncomputable def lowerJB : ℝ := lowerTheta 90
noncomputable def lowerJC : ℝ := lowerTheta 30
noncomputable def lowerJD : ℝ := prefixEval [3,3] lowerJB
noncomputable def lowerJE : ℝ := lowerTheta 63
noncomputable def lowerJX : ℝ := lowerTheta 66
noncomputable def lowerJCoeff : ℝ := (lowerJD-lowerJA)/(lowerJC-lowerJD)
noncomputable def lowerJH (c x0 x1 y0 y1 r s : ℝ) : ℝ :=
  c*(1+s*y0)*(1+s*y1)/((1+r*x0)*(1+r*x1))
noncomputable def lowerJH7 (r s : ℝ) : ℝ := lowerJH (31/100) lowerJA lowerJA2 lowerJE lowerJX r s
noncomputable def lowerJHStar (r s : ℝ) : ℝ :=
  lowerJH (5/7) (prefixEval [3] lowerAlpha) (prefixEval [3] lowerBeta)
    (prefixEval [3] lowerAlpha) (prefixEval [3] lowerBeta) r s
noncomputable def lowerJH1 (r s : ℝ) : ℝ :=
  lowerJH ((lowerJPhi lowerJD-lowerJPhi lowerJA)/(lowerJPhi lowerJC-lowerJPhi lowerJD))
    (lowerJPhi lowerJA) (lowerJPhi lowerJD) (lowerJPhi lowerJC) (lowerJPhi lowerJD) r s
noncomputable def lowerJHBar (r s : ℝ) : ℝ := lowerJH (371/500) (303/1000) (303/1000) (151/500) (151/500) r s
noncomputable def lowerJHK (k : ℕ) (r s : ℝ) : ℝ :=
  lowerJH (lowerJCoeff*(1+lowerJTau k*lowerJC)/(1+lowerJTau k*lowerJA))
    (lowerJIter k lowerJA) (lowerJIter k lowerJD) (lowerJIter k lowerJC) (lowerJIter k lowerJD) r s
noncomputable def lowerJQ (r s q tau : ℝ) : ℝ := q*(1+r*tau)^2/(1+s*tau)^2
noncomputable def lowerJDomain (r s q : ℝ) : Prop :=
  r ∈ Set.Icc (1/4:ℝ) (4/5) ∧ s ∈ Set.Icc (1/4:ℝ) (4/5) ∧ lowerJH7 r s ≤ q ∧ q < lowerJHStar r s
noncomputable def lowerJUpdated (p : LowerPair) (k : ℕ) : Prop :=
  let q := lowerNormalize p
  let u := q.1++List.replicate k 3
  let v := q.2++List.replicate k 3
  lowerRatio u = lowerJIter k (lowerRatio q.1) ∧ lowerRatio v = lowerJIter k (lowerRatio q.2) ∧
    lowerScale (u,v) = lowerJQ (lowerRatio q.1) (lowerRatio q.2) (lowerScale q) (lowerJTau k)
noncomputable def lowerJProd104 (r s : ℝ) : ℝ :=
  ((1+r*lowerTheta 1)*(1+r*lowerTheta 95)*(1+s*lowerTheta 3)*(1+s*lowerTheta 90))/
  ((1+r*lowerTheta 63)*(1+r*lowerTheta 66)*(1+s*lowerTheta 1)*(1+s*lowerTheta 95))
noncomputable def lowerJProd1064 (r s : ℝ) : ℝ :=
  ((1+r*lowerTheta 65)*(1+r*lowerTheta 68)*(1+s*lowerTheta 3)*(1+s*lowerTheta 90))/
  ((1+r*lowerTheta 63)*(1+r*lowerTheta 66)*(1+s*lowerTheta 1)*(1+s*lowerTheta 28))
noncomputable def lowerJSigns (i : Fin 28) : ℝ :=
  ![lowerJE-1/3,lowerJX-1/3,3/5-lowerJA-lowerJA2,9/100-lowerJA*lowerJA2,
    4/5-475020045/601400527,(18/19)^2-4/5,19/5-(19/18)^2/(31/100),
    lowerJD-lowerJA,lowerJC-lowerJD,lowerJB-lowerJC,lowerJC-lowerJA,
    lowerJB-lowerJIter 2 lowerJA,lowerJB-lowerJIter 2 lowerJC,lowerJB^2+3*lowerJB-1,
    lowerJIter 2 lowerJA-151/500,303/1000-lowerJIter 2 lowerJA,
    lowerJIter 2 lowerJD-151/500,303/1000-lowerJIter 2 lowerJD,
    lowerJIter 2 lowerJC-151/500,38/125-lowerJIter 2 lowerJC,
    lowerJIter 2 lowerJD-151/500,38/125-lowerJIter 2 lowerJD,
    lowerJPhi (303/1000)-151/500,303/1000-lowerJPhi (151/500),
    lowerJPhi (38/125)-151/500,38/125-lowerJPhi (151/500),
    lowerJCoeff*(1+(3/10)*lowerJC)-(371/500)*(1+(3/10)*lowerJA),
    lowerJCoeff*(1+(1/3)*lowerJC)-(371/500)*(1+(1/3)*lowerJA)] i
noncomputable def lowerJSignFacts : Prop := ∀ i : Fin 28, 0 < lowerJSigns i
noncomputable def lowerJPolyFacts (r s : ℝ) : Prop :=
  lowerJHStar r s < lowerJH1 r s ∧ lowerJHStar r s < lowerJHBar r s ∧
  lowerJProd104 r s < (26/25:ℝ) ∧ (133/125:ℝ) < lowerJProd1064 r s
noncomputable def lowerJActual (p : LowerPair) (u v : ℝ) : ℝ :=
  let q := lowerNormalize p
  4+prefixEval q.1 u+prefixEval q.2 v
noncomputable def lowerJInnerA (p : LowerPair) (k : ℕ) : ℝ := lowerJActual p (lowerJIter k lowerJA) (lowerJIter k lowerJC)
noncomputable def lowerJInnerB (p : LowerPair) (k : ℕ) : ℝ := lowerJActual p (lowerJIter k lowerJB) (lowerJIter k lowerJB)
noncomputable def lowerJInner (p : LowerPair) (k : ℕ) : Set ℝ := Set.uIcc (lowerJInnerA p k) (lowerJInnerB p k)
noncomputable def lowerJEven (p : LowerPair) (k : ℕ) : Prop := ((lowerNormalize p).1.length+k)%2=0
noncomputable def lowerJFirstCross (p : LowerPair) (k : ℕ) : Prop :=
  if lowerJEven p k then lowerJInnerA p k < lowerJInnerB p (k+2)
  else lowerJInnerB p (k+2) < lowerJInnerA p k
noncomputable def lowerJReverseCross (p : LowerPair) (k : ℕ) : Prop :=
  if lowerJEven p k then lowerJInnerA p (k+2) < lowerJInnerB p k
  else lowerJInnerB p k < lowerJInnerA p (k+2)
noncomputable def lowerJInnerOrder (p : LowerPair) (k : ℕ) : Prop :=
  if lowerJEven p k then lowerJInnerA p k < lowerJInnerB p k else lowerJInnerB p k < lowerJInnerA p k
noncomputable def lowerJEqualQBounds (p : LowerPair) : Prop :=
  let q := lowerNormalize p
  (253/1000:ℝ)*((1+lowerRatio q.2*lowerTheta 3)*(1+lowerRatio q.2*lowerTheta 90))/
    ((1+lowerRatio q.1*lowerTheta 63)*(1+lowerRatio q.1*lowerTheta 66)) < lowerScale q ∧
  (269/1000:ℝ)*((1+lowerRatio q.2*lowerTheta 1)*(1+lowerRatio q.2*lowerTheta 28))/
    ((1+lowerRatio q.1*lowerTheta 65)*(1+lowerRatio q.1*lowerTheta 68)) < lowerScale q
noncomputable def lowerJEqualContact (p : LowerPair) : Prop :=
  0 < (-1:ℝ)^(lowerNormalize p).1.length *
    (lowerJActual p (lowerTheta 63) (lowerTheta 90)-lowerJActual p (lowerTheta 66) (lowerTheta 3)) ∧
  (7/5:ℝ)*lowerWidth ((lowerNormalize p).1++[1,1,3]) < lowerWidth ((lowerNormalize p).2++[3])
noncomputable def lowerJEqualForkFacts (p : LowerPair) : Prop :=
  let even := (lowerNormalize p).1.length % 2 = 0
  (lowerSourceEndpoint (lowerChild p ([1],[])) (decide (¬ even)) = lowerJActual p (lowerTheta 66) (lowerTheta 3)) ∧
  (lowerSourceEndpoint (lowerChild p ([1],[])) (decide even) = lowerJActual p (lowerTheta 90) (lowerTheta 90)) ∧
  (lowerSourceEndpoint (lowerChild p ([2],[])) (decide (¬ even)) = lowerJActual p (lowerTheta 30) (lowerTheta 3)) ∧
  (lowerSourceEndpoint (lowerChild p ([2],[])) (decide even) = lowerJActual p (lowerTheta 63) (lowerTheta 90))
end Freiman


