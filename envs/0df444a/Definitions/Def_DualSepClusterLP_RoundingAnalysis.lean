-- Prove2me | Definitions.Def_DualSepClusterLP_RoundingAnalysis
-- name    : DualSepClusterLP_RoundingAnalysis
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-19T07:54:14.3319+00:00
-- url     : https://prove2.me/theorems/4bbbbcba-c872-4592-b2a7-c4af5511cf7b
-- title:
--   Pair budgets, conditional-affine pivot rules and round-by-round cost accounting
-- statement:
--   For a feasible cluster LP, the co-membership mass of a pair or triple is the total column weight containing its vertices. The model defines the cluster-based and pivot budgets at $2773/2000$, the clipped affine joining rule, and the difference between expected released credit and cost. The weight $1012/25$ multiplies the variance correction for the pivot. The normalized sums define the one-round inequalities over the live vertices. A deterministic trace assigns a removal round to each vertex and records the released budget and incurred disagreements at each label. The graph uses its upper triangle and counts unordered pairs once.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper 79, §7, equations (29)–(47), and Appendix F. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Definitions.Def_DualSepClusterLP_LinearProgram

namespace DualSepClusterLP

/-- LP mass of all columns containing both vertices (paper equation (29)). -/
noncomputable def pairMass {n : ℕ} (z : Finset (Fin n) → ℝ) (i j : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S ∧ j ∈ S then z S else 0

def edgeLPCost (positive : Bool) (y : ℝ) : ℝ := if positive then 1-y else y

/-- The disagreement budget for cluster-based rounding (31). -/
noncomputable def clusterEdgeBudget (positive : Bool) (y : ℝ) : ℝ :=
  if positive then 2*(1-y)/(2-y) else y/(2-y)

/-- The conditional-affine pivot budget at α = 2773/2000 (36). -/
noncomputable def pivotEdgeBudget (positive : Bool) (y : ℝ) : ℝ :=
  if positive then 2*(2773/1227)*(1-y)^2/(2-y)
  else (2773/1227)*y*(3-2*y)/(2-y)

noncomputable def budgetTotal {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (f : Bool → ℝ → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then f (G i j) (pairMass z i j) else 0

end DualSepClusterLP
namespace DualSepClusterLP

noncomputable def tripleMass {n : ℕ} (z : Finset (Fin n) → ℝ) (i j k : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S ∧ j ∈ S ∧ k ∈ S then z S else 0

end DualSepClusterLP
namespace DualSepClusterLP

/-- Released edge budget less the disagreement charged when S is made the next cluster. -/
noncomputable def clockPairSlack {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  (if i ∈ S ∨ j ∈ S then clusterEdgeBudget (G i j) (pairMass z i j) else 0) -
    (if G i j then (if decide (i ∈ S) != decide (j ∈ S) then 1 else 0)
     else (if i ∈ S ∧ j ∈ S then 1 else 0))

def ClockStepOK {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ) : Prop :=
  ∀ W : Finset (Fin n), W.Nonempty → ∃ S : Finset (Fin n),
    0 < z S ∧ (W ∩ S).Nonempty ∧
      0 ≤ ∑ i ∈ W, ∑ j ∈ W, if i < j then clockPairSlack G z S i j else 0

end DualSepClusterLP
namespace DualSepClusterLP

noncomputable def pivotRescue (y : ℝ) : ℝ := max 0 (min 1 ((13/6)*(y-1/2)))

noncomputable def pivotMean (positive : Bool) (y : ℝ) : ℝ :=
  if positive then y+(1-y)*pivotRescue y else min ((3/2)*y) (2*y-y^2)

noncomputable def pivotIncidentPay (positive : Bool) (y : ℝ) : ℝ :=
  if positive then 1 - pivotMean positive y else pivotMean positive y

noncomputable def pivotGamma (positive : Bool) (y : ℝ) : ℝ :=
  if positive then 1-pivotRescue y else 0

noncomputable def varianceShape (positive : Bool) (y : ℝ) : ℝ :=
  if positive then y*(1-y)^2 else 0

/-- Equations (38)--(40). x,y correspond to the two incident edges;
z is the mass of the opposite edge and h is the triple mass. -/
noncomputable def oppositeSlack (sx sy sz : Bool) (x y z h : ℝ) : ℝ :=
  let m := pivotMean sx x
  let m' := pivotMean sy y
  let j := m*m' + pivotGamma sx x * pivotGamma sy y * (h-x*y)
  (m+m'-j) * pivotEdgeBudget sz z - (if sz then m+m'-2*j else j)

/-- The surplus relative to the covariance term at a single pivot of a triangle.
The two incident edges and then the opposite edge are specified in that order. -/
noncomputable def triangleSurplus (sx sy sz : Bool) (x y z h : ℝ) : ℝ :=
  oppositeSlack sx sy sz x y z h -
    2*(1012/25)*varianceShape sx x*varianceShape sy y*(h-x*y)

/-- The sign and pair-value subscripts are in cyclic edge order (uv,vw,wu). -/
def TriangleCertificate : Prop :=
  ∀ (s₁ s₂ s₃ : Bool) (x y z h : ℝ),
    x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → z ∈ Set.Icc (0:ℝ) 1 →
    0 ≤ h → x+y-1 ≤ h → y+z-1 ≤ h → z+x-1 ≤ h →
    h ≤ x → h ≤ y → h ≤ z →
    0 ≤ triangleSurplus s₁ s₃ s₂ x z y h +
      triangleSurplus s₂ s₁ s₃ y x z h + triangleSurplus s₃ s₂ s₁ z y x h

/-- The graph model stores unordered signs only in its strict upper triangle. -/
def unorderedSign {n : ℕ} (G : Graph n) (i j : Fin n) : Bool := G (min i j) (max i j)

/-- Expected budget released less cost at pivot u. In the sum over ordered
triples, v=w encodes an incident edge and half weight accounts for the two
orders of the opponents of a distinct pivot. -/
noncomputable def pivotEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v w : Fin n) : ℝ :=
  if u=v ∨ u=w then 0
  else if v=w then
    pivotEdgeBudget (unorderedSign G u v) (pairMass z u v) -
      pivotIncidentPay (unorderedSign G u v) (pairMass z u v)
  else
    oppositeSlack (unorderedSign G u v) (unorderedSign G u w) (unorderedSign G v w)
      (pairMass z u v) (pairMass z u w) (pairMass z v w) (tripleMass z u v w)/2

def PivotStepOK {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ) : Prop :=
  ∀ W : Finset (Fin n), 0 ≤ ∑ u ∈ W, ∑ v ∈ W, ∑ w ∈ W, pivotEntry G z u v w

end DualSepClusterLP

namespace DualSepClusterLP

/-- The labels of the output blocks give their emission order. A pair is decided
in the first round in which one of the two endpoints is removed. -/
noncomputable def roundTraceMargin {n : ℕ} (G : Graph n) (C : Clustering n)
    (z : Finset (Fin n) → ℝ) (budget : Bool → ℝ → ℝ) (r : Fin n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ min (C i) (C j) = r then
      budget (G i j) (pairMass z i j) - (if G i j ≠ decide (C i = C j) then 1 else 0)
    else 0

def RoundTraceOK {n : ℕ} (G : Graph n) (C : Clustering n) (z : Finset (Fin n) → ℝ)
    (budget : Bool → ℝ → ℝ) : Prop :=
  ∀ r : Fin n, 0 ≤ roundTraceMargin G C z budget r

end DualSepClusterLP
namespace DualSepClusterLP

noncomputable def signedTriangleSurplus (s₁ s₂ s₃ : Bool) (x y z h : ℝ) : ℝ :=
  triangleSurplus s₁ s₃ s₂ x z y h +
    triangleSurplus s₂ s₁ s₃ y x z h + triangleSurplus s₃ s₂ s₁ z y x h

noncomputable def tripleLower (x y z : ℝ) : ℝ :=
  max 0 (max (x+y-1) (max (y+z-1) (z+x-1)))

noncomputable def tripleUpper (x y z : ℝ) : ℝ := min x (min y z)

end DualSepClusterLP


