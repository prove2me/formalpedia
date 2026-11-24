-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedReducedPopulation
-- name    : Sensitivity214439_PairedSemantic_Solutions_PairedReducedPopulation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:28.415255+00:00
-- url     : https://prove2.me/theorems/ca64a2cc-4e19-4658-af2d-081ad96e6478
-- title:
--   Two-count reduction of graded population certificates
-- statement:
--   When all tiers below the last share a price, a four-tier population is priced using only its count $x$ below the tolerance tier and its count $y$ through that tier. The previous-tier and prefix accessors define these counts, and the CommonLowerPrice predicate records the price equality. TierAdmissible and ReducedAdmissible retain the geometric inequalities needed for $(x,y)$. A ReducedCertificate requires the fixed head cost plus $x$ times the lower price and $(y-x)$ times the last price to be at most the proposed bound for every admissible pair. The bundle also defines the tighter finite bounds and the fast certificate variant used by the literal checks.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PairedReducedPopulation.lean lines 12–248; SHA256 bb4f564266cfbd1a4b08b7a05c204f629f7b26199b735a5395226dcf43cb89d7; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityPairedPopulation
end SensitivityPairedPopulation



/-! The literal paired objectives have a common price on all tiers below the
last. Their finite population bound therefore needs two cumulative counts. -/
namespace SensitivityPairedPopulation

def TierAdmissible (data : GradedGeometry) (q : Fin 4) (size spent : ℕ) : Prop :=
  size ≤ data.originalCap q ∧ minimumEdges size data.alpha ≤ spent ∧
  (∀ m : Fin 7, optional (data.markerResidual m) (fun residual =>
    markedConstraint data.alpha size spent (m.val+1) residual ∧
    copyConstraint data.beta size spent (m.val+1) residual ∧
    markerQuadratic data.alpha data.beta q.val size (m.val+1) residual)) ∧
  optional data.powers (fun p => powerConstraints p size spent)

instance (data : GradedGeometry) (q : Fin 4) (size spent : ℕ) :
    Decidable (TierAdmissible data q size spent) := by
  unfold TierAdmissible
  infer_instance







def previousTier (q : Fin 4) : Fin 4 := Fin.ofNat 4 (q.val-1)

def previousCount (n : Population) (q : Fin 4) : ℕ :=
  if q.val = 0 then 0 else prefixCount n (previousTier q)









def ReducedAdmissible (data : GradedGeometry) (x y : ℕ) : Prop :=
  let q := data.tolerance.val
  x ≤ y ∧ (q = 0 → x = 0) ∧
    TierAdmissible data data.tolerance y (q*y-x) ∧
    (0 < q → TierAdmissible data (previousTier data.tolerance) x ((q-1)*x)) ∧
    (q = 1 → x+y ≤ data.forestBound ∧ x+y+data.highOne+data.highZero ≤ 3*data.alpha ∧
      ∀ m : Fin 7, optional (data.markerResidual m)
        (fun residual => markerForest data.alpha data.beta (x+y) (m.val+1) residual)) ∧
    (q = 2 → x ≤ data.forestBound ∧ x+data.highOne+data.highZero ≤ 3*data.alpha ∧
      ∀ m : Fin 7, optional (data.markerResidual m)
        (fun residual => markerForest data.alpha data.beta x (m.val+1) residual)) ∧
    optional data.lowOne (fun lo =>
      (q = 1 → x+y ≤ lo.populationPlusZero ∧ x ≤ lo.zero) ∧
      (q = 2 → x ≤ lo.populationPlusZero))

instance (data : GradedGeometry) (x y : ℕ) : Decidable (ReducedAdmissible data x y) := by
  unfold ReducedAdmissible
  infer_instance





def weightedCount (prices : Fin 4 → ℕ) (n : Population) (q : Fin 4) : ℕ :=
  n 0 * prices 0 + (if 1 ≤ q.val then n 1 * prices 1 else 0) +
    (if 2 ≤ q.val then n 2 * prices 2 else 0) + (if 3 ≤ q.val then n 3 * prices 3 else 0)

def CommonLowerPrice (prices : Fin 4 → ℕ) (q : Fin 4) : Prop :=
  ∀ k : Fin 4, k < q → prices k = prices (previousTier q)



def ReducedCertificate (data : GradedGeometry) (lowPrice lastPrice headCost bound : ℕ) : Prop :=
  ∀ y : Fin (data.originalCap data.tolerance+1), ∀ x : Fin (y.val+1),
    headCost+x.val*lowPrice+(y.val-x.val)*lastPrice ≤ bound ∨
      ¬ ReducedAdmissible data x.val y.val

instance (data : GradedGeometry) (lowPrice lastPrice headCost bound : ℕ) :
    Decidable (ReducedCertificate data lowPrice lastPrice headCost bound) := by
  unfold ReducedCertificate
  infer_instance



def previousCap (data : GradedGeometry) : ℕ :=
  if data.tolerance.val = 0 then 0 else data.originalCap (previousTier data.tolerance)





/-- Most high records satisfy the uniform two-tier cap immediately. Only
the remaining records need the full marker arithmetic reduction. -/
def FastReducedCertificate (data : GradedGeometry) (lowPrice lastPrice headCost bound : ℕ) : Prop :=
  (lastPrice ≤ lowPrice ∧ previousCap data ≤ data.originalCap data.tolerance ∧
    headCost+previousCap data*lowPrice+
      (data.originalCap data.tolerance-previousCap data)*lastPrice ≤ bound) ∨
  ReducedCertificate data lowPrice lastPrice headCost bound

instance (data : GradedGeometry) (lowPrice lastPrice headCost bound : ℕ) :
    Decidable (FastReducedCertificate data lowPrice lastPrice headCost bound) := by
  unfold FastReducedCertificate
  infer_instance








end SensitivityPairedPopulation


