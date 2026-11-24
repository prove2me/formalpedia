-- Prove2me | Definitions.Def_ValueAwareRR_ProxyCounterexample
-- name    : ValueAwareRR_ProxyCounterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T08:52:02.148265+00:00
-- url     : https://prove2.me/theorems/ab54b343-e657-427e-b7c2-162ea8c71178
-- title:
--   Proxy Counterexample
-- statement:
--   Definitions and structural lemmas for Proxy Counterexample, from ipitchford (ipitchford/random-reshuffling-baseline-policy; see pinned CC0-1.0 LICENSE)'s pinned Unbounded proxy separation for random-reshuffling baseline policies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean

import Mathlib
set_option autoImplicit true
namespace ValueAwareRR
set_option backward.isDefEq.respectTransparency false in
/-- The twelve representatives whose first residual is negative. -/
inductive Representative
  | ABCD | ABDC | ACBD | ACDB | ADBC | ADCB
  | BACD | BADC | BCAD | BCDA | BDAC | BDCA
  deriving DecidableEq, Fintype
abbrev SignedOrder := Representative × Bool
def representativeOrder : Representative → Fin 4 → Fin 4
  | .ABCD => ![0, 1, 2, 3]
  | .ABDC => ![0, 1, 3, 2]
  | .ACBD => ![0, 2, 1, 3]
  | .ACDB => ![0, 2, 3, 1]
  | .ADBC => ![0, 3, 1, 2]
  | .ADCB => ![0, 3, 2, 1]
  | .BACD => ![1, 0, 2, 3]
  | .BADC => ![1, 0, 3, 2]
  | .BCAD => ![1, 2, 0, 3]
  | .BCDA => ![1, 2, 3, 0]
  | .BDAC => ![1, 3, 0, 2]
  | .BDCA => ![1, 3, 2, 0]
def negateLabel : Fin 4 → Fin 4 := ![3, 2, 1, 0]
def orderAt (o : SignedOrder) : Fin 4 → Fin 4 :=
  if o.2 then fun k => negateLabel (representativeOrder o.1 k)
  else representativeOrder o.1
theorem orderAt_bijective (o : SignedOrder) : Function.Bijective (orderAt o) := by
  rcases o with ⟨r, s⟩
  cases r <;> cases s <;> decide
noncomputable def encodedPermutation (o : SignedOrder) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (orderAt o) (orderAt_bijective o)
def signReverse (o : SignedOrder) : SignedOrder := (o.1, !o.2)
def trueOptimalOrder : SignedOrder := (.ACDB, false)
def proxySelectedOrder : SignedOrder := (.BDAC, false)
def familyA (m : ℚ) : ℚ := 3 * m - 1
def familyB (m : ℚ) : ℚ := 2 * m
def residual (m : ℚ) : Fin 4 → ℚ :=
  ![-familyA m, -familyB m, familyB m, familyA m]
def contraction : ℚ := 2 / 3
def stepSize : ℚ := 1 / 3
def orderedResidual (m : ℚ) (o : SignedOrder) (k : Fin 4) : ℚ :=
  residual m (orderAt o k)
def scalarUpdate (w r : ℚ) : ℚ := contraction * w - stepSize * r
def prefixOne (m : ℚ) (o : SignedOrder) : ℚ := orderedResidual m o 0
def prefixTwo (m : ℚ) (o : SignedOrder) : ℚ :=
  orderedResidual m o 0 + orderedResidual m o 1
def prefixThree (m : ℚ) (o : SignedOrder) : ℚ :=
  orderedResidual m o 0 + orderedResidual m o 1 + orderedResidual m o 2
def filteredSum (m : ℚ) (o : SignedOrder) : ℚ :=
  contraction ^ 2 * prefixOne m o + contraction * prefixTwo m o + prefixThree m o
def directEndpoint (m : ℚ) (o : SignedOrder) : ℚ :=
  let w1 := scalarUpdate 0 (orderedResidual m o 0)
  let w2 := scalarUpdate w1 (orderedResidual m o 1)
  let w3 := scalarUpdate w2 (orderedResidual m o 2)
  scalarUpdate w3 (orderedResidual m o 3)
def terminalLossFromFiltered (s : ℚ) : ℚ := (stepSize ^ 2 * s) ^ 2 / 2
def exactLoss (m : ℚ) (o : SignedOrder) : ℚ := terminalLossFromFiltered (filteredSum m o)
def excessLoss (w : ℚ) : ℚ := w ^ 2 / 2
def maxPrefixScore (m : ℚ) (o : SignedOrder) : ℚ :=
  max |prefixOne m o| (max |prefixTwo m o| |prefixThree m o|)
def diagonalScore (m : ℚ) (o : SignedOrder) : ℚ :=
  contraction ^ 4 * prefixOne m o ^ 2 +
    contraction ^ 2 * prefixTwo m o ^ 2 + prefixThree m o ^ 2
def lossRatio (m : ℚ) : ℚ :=
  exactLoss m proxySelectedOrder / exactLoss m trueOptimalOrder
def nineFilteredTable (m : ℚ) : Representative → ℚ
  | .ABCD => -69 * m + 19
  | .ABDC => -60 * m + 10
  | .ACBD => -45 * m + 19
  | .ACDB => 10
  | .ADBC => -30 * m + 4
  | .ADCB => 6 * m + 4
  | .BACD => -65 * m + 15
  | .BADC => -56 * m + 6
  | .BCAD => -35 * m + 9
  | .BCDA => 19 * m - 9
  | .BDAC => -20 * m - 6
  | .BDCA => 25 * m - 15
def maxPrefixTable (m : ℚ) : Representative → ℚ
  | .ABCD | .ABDC | .BACD | .BADC => 5 * m - 1
  | .BDAC => 2 * m
  | _ => 3 * m - 1
def diagonalMarginTable (m : ℚ) : Representative → ℚ
  | .ABCD => 1349 * (m - 2) ^ 2 + 4526 * (m - 2) + 3753
  | .ABDC => 944 * (m - 2) ^ 2 + 3392 * (m - 2) + 3024
  | .ACBD => 485 * (m - 2) ^ 2 + 1358 * (m - 2) + 873
  | .ACDB => 80 * (m - 2) ^ 2 + 224 * (m - 2) + 144
  | .ADBC | .ADCB => 44 * (m - 2) ^ 2 + 152 * (m - 2) + 108
  | .BACD => 1269 * (m - 2) ^ 2 + 4302 * (m - 2) + 3609
  | .BADC => 864 * (m - 2) ^ 2 + 3168 * (m - 2) + 2880
  | .BCAD | .BCDA => 369 * (m - 2) ^ 2 + 1062 * (m - 2) + 693
  | .BDAC => 0
  | .BDCA => 405 * (m - 2) ^ 2 + 1134 * (m - 2) + 729
def normalizationScale (m : ℚ) : ℚ := 1 / familyA m
def normalizedResidual (m : ℚ) (i : Fin 4) : ℚ :=
  normalizationScale m * residual m i
def normalizedOrderedResidual (m : ℚ) (o : SignedOrder) (k : Fin 4) : ℚ :=
  normalizedResidual m (orderAt o k)
def normalizedPrefixOne (m : ℚ) (o : SignedOrder) : ℚ :=
  normalizedOrderedResidual m o 0
def normalizedPrefixTwo (m : ℚ) (o : SignedOrder) : ℚ :=
  normalizedOrderedResidual m o 0 + normalizedOrderedResidual m o 1
def normalizedPrefixThree (m : ℚ) (o : SignedOrder) : ℚ :=
  normalizedOrderedResidual m o 0 + normalizedOrderedResidual m o 1 +
    normalizedOrderedResidual m o 2
def normalizedFilteredSum (m : ℚ) (o : SignedOrder) : ℚ :=
  contraction ^ 2 * normalizedPrefixOne m o +
    contraction * normalizedPrefixTwo m o + normalizedPrefixThree m o
def normalizedExactLoss (m : ℚ) (o : SignedOrder) : ℚ :=
  terminalLossFromFiltered (normalizedFilteredSum m o)
def normalizedMaxPrefixScore (m : ℚ) (o : SignedOrder) : ℚ :=
  max |normalizedPrefixOne m o|
    (max |normalizedPrefixTwo m o| |normalizedPrefixThree m o|)
def normalizedDiagonalScore (m : ℚ) (o : SignedOrder) : ℚ :=
  contraction ^ 4 * normalizedPrefixOne m o ^ 2 +
    contraction ^ 2 * normalizedPrefixTwo m o ^ 2 + normalizedPrefixThree m o ^ 2
def residualMax (m : ℚ) : ℚ :=
  max |residual m 0| (max |residual m 1| (max |residual m 2| |residual m 3|))
def normalizedResidualMax (m : ℚ) : ℚ :=
  max |normalizedResidual m 0|
    (max |normalizedResidual m 1|
      (max |normalizedResidual m 2| |normalizedResidual m 3|))
def normalizedLossRatio (m : ℚ) : ℚ :=
  normalizedExactLoss m proxySelectedOrder /
    normalizedExactLoss m trueOptimalOrder
def NaturalFamilyCertificate (m : ℕ) : Prop :=
  normalizedResidualMax (m : ℚ) = 1 ∧
  0 < normalizedExactLoss (m : ℚ) trueOptimalOrder ∧
  (∀ o : SignedOrder,
    normalizedExactLoss (m : ℚ) trueOptimalOrder ≤ normalizedExactLoss (m : ℚ) o) ∧
  (∀ o : SignedOrder,
    normalizedExactLoss (m : ℚ) o = normalizedExactLoss (m : ℚ) trueOptimalOrder ↔
      o = trueOptimalOrder ∨ o = signReverse trueOptimalOrder) ∧
  (∀ o : SignedOrder,
    normalizedMaxPrefixScore (m : ℚ) proxySelectedOrder ≤
      normalizedMaxPrefixScore (m : ℚ) o) ∧
  (∀ o : SignedOrder,
    normalizedMaxPrefixScore (m : ℚ) o =
        normalizedMaxPrefixScore (m : ℚ) proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder) ∧
  (∀ o : SignedOrder,
    normalizedDiagonalScore (m : ℚ) proxySelectedOrder ≤
      normalizedDiagonalScore (m : ℚ) o) ∧
  (∀ o : SignedOrder,
    normalizedDiagonalScore (m : ℚ) o =
        normalizedDiagonalScore (m : ℚ) proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder) ∧
  normalizedLossRatio (m : ℚ) = (10 * (m : ℚ) + 3) ^ 2 / 25 ∧
  4 * (m : ℚ) ^ 2 ≤ normalizedLossRatio (m : ℚ)
end ValueAwareRR


