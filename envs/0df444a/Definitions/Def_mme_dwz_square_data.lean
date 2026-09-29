-- Prove2me | Definitions.Def_mme_dwz_square_data
-- name    : mme_dwz_square_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T09:47:06.684204+00:00
-- url     : https://prove2.me/theorems/6388c0ab-5dea-4a18-9252-3f1318f1fdc2
-- title:
--   DWZ Equation (25): exact q=6 second-power data
-- statement:
--   Transcribe the fifteen level-2 component shapes and weights from
--   DWZ Table 2, with a=0.03477403 and b=0.00021015 as exact rationals. Define the
--   Section 6.3 split distributions, Definition 6.4's typical distribution gamma,
--   Lemma 6.7's closed compatibility exponent, Algorithm 2's same-marginal entropy
--   maximum, all Section 6.3 component lower-bound bases for q=6, and the complete
--   right-hand side `squareRate tau` of Equation (25). The module also proves the
--   finite normalization and nonnegativity checks; it contains no asserted value
--   or exponent bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Definition 6.4, Lemma 6.7, Equation (25), Section 6.3 and Table 2 (printed pp. 54-59).

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Definitions.Def_mme_modern_entropy_data

/-!
# The exact Duan--Wu--Zhou second-power witness

This module transcribes the joint distribution and restricted Z-splits from
Table 2 of Duan--Wu--Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*.  It also gives the closed right-hand side of their Equation (25),
specialized to `q = 6` and to the level-2 component-value formulas in Section
6.3.

All printed decimal parameters are interpreted as exact terminating decimals.
The ordering is exactly the row-major component ordering in Table 2.  In
particular, `(1,3,0)` precedes `(3,0,1)`.
-/

open BigOperators Finset

namespace MME.DWZSquare

/-! ## Table 2 -/

/-- X-coordinate of the fifteen level-2 component shapes, in Table 2 order. -/
def shapeX : Fin 15 → Fin 5 :=
  ![0, 0, 4, 0, 0, 1, 1, 3, 3, 0, 2, 2, 1, 1, 2]

/-- Y-coordinate of the fifteen level-2 component shapes, in Table 2 order. -/
def shapeY : Fin 15 → Fin 5 :=
  ![0, 4, 0, 1, 3, 0, 3, 0, 1, 2, 0, 2, 1, 2, 1]

/-- Z-coordinate of the fifteen level-2 component shapes, in Table 2 order. -/
def shapeZ : Fin 15 → Fin 5 :=
  ![4, 0, 0, 3, 1, 3, 0, 1, 0, 2, 2, 0, 2, 1, 1]

/-- Every listed component is a level-2 component. -/
theorem shape_sum (s : Fin 15) :
    (shapeX s).val + (shapeY s).val + (shapeZ s).val = 4 := by
  fin_cases s <;> rfl

/-- Table 2's joint component distribution. -/
noncomputable def alpha : Fin 15 → ℝ := fun s ↦
  (![20860, 24731, 24731,
      1211153, 1333318, 1211153, 1251758, 1333318, 1251758,
      10366945, 10366945, 10045791,
      20088623, 20734458, 20734458] s : ℝ) / 100000000

/-- Table 2's parameter `a` for `(0,2,2)` and `(2,0,2)`. -/
noncomputable def splitA : ℝ := 3477403 / 100000000

/-- Table 2's parameter `b` for `(1,1,2)`. -/
noncomputable def splitB : ℝ := 21015 / 100000000

theorem alpha_sum : ∑ s, alpha s = 1 := by
  norm_num [alpha, Fin.sum_univ_succ]

theorem alpha_pos (s : Fin 15) : 0 < alpha s := by
  fin_cases s <;> norm_num [alpha]

/-- The Section 6.3 Z-split distribution attached to a component. -/
noncomputable def zSplit (s : Fin 15) : Fin 3 → ℝ :=
  if s = 9 ∨ s = 10 then
    ![splitA, 1 - 2 * splitA, splitA]
  else if s = 12 then
    ![splitB, 1 - 2 * splitB, splitB]
  else if shapeZ s = 0 then
    ![1, 0, 0]
  else if shapeZ s = 1 then
    ![1 / 2, 1 / 2, 0]
  else if shapeZ s = 3 then
    ![0, 1 / 2, 1 / 2]
  else
    ![0, 0, 1]

theorem zSplit_sum (s : Fin 15) : ∑ r, zSplit s r = 1 := by
  fin_cases s <;>
    simp [zSplit, shapeZ, splitA, splitB, Fin.sum_univ_succ] <;>
    norm_num

theorem zSplit_nonneg (s : Fin 15) (r : Fin 3) : 0 ≤ zSplit s r := by
  fin_cases s <;> fin_cases r <;>
    simp [zSplit, shapeZ, splitA, splitB] <;>
    norm_num

/-! ## Definitions 6.4 and 6.7 -/

/-- The typical pair distribution `gamma` from Definition 6.4. -/
noncomputable def gamma : Fin 3 × Fin 3 → ℝ := fun r ↦
  ∑ s : Fin 15,
    if (shapeZ s).val = r.1.val + r.2.val then
      alpha s * zSplit s r.1
    else 0

/-- `alpha(+,+,k)` in Lemma 6.7. -/
noncomputable def plusMass (k : Fin 5) : ℝ :=
  ∑ s : Fin 15,
    if shapeZ s = k ∧ shapeX s ≠ 0 ∧ shapeY s ≠ 0 then alpha s else 0

/-- `tilde alpha_(+,+,k)` in Lemma 6.7. -/
noncomputable def plusSplit (k : Fin 5) : Fin 3 → ℝ := fun r ↦
  if plusMass k = 0 then 0 else
    (∑ s : Fin 15,
      if shapeZ s = k ∧ shapeX s ≠ 0 ∧ shapeY s ≠ 0 then
        alpha s * zSplit s r
      else 0) / plusMass k

/-- `log₂(alpha_P)`, the compatibility exponent in Lemma 6.7. -/
noncomputable def logAlphaP : ℝ :=
  mme_modern_entropyBits (mme_modern_marginal shapeZ alpha) -
    mme_modern_entropyBits gamma +
    (∑ s : Fin 15,
      if shapeX s = 0 ∨ shapeY s = 0 then
        alpha s * mme_modern_entropyBits (zSplit s)
      else 0) +
    ∑ k : Fin 5, plusMass k * mme_modern_entropyBits (plusSplit k)

/-! ## Algorithm 2's same-marginal maximum -/

def sameMarginalEntropyValues : Set ℝ :=
  {h | ∃ p : Fin 15 → ℝ,
    (∀ s, 0 ≤ p s) ∧
    (∑ s, p s = 1) ∧
    (∀ i, mme_modern_marginal shapeX p i =
      mme_modern_marginal shapeX alpha i) ∧
    (∀ i, mme_modern_marginal shapeY p i =
      mme_modern_marginal shapeY alpha i) ∧
    (∀ i, mme_modern_marginal shapeZ p i =
      mme_modern_marginal shapeZ alpha i) ∧
    h = mme_modern_entropyBits p}

/-- `log₂(max_{α'∈Dα} α_N')` in Algorithm 2. -/
noncomputable def maxSameMarginalEntropy : ℝ :=
  sSup sameMarginalEntropyValues

/-- A rational additive-potential certificate for the Table 2 distribution.
The coefficients were rounded to seven decimal places; their maximum residual
is below `4·10⁻⁶` bits. -/
noncomputable def entropyLambdaZero : ℝ := 134993787 / 10000000

noncomputable def entropyLambdaX : Fin 5 → ℝ :=
  ![-128631760 / 10000000, -70036778 / 10000000,
    -20985623 / 10000000, -1980051 / 10000000, 0]

noncomputable def entropyLambdaY : Fin 5 → ℝ :=
  ![-128631760 / 10000000, -70036778 / 10000000,
    -20985623 / 10000000, -1980051 / 10000000, 0]

noncomputable def entropyLambdaZ : Fin 5 → ℝ :=
  ![-126175945 / 10000000, -66670346 / 10000000,
    -18075760 / 10000000, 0, 0]

noncomputable def entropyEpsilon : ℝ := 1 / 250000

/-- The logarithm of Equation (25)'s retained-copy factor. -/
noncomputable def retainedLogRate : ℝ :=
  min
    (mme_modern_entropyBits alpha +
      mme_modern_entropyBits (mme_modern_marginal shapeX alpha) -
      maxSameMarginalEntropy)
    (mme_modern_entropyBits (mme_modern_marginal shapeZ alpha) - logAlphaP)

/-! ## Section 6.3 component values -/

/-- The Section 6.3 lower-bound base for each level-2 component at `q=6`. -/
noncomputable def componentBase (tau : ℝ) : Fin 15 → ℝ := fun s ↦
  if s.val ≤ 2 then
    1
  else if s.val ≤ 8 then
    Real.rpow 12 tau
  else if s = 9 ∨ s = 10 then
    Real.rpow
      (Real.rpow 6 (2 * (1 - 2 * splitA)) /
        (Real.rpow splitA (2 * splitA) *
          Real.rpow (1 - 2 * splitA) (1 - 2 * splitA))) tau
  else if s = 11 then
    Real.rpow 38 tau
  else if s = 12 then
    Real.rpow
        (4 / (Real.rpow (1 - 2 * splitB) (1 - 2 * splitB) *
          Real.rpow splitB (2 * splitB))) (1 / 3) *
      Real.rpow 6 ((2 - 2 * splitB) * tau)
  else
    Real.rpow 2 (2 / 3) * Real.rpow 6 tau *
      Real.rpow (Real.rpow 6 (3 * tau) + 2) (1 / 3)

/-- `log₂(alpha_V_tau)` in Equation (25). -/
noncomputable def componentLogRate (tau : ℝ) : ℝ :=
  ∑ s : Fin 15, alpha s * (Real.log (componentBase tau s) / Real.log 2)

/-- Equation (25)'s right-hand side, specialized to Section 6.3 and Table 2. -/
noncomputable def squareRate (tau : ℝ) : ℝ :=
  Real.rpow 2 (retainedLogRate + componentLogRate tau)

end MME.DWZSquare


