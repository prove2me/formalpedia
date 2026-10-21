-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
-- name    : QAlgorithms_Papers_Independent_Next46_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T18:34:54.761605+00:00
-- url     : https://prove2.me/theorems/790e55cb-3a00-4089-ac9f-981ea835a730
-- title:
--   Definitions for Efficient Clifford+T approximation of single-qubit operators
-- statement:
--   The objects the formalized statements of *Efficient Clifford+T approximation of single-qubit operators* (arXiv:1212.6253) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `quadraticReal`: Positive real embedding of Z[sqrt(2)] (paper pp.3-4).
--   - `smallUnit`: The quadratic unit sqrt(2)-1, with inverse sqrt(2)+1 (Lemma 10, p.4).
--   - `rectangleSolutions`: Feasible quadratic integers in the two closed intervals of (16), p.6.
--   - `scaleUnit`: The positive real scaling unit used in Lemma 17(c), p.7.
--   - `basePoint`: Lemma 17(d), pp.7-8: its three explicit floor-based candidates and branch tests.
--   - `normalizedPoint`: Lemma 17(f), p.8: solve a normalized rectangle using (d), swaps and unit scaling. The second branch is the inverse of the transformations in (e), followed by (b).
--   - `RectangleRun`: Operational semantics of the explicit Lemma-17 constructor, pp.7-8. Each transition computes the displayed transformed endpoints and reverses the corresponding quadratic-unit multiplication. Cost is a padded primitive-operation budget: 50 for the fixed floor/branch base calculation, 20 per normalization step. These fixed budgets bound additions, multiplications, divisions, floors and comparisons; quadratic-integer multiplication by the fixed units uses a fixed number of integer operations. This relation contains no feasibility or correctness premise.
--   - `evenLift`: Corollary 19, p.8: multiply by sqrt(2), making the constant coefficient even.
--   - `ParityRun`: Corollary 19's two concrete calls to the rectangle constructor, p.8. The odd output is translated by 1 after solving the shifted rectangle.
--   - `IsCyclotomicInteger`: The coefficient presentation of Z[omega] in section 3.1, p.3.
--   - `zPhase`: Upper-left entry of Rz(theta), section 6.1, p.9.
--   - `zRotation`: Rz(theta) including its absolute phase, sections 2 and 6.1, pp.2,9.
--   - `completion`: The special completion (23), pp.8-9; this is not an arbitrary U(2) matrix.
--   - `unitDisk`: The closed complex unit disk, section 6.1, p.9.
--   - `epsilonRegion`: The cap (27), p.9, applied to the normalized coordinate, not the integer numerator.
--   - `IsCandidate`: Definition 20, p.9: candidate, including every number-theoretic condition. Primality is deliberately absent.
--   - `quadraticComplex`: The restricted Z[sqrt(2),i] coordinate used in Lemma 21, p.10.
--   - `normalizedBullet`: The conjugate of the normalized restricted coordinate, Lemma 21, p.10. The denominator (sqrt(2))^k acquires the sign (-1)^k under bullet conjugation.
--   - `candidateDefect`: The actual defect in (28), p.10, retaining the negative sqrt(2) coefficient.
--   - `Letter`: The four discrete generators of the paper's single-qubit gate words, p.1. There is no arbitrary global-phase constructor, ancilla, measurement or resource state.
--   - `letterMatrix`: Exact matrix of each generator, equation (1), p.1.
--   - `wordMatrix`: Chronological gate-list semantics: the first letter acts first (p.1).
--   - `tCount`: Number of actual T instructions in the gate list, p.1 footnote 1.
--   - `assemble`: Chronological assembly for the displayed matrix product A H B H D, section 7.2, p.12.
--   - `WorstCaseBound`: Worst-case lower-bound property, (36), p.13. The input follows the error threshold, while every possible approximating word follows the chosen hard input.
--   - `lowCountEvent`: The Haar event in section 9, p.13; approximating words may have any allowed determinant.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, https://arxiv.org/abs/1212.6253v2

import Definitions.Def_QAlgorithms_Defs_Gates

/-!
Statements from Selinger, arXiv:1212.6253v2. All new objects are paper-local.
The computational rectangle model counts exact real arithmetic, comparisons,
and integer floors; it makes no bit-runtime claim for unencoded real inputs.
See HARD.md for whole nodes whose computational clauses remain deferred.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set
open scoped ComplexConjugate

/-- Borel sigma-algebra on the actual SU(2) subgroup for the Haar statement, section 9, p.13. -/
instance su2MeasurableSpace : MeasurableSpace (Matrix.specialUnitaryGroup Bool ℂ) :=
  borel (Matrix.specialUnitaryGroup Bool ℂ)

/-- The measurable structure used for section 9, p.13, is exactly Borel, not an arbitrary one. -/
instance su2BorelSpace : BorelSpace (Matrix.specialUnitaryGroup Bool ℂ) where
  measurable_eq := rfl

/-- Positive real embedding of Z[sqrt(2)] (paper pp.3-4). -/
abbrev quadraticReal : Zsqrtd 2 →+* ℝ := Zsqrtd.toReal (by norm_num)

/-- The quadratic unit sqrt(2)-1, with inverse sqrt(2)+1 (Lemma 10, p.4). -/
def smallUnit : (Zsqrtd 2)ˣ where
  val := ⟨-1, 1⟩
  inv := ⟨1, 1⟩
  val_inv := by ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul]
  inv_val := by ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul]

/-- Feasible quadratic integers in the two closed intervals of (16), p.6. -/
def rectangleSolutions (x0 x1 y0 y1 : ℝ) : Set (Zsqrtd 2) :=
  {a | quadraticReal a ∈ Icc x0 x1 ∧ quadraticReal (star a) ∈ Icc y0 y1}

/-- The positive real scaling unit used in Lemma 17(c), p.7. -/
def scaleUnit : ℝ := 1 + Real.sqrt 2

/-- Lemma 17(d), pp.7-8: its three explicit floor-based candidates and branch tests. -/
def basePoint (x y : ℝ) : Zsqrtd 2 :=
  let a : ℤ := Int.floor ((x + y + Real.sqrt 2) / 2) + 1
  let b : ℤ := Int.floor ((x - y - Real.sqrt 2) / (2 * Real.sqrt 2)) + 1
  if (a : ℝ) - (b : ℝ) * Real.sqrt 2 ≤ y + Real.sqrt 2 then ⟨a, b⟩
  else if (a : ℝ) + (b : ℝ) * Real.sqrt 2 ≤ x + 1 then ⟨a, b + 1⟩
  else ⟨a - 1, b⟩

/-- Lemma 17(f), p.8: solve a normalized rectangle using (d), swaps and unit scaling.
The second branch is the inverse of the transformations in (e), followed by (b). -/
def normalizedPoint (x y delta : ℝ) : Zsqrtd 2 :=
  if Real.sqrt 2 < delta then star (basePoint y x)
  else (⟨1, -1⟩ : Zsqrtd 2) * basePoint (-scaleUnit * (x + 1)) (y / scaleUnit)

/-- Operational semantics of the explicit Lemma-17 constructor, pp.7-8.
Each transition computes the displayed transformed endpoints and reverses the
corresponding quadratic-unit multiplication. Cost is a padded primitive-operation
budget: 50 for the fixed floor/branch base calculation, 20 per normalization step.
These fixed budgets bound additions, multiplications, divisions, floors and comparisons;
quadratic-integer multiplication by the fixed units uses a fixed number of integer operations.
This relation contains no feasibility or correctness premise. -/
inductive RectangleRun : ℝ → ℝ → ℝ → ℝ → Zsqrtd 2 → ℕ → Prop where
  | base {x0 x1 y0 y1 : ℝ} (hlo : 1 < x1 - x0) (hhi : x1 - x0 ≤ scaleUnit) :
      RectangleRun x0 x1 y0 y1 (normalizedPoint x0 y0 (x1 - x0)) 50
  | expand {x0 x1 y0 y1 : ℝ} {a : Zsqrtd 2} {cost : ℕ}
      (h : x1 - x0 ≤ 1)
      (next : RectangleRun (scaleUnit * x0) (scaleUnit * x1)
        (-y1 / scaleUnit) (-y0 / scaleUnit) a cost) :
      RectangleRun x0 x1 y0 y1 ((smallUnit : Zsqrtd 2) * a) (cost + 20)
  | contract {x0 x1 y0 y1 : ℝ} {a : Zsqrtd 2} {cost : ℕ}
      (h : scaleUnit < x1 - x0)
      (next : RectangleRun (x0 / scaleUnit) (x1 / scaleUnit)
        (-scaleUnit * y1) (-scaleUnit * y0) a cost) :
      RectangleRun x0 x1 y0 y1 (((smallUnit⁻¹ : (Zsqrtd 2)ˣ) : Zsqrtd 2) * a)
        (cost + 20)

/-- Corollary 19, p.8: multiply by sqrt(2), making the constant coefficient even. -/
def evenLift (a : Zsqrtd 2) : Zsqrtd 2 := ⟨2 * a.im, a.re⟩

/-- Corollary 19's two concrete calls to the rectangle constructor, p.8.
The odd output is translated by 1 after solving the shifted rectangle. -/
def ParityRun (x0 x1 y0 y1 : ℝ) (ae ao : Zsqrtd 2) (cost : ℕ) : Prop :=
  ∃ be bo : Zsqrtd 2, ∃ ce co : ℕ,
    RectangleRun (x0 / Real.sqrt 2) (x1 / Real.sqrt 2)
      (-y1 / Real.sqrt 2) (-y0 / Real.sqrt 2) be ce ∧
    RectangleRun ((x0 - 1) / Real.sqrt 2) ((x1 - 1) / Real.sqrt 2)
      (-(y1 - 1) / Real.sqrt 2) (-(y0 - 1) / Real.sqrt 2) bo co ∧
    ae = evenLift be ∧ ao = evenLift bo + 1 ∧ cost = ce + co + 30

/-- The coefficient presentation of Z[omega] in section 3.1, p.3. -/
def IsCyclotomicInteger (u : ℂ) : Prop :=
  ∃ a b c d : ℤ, u = (a : ℂ) * (QAlgorithms.gateT true true) ^ 3 +
    (b : ℂ) * (QAlgorithms.gateT true true) ^ 2 +
    (c : ℂ) * QAlgorithms.gateT true true + (d : ℂ)

/-- Upper-left entry of Rz(theta), section 6.1, p.9. -/
def zPhase (theta : ℝ) : ℂ := Complex.exp (-Complex.I * (theta : ℂ) / 2)

/-- Rz(theta) including its absolute phase, sections 2 and 6.1, pp.2,9. -/
def zRotation (theta : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then Complex.exp (Complex.I * (theta : ℂ) / 2)
    else zPhase theta

/-- The special completion (23), pp.8-9; this is not an arbitrary U(2) matrix. -/
def completion (k : ℕ) (u t : ℂ) : Matrix Bool Bool ℂ :=
  let denom : ℂ := (Real.sqrt ((2 : ℝ) ^ k) : ℂ)
  fun i j => if i then (if j then star (u / denom) else t / denom)
    else (if j then -star (t / denom) else u / denom)

/-- The closed complex unit disk, section 6.1, p.9. -/
def unitDisk : Set ℂ := {u | Complex.normSq u ≤ 1}

/-- The cap (27), p.9, applied to the normalized coordinate, not the integer numerator. -/
def epsilonRegion (eps theta : ℝ) : Set ℂ :=
  {u | u ∈ unitDisk ∧ 1 - eps ^ 2 / 2 ≤ (star u * zPhase theta).re}

/-- Definition 20, p.9: candidate, including every number-theoretic condition.
Primality is deliberately absent. -/
def IsCandidate (eps theta : ℝ) (k : ℕ) (u : ℂ) : Prop :=
  IsCyclotomicInteger u ∧ (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ epsilonRegion eps theta ∧
    ∃ xi : Zsqrtd 2,
      (quadraticReal xi : ℂ) = (2 : ℂ) ^ k - star u * u ∧
      Odd xi.re ∧ Even xi.im ∧ 0 ≤ quadraticReal xi ∧ 0 ≤ quadraticReal (star xi)

/-- The restricted Z[sqrt(2),i] coordinate used in Lemma 21, p.10. -/
def quadraticComplex (alpha beta : Zsqrtd 2) : ℂ :=
  (quadraticReal alpha : ℂ) + (quadraticReal beta : ℂ) * Complex.I

/-- The conjugate of the normalized restricted coordinate, Lemma 21, p.10.
The denominator (sqrt(2))^k acquires the sign (-1)^k under bullet conjugation. -/
def normalizedBullet (k : ℕ) (alpha beta : Zsqrtd 2) : ℂ :=
  (-1 : ℂ) ^ k * (quadraticComplex (star alpha) (star beta) /
    (Real.sqrt ((2 : ℝ) ^ k) : ℂ))

/-- The actual defect in (28), p.10, retaining the negative sqrt(2) coefficient. -/
def candidateDefect (k : ℕ) (alpha beta : Zsqrtd 2) : Zsqrtd 2 :=
  (2 : Zsqrtd 2) ^ k - alpha ^ 2 - beta ^ 2

/-- The four discrete generators of the paper's single-qubit gate words, p.1.
There is no arbitrary global-phase constructor, ancilla, measurement or resource state. -/
inductive Letter where
  | h | s | t | phase
  deriving DecidableEq

/-- Exact matrix of each generator, equation (1), p.1. -/
def letterMatrix : Letter → Matrix Bool Bool ℂ
  | .h => QAlgorithms.hadamard
  | .s => QAlgorithms.phaseS
  | .t => QAlgorithms.gateT
  | .phase => (QAlgorithms.gateT true true) • (1 : Matrix Bool Bool ℂ)

/-- Chronological gate-list semantics: the first letter acts first (p.1). -/
def wordMatrix (c : List Letter) : Matrix Bool Bool ℂ :=
  (c.map letterMatrix).reverse.prod

/-- Number of actual T instructions in the gate list, p.1 footnote 1. -/
def tCount (c : List Letter) : ℕ := (c.filter fun g => g == Letter.t).length

/-- Chronological assembly for the displayed matrix product A H B H D, section 7.2, p.12. -/
def assemble (a b d : List Letter) : List Letter :=
  d ++ [Letter.h] ++ b ++ [Letter.h] ++ a

/-- Worst-case lower-bound property, (36), p.13. The input follows the error threshold,
while every possible approximating word follows the chosen hard input. -/
def WorstCaseBound (K : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ U : Matrix.specialUnitaryGroup Bool ℂ,
    ∀ c : List Letter, QAlgorithms.specNorm (wordMatrix c - (U : Matrix Bool Bool ℂ)) ≤ eps →
      K + 3 * Real.logb 2 (1 / eps) ≤ (tCount c : ℝ)

/-- The Haar event in section 9, p.13; approximating words may have any allowed determinant. -/
def lowCountEvent (K eps : ℝ) (deficit : ℕ) : Set (Matrix.specialUnitaryGroup Bool ℂ) :=
  {U | ∃ c : List Letter,
    (tCount c : ℝ) ≤ K + 3 * Real.logb 2 (1 / eps) - (deficit : ℝ) ∧
    QAlgorithms.specNorm (wordMatrix c - (U : Matrix Bool Bool ℂ)) ≤ eps}

example : su2MeasurableSpace = borel (Matrix.specialUnitaryGroup Bool ℂ) := rfl

example : QAlgorithms.gateT true true = Complex.exp (Complex.I * Real.pi / 4) := by
  simp [QAlgorithms.gateT]

example : quadraticReal (0 : Zsqrtd 2) = 0 := map_zero quadraticReal

example : ((smallUnit : Zsqrtd 2) * ((smallUnit⁻¹ : (Zsqrtd 2)ˣ) : Zsqrtd 2)) = 1 := by
  exact smallUnit.val_inv

example : evenLift (⟨3, 2⟩ : Zsqrtd 2) = ⟨4, 3⟩ := rfl

example : (candidateDefect 1 (⟨1, 1⟩ : Zsqrtd 2) 0).im = -2 := by decide

example : IsCyclotomicInteger 0 := by
  refine ⟨0, 0, 0, 0, ?_⟩
  simp

example : completion 0 1 0 false false = 1 := by
  simp [completion]

example : letterMatrix Letter.t = QAlgorithms.gateT := rfl

example : wordMatrix [] = 1 := rfl

example : wordMatrix [Letter.h] = QAlgorithms.hadamard := by
  simp [wordMatrix, letterMatrix]

example : tCount [Letter.s, Letter.t, Letter.h, Letter.phase] = 1 := by decide

example (x0 x1 y0 y1 : ℝ) (hlo : 1 < x1 - x0) (hhi : x1 - x0 ≤ scaleUnit) :
    RectangleRun x0 x1 y0 y1 (normalizedPoint x0 y0 (x1 - x0)) 50 :=
  RectangleRun.base hlo hhi

end QAlgorithms.Papers.Independent.Next46.P21


