-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28
-- name    : QAlgorithms_Papers_Independent_Frontier30_P28
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:14:43.184002+00:00
-- url     : https://prove2.me/theorems/8bc00fc5-8dd3-4608-9c72-e53c3bfaaa00
-- title:
--   Definitions for Contractivity of positive and trace preserving maps under $L_p$ norms
-- statement:
--   The objects the formalized statements of *Contractivity of positive and trace preserving maps under $L_p$ norms* (arXiv:math-ph/0601063) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `restrictedPNorm`: Induced norm on a specified input domain, PDF pp.2,4–6. Using an extended nonnegative supremum guards against unbounded real suprema. All domains occurring below contain zero, hence their unit balls are nonempty.
--   - `inducedPNorm`: Full induced norm on all complex matrices, source PDF p.2.
--   - `InHermitianTraceZero`: H_0 is precisely the traceless Hermitian domain, source PDF p.4.
--   - `inverseExponent`: Reciprocal exponent with the source convention 1/infinity = 0, PDF p.2.
--   - `generalBound`: Sharp unrestricted bound from Theorem II.1, PDF p.2.
--   - `traceChannel`: Ordinary trace as a map to M_1, canonically identified with C, PDF p.2.
--   - `hermitianTraceZeroBound`: Theorem III.1's sharp constant, PDF p.4; used only for n ≥ 2, p ≥ 1. The infinity endpoint is its limit floor(n/2), not the finite-p formula with top.toReal substituted. Finite odd powers and divisions are real operations.
--   - `nonunitalOffset`: The constructed traceless correction N = (T(I)-I)/n, source PDF p.5. The dimension n is the square matrix size, not an independently supplied rank.
--   - `traceTerm`: A ↦ N tr(A) as a complex-linear map, source PDF p.5.
--   - `unitalPart`: The uniquely constructed unital part T_1 = T - N tr, source PDF p.5.
-- source:
--   Contractivity of positive and trace preserving maps under Lₚ norms, arXiv:math-ph/0601063v1, https://arxiv.org/abs/math-ph/0601063v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

/-!
Statements from Pérez-García, Wolf, Petz and Ruskai,
"Contractivity of positive and trace preserving maps under Lp norms",
arXiv:math-ph/0601063v1. Only the ten stateable original-result nodes are included.
The two erroneous claims on PDF p.6 are documented in the unit's HARD.md.

All dimensions in the results are positive. Trace is unnormalized, and maps are
complex linear. Supremum norms take values in ENNReal, so an unbounded supremum
cannot collapse to zero. The results assert finite bounds; this is equivalent to
the source's real induced norms. No boundedness conclusion is assumed.
-/

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

-- Reuse the pinned accepted library as explicitly required by this repair.
-- M and Lin carry the same Fin-indexed complex matrices and complex linearity.
open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Induced norm on a specified input domain, PDF pp.2,4–6.
Using an extended nonnegative supremum guards against unbounded real suprema.
All domains occurring below contain zero, hence their unit balls are nonempty. -/
def restrictedPNorm {n r : ℕ} (p : ℝ≥0∞) (T : Lin n r)
    (D : M n → Prop) : ℝ≥0∞ :=
  ⨆ A : {A : M n // D A ∧ schattenNorm p A ≤ 1},
    ENNReal.ofReal (schattenNorm p (T A.val))

/-- Full induced norm on all complex matrices, source PDF p.2. -/
def inducedPNorm {n r : ℕ} (p : ℝ≥0∞) (T : Lin n r) : ℝ≥0∞ :=
  restrictedPNorm p T (fun _ => True)

/-- H_0 is precisely the traceless Hermitian domain, source PDF p.4. -/
def InHermitianTraceZero {n : ℕ} (A : M n) : Prop :=
  A.IsHermitian ∧ A.trace = 0

/-- Reciprocal exponent with the source convention 1/infinity = 0, PDF p.2. -/
def inverseExponent (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then 0 else 1 / p.toReal

/-- Sharp unrestricted bound from Theorem II.1, PDF p.2. -/
def generalBound (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  Real.rpow (n : ℝ) (1 - inverseExponent p)

/-- Ordinary trace as a map to M_1, canonically identified with C, PDF p.2. -/
def traceChannel (n : ℕ) : Lin n 1 where
  toFun A := fun _ _ => A.trace
  map_add' A B := by
    ext i j
    exact Matrix.trace_add A B
  map_smul' c A := by
    ext i j
    exact Matrix.trace_smul c A

/-- Theorem III.1's sharp constant, PDF p.4; used only for n ≥ 2, p ≥ 1.
The infinity endpoint is its limit floor(n/2), not the finite-p formula with
top.toReal substituted. Finite odd powers and divisions are real operations. -/
def hermitianTraceZeroBound (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then (n / 2 : ℕ)
  else if Even n then Real.rpow ((n : ℝ) / 2) (1 - inverseExponent p)
  else Real.rpow
    (Real.rpow 2 (2 - p.toReal) /
      (Real.rpow ((n : ℝ) - 1) (1 - p.toReal) +
       Real.rpow ((n : ℝ) + 1) (1 - p.toReal)))
    (inverseExponent p)

/-- The constructed traceless correction N = (T(I)-I)/n, source PDF p.5.
The dimension n is the square matrix size, not an independently supplied rank. -/
def nonunitalOffset {n : ℕ} (T : Lin n n) : M n :=
  ((n : ℂ)⁻¹) • (T 1 - 1)

/-- A ↦ N tr(A) as a complex-linear map, source PDF p.5. -/
def traceTerm {n : ℕ} (N : M n) : Lin n n where
  toFun A := A.trace • N
  map_add' A B := by
    simp only [Matrix.trace_add, add_smul]
  map_smul' c A := by
    simp [smul_smul]

/-- The uniquely constructed unital part T_1 = T - N tr, source PDF p.5. -/
def unitalPart {n : ℕ} (T : Lin n n) : Lin n n :=
  T - traceTerm (nonunitalOffset T)

/-- Endpoint sanity check for the exportable accepted trace-norm interface. -/
example {n : ℕ} (A : M n) : schattenNorm 1 A = QAlgorithms.traceNorm A := by
  have hsqrt : (fun t : ℝ => Real.rpow t ((1 : ℝ) / 2)) = Real.sqrt := by
    funext t
    exact (Real.sqrt_eq_rpow t).symm
  unfold schattenNorm QAlgorithms.traceNorm
  rw [if_neg ENNReal.one_ne_top, ENNReal.toReal_one,
    div_self (one_ne_zero : (1 : ℝ) ≠ 0)]
  exact (Real.rpow_one _).trans
    (congrArg (fun f : ℝ → ℝ => (cfc f (Aᴴ * A)).trace.re) hsqrt)

/-- Endpoint sanity check: infinity uses the spectral operator norm. -/
example {n : ℕ} (A : M n) : schattenNorm ⊤ A = QAlgorithms.specNorm A := by
  simp [schattenNorm]

/-- Reciprocal infinity is zero. -/
example : inverseExponent ⊤ = 0 := by
  simp [inverseExponent]

/-- The qutrit sharp infinity constant is one. -/
example : hermitianTraceZeroBound 3 ⊤ = 1 := by
  norm_num [hermitianTraceZeroBound]

/-- Positive and trace-preserving identity maps exist in every source dimension. -/
example (n : ℕ) : IsPositiveMap (LinearMap.id : Lin n n) ∧
    TracePreserving (LinearMap.id : Lin n n) := by
  constructor
  · intro A hA
    exact hA
  · intro A
    rfl

/-- The trace channel really returns the ordinary trace in its unique entry. -/
example (n : ℕ) (A : M n) : traceChannel n A 0 0 = A.trace := rfl

/-- An already unital map has zero nonunital correction. -/
example {n : ℕ} (T : Lin n n) (h : IsUnital T) : nonunitalOffset T = 0 := by
  change T 1 = 1 at h
  simp [nonunitalOffset, h]

/-- The decomposition reconstructs the original map before imposing any positivity. -/
example {n : ℕ} (T : Lin n n) :
    unitalPart T + traceTerm (nonunitalOffset T) = T := by
  simp [unitalPart]

end QAlgorithms.Papers.Independent.Frontier30.P28


