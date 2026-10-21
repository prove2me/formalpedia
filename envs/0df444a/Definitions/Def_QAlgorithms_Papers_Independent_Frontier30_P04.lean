-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P04
-- name    : QAlgorithms_Papers_Independent_Frontier30_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:16:24.276219+00:00
-- url     : https://prove2.me/theorems/133b2f87-5c09-4a0b-b2f5-1c95103a9bd2
-- title:
--   Definitions for Measuring Gaussian quantum information and correlations using the Renyi entropy of order 2
-- statement:
--   The objects that formalizations building on *Measuring Gaussian quantum information and correlations using the Renyi entropy of order 2* (arXiv:1203.5116) are stated in. Every numbered result of this paper itself was deferred, so it has no mission of its own; its definitions are published for the papers that import them.
--
--   - `modePhase`: PDF p.2: interleaved indices `(mode, q-or-p)`, with q=0 and p=1. This is a phase-space index, not the quantum Hilbert-space dimension.
--   - `PhaseSpace`: PDF p.2: real phase space of n modes, including the zero-dimensional space.
--   - `Covariance`: PDF p.2: real covariance arrays. Physicality and association to a density operator are separate requirements, not consequences of this abbreviation.
--   - `covarianceBlock`: PDF pp.2-3, Eqs.(8),(12): principal block retaining whole named modes. Compatibility with an actual partial trace is not assumed or asserted here.
--   - `differentialEntropy`: PDF p.2, Eq.(6): differential entropy functional on a Lebesgue-integrable entropy integrand. Positivity and normalization belong to the law being used.
--   - `relativeSamplingEntropy`: PDF pp.2,7, Eqs.(7),(A5): ordered relative sampling entropy functional. Applications require positive densities; integrability is carried explicitly.
--   - `conditionalCovariance`: PDF p.3, Eq.(12): Schur-complement matrix construction. On physical data `B + seed` is positive definite. This raw matrix function does not assert that an arbitrary input is a conditional quantum state.
--   - `twoModeStandard`: PDF p.7, Eq.(B1): standard two-mode covariance array in interleaved order. The physical domain requires the full uncertainty inequality, not just `a,b ≥ 1`.
--   - `seedRotation`: PDF p.8, Eq.(B6): rotation convention fixing the sign of cos(2 phi).
--   - `pureSeed`: PDF p.8, Eqs.(B4)-(B6): finite pure seed covariance, with positive squeezing parameter. The optimization uses phi in [0,2 pi]; this periodic matrix is defined for every real phi. No infinite-squeezing density is included.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Papers.Independent.Frontier30.P04

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
# Gaussian Renyi-2 information: preliminary source objects

Source: Adesso, Girolami, Serafini, arXiv:1203.5116v3, PDF pp.2-3,7-8.
These are only finite phase-space and matrix constructions. They do not represent
Gaussian density operators, Wigner transforms, or Gaussian measurement instruments.
All 23 result nodes are explicitly deferred in the assigned HARD.md and GAPS.json.
No determinant-only surrogate for a density-operator statement is asserted.
Compilation is pending the requested batch handoff.
-/

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Frontier30.P04

/-- PDF p.2: interleaved indices `(mode, q-or-p)`, with q=0 and p=1.
This is a phase-space index, not the quantum Hilbert-space dimension. -/
abbrev modePhase (n : ℕ) := Fin n × Fin 2

/-- PDF p.2: real phase space of n modes, including the zero-dimensional space. -/
abbrev PhaseSpace (n : ℕ) := EuclideanSpace ℝ (modePhase n)

/-- PDF p.2: real covariance arrays. Physicality and association to a density
operator are separate requirements, not consequences of this abbreviation. -/
abbrev Covariance (n : ℕ) := Matrix (modePhase n) (modePhase n) ℝ

/-! PDF p.2: the canonical CCR form is reused from the accepted
`QAlgorithms.Papers.Independent.Dependency50.P10.sigma`. Its indices are grouped
`Fin n ⊕ Fin n` (all q, then all p), whereas the covariance arrays below use
interleaved `(mode, q-or-p)` indices. No implicit identification of these orders
is made, and no physicality predicate is applied to the raw arrays here. -/

/-- PDF pp.2-3, Eqs.(8),(12): principal block retaining whole named modes.
Compatibility with an actual partial trace is not assumed or asserted here. -/
def covarianceBlock {m n : ℕ} (G : Covariance n) (e : Fin m ↪ Fin n) :
    Covariance m :=
  G.submatrix (fun i => (e i.1, i.2)) (fun i => (e i.1, i.2))

/-- PDF p.2, Eq.(6): differential entropy functional on a Lebesgue-integrable
entropy integrand. Positivity and normalization belong to the law being used. -/
def differentialEntropy {n : ℕ} (P : PhaseSpace n → ℝ)
    (_h : Integrable (fun x => P x * Real.log (P x))) : ℝ :=
  -(∫ x, P x * Real.log (P x))

/-- PDF pp.2,7, Eqs.(7),(A5): ordered relative sampling entropy functional.
Applications require positive densities; integrability is carried explicitly. -/
def relativeSamplingEntropy {n : ℕ} (P Q : PhaseSpace n → ℝ)
    (_h : Integrable (fun x => P x * Real.log (P x / Q x))) : ℝ :=
  ∫ x, P x * Real.log (P x / Q x)

/-- PDF p.3, Eq.(12): Schur-complement matrix construction. On physical data
`B + seed` is positive definite. This raw matrix function does not assert that
an arbitrary input is a conditional quantum state. -/
def conditionalCovariance {nA nB : ℕ} (A : Covariance nA) (B : Covariance nB)
    (C : Matrix (modePhase nA) (modePhase nB) ℝ) (seed : Covariance nB) :
    Covariance nA :=
  A - C * (B + seed)⁻¹ * C.transpose

/-- PDF p.7, Eq.(B1): standard two-mode covariance array in interleaved order.
The physical domain requires the full uncertainty inequality, not just `a,b ≥ 1`. -/
def twoModeStandard (a b cPlus cMinus : ℝ) : Covariance 2 :=
  fun i j => if i.1 = j.1 then
    if i.2 = j.2 then if i.1 = 0 then a else b else 0
  else if i.2 = j.2 then if i.2 = 0 then cPlus else cMinus else 0

/-- PDF p.8, Eq.(B6): rotation convention fixing the sign of cos(2 phi). -/
def seedRotation (phi : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then
    if j = 0 then Real.cos phi else -Real.sin phi
  else if j = 0 then Real.sin phi else Real.cos phi

/-- PDF p.8, Eqs.(B4)-(B6): finite pure seed covariance, with positive squeezing
parameter. The optimization uses phi in [0,2 pi]; this periodic matrix is defined
for every real phi. No infinite-squeezing density is included. -/
def pureSeed (lambda phi : ℝ) (_hlambda : 0 < lambda) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  seedRotation phi * Matrix.diagonal (fun i => if i = 0 then lambda else 1 / lambda) *
    (seedRotation phi).transpose

/-! Small source-convention sanity examples; these are not paper-result nodes. -/

example : QAlgorithms.Papers.Independent.Dependency50.P10.sigma 1
    (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp [QAlgorithms.Papers.Independent.Dependency50.P10.sigma]

example : QAlgorithms.Papers.Independent.Dependency50.P10.sigma 1
    (Sum.inr 0) (Sum.inl 0) = -1 := by
  simp [QAlgorithms.Papers.Independent.Dependency50.P10.sigma]

example : QAlgorithms.Papers.Independent.Dependency50.P10.sigma 0 = 0 := by
  ext i j
  cases i with
  | inl k => exact Fin.elim0 k
  | inr k => exact Fin.elim0 k

example (a b cPlus cMinus : ℝ) :
    twoModeStandard a b cPlus cMinus (0, 0) (1, 0) = cPlus := by
  norm_num [twoModeStandard]

example : seedRotation 0 0 0 = 1 := by
  simp [seedRotation]

example {nA nB : ℕ} (A : Covariance nA) (B seed : Covariance nB) :
    conditionalCovariance A B 0 seed = A := by
  simp [conditionalCovariance]

end QAlgorithms.Papers.Independent.Frontier30.P04


