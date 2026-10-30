-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P34
-- name    : QAlgorithms_Papers_Independent_Bridge50_P34
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T16:03:25.127156+00:00
-- url     : https://prove2.me/theorems/defa2b11-b110-4948-a951-ab32d32e1151
-- title:
--   Definitions for Continuity bounds for entanglement
-- statement:
--   The objects the formalized statements of *Continuity bounds for entanglement* (arXiv:quant-ph/9908086) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `fullTraceDistance`: PDF p.1: the full trace distance Tr|rho-sigma|.
--   - `purificationDistance`: PDF pp.2–3, (13),(16),(17): the PROOF-INTENDED minimum full trace norm distance of purifications, explicitly different from printed (10).
--   - `printedBures`: PDF p.2, literal (10). Used only in the uniform hypothesis (24).
--   - `outcomeVector`: PDF pp.2–3: unnormalized AB vector for reference outcome m. Columns of U are the measured orthonormal basis; conjugation is on the basis coordinate.
--   - `measuredAR`: PDF p.3, (11)–(12): postmeasurement A:Rprime state as unnormalized outcome blocks. No division by a possibly zero outcome probability occurs.
--   - `outcomeProbability`: PDF p.3: the classical outcome probabilities, with null outcomes allowed.
--   - `uniformMatrix`: PDF p.3, (20)–(23): completely mixed matrix, used only at d>0.
--   - `perturbedMatrix`: PDF p.3: the source's actual diagonal perturbation, physical for 0<epsilon*d<=1. The chosen basis vector is explicit.
--   - `EntanglementFamily`: PDF p.4: one functional family across ALL finite local dimensions. Values at non-density inputs are immaterial and never constrained or used.
--   - `groupedTensor`: PDF p.4: tensor product regrouped as (A,C):(B,D), with the explicit standard finite product indexing from Mathlib's finProdFinEquiv.
--   - `IsAdditive`: PDF pp.3–4: full tensor additivity, with the correct grouped local cut.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, https://arxiv.org/abs/quant-ph/9908086v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

/-!
Nielsen, Continuity bounds for entanglement, quant-ph/9908086v2, PDF pp.1–4.
All distances called fullTraceDistance have no factor 1/2; entropies are in bits.
SOURCE CORRECTION: (10) prints 2 sqrt(1-F) for ROOT fidelity F, but the identity
used in (16)–(18) requires 2 sqrt(1-F^2). The formation statements below expressly
use purificationDistance. They do not certify (18)/(19) with the printed scale.
The false literal pure-state identity is deferred in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P34

attribute [local instance] Classical.propDecidable Classical.decEq

-- Accepted definition providers, authorized by the independent-paper workflow.
open QAlgorithms.Papers.Independent.Information100.P08 (formation bellVector)
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open QAlgorithms.Papers.Independent.Support50.P42 (outcomeEntropy)

-- The supplied diagnostic timed out while elaborating the remote-control statement.
set_option maxHeartbeats 800000

/-- PDF p.1: the full trace distance Tr|rho-sigma|. -/
def fullTraceDistance {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ := traceNorm (rho - sigma)

/-- PDF pp.2–3, (13),(16),(17): the PROOF-INTENDED minimum full trace
norm distance of purifications, explicitly different from printed (10). -/
def purificationDistance {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ :=
  2 * Real.sqrt (1 - rootFidelity rho sigma ^ 2)

/-- PDF p.2, literal (10). Used only in the uniform hypothesis (24). -/
def printedBures {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ :=
  2 * Real.sqrt (1 - rootFidelity rho sigma)

/-- PDF pp.2–3: unnormalized AB vector for reference outcome m. Columns of U
are the measured orthonormal basis; conjugation is on the basis coordinate. -/
def outcomeVector {A B R : Type*} [Fintype R] [DecidableEq R]
    (psi : EuclideanSpace ℂ ((A × B) × R)) (U : Matrix.unitaryGroup R ℂ)
    (m : R) : EuclideanSpace ℂ (A × B) :=
  WithLp.toLp 2 fun ab => ∑ r, star ((U : Matrix R R ℂ) r m) * psi (ab, r)

/-- PDF p.3, (11)–(12): postmeasurement A:Rprime state as unnormalized
outcome blocks. No division by a possibly zero outcome probability occurs. -/
def measuredAR {A B R : Type*} [Fintype B] [Fintype R] [DecidableEq R]
    (psi : EuclideanSpace ℂ ((A × B) × R)) (U : Matrix.unitaryGroup R ℂ) :
    Matrix (A × R) (A × R) ℂ :=
  fun x y => if x.2 = y.2 then
    traceRight (pureDensity (outcomeVector psi U x.2)) x.1 y.1 else 0

/-- PDF p.3: the classical outcome probabilities, with null outcomes allowed. -/
def outcomeProbability {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq R]
    (psi : EuclideanSpace ℂ ((A × B) × R)) (U : Matrix.unitaryGroup R ℂ)
    (m : R) : ℝ := (pureDensity (outcomeVector psi U m)).trace.re

/-- PDF p.3, (20)–(23): completely mixed matrix, used only at d>0. -/
def uniformMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (1 / (d : ℂ)) • 1

/-- PDF p.3: the source's actual diagonal perturbation, physical for
0<epsilon*d<=1. The chosen basis vector is explicit. -/
def perturbedMatrix {d : ℕ} (i : Fin d) (epsilon : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  ((epsilon * d : ℝ) : ℂ) • pureDensity (ket i) +
    ((1 / (d : ℝ) - epsilon : ℝ) : ℂ) • 1

/-- PDF p.4: one functional family across ALL finite local dimensions.
Values at non-density inputs are immaterial and never constrained or used. -/
abbrev EntanglementFamily := (a b : ℕ) →
  Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ → ℝ

/-- PDF p.4: tensor product regrouped as (A,C):(B,D), with the explicit
standard finite product indexing from Mathlib's finProdFinEquiv. -/
def groupedTensor {a b c d : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (sigma : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) :
    Matrix (Fin (a*c) × Fin (b*d)) (Fin (a*c) × Fin (b*d)) ℂ :=
  fun x y =>
    let xa : Fin a × Fin c := finProdFinEquiv.symm x.1
    let xb : Fin b × Fin d := finProdFinEquiv.symm x.2
    let ya : Fin a × Fin c := finProdFinEquiv.symm y.1
    let yb : Fin b × Fin d := finProdFinEquiv.symm y.2
    rho (xa.1,xb.1) (ya.1,yb.1) * sigma (xa.2,xb.2) (ya.2,yb.2)

/-- PDF pp.3–4: full tensor additivity, with the correct grouped local cut. -/
def IsAdditive (M : EntanglementFamily) : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
  ∀ (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (sigma : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ),
    IsDensityMatrix rho → IsDensityMatrix sigma →
    M (a*c) (b*d) (groupedTensor rho sigma) = M a b rho + M c d sigma

/-! Sanity checks for the retained local interfaces; no source theorem is proved here. -/

example {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    fullTraceDistance rho rho = 0 := by simp [fullTraceDistance, traceNorm, cfc_zero]

example {A B R : Type*} [Fintype B] [Fintype R] [DecidableEq R]
    (U : Matrix.unitaryGroup R ℂ) :
    measuredAR (0 : EuclideanSpace ℂ ((A × B) × R)) U = 0 := by
  ext x y
  simp [measuredAR, outcomeVector, pureDensity, traceRight]

example : uniformMatrix 1 = 1 := by simp [uniformMatrix]

example (i : Fin 1) : perturbedMatrix i 1 = pureDensity (ket i) := by
  simp [perturbedMatrix]

example {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ)
    (h : rootFidelity rho sigma = 1) :
    purificationDistance rho sigma = 0 ∧ printedBures rho sigma = 0 := by
  simp [purificationDistance, printedBures, h]

example {A B R : Type*} [Fintype R] [DecidableEq R]
    (psi : EuclideanSpace ℂ ((A × B) × R)) (m : R) :
    outcomeVector psi 1 m = WithLp.toLp 2 (fun ab => psi (ab,m)) := by
  ext ab
  simp [outcomeVector, Matrix.one_apply]

example {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq R]
    (U : Matrix.unitaryGroup R ℂ) :
    outcomeEntropy (outcomeProbability (0 : EuclideanSpace ℂ ((A × B) × R)) U) = 0 := by
  simp [outcomeEntropy, outcomeProbability, outcomeVector, pureDensity, Matrix.trace]

example : IsAdditive (fun _ _ _ => 0) := by simp [IsAdditive]

end QAlgorithms.Papers.Independent.Bridge50.P34


