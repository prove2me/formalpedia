-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
-- name    : QAlgorithms_Papers_Independent_Gap48_P40
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:14:59.994375+00:00
-- url     : https://prove2.me/theorems/4abe591b-6497-4bf7-a2c9-52aaa655afe3
-- title:
--   Definitions for Continuity bounds on the quantum relative entropy
-- statement:
--   The objects the formalized statements of *Continuity bounds on the quantum relative entropy* (arXiv:quant-ph/0503218) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `matrixE`: PDF p.2, Eq.(7): rank-one diagonal matrix E (used only for d>0).
--   - `matrixF`: PDF p.2, Eq.(8): F=Diag(1,-1,0,...), used only for d>=2.
--   - `rescaled`: PDF p.3: rescaled norm of a difference. Theorems require a genuine UI norm and d>=2.
--   - `minimumAt`: PDF p.6, Eq.(21): extended infimum at the raw (unrescaled) norm distance T. Empty constraint sets have value +infinity, rather than the real empty-infimum default.
--   - `binaryProfile`: PDF p.7, Eq.(26): s(x) is the binary minimization. Its extension at x=1 is +infinity. Only 0<=x<=1 is used; finiteness on 0<x<1 is a conclusion below.
--   - `qubitObjectiveOne`: PDF p.9, Eq.(44): the actual first objective, as a real finite entropy. The imported pureDensity constructs the canonical projector at cos(2 alpha)=t; its unit vector on [-1,1] is (sqrt((1+t)/2), sqrt((1-t)/2)). The reference is positive definite on the theorem's domain, so toReal is finite.
--   - `qubitObjectiveTwo`: PDF p.9, Eq.(45): second objective, including zero residual weight at T=1-beta. The imported pureDensity constructs the same canonical projector as in (44). The reference is positive definite on the theorem's domain, so toReal is finite.
--   - `qubitSmallBound`: PDF p.10, Eq.(46). Zero-weight logarithmic terms have continuous value zero.
--   - `qubitLargeBound`: PDF p.10, Eq.(47).
--   - `traceSmallBound`: PDF p.12, Eq.(55). Here beta>0 and 0<=T<=beta in all uses.
--   - `smallSigma`: PDF p.11: sigma=beta I+(1-d beta)|e3><e3|, with 0-based coordinate 2.
--   - `smallRho`: PDF p.11: the source constructs rho from sigma and Delta=T F.
--   - `largeEta`: PDF p.12, Eq.(54): eta is computed from d,J,beta,T.
--   - `largeRho`: PDF p.12, Eq.(54): K=d-3-J; the last coordinate is the beta+eta entry.
--   - `largeSigma`: PDF p.12, Eq.(54): the second coordinate is the residual T-J beta.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, https://arxiv.org/abs/quant-ph/0503218v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

/-! Statements from Audenaert–Eisert, quant-ph/0503218v3.
Natural logarithms, positive finite dimensions, and support-aware signed Umegaki entropy.
The four defective source claims are recorded separately in HARD.md. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator
open Filter MeasureTheory Asymptotics
open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.2, Eq.(7): rank-one diagonal matrix E (used only for d>0). -/
def matrixE (d : ℕ) : Mat d := Matrix.diagonal fun i => if i.val = 0 then 1 else 0

/-- PDF p.2, Eq.(8): F=Diag(1,-1,0,...), used only for d>=2. -/
def matrixF (d : ℕ) : Mat d :=
  Matrix.diagonal fun i => if i.val = 0 then 1 else if i.val = 1 then -1 else 0

/-- PDF p.3: rescaled norm of a difference. Theorems require a genuine UI norm and d>=2. -/
def rescaled {d : ℕ} (N : Mat d → ℝ) (A : Mat d) : ℝ := N A / N (matrixF d)

/-- PDF p.6, Eq.(21): extended infimum at the raw (unrescaled) norm distance T.
Empty constraint sets have value +infinity, rather than the real empty-infimum default. -/
def minimumAt (d : ℕ) (N : Mat d → ℝ) (T : ℝ) : EReal :=
  sInf {v | ∃ rho sigma : Mat d, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
    N (rho - sigma) = T ∧ v = relativeEntropy rho sigma}

/-- PDF p.7, Eq.(26): s(x) is the binary minimization. Its extension at x=1 is +infinity.
Only 0<=x<=1 is used; finiteness on 0<x<1 is a conclusion below. -/
def binaryProfile (x : ℝ) : EReal :=
  sInf {v | ∃ r : ℝ, 0 < r ∧ r < 1 - x ∧ v = relativeEntropy (Matrix.diagonal ![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)])
      (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)])}

/-- PDF p.9, Eq.(44): the actual first objective, as a real finite entropy.
The imported pureDensity constructs the canonical projector at cos(2 alpha)=t;
its unit vector on [-1,1] is (sqrt((1+t)/2), sqrt((1-t)/2)).
The reference is positive definite on the theorem's domain, so toReal is finite. -/
def qubitObjectiveOne (beta T t : ℝ) : ℝ :=
  let psi : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(Real.sqrt ((1 + t) / 2) : ℂ),
    (Real.sqrt ((1 - t) / 2) : ℂ)]
  (relativeEntropy
    (Matrix.diagonal ![((beta + T : ℝ) : ℂ), ((beta - T : ℝ) : ℂ)] +
      ((1 - 2 * beta : ℝ) : ℂ) • pureDensity psi)
    (Matrix.diagonal ![(beta : ℂ), (beta : ℂ)] +
      ((1 - 2 * beta : ℝ) : ℂ) • pureDensity psi)).toReal

/-- PDF p.9, Eq.(45): second objective, including zero residual weight at T=1-beta.
The imported pureDensity constructs the same canonical projector as in (44).
The reference is positive definite on the theorem's domain, so toReal is finite. -/
def qubitObjectiveTwo (beta T t : ℝ) : ℝ :=
  let psi : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(Real.sqrt ((1 + t) / 2) : ℂ),
    (Real.sqrt ((1 - t) / 2) : ℂ)]
  (relativeEntropy
    (Matrix.diagonal ![((beta + T : ℝ) : ℂ), 0] +
      ((1 - beta - T : ℝ) : ℂ) • pureDensity psi)
    (Matrix.diagonal ![(beta : ℂ), (T : ℂ)] +
      ((1 - beta - T : ℝ) : ℂ) • pureDensity psi)).toReal

/-- PDF p.10, Eq.(46). Zero-weight logarithmic terms have continuous value zero. -/
def qubitSmallBound (beta T : ℝ) : ℝ :=
  (T + 1 - beta) * Real.log ((T + 1 - beta) / (1 - beta)) +
    (beta - T) * Real.log (1 - T / beta)

/-- PDF p.10, Eq.(47). -/
def qubitLargeBound (beta T : ℝ) : ℝ :=
  max (-Real.log (1 - T)) ((beta + T) * Real.log (1 + T / beta) +
    (1 - beta - T) * Real.log (1 - T / (1 - beta)))

/-- PDF p.12, Eq.(55). Here beta>0 and 0<=T<=beta in all uses. -/
def traceSmallBound (beta T : ℝ) : ℝ :=
  (beta + T) * Real.log ((beta + T) / beta) +
    (beta - T) * Real.log ((beta - T) / beta)

/-- PDF p.11: sigma=beta I+(1-d beta)|e3><e3|, with 0-based coordinate 2. -/
def smallSigma (d : ℕ) (beta : ℝ) : Mat d :=
  Matrix.diagonal fun i => ((if i.val = 2 then beta + (1 - d * beta) else beta : ℝ) : ℂ)

/-- PDF p.11: the source constructs rho from sigma and Delta=T F. -/
def smallRho (d : ℕ) (beta T : ℝ) : Mat d :=
  smallSigma d beta + (T : ℂ) • matrixF d

/-- PDF p.12, Eq.(54): eta is computed from d,J,beta,T. -/
def largeEta (d J : ℕ) (beta T : ℝ) : ℝ :=
  1 - T - ((d : ℝ) - 1 - J) * beta

/-- PDF p.12, Eq.(54): K=d-3-J; the last coordinate is the beta+eta entry. -/
def largeRho (d J : ℕ) (beta T : ℝ) : Mat d :=
  Matrix.diagonal fun i => ((if i.val = 0 then T + beta
    else if i.val = 1 then 0 else if i.val < 2 + J then 0
    else if i.val + 1 = d then beta + largeEta d J beta T else beta : ℝ) : ℂ)

/-- PDF p.12, Eq.(54): the second coordinate is the residual T-J beta. -/
def largeSigma (d J : ℕ) (beta T : ℝ) : Mat d :=
  Matrix.diagonal fun i => ((if i.val = 0 then beta
    else if i.val = 1 then T - J * beta
    else if i.val + 1 = d then beta + largeEta d J beta T else beta : ℝ) : ℂ)

/-! Small definitional sanity checks; no result from the paper is proved here. -/

example : matrixE 2 0 0 = 1 := by simp [matrixE]

example : matrixF 2 1 1 = -1 := by simp [matrixF]

example {d : ℕ} (N : Mat d → ℝ) (A : Mat d) :
    rescaled N A = N A / N (matrixF d) := rfl

example {d : ℕ} (B : Mat d) : (relativeEntropy (0 : Mat d) B).toReal = 0 := by
  simp [relativeEntropy, QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported, cfc_zero]

example : binaryProfile 1 = ⊤ := by
  have h : {v : EReal | ∃ r : ℝ, 0 < r ∧ r < 1 - (1 : ℝ) ∧
      v = relativeEntropy (Matrix.diagonal ![((r + 1 : ℝ) : ℂ), ((1 - r - 1 : ℝ) : ℂ)])
      (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)])} = ∅ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro r hr
    linarith [hr.1, hr.2.1]
  rw [binaryProfile, h, sInf_empty]

example {d : ℕ} (N : Mat d → ℝ) (T : ℝ) :
    minimumAt d N T = sInf {v | ∃ rho sigma : Mat d,
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧ N (rho - sigma) = T ∧
        v = relativeEntropy rho sigma} := rfl

example (beta T t : ℝ) : qubitObjectiveOne beta T t =
  let psi : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(Real.sqrt ((1 + t) / 2) : ℂ),
    (Real.sqrt ((1 - t) / 2) : ℂ)]
  (relativeEntropy
    (Matrix.diagonal ![((beta + T : ℝ) : ℂ), ((beta - T : ℝ) : ℂ)] +
      ((1 - 2 * beta : ℝ) : ℂ) • pureDensity psi)
    (Matrix.diagonal ![(beta : ℂ), (beta : ℂ)] +
      ((1 - 2 * beta : ℝ) : ℂ) • pureDensity psi)).toReal := rfl

example (beta T t : ℝ) : qubitObjectiveTwo beta T t =
  let psi : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(Real.sqrt ((1 + t) / 2) : ℂ),
    (Real.sqrt ((1 - t) / 2) : ℂ)]
  (relativeEntropy
    (Matrix.diagonal ![((beta + T : ℝ) : ℂ), 0] +
      ((1 - beta - T : ℝ) : ℂ) • pureDensity psi)
    (Matrix.diagonal ![(beta : ℂ), (T : ℂ)] +
      ((1 - beta - T : ℝ) : ℂ) • pureDensity psi)).toReal := rfl

example : qubitSmallBound (1 / 2) 0 = 0 := by norm_num [qubitSmallBound]

example : qubitLargeBound (1 / 2) 0 = 0 := by norm_num [qubitLargeBound]

example : traceSmallBound (1 / 2) 0 = 0 := by norm_num [traceSmallBound]

example : smallSigma 3 (1 / 3) 2 2 = (1 / 3 : ℂ) := by norm_num [smallSigma]

example (d : ℕ) (b : ℝ) : smallRho d b 0 = smallSigma d b := by simp [smallRho]

example : largeEta 3 0 (1 / 4) (1 / 2) = 0 := by norm_num [largeEta]

example : largeRho 3 0 (1 / 4) (1 / 2) 1 1 = 0 := by norm_num [largeRho]

example : largeSigma 3 0 (1 / 4) (1 / 2) 1 1 = (1 / 2 : ℂ) := by
  norm_num [largeSigma]

end QAlgorithms.Papers.Independent.Gap48.P40


