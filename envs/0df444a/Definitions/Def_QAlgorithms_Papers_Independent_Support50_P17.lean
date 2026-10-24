-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17
-- name    : QAlgorithms_Papers_Independent_Support50_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T19:57:57.843438+00:00
-- url     : https://prove2.me/theorems/3c30cc74-effe-452c-8a6c-f541bd8c0f97
-- title:
--   Definitions for Continuity bounds on the quantum relative entropy - II
-- statement:
--   The objects the formalized statements of *Continuity bounds on the quantum relative entropy - II* (arXiv:1105.2656) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `zeroExtendedLogCorrection`: PDF p.6, (13), and p.8: the continuous zero-alpha extension of the correction. Only alpha,T ≥ 0 are used in statements.
--   - `regularisedRelativeEntropy`: PDF p.2 and p.9, (21): fixed dimension-dependent positive normalization c. The arguments shifted by I have trace d+1, not one.
--   - `resolventIntegrand`: PDF p.3, (6): the genuine resolvent integrand, with s meaning sI.
--   - `logarithmDerivativeMap`: PDF p.3, (6): entrywise Lebesgue integral for the logarithmic derivative map. For B positive definite every entry is integrable on (0,infinity); the actual convergence needed in Lemma 3 is included in its conclusion, not assumed. The definition's values outside this domain are not used.
--   - `propositionA`: PDF p.8: the first explicit extremal matrix of Proposition 1.
--   - `propositionB`: PDF p.8: the second explicit extremal matrix of Proposition 1.
--   - `regularisedRho`: PDF p.9: Diag(1−t,t,0), padded with zeros in higher dimensions. The sharpness statement uses d≥3.
--   - `regularisedSigma`: PDF p.9: Diag(1−t,0,t), padded with zeros in higher dimensions.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, https://arxiv.org/abs/1105.2656v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

/-!
Statements from Audenaert and Eisert, arXiv:1105.2656v3, PDF pp.2–9.
All logarithms are natural. The shifted matrices are never renormalized.
The arbitrary-path part of Lemma 1 and the dimensional necessity remark are
explicitly deferred in HARD.md; the separately displayed linear formula is retained.
The support and signed entropy definitions are imported from the pinned accepted
Dependency50.P21 module, as explicitly required by the repair instructions.
The other imports are Mathlib and frozen Defs modules.
Compilation is pending the batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.
open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF p.6, (13), and p.8: the continuous zero-alpha extension of the correction.
Only alpha,T ≥ 0 are used in statements. -/
def zeroExtendedLogCorrection (alpha T : ℝ) : ℝ :=
  if alpha = 0 then 0 else -alpha * Real.log (1 + T / alpha)

/-- PDF p.2 and p.9, (21): fixed dimension-dependent positive normalization c.
The arguments shifted by I have trace d+1, not one. -/
def regularisedRelativeEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℝ) (rho sigma : Matrix I I ℂ) : EReal :=
  (c : EReal) * relativeEntropy (rho + 1) (sigma + 1)

/-- PDF p.3, (6): the genuine resolvent integrand, with s meaning sI. -/
def resolventIntegrand {I : Type*} [Fintype I] [DecidableEq I]
    (B D : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
  (B + (s : ℂ) • (1 : Matrix I I ℂ))⁻¹ * D *
    (B + (s : ℂ) • (1 : Matrix I I ℂ))⁻¹

/-- PDF p.3, (6): entrywise Lebesgue integral for the logarithmic derivative map.
For B positive definite every entry is integrable on (0,infinity); the actual
convergence needed in Lemma 3 is included in its conclusion, not assumed.
The definition's values outside this domain are not used. -/
def logarithmDerivativeMap {I : Type*} [Fintype I] [DecidableEq I]
    (B D : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => ∫ s in Set.Ioi (0 : ℝ), resolventIntegrand B D s i j

/-- PDF p.8: the first explicit extremal matrix of Proposition 1. -/
def propositionA (alpha T : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((1 + T : ℝ) : ℂ), (alpha : ℂ)]

/-- PDF p.8: the second explicit extremal matrix of Proposition 1. -/
def propositionB (alpha T : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 : ℂ), ((T + alpha : ℝ) : ℂ)]

/-- PDF p.9: Diag(1−t,t,0), padded with zeros in higher dimensions.
The sharpness statement uses d≥3. -/
def regularisedRho (d : ℕ) (t : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i =>
    if i.val = 0 then ((1 - t : ℝ) : ℂ) else if i.val = 1 then (t : ℂ) else 0

/-- PDF p.9: Diag(1−t,0,t), padded with zeros in higher dimensions. -/
def regularisedSigma (d : ℕ) (t : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i =>
    if i.val = 0 then ((1 - t : ℝ) : ℂ) else if i.val = 2 then (t : ℂ) else 0

/-- PDF p.2: a matrix is supported in itself. -/
example {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    IsSupported A A := le_rfl

/-- PDF p.3, (2): the scalar identity has zero divergence from itself. -/
example : relativeEntropy (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  have hs : IsSupported (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 := le_rfl
  simp [relativeEntropy, hs, cfc_one]

/-- PDF p.6: the correction has its stated zero-alpha value. -/
example (T : ℝ) : zeroExtendedLogCorrection 0 T = 0 := by
  simp [zeroExtendedLogCorrection]

/-- PDF p.6: zero distance gives zero correction. -/
example (alpha : ℝ) : zeroExtendedLogCorrection alpha 0 = 0 := by
  simp [zeroExtendedLogCorrection]

/-- PDF p.2: normalization c=1 leaves the shifted entropy unchanged. -/
example {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    regularisedRelativeEntropy 1 rho sigma = relativeEntropy (rho + 1) (sigma + 1) := by
  simp [regularisedRelativeEntropy]

/-- PDF p.3: zero direction has identically zero resolvent integrand. -/
example {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I ℂ) (s : ℝ) :
    resolventIntegrand B 0 s = 0 := by
  simp [resolventIntegrand]

/-- PDF pp.3–4: the logarithmic derivative map sends zero to zero. -/
example {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I ℂ) :
    logarithmDerivativeMap B 0 = 0 := by
  ext i j
  simp [logarithmDerivativeMap, resolventIntegrand]

/-- PDF p.8: the first diagonal entry of the proposed extremal A. -/
example (alpha T : ℝ) : propositionA alpha T 0 0 = ((1 + T : ℝ) : ℂ) := by
  simp [propositionA]

/-- PDF p.8: the second diagonal entry of the proposed extremal B. -/
example (alpha T : ℝ) : propositionB alpha T 1 1 = ((T + alpha : ℝ) : ℂ) := by
  simp [propositionB]

/-- PDF p.9: at t=0 the two explicit states coincide, including their zero padding. -/
example (d : ℕ) : regularisedRho d 0 = regularisedSigma d 0 := by
  simp [regularisedRho, regularisedSigma]

/-- PDF p.9: the nonzero second entry of the first sharpness state is t. -/
example (t : ℝ) : regularisedRho 3 t 1 1 = (t : ℂ) := by
  simp [regularisedRho]

/-- PDF p.9: the nonzero third entry of the second sharpness state is t. -/
example (t : ℝ) : regularisedSigma 3 t 2 2 = (t : ℂ) := by
  simp [regularisedSigma]

end QAlgorithms.Papers.Independent.Support50.P17


