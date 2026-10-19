-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41
-- name    : QAlgorithms_Papers_Independent_Information100_P41
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:23:15.797981+00:00
-- url     : https://prove2.me/theorems/1be7267b-0b8f-4bef-b5bb-8ffda022223e
-- title:
--   Definitions for Anomaly fluctuation theorem for quantum coherence dynamics
-- statement:
--   The objects the formalized statements of *Anomaly fluctuation theorem for quantum coherence dynamics* (arXiv:2609.06632) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `entropy`: PDF p.1: entropy in nats; the accepted entropy in bits is multiplied by ln 2. The spectral convention is 0 log 0 = 0; this defines no stochastic logarithm at zero.
--   - `coherence`: PDF p.1: relative-entropy coherence C(X) = S(DX) - S(X).
--   - `outputAnomaly`: PDF p.2, Eq.(4): complex trace anomaly from output R and reference output T. Only used with positive diagonal populations, so the inverse is the ordinary matrix inverse.
--   - `anomaly`: PDF p.2, Eq.(4): both outputs are constructed from the input and the channel.
--   - `coherenceChange`: PDF p.2, Eq.(1): change in relative-entropy coherence.
--   - `coheringPower`: PDF p.2: maximum output coherence on incoherent density matrices. For d>0 and a channel this supremum is attained: its domain is nonempty and compact, coherence is continuous and bounded by ln d. The empty-domain value at d=0 is never used.
--   - `minPopulation`: PDF p.2, Eq.(5): minimum final reference population. With d>0 and full-rank dephasing this is the attained positive minimum of a finite nonempty set.
--   - `referenceProjector`: PDF p.2, Eq.(3): rank-one reference projector.
--   - `eigenProjector`: PDF p.2: eigenbasis projector, with normalized eigenvectors in the columns of U.
--   - `fieldState`: PDF p.4, Eq.(10): single-rail field density, used only for 0<=eta,nbar<=1.
--   - `jcIsometry`: PDF p.4: exact resonant interaction-picture evolution for ground atom and single-rail field. Atom first: V|0>=|g,0>, V|1>=cos(theta)|g,1>-i sin(theta)|e,0>. This is the isometry restricted to the invariant zero/one-excitation sector.
--   - `jcOutput`: PDF p.4: atomic output constructed by evolving Eq.(10) and tracing out the field.
--   - `groundState`: PDF p.4: initial atom |g><g|, with 0=g and 1=e.
--   - `jcAnomaly`: PDF p.4, Eq.(11): computed trace anomaly for the ground atomic input. Reference output and output coincide because the input is incoherent; Eq.(11) is not assigned as the definition.
--   - `jcChange`: PDF p.4: coherence transferred to the initially ground-state atom.
--   - `jcKD`: PDF pp.2,4: Eq.(3) specialized to ground input. Initial spectral projectors are reference projectors with eigenvalues (1,0). Pi_x Pi_n rho vanishes unless n=x=0, when it equals rho. Thus its channel output is exactly the constructed JC output. The final projector order is Pi_xOut Pi_nOut. No stochastic logarithmic variable is defined.
--   - `visibilityGap`: PDF pp.4–5: logarithmic bound minus transfer, at equal populations and optimal angle.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, https://arxiv.org/abs/2609.06632v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/- PDF pp.1–2: reference-basis dephasing is expressed directly using the imported
Mathlib operations Matrix.diagonal and Matrix.diag, which support every Fin d. -/

/-- PDF p.1: entropy in nats; the accepted entropy in bits is multiplied by ln 2.
The spectral convention is 0 log 0 = 0; this defines no stochastic logarithm at zero. -/
def entropy {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.log 2 * vnEntropy X

/-- PDF p.1: relative-entropy coherence C(X) = S(DX) - S(X). -/
def coherence {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  entropy (Matrix.diagonal (Matrix.diag X)) - entropy X

/-- PDF p.2, Eq.(4): complex trace anomaly from output R and reference output T.
Only used with positive diagonal populations, so the inverse is the ordinary matrix inverse. -/
def outputAnomaly {d : ℕ} (R T : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((Matrix.diagonal (Matrix.diag R))⁻¹ * (R - (Matrix.diagonal (Matrix.diag R))) * T).trace

/-- PDF p.2, Eq.(4): both outputs are constructed from the input and the channel. -/
def anomaly {d : ℕ} (E : Superop (Fin d) (Fin d)) (rho : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  outputAnomaly (E rho) (E (Matrix.diagonal (Matrix.diag rho)))

/-- PDF p.2, Eq.(1): change in relative-entropy coherence. -/
def coherenceChange {d : ℕ} (E : Superop (Fin d) (Fin d))
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  coherence (E rho) - coherence rho

/-- PDF p.2: maximum output coherence on incoherent density matrices.
For d>0 and a channel this supremum is attained: its domain is nonempty and compact, coherence
is continuous and bounded by ln d. The empty-domain value at d=0 is never used. -/
def coheringPower {d : ℕ} (E : Superop (Fin d) (Fin d)) : ℝ :=
  sSup {r : ℝ | ∃ omega : Matrix (Fin d) (Fin d) ℂ,
    IsDensityMatrix omega ∧ (Matrix.diagonal (Matrix.diag omega)) = omega ∧ r = coherence (E omega)}

/-- PDF p.2, Eq.(5): minimum final reference population. With d>0 and full-rank dephasing
this is the attained positive minimum of a finite nonempty set. -/
def minPopulation {d : ℕ} (R : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf (Set.range fun x : Fin d => (R x x).re)

/-- PDF p.2, Eq.(3): rank-one reference projector. -/
def referenceProjector {d : ℕ} (x : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun j => if j = x then 1 else 0

/-- PDF p.2: eigenbasis projector, with normalized eigenvectors in the columns of U. -/
def eigenProjector {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (n : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * referenceProjector n *
    (U : Matrix (Fin d) (Fin d) ℂ)ᴴ

/-- PDF p.4, Eq.(10): single-rail field density, used only for 0<=eta,nbar<=1. -/
def fieldState (eta nbar : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 - nbar : ℝ) : ℂ), ((eta * Real.sqrt (nbar * (1 - nbar)) : ℝ) : ℂ);
     ((eta * Real.sqrt (nbar * (1 - nbar)) : ℝ) : ℂ), (nbar : ℂ)]

/-- PDF p.4: exact resonant interaction-picture evolution for ground atom and single-rail field.
Atom first: V|0>=|g,0>, V|1>=cos(theta)|g,1>-i sin(theta)|e,0>.
This is the isometry restricted to the invariant zero/one-excitation sector. -/
def jcIsometry (theta : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun af k => if k = 0 then (if af = (0, 0) then 1 else 0)
    else if af = (0, 1) then (Real.cos theta : ℂ)
    else if af = (1, 0) then -Complex.I * (Real.sin theta : ℂ) else 0

/-- PDF p.4: atomic output constructed by evolving Eq.(10) and tracing out the field. -/
def jcOutput (eta nbar theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  traceRight (jcIsometry theta * fieldState eta nbar * (jcIsometry theta)ᴴ)

/-- PDF p.4: initial atom |g><g|, with 0=g and 1=e. -/
def groundState : Matrix (Fin 2) (Fin 2) ℂ := referenceProjector 0

/-- PDF p.4, Eq.(11): computed trace anomaly for the ground atomic input. Reference output
and output coincide because the input is incoherent; Eq.(11) is not assigned as the definition. -/
def jcAnomaly (eta nbar theta : ℝ) : ℂ :=
  outputAnomaly (jcOutput eta nbar theta) (jcOutput eta nbar theta)

/-- PDF p.4: coherence transferred to the initially ground-state atom. -/
def jcChange (eta nbar theta : ℝ) : ℝ :=
  coherence (jcOutput eta nbar theta) - coherence groundState

/-- PDF pp.2,4: Eq.(3) specialized to ground input. Initial spectral projectors are reference
projectors with eigenvalues (1,0). Pi_x Pi_n rho vanishes unless n=x=0, when it equals rho.
Thus its channel output is exactly the constructed JC output. The final projector order is
Pi_xOut Pi_nOut. No stochastic logarithmic variable is defined. -/
def jcKD (eta nbar theta : ℝ) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (n x nOut xOut : Fin 2) : ℂ :=
  if n = 0 ∧ x = 0 then
    (referenceProjector xOut * eigenProjector U nOut * jcOutput eta nbar theta).trace
  else 0

/-- PDF pp.4–5: logarithmic bound minus transfer, at equal populations and optimal angle. -/
def visibilityGap (eta : ℝ) : ℝ :=
  Real.log (1 + (jcAnomaly eta (1 / 2) (Real.pi / 2)).re) -
    jcChange eta (1 / 2) (Real.pi / 2)

example {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : (Matrix.diagonal (Matrix.diag (Matrix.diagonal (Matrix.diag X)))) = (Matrix.diagonal (Matrix.diag X)) := by
  ext i j
  simp [Matrix.diagonal_apply]

example {d : ℕ} (v : Fin d → ℂ) : coherence (Matrix.diagonal v) = 0 := by
  simp [coherence]

example {d : ℕ} (v : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ) :
    outputAnomaly (Matrix.diagonal v) T = 0 := by
  simp [outputAnomaly]

example (eta nbar : ℝ) : fieldState eta nbar 1 1 = (nbar : ℂ) := by
  rfl

example (theta : ℝ) : jcIsometry theta (0, 0) 0 = 1 := by
  simp [jcIsometry]

example (theta : ℝ) : jcIsometry theta (1, 0) 1 = -Complex.I * (Real.sin theta : ℂ) := by
  simp [jcIsometry]

example (eta nbar theta : ℝ) (U : Matrix.unitaryGroup (Fin 2) ℂ) (nOut xOut : Fin 2) :
    jcKD eta nbar theta U 1 0 nOut xOut = 0 := by
  simp [jcKD]

end QAlgorithms.Papers.Independent.Information100.P41


