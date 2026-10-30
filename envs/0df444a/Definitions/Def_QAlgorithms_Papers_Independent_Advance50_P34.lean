-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P34
-- name    : QAlgorithms_Papers_Independent_Advance50_P34
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:37:07.305894+00:00
-- url     : https://prove2.me/theorems/5d98cdf8-47f1-46f0-ab1d-95bf8fdea516
-- title:
--   Definitions for Demonstration of a Controlled-Phase Gate for Continuous-Variable One-Way Quantum Computation
-- statement:
--   The objects the formalized statements of *Demonstration of a Controlled-Phase Gate for Continuous-Variable One-Way Quantum Computation* (arXiv:1107.0514) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `controlledPhaseShear`: PDF p.2: M s in the order (x_first,p_first,x_second,p_second), where M has blocks (I,S;S,I), S=(0,0;1,0).
--   - `controlledPhasePullback`: PDF p.2: M-transpose k, the dual argument for exp(i k.R). This is not the inverse map or the active displacement shear.
--   - `twoModeDisplacement`: PDF p.2, displacement convention: D(s_x+i s_p) shifts x,p by s_x,s_p. The symmetric Weyl displacement differs from the printed ordered X Z only by scalar phase; its action on density operators is exactly the same.
--   - `opticalWeyl`: PDF p.2: W(k)=exp(i k.R) with the source's hbar=1/2. Since a=x+i p, its one-mode displacement argument is (-k_p+i k_x)/2.
--   - `RealizesControlledPhase`: PDF p.2: bounded all-Weyl characterization of C_Z=exp(2i x_first x_second), up to scalar phase. Its Heisenberg action is U-adjoint R U=M R. Existence of an actual unitary satisfying this predicate is a theorem conclusion.
-- source:
--   Demonstration of a Controlled-Phase Gate for Continuous-Variable One-Way Quantum Computation, arXiv:1107.0514v1, https://arxiv.org/abs/1107.0514v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

/-!
Ukai et al., arXiv:1107.0514v1, PDF pp.2,4, Fig.1(b) and note [18].

The independent-paper override permits pinned accepted paper modules as definition
providers. The completed two-mode space is l2(N x N), without a photon cutoff.
The optical normalization is x=(a+a-adjoint)/2, p=(a-a-adjoint)/(2i),
[x,p]=i/2 and vacuum variance 1/4. Only bounded Weyl operators are used.

This module states the ideal displacement propagation rule underlying composition.
The actual Bell/homodyne/feedforward instrument, its finite-squeezing predictions,
and the experimental claims are explicitly deferred in HARD.md and GAPS.json.
In particular, no normalized infinitely squeezed resource is introduced.
Compilation and independent moderation are pending the separate batch handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P34

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State productCoeff tensorApply)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff boundedUnitaryConjugation)

/-- PDF p.2: M s in the order (x_first,p_first,x_second,p_second),
where M has blocks (I,S;S,I), S=(0,0;1,0). -/
def controlledPhaseShear (s : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![s 0, s 1 + s 2, s 2, s 3 + s 0]

/-- PDF p.2: M-transpose k, the dual argument for exp(i k.R).
This is not the inverse map or the active displacement shear. -/
def controlledPhasePullback (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![k 0 + k 3, k 1, k 2 + k 1, k 3]

/-- PDF p.2, displacement convention: D(s_x+i s_p) shifts x,p by s_x,s_p.
The symmetric Weyl displacement differs from the printed ordered X Z only
by scalar phase; its action on density operators is exactly the same. -/
def twoModeDisplacement (s : Fin 4 → ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  productCoeff
    (displacementMatrix ((s 0 : ℂ) + Complex.I * (s 1 : ℂ)))
    (displacementMatrix ((s 2 : ℂ) + Complex.I * (s 3 : ℂ)))

/-- PDF p.2: W(k)=exp(i k.R) with the source's hbar=1/2.
Since a=x+i p, its one-mode displacement argument is (-k_p+i k_x)/2. -/
def opticalWeyl (k : Fin 4 → ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  productCoeff
    (displacementMatrix ((-(k 1 : ℂ) + Complex.I * (k 0 : ℂ)) / 2))
    (displacementMatrix ((-(k 3 : ℂ) + Complex.I * (k 2 : ℂ)) / 2))

/-- PDF p.2: bounded all-Weyl characterization of C_Z=exp(2i x_first x_second),
up to scalar phase. Its Heisenberg action is U-adjoint R U=M R.
Existence of an actual unitary satisfying this predicate is a theorem conclusion. -/
def RealizesControlledPhase
    (U : Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)) : Prop :=
  ∀ k : Fin 4 → ℝ,
    boundedUnitaryConjugation U.symm (opticalWeyl k) =
      opticalWeyl (controlledPhasePullback k)

/-- Sanity: a position displacement of the first mode produces the positive
momentum displacement of the second mode dictated by the source's C_Z sign. -/
example (s : Fin 4 → ℝ) : controlledPhaseShear s 3 = s 3 + s 0 := by
  rfl

/-- Sanity: the dual pullback adds the fourth Weyl coefficient to the first. -/
example (k : Fin 4 → ℝ) : controlledPhasePullback k 0 = k 0 + k 3 := by
  rfl

/-- Sanity: the undisplaced two-mode vacuum diagonal is one, not zero. -/
example : twoModeDisplacement 0 (0, 0) (0, 0) = 1 := by
  simp [twoModeDisplacement, productCoeff, displacementMatrix]

/-- Sanity: the zero Weyl parameter has unit two-mode vacuum expectation. -/
example : opticalWeyl 0 (0, 0) (0, 0) = 1 := by
  simp [opticalWeyl, productCoeff, displacementMatrix]

end QAlgorithms.Papers.Independent.Advance50.P34


