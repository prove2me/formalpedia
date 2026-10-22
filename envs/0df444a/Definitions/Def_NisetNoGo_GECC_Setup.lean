-- Prove2me | Definitions.Def_NisetNoGo_GECC_Setup
-- name    : NisetNoGo_GECC_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:33.875855+00:00
-- url     : https://prove2.me/theorems/3a21d074-a841-4fcd-bf80-263d01021d64
-- title:
--   Covariance model for single-mode Gaussian channels and Gaussian error-correcting codes
-- statement:
--   A single-mode Gaussian channel is represented by real $2\times2$ matrices $M,N$, acting on a covariance matrix by $\gamma\mapsto M\gamma M^{\mathsf T}+N$. Complete positivity means that $N$ is symmetric and $N_{\mathbb C}-i(J-MJM^{\mathsf T})_{\mathbb C}$ is positive semidefinite, where $J$ is the canonical symplectic matrix. A Gaussian unitary on $n$ modes is represented by a real matrix $S$ satisfying $SJS^{\mathsf T}=J$.
--
--   The code $G(n,E,D)$ uses the first of $n\ge1$ modes as its input, puts the other modes in vacuum, applies a symplectic encoder $S_E$, sends all modes through the same channel, applies a symplectic decoder $S_D$, and retains the first mode. The definitions `geccM` and `geccN` give the resulting channel matrices, including both the ancilla and channel noise. The degradation $D[T]$ is the lesser of $1$ and $\det N/(1+\det M)^2$, with the infinite quotient at $\det M=-1$ saturated at $1$. The two-mode output covariance and logarithmic negativity use a squeezed input with parameter $2r$ and the smallest symplectic eigenvalue after partial transpose.
--
--   These definitions provide the shared covariance model for the theorem and its supporting results.
--
--   **Formalization Note** Modes use interleaved $(x,p)$ coordinates and vacuum covariance $I$. Displacements do not change covariance matrices and are omitted. The eigenvalue is the intrinsic `lambdaMin` imported from the published covariance layer.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, pp. 1–3, (1)–(3), Fig. 1, (5), (6)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open QAlgorithms.Papers.Independent.Frontier30.P13
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open scoped ComplexOrder

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

namespace NisetNoGo.GECC

/-- The covariance form of complete positivity for a single-mode Gaussian channel. -/
def IsCPChannel
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) : Prop :=
  N.transpose = N ∧
    (complexify N - Complex.I • complexify
      (phaseJ (Fin 1) - M * phaseJ (Fin 1) * M.transpose)).PosSemidef

/-- A Gaussian unitary acts on covariances by a matrix preserving the symplectic form. -/
def IsSymplecticMat {n : ℕ}
    (S : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ) : Prop :=
  S * phaseJ (Fin n) * S.transpose = phaseJ (Fin n)

/-- Parallel use of the same single-mode covariance matrix on all modes. -/
def channelPower (n : ℕ)
    (M : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) :
    Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ :=
  fun i j => if i.1 = j.1 then M (0, i.2) (0, j.2) else 0

/-- The first mode carries the input and is retained at the output. -/
def inputMode (n : ℕ) [NeZero n] : ModeQuadrature (Fin 1) → ModeQuadrature (Fin n) :=
  fun q => (0, q.2)

/-- Zero input covariance on the signal mode, vacuum covariance on every ancilla. -/
def ancillaVacuum (n : ℕ) [NeZero n] :
    Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ :=
  Matrix.diagonal (fun i => if i.1 = 0 then 0 else 1)

/-- Signal matrix of the code in Fig. 1. -/
def geccM (n : ℕ) [NeZero n]
    (M : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (SE SD : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ) :
    Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ :=
  (SD * channelPower n M * SE).submatrix (inputMode n) (inputMode n)

/-- Noise matrix of the code in Fig. 1, including all vacuum ancillas. -/
def geccN (n : ℕ) [NeZero n]
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (SE SD : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ) :
    Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ :=
  let K := SD * channelPower n M * SE
  (K * ancillaVacuum n * K.transpose +
    SD * channelPower n N * SD.transpose).submatrix (inputMode n) (inputMode n)

/-- Entanglement degradation, with the infinite quotient at `det M = -1` saturated at one. -/
def entDeg
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) : ℝ :=
  if (1 + M.det) ^ 2 ≤ N.det then 1 else N.det / (1 + M.det) ^ 2

/-- Phase shifter in the `x,p` order of equation (3). -/
def phaseShift (θ : ℝ) :
    Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ :=
  fun i j => if i.2 then
    if j.2 then Real.cos θ else -Real.sin θ
  else if j.2 then Real.sin θ else Real.cos θ

/-- Squeezer in the `x,p` order of equation (3). -/
def squeezer (s : ℝ) :
    Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ :=
  Matrix.diagonal (fun i => if i.2 then Real.exp s else Real.exp (-s))

/-- Covariance after applying a channel to one half of a two-mode squeezed vacuum. -/
def gammaOut
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) (r : ℝ) :
    Matrix (BipPhase (Fin 1) (Fin 1)) (BipPhase (Fin 1) (Fin 1)) ℝ :=
  let L := Matrix.fromBlocks
    (1 : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    0 0 M
  L * squeezedCM 1 (2 * r) * L.transpose + Matrix.fromBlocks 0 0 0 N

/-- The partially transposed two-mode symplectic invariant of page 3. -/
def deltaTilde
    (G : Matrix (BipPhase (Fin 1) (Fin 1)) (BipPhase (Fin 1) (Fin 1)) ℝ) : ℝ :=
  G.toBlocks₁₁.det + G.toBlocks₂₂.det - 2 * G.toBlocks₁₂.det

/-- Finite-squeezing logarithmic negativity, using P13's intrinsic symplectic eigenvalue. -/
def logNeg
    (G : Matrix (BipPhase (Fin 1) (Fin 1)) (BipPhase (Fin 1) (Fin 1)) ℝ) : ℝ :=
  max 0 (-Real.log (lambdaMin G))

end NisetNoGo.GECC


