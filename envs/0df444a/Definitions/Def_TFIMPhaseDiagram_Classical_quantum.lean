-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_quantum
-- name    : TFIMPhaseDiagram_Classical_quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:07.103208+00:00
-- url     : https://prove2.me/theorems/12047161-98be-45aa-b50a-336927dd8f36
-- title:
--   TFIM matrices, spectral width and signed accuracy
-- statement:
--   The computational basis is $\{0,1\}^n$, with $0$ the $+1$ eigenstate of $Z$. The local Pauli matrices are the published complex matrices; a Pauli string is their tensor product, represented entry by entry. For real $J,h,\eta$ define
--   $$H=\tfrac12\sum_{i,j}J_{ij}Z_iZ_j+\sum_i h_i Z_i+\sum_i\eta_iX_i,\qquad Z=\operatorname{Tr}(e^H),\qquad\rho=e^H/Z.$$
--   Here $e^H$ is the algebra exponential. Spectral width is the difference of the maximum and minimum Rayleigh quotients on the real Euclidean unit sphere, used with $n\ge1$ and symmetric $J$. The row norm sums absolute entries; the maximum-entry and vector maximum norms are separate. The functions $\alpha(t)$ and $\alpha_M(t)$ take value $1$ at zero. Signed multiplicative accuracy means $a=\theta b$ with $e^{-\epsilon}\le\theta\le e^\epsilon$, including negative and zero targets.
--
--   These definitions supply the quantum targets and the explicit mesh and annealing-length choices. The one-term, $\beta=-1$ adapter reuses the published Gibbs-family API; its equality to the algebra exponential is a separate theorem.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, §§1–3, pp.1,5–7, Pauli matrices, (5)–(6), Theorem 11

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical

/-- The computational basis, with false the +1 eigenstate of Z. -/
abbrev Bits (n : ℕ) := Fin n → Bool
abbrev QMat (n : ℕ) := Matrix (Bits n) (Bits n) ℂ
inductive Pauli where
  | I | X | Y | Z
  deriving DecidableEq

def pauliEntry : Pauli → Bool → Bool → ℂ
  | .I => (1 : Matrix Bool Bool ℂ)
  | .X => QAlgorithms.pauliX
  | .Y => QAlgorithms.pauliY
  | .Z => QAlgorithms.pauliZ

def pauliString {n : ℕ} (P : Fin n → Pauli) : QMat n :=
  fun a b => ∏ i, pauliEntry (P i) (a i) (b i)
def localPauli {n : ℕ} (P : Pauli) (i : Fin n) : QMat n :=
  pauliString (fun j => if j = i then P else .I)
def xSubset {n : ℕ} (S : Finset (Fin n)) : QMat n :=
  pauliString (fun i => if i ∈ S then .X else .I)

def hz {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : QMat n :=
  (1 / 2 : ℂ) • (∑ i, ∑ j, (J i j : ℂ) • (localPauli .Z i * localPauli .Z j)) +
    ∑ i, (h i : ℂ) • localPauli .Z i
def hx {n : ℕ} (η : Fin n → ℝ) : QMat n := ∑ i, (η i : ℂ) • localPauli .X i
def hamiltonian {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) : QMat n :=
  hz J h + hx η

/-- Actual algebra exponential, not entrywise exponentiation. -/
def matrixExp {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :=
  NormedSpace.exp A
def partition {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) : ℂ :=
  Matrix.trace (matrixExp (hamiltonian J h η))
def density {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) : QMat n :=
  (partition J h η)⁻¹ • matrixExp (hamiltonian J h η)
/-- The published Gibbs-family API, one term and beta = -1. The exponential adapter is a theorem. -/
def gibbsAdapter {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) : QMat n :=
  RouzeFranca.LearnGibbs.gibbs (fun _ : Fin 1 => hamiltonian J h η) (-1)
    (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)))
def trotter {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) (M : ℕ) : QMat n :=
  (matrixExp ((1 / (M : ℂ)) • hz J h) * matrixExp ((1 / (M : ℂ)) • hx η)) ^ M

def alpha (t : ℝ) : ℝ := if t = 0 then 1 else Real.tanh t / t
def alphaMesh (M : ℕ) (t : ℝ) : ℝ :=
  if t = 0 then 1 else Real.tanh t / ((M : ℝ) * Real.tanh (t / M))
def minField {n : ℕ} (η : Fin n → ℝ) : ℝ := ⨅ i, |η i|
def maxField {n : ℕ} (h : Fin n → ℝ) : ℝ := ⨆ i, |h i|
def maxEntry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : ℝ := ⨆ i, ⨆ j, |J i j|
def rowNorm {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : ℝ := ⨆ i, ∑ j, |J i j|
/-- Rayleigh quotient on the real Euclidean unit sphere; n > 0 at every use. -/
def spectralWidth {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
    r = ∑ i, ∑ j, J i j * x i * x j} -
  sInf {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
    r = ∑ i, ∑ j, J i j * x i * x j}
/-- Signed multiplicative accuracy. The target zero requires output zero. -/
def ExpApprox (ε : ℝ) (a b : ℂ) : Prop :=
  ∃ θ : ℝ, Real.exp (-ε) ≤ θ ∧ θ ≤ Real.exp ε ∧ a = (θ : ℂ) * b

def potential {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (s : Fin n → ℝ) : ℝ := (1/2) * (∑ i, ∑ j, J i j * s i * s j) + ∑ i, h i * s i

def meshChoice {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) (ε : ℝ) : ℕ :=
  let c := rowNorm J + maxField h + maxField η + 1
  ⌈1000 * max ((n : ℝ) * c^2 / ε) (Real.rpow ((n : ℝ) * c / ε) (3/2))⌉₊
def annealingLength {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : ℕ := n * ⌈rowNorm J⌉₊ + 1
end TFIMPhaseDiagram.Classical


