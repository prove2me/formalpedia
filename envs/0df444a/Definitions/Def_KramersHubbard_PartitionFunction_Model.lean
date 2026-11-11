-- Prove2me | Definitions.Def_KramersHubbard_PartitionFunction_Model
-- name    : KramersHubbard_PartitionFunction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:32.133874+00:00
-- url     : https://prove2.me/theorems/dc69d540-6adb-438f-afdd-3885d9d9637e
-- title:
--   Attractive Kramers Hamiltonians and thermal expectations
-- statement:
--   The one-particle space has $2N$ complex modes and the full occupation-basis Fock space has dimension $2^{2N}$. Raw data consist of a Hermitian hopping matrix $h$, a matrix $T$ for the antiunitary $\Theta v=T\overline v$, vectors $v_i$, and real couplings $U_i$. Admissibility means $T^\dagger T=I$, $T\overline T=-I$, $T\overline h=hT$, $\|v_i\|=1$, and $U_i\ge0$. With $w_i=\Theta v_i$ and the published CAR annihilators, define
--
--   $$a(v)=\sum_j\overline{v_j}a_j,\qquad H_0=\sum_{jk}h_{jk}a_j^\dagger a_k,\qquad H=H_0-\sum_iU_i n(v_i)n(w_i).$$
--
--   The module defines $Z=\operatorname{Tr}e^{-\beta H}$, $Z_0=\operatorname{Tr}e^{-\beta H_0}$, normalized free thermal expectations, $\rho=(I+e^{\beta h})^{-1}$ and the alternating Wick matrix. All traces remain complex until reality is established. The Schatten trace norm is the sum of absolute Hermitian eigenvalues, and $\Lambda=\|h\|_1+\sum_iU_i$. The zero branch of traceNorm outside the Hermitian class is never used by the mission statements. No approximability, locality, coupling bound or sampler is an input condition.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Definition 1 and Eqs.(1)-(2), (21), (26)-(28), pp.4,13-14; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Mathlib
import Definitions.Def_GaussTesting_annihilator

noncomputable section
open scoped BigOperators
open Matrix

namespace KramersHubbard.PartitionFunction

/-- Full occupation-basis Fock space, including the vacuum at zero modes. -/
abbrev FockOp (N : ℕ) := FermiCap.Gaussian.Op (2 * N)
abbrev Vec (N : ℕ) := Fin (2 * N) → ℂ
abbrev OneOp (N : ℕ) := Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ

/-- Raw input of Definition 1, p.4; no algorithmic promise is a field. -/
structure Data (N r : ℕ) where
  h : OneOp N
  theta : OneOp N
  v : Fin r → Vec N
  U : Fin r → ℝ

def partner {N r} (D : Data N r) (i : Fin r) : Vec N :=
  D.theta.mulVec (star (D.v i))

/-- Theta(v)=theta*conj(v); unitarity, square -I, invariance and attraction. -/
def Attractive {N r} (D : Data N r) : Prop :=
  D.theta.conjTranspose * D.theta = 1 ∧
  D.theta * D.theta.map star = -1 ∧ D.h.IsHermitian ∧
  D.theta * D.h.map star = D.h * D.theta ∧
  (∀ i, ∑ j, Complex.normSq (D.v i j) = 1) ∧ (∀ i, 0 ≤ D.U i)

def annihilate {N} (v : Vec N) : FockOp N :=
  ∑ j, star (v j) • GaussTesting.annihilator (2 * N) j

def number {N} (v : Vec N) : FockOp N := (annihilate v).conjTranspose * annihilate v

def freeH {N r} (D : Data N r) : FockOp N :=
  ∑ j, ∑ k, D.h j k •
    ((GaussTesting.annihilator (2 * N) j).conjTranspose *
      GaussTesting.annihilator (2 * N) k)

def pairProjector {N r} (D : Data N r) (i : Fin r) : FockOp N :=
  number (D.v i) * number (partner D i)

def hamiltonian {N r} (D : Data N r) : FockOp N :=
  freeH D + ∑ i, (-D.U i : ℂ) • pairProjector D i

/-- The complex trace is retained; reality/positivity are never discarded. -/
def partition {N r} (D : Data N r) (β : ℝ) : ℂ :=
  (NormedSpace.exp ((-β : ℂ) • hamiltonian D)).trace

def freeZ {N r} (D : Data N r) (β : ℝ) : ℂ :=
  (NormedSpace.exp ((-β : ℂ) • freeH D)).trace

def thermal {N r} (D : Data N r) (β : ℝ) (O : FockOp N) : ℂ :=
  (NormedSpace.exp ((-β : ℂ) • freeH D) * O).trace / freeZ D β

def density {N r} (D : Data N r) (β : ℝ) : OneOp N :=
  (1 + NormedSpace.exp ((β : ℂ) • D.h))⁻¹

/-- Schatten trace norm on the Hermitian inputs used here. The outside-class branch is unused. -/
def traceNorm {N} (h : OneOp N) : ℝ :=
  if hh : h.IsHermitian then ∑ j, |hh.eigenvalues j| else 0

def sizeParameter {N r} (D : Data N r) : ℝ := traceNorm D.h + ∑ i, D.U i

/-- Eq.(28); row j is an annihilator and column i is a creator. -/
def wickMatrix {N r n} (D : Data N r) (β : ℝ) (x y : Fin n → Vec N) :
    Matrix (Fin n) (Fin n) ℂ := fun j i =>
  if i ≤ j then dotProduct (star (y j)) ((density D β).mulVec (x i))
  else -dotProduct (star (y j)) ((1 - density D β).mulVec (x i))

end KramersHubbard.PartitionFunction


