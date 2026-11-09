-- Prove2me | Definitions.Def_LeeYangGap_SpectralGap_MatrixTools
-- name    : LeeYangGap_SpectralGap_MatrixTools
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:24.618195+00:00
-- url     : https://prove2.me/theorems/2fba86fb-394b-4c26-87f5-a4bc5e5421ad
-- title:
--   Finite complex operators, Gibbs moments, spectral powers and ground gap
-- statement:
--   Let $H,A,B$ be complex matrices on a finite-dimensional Hilbert space. All operator norms are induced by its Euclidean norm. Define the matrix exponential, the spectral real power $A^r$ and, for positive semidefinite $A$ and real $p>0$, the Schatten trace quantity $(\operatorname{Tr}A^p)^{1/p}$. Zero eigenvalues and exponent zero use $0^0=1$.
--
--   For inverse temperature $\beta$, define
--   $$Z=\operatorname{Tr}e^{-\beta H},\quad \rho=Z^{-1}e^{-\beta H},\quad \langle A\rangle_\beta=\operatorname{Tr}(\rho A),\quad \langle A(0)B(t)\rangle_\beta=\operatorname{Tr}(\rho A e^{-tH}Be^{tH}).$$
--   The centered observable is $\widehat A=A-\langle A\rangle_\beta I$. The spectral midpoint sum uses the complete orthonormal eigenbasis and eigenvalues of the actual Hermitian matrix $H$, retaining multiplicities. Its weights are $Z^{-1}e^{-\beta(E_l+E_{l'})/2}$ and squared matrix elements are $|\langle l|\widehat A|l'\rangle|^2$.
--
--   The ground-gap predicate asserts existence of a normalized eigenvector of energy $E$, that every eigenvector at $E$ is its scalar multiple, and that every eigenvalue $F$ satisfies $E\le F$ and either $F=E$ or $F\ge E+g$. This predicate defines the conclusion; it supplies no assumption about the physical model. These generic constructions support the thermal and spectral statements. Physical uses have Hermitian $H$ and positive $\beta$, so $Z>0$; spectral helpers use defaults off the Hermitian domain, never in the mission's statements.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, pp. 5–6, Eqs. (9)–(11); p. 12, Eqs. (41)–(44); p. 19, Eq. (74)

import Mathlib
open scoped BigOperators Matrix Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Finite complex matrices with the Hilbert-space operator norm. -/
abbrev Operator (ι : Type*) := Matrix ι ι ℂ

/-- Actual matrix exponential; the L2 operator norm supplies the Banach algebra. -/
def mexp {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Operator ι) : Operator ι :=
  NormedSpace.exp A

/-- Spectral real powers, including singular PSD inputs and exponent zero. -/
def realPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Operator ι) (r : ℝ) : Operator ι := cfc (fun x : ℝ => x ^ r) A

def schattenPSD {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Operator ι) (p : ℝ) : ℝ := (Matrix.trace (realPower A p)).re ^ (1 / p)

def partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Operator ι) (β : ℝ) : ℂ := Matrix.trace (mexp ((-β : ℂ) • H))

def gibbs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Operator ι) (β : ℝ) : Operator ι := (partition H β)⁻¹ • mexp ((-β : ℂ) • H)

def mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : Operator ι) (β : ℝ) : ℂ := Matrix.trace (gibbs H β * A)

def twoPoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A B : Operator ι) (β t : ℝ) : ℂ :=
  Matrix.trace (gibbs H β * A * mexp ((-t : ℂ) • H) * B * mexp ((t : ℂ) • H))

def centered {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : Operator ι) (β : ℝ) : Operator ι := A - mean H A β • 1

/-- Complete spectrum with multiplicities, no ordering or strictness imposed. -/
def energies {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Operator ι) : ι → ℝ :=
  if h : H.IsHermitian then h.eigenvalues else fun _ => 0

def eigenbasisMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Operator ι) : Operator ι :=
  if h : H.IsHermitian then h.eigenvectorUnitary else 1

def midpointSpectralSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : Operator ι) (β : ℝ) : ℝ :=
  (partition H β).re⁻¹ * ∑ l : ι, ∑ l' : ι,
    Real.exp (-β * (energies H l + energies H l') / 2) *
      Complex.normSq (((eigenbasisMatrix H)ᴴ * centered H A β * eigenbasisMatrix H) l l')

/-- A ground eigenvector, its full one-dimensional eigenspace, and a gap above it.
For Hermitian H this is exactly simplicity plus the sorted multiplicity-counting gap. -/
def HasGroundGap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Operator ι) (g : ℝ) : Prop :=
  ∃ E : ℝ, ∃ ψ : EuclideanSpace ℂ ι,
    ‖ψ‖ = 1 ∧ H *ᵥ (ψ : ι → ℂ) = (E : ℂ) • (ψ : ι → ℂ) ∧
    (∀ φ : ι → ℂ, H *ᵥ φ = (E : ℂ) • φ → ∃ c : ℂ, φ = c • (ψ : ι → ℂ)) ∧
    (∀ (F : ℝ) (φ : ι → ℂ), φ ≠ 0 → H *ᵥ φ = (F : ℂ) • φ →
      E ≤ F ∧ (F = E ∨ E + g ≤ F))
end LeeYangGap.SpectralGap


