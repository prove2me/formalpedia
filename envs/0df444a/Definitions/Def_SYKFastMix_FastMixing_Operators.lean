-- Prove2me | Definitions.Def_SYKFastMix_FastMixing_Operators
-- name    : SYKFastMix_FastMixing_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:05:28.861839+00:00
-- url     : https://prove2.me/theorems/0d0bcf0e-79e8-4448-962f-744cfca246f0
-- title:
--   Unnormalized operator geometry and the exact Gibbs sampler
-- statement:
--   For a finite complex Hilbert space, write $\operatorname{Tr}$ for the unnormalized trace, $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}(X^\dagger Y)$ and $\|X\|_2^2=\langle X,X\rangle_{\rm HS}$. The trace norm is the sum of the square roots of the eigenvalues of $X^\dagger X$. A density matrix is positive semidefinite with trace one. Matrix units identify operator space isometrically with $\mathbb C^{d^2}$.
--
--   For Hermitian $H$, Hermitian couplings $\gamma_i$, and inverse temperature $\beta$, define
--   $$\rho=\frac{e^{-\beta H}}{\operatorname{Tr}e^{-\beta H}},\quad Y_i=e^{-\beta^2\operatorname{ad}_H^2/8}(\gamma_i),\quad A_i=e^{-\beta H/4}Y_ie^{\beta H/4},$$
--   $$B=\frac{\mathrm i}{2}\tanh(\beta\operatorname{ad}_H/4)\sum_i A_i^\dagger A_i,\qquad \mathcal L(X)=-\mathrm i[B,X]+\sum_i\left(A_iXA_i^\dagger-\tfrac12\{A_i^\dagger A_i,X\}\right).$$
--   The discriminant is the negative generator conjugated by the Gibbs quarter-power sandwich. A gap bound includes self-adjointness, nonnegativity, stationarity of $\sqrt\rho$, and coercivity on its entire orthogonal complement. Mixing time is the infimum of nonnegative real times at which every density matrix has trace-norm error at most $\epsilon$.
--
--   These definitions provide reusable finite-dimensional quantum sampling conventions. **Formalization Note** Exponentials act on the algebra in question; the superoperator hyperbolic tangent is $(e^{2T}-I)(e^{2T}+I)^{-1}$. The mixing-time infimum is valued in $[0,\infty]$, with value $+\infty$ on the empty set. No gap, detailed-balance, or stationarity property is assumed.
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), pp.9–13, Eqs. (2.4)–(2.8), (2.17)–(2.33), (3.3)

import Mathlib
import Definitions.Def_SYKEdge_MatrixNorms

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory
open scoped ComplexOrder ENNReal NNReal

namespace SYKFastMix.FastMixing

/-! Unnormalized finite-dimensional operator conventions, source (2.4)–(2.8), (2.28)–(2.33).
The standard matrix-unit basis identifies operator space with a Euclidean space of dimension d².
All exponential functions below are the convergent algebra exponential, not entrywise exponentials. -/
abbrev Mat (ι : Type) := Matrix ι ι ℂ
abbrev Super (ι : Type) := Mat (ι × ι)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def hsInner (X Y : Mat ι) : ℂ := Matrix.trace (Xᴴ * Y)
def hsSq (X : Mat ι) : ℝ := (hsInner X X).re
def hs (X : Mat ι) : ℝ := Real.sqrt (hsSq X)
def traceNorm (X : Mat ι) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)
def mexp (X : Mat ι) : Mat ι := NormedSpace.exp X
def applySuper (T : Super ι) (X : Mat ι) : Mat ι :=
  fun a b => ∑ p : ι × ι, T (a,b) p * X p.1 p.2
def super (f : Mat ι → Mat ι) : Super ι :=
  fun a b => f (Matrix.single b.1 b.2 1) a.1 a.2
def qform (T : Super ι) (X : Mat ι) : ℝ := (hsInner X (applySuper T X)).re
def ad (H : Mat ι) : Super ι := super (fun X => H * X - X * H)
def anticomm (X Y : Mat ι) : Mat ι := X * Y + Y * X

def gibbs (H : Mat ι) (β : ℝ) : Mat ι :=
  (Matrix.trace (mexp ((-β : ℂ) • H)))⁻¹ • mexp ((-β : ℂ) • H)
def gibbsRoot (H : Mat ι) (β : ℝ) : Mat ι :=
  ((Real.sqrt (Matrix.trace (mexp ((-β : ℂ) • H))).re : ℂ))⁻¹ •
    mexp ((-(β / 2) : ℂ) • H)

def IsDensity (X : Mat ι) : Prop := X.PosSemidef ∧ Matrix.trace X = 1

def HasGap (T : Super ι) (root : Mat ι) (rate : ℝ) : Prop :=
  Tᴴ = T ∧ (∀ X, 0 ≤ qform T X) ∧ applySuper T root = 0 ∧
    ∀ X, hsInner root X = 0 → rate * hsSq X ≤ qform T X

def KernelSpan (T : Super ι) (root : Mat ι) : Prop :=
  ∀ X, applySuper T X = 0 ↔ ∃ z : ℂ, X = z • root

def evolve (L : Super ι) (τ : ℝ) (X : Mat ι) : Mat ι :=
  applySuper (mexp ((τ : ℂ) • L)) X

/-- The empty set of successful times has infimum +∞. The universal state bound is exactly
 the supremum condition in (2.31), with no restriction on operator parity. -/
def mixingTime (L : Super ι) (ρ : Mat ι) (ε : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ τ : ℝ, 0 ≤ τ ∧ t = ENNReal.ofReal τ ∧
    ∀ X, IsDensity X → traceNorm (evolve L τ X - ρ) ≤ ε}

/-- Exact Gaussian filter, Gibbs bias, coherent correction, generator, and discriminant.
 No stationarity, balance, gap, or norm bound is stored as input data. -/
def filtered {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (β : ℝ) (i : Fin N) : Mat ι :=
  applySuper (mexp ((-(β^2 / 8) : ℂ) • (ad H * ad H))) (γ i)
def jump {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (β : ℝ) (i : Fin N) : Mat ι :=
  mexp ((-(β / 4) : ℂ) • H) * filtered H γ β i * mexp (((β / 4) : ℂ) • H)
def correction {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (β : ℝ) : Mat ι :=
  let E := mexp (((β / 2) : ℂ) • ad H)
  let T := (E - 1) * (E + 1)⁻¹
  (Complex.I / 2) • applySuper T (∑ i, (jump H γ β i)ᴴ * jump H γ β i)
def lindblad {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (β : ℝ) : Super ι :=
  super (fun X => (-Complex.I) • (correction H γ β * X - X * correction H γ β) +
    ∑ i, (jump H γ β i * X * (jump H γ β i)ᴴ -
      (1 / 2 : ℂ) • anticomm ((jump H γ β i)ᴴ * jump H γ β i) X))
def discriminant {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (β : ℝ) : Super ι :=
  super (fun X => - (mexp (((β / 4) : ℂ) • H) *
    applySuper (lindblad H γ β)
      (mexp ((-(β / 4) : ℂ) • H) * X * mexp ((-(β / 4) : ℂ) • H)) *
    mexp (((β / 4) : ℂ) • H)))

end SYKFastMix.FastMixing


