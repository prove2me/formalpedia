-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_PhaseKernel
-- name    : SparseHamiltonianNorm_Simulation_PhaseKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:56.057781+00:00
-- url     : https://prove2.me/theorems/73c2f50a-fa12-4cd7-953a-0a7555c5c5cd
-- title:
--   Signed reproducing kernel and phase-twisted clock states
-- statement:
--   For positive integers $m,p$, put $K=mp$ and
--   $$c(z)=\left(\sum_{j=0}^{K-1}z^j\right)\left(\frac1m\sum_{j=0}^{m-1}z^j\right)^p.$$
--   Coefficients $c_j$ are extended by zero to negative integer indices. Define
--   $$\kappa_{m,p}(\theta)=\frac{|c(e^{i\theta})|^2}{2\pi K}(1+2\cos K\theta).$$
--   Its operator integral uses the previously defined boundary evolution. The kernel is represented as real-valued; evenness, integrability, reproduction, and approximation estimates remain theorem conclusions.
--
--   The clock normalization is $\lambda=(2\sum_jc_j^2+\sum_jc_{j+K}c_j)/K$. With $\omega=e^{i\pi/3}$, the input and output coefficients are $(\omega c_j+c_{j-K})/\sqrt{K\lambda}$ and $(c_j+\omega c_{j-K})/\sqrt{K\lambda}$, on horizon $R=3mp-p$. Finite sums implement the integer coefficient sums using their full support. Every scheduled interaction contains one private Cayley call. These definitions permit the signed kernel and distinct input/output states without assuming their normalizations.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), pp.19–24, Eqs. (62)–(79); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Routing

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace SparseHamiltonianNorm.Simulation
open MeasureTheory Polynomial
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Shaping polynomial, Eq. (62). -/
def shaping (m p : ℕ) : Polynomial ℝ :=
  (∑ j ∈ Finset.range (m * p), Polynomial.X ^ j) *
    (Polynomial.C (1 / (m : ℝ)) * ∑ j ∈ Finset.range m, Polynomial.X ^ j) ^ p

/-- Integer zero extension: the negative indices do not truncate to zero. -/
def shapeCoeff (m p : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (shaping m p).coeff j.toNat else 0

/-- Signed real phase kernel, Eq. (63); its bounds and reproduction are not assumed. -/
def phaseKernel (m p : ℕ) (θ : ℝ) : ℝ :=
  ‖(shaping m p).eval₂ (algebraMap ℝ ℂ) (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 /
    (2 * Real.pi * (m * p : ℕ)) * (1 + 2 * Real.cos ((m * p : ℕ) * θ))

/-- Actual Bochner phase integral, Eq. (64), using the specified radial boundary extension. -/
def phaseIntegral {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (m p : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  ∫ θ in Set.Icc (-Real.pi) Real.pi, phaseKernel m p θ • boundaryResponse d Λ t V M θ

/-- Finite support realizes the integer coefficient sums in Eq. (73). -/
def clockLambda (m p : ℕ) : ℝ :=
  (2 * (∑ j ∈ Finset.range (2 * m * p - p), shapeCoeff m p j ^ 2) +
    ∑ j ∈ Finset.range (2 * m * p - p), shapeCoeff m p ((j : ℤ) + (m * p : ℕ)) * shapeCoeff m p j) /
      (m * p : ℕ)

def clockHorizon (m p : ℕ) : ℕ := 3 * m * p - p
def twist : ℂ := Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)

/-- Opposite placements of the same phase, Eq. (75). -/
def inputClock (m p : ℕ) (j : Fin (clockHorizon m p)) : ℂ :=
  (twist * (shapeCoeff m p j.val : ℂ) + shapeCoeff m p ((j.val : ℤ) - (m * p : ℕ))) /
    (Real.sqrt ((m * p : ℕ) * clockLambda m p) : ℂ)
def outputClock (m p : ℕ) (j : Fin (clockHorizon m p)) : ℂ :=
  ((shapeCoeff m p j.val : ℂ) + twist * shapeCoeff m p ((j.val : ℤ) - (m * p : ℕ))) /
    (Real.sqrt ((m * p : ℕ) * clockLambda m p) : ℂ)

/-- One private Cayley use in every scheduled slot, source p.24. -/
def routedCayleyCalls (R : ℕ) : ℕ := (List.finRange R).length

end SparseHamiltonianNorm.Simulation


