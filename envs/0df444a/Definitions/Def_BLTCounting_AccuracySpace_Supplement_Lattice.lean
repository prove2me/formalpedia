-- Prove2me | Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice
-- name    : BLTCounting_AccuracySpace_Supplement_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:27.744018+00:00
-- url     : https://prove2.me/theorems/475c46e3-5fe9-4678-8ff4-6408aa675557
-- title:
--   The logarithmic lattice and normalized Hankel matrices of Section 3
-- statement:
--   For an integer $m\ge2$ and fixed $\gamma\in(0,1]$, put
--   $$L=\log m,\quad \ell=\gamma L/2,\quad h=L e^{-(L-\ell)},\quad K=\lfloor\ell/h\rfloor,\quad \xi_i=L-\ell+ih,\quad k_i=\lfloor e^{\xi_i}\rfloor.$$
--   The lattice matrices have rows and columns indexed by $0\le i<K$: $H_S[i,j]=f[k_i+k_j]$, $\widetilde H_S[i,j]=(k_i k_j)^{1/4}f[k_i+k_j]$ and $T_h[i,j]=c_0((i-j)h)$. Define $\tau_1=m^{1-\gamma}$ and let the threshold relation mean $\omega>0$ and $\widehat c_0(\omega)=2(1+\varepsilon)\tau_1h$.
--
--   These are computed objects used throughout the inverse-polynomial error argument. The normalization is $D^{-1}H_SD^{-1}$ with $D=\operatorname{diag}(k_i^{-1/4})$; it differs from the weighted Hankel matrix used in Section 4. The relation does not assert existence, uniqueness or asymptotics.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Section 3, printed pp. 13, 19–20 (PDF pp. 14, 20–21)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Sequences
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

namespace BLTCounting.AccuracySpace.Supplement

/-- Section 3 logarithmic lattice, printed p.13 / PDF p.14. Statements use m ≥ 2 and 0 < γ ≤ 1. -/
noncomputable def latticeL (m : ℕ) : ℝ := Real.log m
noncomputable def latticeEll (m : ℕ) (γ : ℝ) : ℝ := γ * latticeL m / 2
noncomputable def latticeH (m : ℕ) (γ : ℝ) : ℝ :=
  latticeL m * Real.exp (-(latticeL m - latticeEll m γ))
noncomputable def latticeK (m : ℕ) (γ : ℝ) : ℕ := ⌊latticeEll m γ / latticeH m γ⌋₊
noncomputable def latticeXi (m : ℕ) (γ : ℝ) (i : ℕ) : ℝ :=
  latticeL m - latticeEll m γ + i * latticeH m γ
noncomputable def latticeIndex (m : ℕ) (γ : ℝ) (i : ℕ) : ℕ :=
  ⌊Real.exp (latticeXi m γ i)⌋₊

/-- Actual submatrix in the lattice order; no rank or spectral condition is assumed. -/
noncomputable def latticeHankel (m : ℕ) (γ : ℝ) :
    Matrix (Fin (latticeK m γ)) (Fin (latticeK m γ)) ℂ :=
  Matrix.of fun i j => sqrtSeq (latticeIndex m γ i + latticeIndex m γ j)

/-- D⁻¹ H_S D⁻¹, distinct from the published Section 4 weightedHankel. -/
noncomputable def normalizedHankel (m : ℕ) (γ : ℝ) :
    Matrix (Fin (latticeK m γ)) (Fin (latticeK m γ)) ℂ :=
  Matrix.of fun i j =>
    (((((latticeIndex m γ i : ℕ) : ℝ) * (latticeIndex m γ j : ℕ)) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      latticeHankel m γ i j

/-- Unscaled T_h of Section 3, rather than V_h = h T_h of Section 4. -/
noncomputable def latticeToeplitz (m : ℕ) (γ : ℝ) :
    Matrix (Fin (latticeK m γ)) (Fin (latticeK m γ)) ℂ :=
  toeplitz (latticeK m γ) (fun t => (c0 ((t : ℝ) * latticeH m γ) : ℂ))

noncomputable def tauOne (m : ℕ) (γ : ℝ) : ℝ := (m : ℝ) ^ (1 - γ)

/-- Claim 3.10's actual threshold equation; existence and uniqueness are not built into it. -/
def IsThreshold (m : ℕ) (γ ε ω : ℝ) : Prop :=
  0 < ω ∧ c0Hat ω = ((2 * (1 + ε) * tauOne m γ * latticeH m γ : ℝ) : ℂ)

end BLTCounting.AccuracySpace.Supplement


