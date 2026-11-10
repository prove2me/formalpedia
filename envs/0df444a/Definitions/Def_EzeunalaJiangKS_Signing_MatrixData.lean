-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_MatrixData
-- name    : EzeunalaJiangKS_Signing_MatrixData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:00:25.423947+00:00
-- url     : https://prove2.me/theorems/18805253-5f49-40e3-bc41-f5926b23258b
-- title:
--   Finite complex matrices and normalized signing data
-- statement:
--   For matrices $H_i\in\mathbb C^{d\times d}$, put
--   $$T=\sum_i|\operatorname{Tr}H_i|,\qquad A_i=\frac{\operatorname{sign}(\operatorname{Tr}H_i)}{T}H_i.$$
--   The spectral norm is the norm induced on Euclidean complex space, and $\operatorname{tr}$ takes the real part of the complex trace. Normalized analytic data have $N,d>0$, rational nonzero positive semidefinite rank-one $A_i$, trace $\operatorname{tr}(\sum_i A_i)=1$, and a rational $x^0\in[-1,1]^N$. Define $\nu=\|\sum_i A_i^2\|$, $\varepsilon=\nu/d$ and $S(x)=\sum_i(x_i-x_i^0)A_i$.
--
--   These objects provide the shared matrix setting. The headline uses unnormalized inputs and does not exclude zeros. At zero normalization scale the total division convention is zero and is unused for nonzero normalized data. The rationality predicate is imported from the published definition.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §2, (3), and §3 standing assumptions, printed p. 3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Mathlib
import Definitions.Def_KSPolySign_IsRatC

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

abbrev CMat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev RMat (N : ℕ) := Matrix (Fin N) (Fin N) ℝ
abbrev State (N : ℕ) := Fin N → ℝ

def spectral {d : ℕ} (B : CMat d) : ℝ := ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) B‖
def tr {d : ℕ} (B : CMat d) : ℝ := B.trace.re
def loewner {d : ℕ} (B C : CMat d) : Prop := (C - B).PosSemidef

def cube {N : ℕ} (x : State N) : Prop := ∀ i, |x i| ≤ 1

def normalized {N d : ℕ} (A : Fin N → CMat d) (x₀ : State N) : Prop :=
  0 < N ∧ 0 < d ∧ (∀ i, (A i).PosSemidef ∧ (A i).rank = 1 ∧
    ∀ j k, KSPolySign.IsRatC (A i j k)) ∧ tr (∑ i, A i) = 1 ∧
    cube x₀ ∧ (∀ i, ∃ q : ℚ, x₀ i = q)

def variance {N d : ℕ} (A : Fin N → CMat d) : ℝ := spectral (∑ i, A i * A i)
def epsilon {N d : ℕ} (A : Fin N → CMat d) : ℝ := variance A / d

def normalizingScale {N d : ℕ} (H : Fin N → CMat d) : ℝ := ∑ i, |tr (H i)|
def normalize {N d : ℕ} (H : Fin N → CMat d) (i : Fin N) : CMat d :=
  ((SignType.sign (tr (H i)) : ℝ) / normalizingScale H) • H i

def shift {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) : CMat d :=
  ∑ i, (x i - x₀ i) • A i

end EzeunalaJiangKS.Signing


