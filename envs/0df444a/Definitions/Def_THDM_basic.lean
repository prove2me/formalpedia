-- Prove2me | Definitions.Def_THDM_basic
-- name    : THDM_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T23:24:10.074974+00:00
-- url     : https://prove2.me/theorems/1d180db0-d08e-4d57-b938-69d298873fbe
-- title:
--   THDM: the gauge invariants $K_0, K_a$ and gauge orbits
-- statement:
--   Basic objects for the general Two-Higgs-Doublet Model in the gauge-invariant formulation of Section 3 and Appendix A of arXiv:hep-ph/0605184.
--
--   A configuration of the two Higgs doublets at a space-time point is recorded as the $2\times 2$ complex matrix
--   $$\phi=\begin{pmatrix}\varphi_1^+&\varphi_1^0\\ \varphi_2^+&\varphi_2^0\end{pmatrix},$$
--   whose row $i$ is the doublet $\varphi_i$. The hermitian matrix of gauge-invariant scalar products is $K=\phi\phi^\dagger$, i.e. $K^{ij}=\varphi_j^\dagger\varphi_i$ (3.8), and its Pauli decomposition (3.9)-(3.10) gives the four real invariants $K_0=\operatorname{tr}K$ and $K_a=\operatorname{tr}(K\sigma^a)$ for $a=1,2,3$. A gauge transformation of $SU(2)_L\times U(1)_Y$ acts as $\phi\mapsto\phi U^{\mathsf T}$ with $U$ unitary (A5)-(A7). The forward light cone is the set of pairs $(K_0,K)$ with $K_0\ge 0$ and $|K|^2\le K_0^2$, which is the range of the invariants by (3.19). Auxiliary notation for real three-vectors (dot product, length, the bilinear form attached to a matrix, and the closed unit ball $|k|\le1$ of the variable $k=K/K_0$ of (4.1)) is fixed here as well.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 3 (eqs. 3.8-3.11, 3.19) and Appendix A (eqs. A2-A7)

import Mathlib

/-!
# The general Two-Higgs-Doublet Model: gauge-invariant variables

Basic objects for the analysis of the general THDM scalar potential following

  M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel,
  *Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model*,
  arXiv:hep-ph/0605184.

Section 3 and Appendix A of that paper.
-/

open scoped BigOperators
open Matrix

namespace THDM

/-! ### Real three-vectors -/

/-- Euclidean scalar product of two real three-vectors. -/
def dot3 (x y : Fin 3 → ℝ) : ℝ := ∑ a, x a * y a

/-- Euclidean length of a real three-vector. -/
noncomputable def norm3 (x : Fin 3 → ℝ) : ℝ := Real.sqrt (dot3 x x)

/-- The bilinear form `xᵀ E y` attached to a real `3 × 3` matrix `E`. -/
def quad3 (E : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) : ℝ :=
  ∑ a, ∑ b, x a * E a b * y b

/-- The closed unit ball `|k| ≤ 1` of the variable `k = K/K₀`, cf. (4.1). -/
def ballK : Set (Fin 3 → ℝ) := {k | dot3 k k ≤ 1}

/-! ### Higgs fields, the matrix `K`, and gauge transformations -/

/-- A configuration of the two Higgs doublets at a space-time point, arranged as the
`2 × 2` complex matrix `φ` of (A2): row `i` is the doublet `ϕᵢ = (ϕᵢ⁺, ϕᵢ⁰)`. -/
abbrev HiggsMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli matrices `σ¹, σ², σ³`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The hermitian matrix of gauge-invariant scalar products,
`K^{ij} = ϕⱼ† ϕᵢ`, equivalently `K = φ φ†`; see (3.8) and (A3). -/
noncomputable def Kmat (φ : HiggsMat) : Matrix (Fin 2) (Fin 2) ℂ := φ * φᴴ

/-- `K₀ = ϕᵢ† ϕᵢ = tr K`, the first gauge-invariant function of (3.10). -/
noncomputable def K0 (φ : HiggsMat) : ℝ := (Matrix.trace (Kmat φ)).re

/-- `Kₐ = (ϕᵢ† ϕⱼ) σᵃ_{ij} = tr (K σᵃ)`, the remaining gauge-invariant
functions of (3.10). -/
noncomputable def Kvec (φ : HiggsMat) (a : Fin 3) : ℝ :=
  (Matrix.trace (Kmat φ * pauli a)).re

/-- Two Higgs-field configurations are related by an `SU(2)_L × U(1)_Y` gauge
transformation if `φ' = φ Uᵀ` for some `U ∈ U(2)`; see (A5)–(A7). -/
def GaugeEquiv (φ φ' : HiggsMat) : Prop :=
  ∃ U : Matrix (Fin 2) (Fin 2) ℂ, Uᴴ * U = 1 ∧ φ' = φ * Uᵀ

/-- The closed forward light cone `K₀ ≥ 0`, `K₀² - |K|² ≥ 0` of (3.19). -/
def forwardCone : Set (ℝ × (Fin 3 → ℝ)) :=
  {p | 0 ≤ p.1 ∧ dot3 p.2 p.2 ≤ p.1 ^ 2}

end THDM


