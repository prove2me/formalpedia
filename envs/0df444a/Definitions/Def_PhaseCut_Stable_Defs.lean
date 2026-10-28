-- Prove2me | Definitions.Def_PhaseCut_Stable_Defs
-- name    : PhaseCut_Stable_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:29.139931+00:00
-- url     : https://prove2.me/theorems/c3a81aff-0ac1-447e-a538-d9bdf81f395a
-- title:
--   §4.2, §4.4, pp. 10–11, 13–14 — AA†, the face F, d₁(·, F), 𝓗_b, problems (13) and (14), C-stability (Definition 4.5), V^∥ and V^⊥
-- statement:
--   Fix integers $n, p$ and a complex measurement matrix $A \in \mathbb{C}^{n\times p}$. Write $\mathbf{H}_n$ for the Hermitian $n\times n$ complex matrices and $\mathbf{H}_n^+$ for the positive semidefinite ones. This file defines the objects of §4.2 and §4.4 of Waldspurger, d'Aspremont and Mallat.
--
--   1. **The projector $AA^\dagger$.** $P = AA^\dagger \in \mathbb{C}^{n\times n}$ is the orthogonal projector of $\mathbb{C}^n$ onto the range $\mathcal{R}(A)$ ($A^\dagger$ the Moore–Penrose pseudoinverse). No injectivity of $A$ is assumed.
--   2. **The face $\mathcal{F}$** (p. 10):
--   $$\mathcal{F} = \{V \in \mathbf{H}_n : x^*Vx = 0 \ \text{ for all } x \in \mathcal{R}(A)^\perp\},$$
--   where $x \in \mathcal{R}(A)^\perp$ exactly when $Px = 0$.
--   3. **The trace-norm distance** $d_1(V, \mathcal{F}) = \inf_{W \in \mathcal{F}} \|V - W\|_1$, with $\|X\|_1 = \operatorname{Tr}\sqrt{X^*X}$ the trace (nuclear, Schatten 1-) norm.
--   4. **Norms.** $\|X\|_2 = (\sum_{i,j}|X_{ij}|^2)^{1/2}$ is the Schatten 2-norm (Frobenius norm) of a matrix; $\|v\|_2$ is the Euclidean norm of a real or complex vector. $|Ax_0|$ is the vector of moduli $(|(Ax_0)_i|)_i$, and $(Ax_0)(Ax_0)^*$ the rank-one matrix built from $Ax_0$.
--   5. **The affine section** $\mathcal{H}_b = \{V \in \mathbf{H}_n : V_{ii} = b_i^2,\ i = 1,\dots,n\}$ for $b \in \mathbb{R}^n$ (p. 11).
--   6. **Problem (13)** (PhaseCut as a projection): a minimizer of (13) is a $V \in \mathbf{H}_n^+ \cap \mathcal{H}_b$ with $d_1(V,\mathcal{F}) \le d_1(W,\mathcal{F})$ for every $W \in \mathbf{H}_n^+ \cap \mathcal{H}_b$.
--   7. **Problem (14)** (Weak PhaseLift, first-order form with the $\ell^s$-distance, $s \ge 1$): a minimizer of (14) is a $V \in \mathbf{H}_n^+ \cap \mathcal{F}$ minimizing over $\mathbf{H}_n^+ \cap \mathcal{F}$ the objective
--   $$d(\operatorname{diag}(V), b^2) = \Big(\sum_{i=1}^n \big|V_{ii} - b_i^2\big|^s\Big)^{1/s},$$
--   which the paper identifies with the Schatten-$s$ distance $d_s(V, \mathcal{H}_b)$.
--   8. **$C$-stability** (Definition 4.5): PhaseCut (resp. Weak PhaseLift) is $C$-stable at $x_0 \in \mathbb{C}^p$ if there is $\delta > 0$ such that for every $b_{\rm noise} \in \mathbb{R}^n$ with $\|b_{\rm noise}\|_2 < \delta$, every minimizer $V$ of (13) (resp. (14)) with $b = |Ax_0| + b_{\rm noise}$ satisfies
--   $$\|V - (Ax_0)(Ax_0)^*\|_2 \le C\,\|Ax_0\|_2\,\|b_{\rm noise}\|_2 .$$
--   9. **Compressions.** $V^{/\!/} = PVP$, the restriction of $V$ to $\mathcal{R}(A)$, and $V^\perp = (I-P)V(I-P)$, its restriction to $\mathcal{R}(A)^\perp$ (proof of Theorem 4.7).
--
--   These are the objects in which the paper's stability theorem compares the two convex relaxations of phase recovery: PhaseCut moves from $\mathbf{H}_n^+ \cap \mathcal{H}_b$ towards $\mathcal{F}$, Weak PhaseLift moves from $\mathbf{H}_n^+\cap\mathcal{F}$ towards $\mathcal{H}_b$.
--
--   **Formalization Note.** $P$ is the matrix of Mathlib's orthogonal projection (`Submodule.starProjection`) onto the range of $A$ acting on `EuclideanSpace ℂ (Fin n)`. The trace norm is the published definition `WildeQIT.traceNorm` ($\operatorname{Re}\operatorname{Tr}\sqrt{X^*X}$). $d_1$ is a real infimum over a set that is nonempty ($0 \in \mathcal{F}$) and bounded below by $0$. The diagonal entries of a Hermitian matrix are real; the objective of (14) reads them through their real part. "Close enough to zero" in Definition 4.5 is the existence of $\delta > 0$; the condition $C > 0$ of Definition 4.5 is a hypothesis of the theorems, not part of the predicate. The signal $x_0$ lives in $\mathbb{C}^p$ (the page writes $\mathbb{C}^n$; $Ax_0$ requires the column dimension).
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, §4.2 pp. 10–11 (F, (13), 𝓗_b, (14)), Definition 4.5 p. 13, proof of Theorem 4.7 p. 14 (V^∥, V^⊥)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

namespace PhaseCut.Stable

open Matrix
open scoped ComplexOrder

/-- The orthogonal projector onto the range of `A : ℂ^{n×p}`, as an `n × n` matrix. This is the
paper's `AA†` (with `A†` the Moore–Penrose pseudoinverse): "Because `AA†` is the orthogonal projection
onto `R(A)`" (p. 11). It is the matrix of the orthogonal projection of `EuclideanSpace ℂ (Fin n)` onto
`LinearMap.range (toEuclideanLin A)`. -/
noncomputable def projRange {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.toEuclideanLin.symm
    (((LinearMap.range (Matrix.toEuclideanLin A)).starProjection :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))

/-- The face `F = {V ∈ 𝐇ₙ : x*Vx = 0 for all x ∈ R(A)⊥}` (§4.2, p. 10). A vector `x` lies in
`R(A)⊥` iff `AA† x = 0`. -/
def faceF {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {V | V.IsHermitian ∧ ∀ x : Fin n → ℂ, projRange A *ᵥ x = 0 → star x ⬝ᵥ (V *ᵥ x) = 0}

/-- `d₁(V, F)`, the distance from `V` to `F` generated by the trace norm (Schatten 1-norm)
`‖X‖₁ = Tr √(X*X)` (`WildeQIT.traceNorm`). The set of values is nonempty (`0 ∈ F`) and bounded
below by `0`, so the real infimum is the honest one. -/
noncomputable def d1 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {r : ℝ | ∃ W ∈ faceF A, r = WildeQIT.traceNorm (V - W)}

/-- The Schatten 2-norm (Frobenius norm) `‖X‖₂` of a square complex matrix. -/
noncomputable def frob {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

/-- The Euclidean norm `‖v‖₂` of a real vector. -/
noncomputable def vnorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The Euclidean norm `‖v‖₂` of a complex vector. -/
noncomputable def cnorm {n : ℕ} (v : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- The vector of moduli `|Ax₀|`, `(|Ax₀|)ᵢ = |(Ax₀)ᵢ|`. -/
noncomputable def absAx {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (x₀ : Fin p → ℂ) : Fin n → ℝ :=
  fun i => ‖(A *ᵥ x₀) i‖

/-- The rank-one matrix `(Ax₀)(Ax₀)*`. -/
def outer {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (x₀ : Fin p → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec (A *ᵥ x₀) (star (A *ᵥ x₀))

/-- The affine subspace `𝓗_b = {V ∈ 𝐇ₙ : V_{ii} = bᵢ², i = 1, …, n}` (p. 11). -/
def Hb {n : ℕ} (b : Fin n → ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {V | V.IsHermitian ∧ ∀ i, V i i = ((b i ^ 2 : ℝ) : ℂ)}

/-- `V` is a minimizer of problem (13): minimize `d₁(V, F)` subject to `V ∈ 𝐇ₙ⁺ ∩ 𝓗_b` (p. 11). -/
def IsMin13 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  V.PosSemidef ∧ V ∈ Hb b ∧ ∀ W : Matrix (Fin n) (Fin n) ℂ, W.PosSemidef → W ∈ Hb b → d1 A V ≤ d1 A W

/-- The objective `d(diag(V), b²)` of Weak PhaseLift for the `lˢ`-distance on `ℝⁿ`,
`(∑ᵢ |V_{ii} − bᵢ²|ˢ)^{1/s}` (p. 11), which the paper identifies with `d_s(V, 𝓗_b)`.
For Hermitian `V` the diagonal is real, so `V_{ii}` is read through its real part. -/
noncomputable def lsDist {n : ℕ} (s : ℝ) (b : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (∑ i, |(V i i).re - b i ^ 2| ^ s) ^ (1 / s)

/-- `V` is a minimizer of problem (14): minimize `d_s(V, 𝓗_b)` subject to `V ∈ 𝐇ₙ⁺ ∩ F` (p. 11). -/
def IsMin14 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (s : ℝ) (b : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  V.PosSemidef ∧ V ∈ faceF A ∧
    ∀ W : Matrix (Fin n) (Fin n) ℂ, W.PosSemidef → W ∈ faceF A → lsDist s b V ≤ lsDist s b W

/-- Definition 4.5 (p. 13) for PhaseCut: PhaseCut is `C`-stable at `x₀` iff for every `b_noise`
close enough to zero, every minimizer `V` of (13) with `b = |Ax₀| + b_noise` satisfies
`‖V − (Ax₀)(Ax₀)*‖₂ ≤ C ‖Ax₀‖₂ ‖b_noise‖₂`. (The condition `C > 0` is a hypothesis of the
theorems, not part of this predicate.) -/
def PhaseCutStable {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (x₀ : Fin p → ℂ) (C : ℝ) : Prop :=
  ∃ δ > 0, ∀ bn : Fin n → ℝ, vnorm bn < δ → ∀ V : Matrix (Fin n) (Fin n) ℂ,
    IsMin13 A (absAx A x₀ + bn) V → frob (V - outer A x₀) ≤ C * cnorm (A *ᵥ x₀) * vnorm bn

/-- Definition 4.5 (p. 13) for Weak PhaseLift, solved in the form (14) with the `lˢ`-distance:
every minimizer `V` of (14) with `b = |Ax₀| + b_noise`, `b_noise` close enough to zero, satisfies
`‖V − (Ax₀)(Ax₀)*‖₂ ≤ C ‖Ax₀‖₂ ‖b_noise‖₂`. -/
def WeakPhaseLiftStable {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (s : ℝ) (x₀ : Fin p → ℂ)
    (C : ℝ) : Prop :=
  ∃ δ > 0, ∀ bn : Fin n → ℝ, vnorm bn < δ → ∀ V : Matrix (Fin n) (Fin n) ℂ,
    IsMin14 A s (absAx A x₀ + bn) V → frob (V - outer A x₀) ≤ C * cnorm (A *ᵥ x₀) * vnorm bn

/-- `V^∥`, the restriction of `V` to `range(A)`: `x*(V^∥)y = x*Vy` for `x, y ∈ range(A)` and `0` if
`x` or `y ∈ range(A)⊥` (proof of Theorem 4.7, p. 14). It is `AA† V AA†`. -/
noncomputable def Vpar {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  projRange A * V * projRange A

/-- `V^⊥`, the restriction of `V` to `range(A)⊥`: `(I − AA†) V (I − AA†)`. -/
noncomputable def Vperp {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 - projRange A) * V * (1 - projRange A)

end PhaseCut.Stable


