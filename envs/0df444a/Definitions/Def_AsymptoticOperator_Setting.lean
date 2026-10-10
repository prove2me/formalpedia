-- Prove2me | Definitions.Def_AsymptoticOperator_Setting
-- name    : AsymptoticOperator_Setting
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-09T14:31:10.836096+00:00
-- url     : https://prove2.me/theorems/222957b5-5b43-4f55-8854-fb0a40ab0dc6
-- title:
--   Asymptotic operators $-J_0\partial_t - S$ on $L^2(S^1,\mathbb{R}^{2n})$ and fundamental solutions
-- statement:
--   Objects for the spectral theory of asymptotic operators on the circle, following Wendl, *Lectures on Symplectic Field Theory*, §3.2.
--
--   1. **Circle and $L^2$.** $S^1=\mathbb{R}/\mathbb{Z}$ with its Haar probability measure. $L^2=L^2(S^1,\mathbb{R}^{2n})$ is the real Hilbert space of square-integrable maps to $\mathbb{R}^{2n}$ with the Euclidean inner product.
--   2. **Loops of symmetric matrices.** $S:S^1\to\mathbb{R}^{2n\times2n}$ is continuous; it is a symmetric loop if $S(t)^{\mathsf T}=S(t)$ for every $t$.
--   3. **Fourier coefficients.** $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb{C}^{2n}$, $k\in\mathbb{Z}$, and $(Sf)^\wedge_k$ is the coefficient of $t\mapsto S(t)f(t)$.
--   4. **Sobolev space.** $W^{1,2}$ is the set of $f\in L^2$ with $\sum_k(1+k^2)|\hat f_k|^2<\infty$.
--   5. **Asymptotic operator.** With
--   $$J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix},$$
--   $A_Sf=g$ means $f\in W^{1,2}$ and $\hat g_k=-2\pi ik\,J_0\hat f_k-(Sf)^\wedge_k$ for all $k$, i.e. $A_S=-J_0\partial_t-S(t)$ (Wendl (3.4)). $A_S$ is the partially defined linear map on $L^2$ with this graph.
--   6. **Eigenspaces and discrete spectrum.** The $\mu$-eigenspace is $\ker(A_S-\mu)\subset W^{1,2}$. $A$ has a discrete eigenbasis if $L^2$ has an orthonormal basis $(e_i)$ of vectors in the domain with $Ae_i=\lambda_ie_i$, $\lambda_i\in\mathbb{R}$, and $|\lambda_i|\to\infty$ along the cofinite filter (only finitely many $i$ have $|\lambda_i|\le c$, for every $c$).
--   7. **Fundamental solution.** $\Psi:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ with $\Psi(0)=\mathrm{Id}$ and $\Psi'(t)=J_0S(t)\Psi(t)$ for all $t\in\mathbb{R}$.
--
--   **Formalization Note** $L^2$ is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2 haarAddCircle` on `UnitAddCircle`. Fourier coefficients are Mathlib's `fourierCoeff` of the componentwise complexification, and $J_0$ (`Matrix.J`) and $S(t)$ act on $\mathbb{C}^{2n}$ by the real-to-complex coercion. `asymptoticOperator S` is chosen as the `LinearPMap` whose graph is the set of pairs $(f,g)$ above and is $0$ if no such map exists; a separate theorem shows that it exists. `Mat n`, `J₀`, `IsSymplectic` and `SP` come from `ConleyZehnder_Setting`.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3: Section 3.2, equation (3.4), p. 46; Section 3.4, Exercise 3.29, p. 61; Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, pp. 285-288, equation (35)

import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Asymptotic operators on the circle

Wendl, *Lectures on Symplectic Field Theory*, arXiv:1612.01009, §3.2, equation (3.4):
for a loop `S : S¹ → ℝ^{2n×2n}` of symmetric matrices, the asymptotic operator
`A_S = -J₀ ∂ₜ - S(t)` acts on `L²(S¹, ℝ²ⁿ)` with domain `W^{1,2}(S¹, ℝ²ⁿ)`.

Conventions. `S¹ = ℝ/ℤ` (`UnitAddCircle`) with its Haar probability measure. `ℝ²ⁿ` is
`EuclideanSpace ℝ (Fin n ⊕ Fin n)` and `J₀ = Matrix.J`, as in `ConleyZehnder_Setting`.
The `k`-th Fourier coefficient of `f : S¹ → ℝ²ⁿ` is `f̂ₖ = ∫ e^{-2πikt} f(t) dt ∈ ℂ²ⁿ`,
computed componentwise on the complexification. `W^{1,2}` is the set of `f ∈ L²` with
`∑ₖ (1 + k²) |f̂ₖ|² < ∞`, and `A_S f = g` means `ĝₖ = -2πik J₀ f̂ₖ - (S f)^ₖ` for all `k`,
i.e. `g = -J₀ f' - S f` with the derivative taken in `L²`.

The fundamental solution of `S` is `Ψ : ℝ → ℝ^{2n×2n}` with `Ψ(0) = Id` and
`Ψ' = J₀ S Ψ`; these are the solutions of `(-J₀ ∂ₜ - S) Ψ = 0`.
-/

namespace AsymptoticOperator

noncomputable section

open MeasureTheory Matrix Classical ConleyZehnder

/-- `ℝ²ⁿ` with its Euclidean inner product, coordinates indexed by `Fin n ⊕ Fin n`. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n ⊕ Fin n)

/-- `L²(S¹, ℝ²ⁿ)` for `S¹ = ℝ/ℤ` with the Haar probability measure. -/
abbrev L2 (n : ℕ) := Lp (Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)

variable {n : ℕ}

/-- A loop `S : S¹ → ℝ^{2n×2n}` of symmetric matrices. -/
def IsSymLoop (S : C(UnitAddCircle, Mat n)) : Prop := ∀ t, (S t).IsSymm

/-- The complexification `ℝ²ⁿ → ℂ²ⁿ` of a vector. -/
def complexify (v : Vec n) : Fin n ⊕ Fin n → ℂ := fun i => ((v i : ℝ) : ℂ)

/-- The `k`-th Fourier coefficient `f̂ₖ = ∫ e^{-2πikt} f(t) dt ∈ ℂ²ⁿ`. -/
def coeff (f : UnitAddCircle → Vec n) (k : ℤ) : Fin n ⊕ Fin n → ℂ :=
  fourierCoeff (fun t => complexify (f t)) k

/-- The `k`-th Fourier coefficient of `t ↦ S(t) f(t)`. -/
def coeffMul (S : C(UnitAddCircle, Mat n)) (f : UnitAddCircle → Vec n) (k : ℤ) :
    Fin n ⊕ Fin n → ℂ :=
  fourierCoeff (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (f t)) k

/-- `f ∈ W^{1,2}(S¹, ℝ²ⁿ)`: `∑ₖ (1 + k²) |f̂ₖ|² < ∞`. -/
def InW12 (f : L2 n) : Prop :=
  Summable fun k : ℤ => (1 + (k : ℝ) ^ 2) * ∑ i, ‖coeff f k i‖ ^ 2

/-- `A_S f = g`: `f ∈ W^{1,2}` and `ĝₖ = -2πik J₀ f̂ₖ - (S f)^ₖ` for every `k ∈ ℤ`,
that is, `g = -J₀ f' - S f`. -/
def IsAsymptoticAction (S : C(UnitAddCircle, Mat n)) (f g : L2 n) : Prop :=
  InW12 f ∧ ∀ k : ℤ, coeff g k =
    -((2 * Real.pi * k : ℝ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff f k) -
      coeffMul S f k

/-- The graph `{(f, A_S f)}` of the asymptotic operator, as a set of pairs. -/
def graphSet (S : C(UnitAddCircle, Mat n)) : Set (L2 n × L2 n) :=
  {p | IsAsymptoticAction S p.1 p.2}

/-- Wendl (3.4): the asymptotic operator `A_S = -J₀ ∂ₜ - S` as an unbounded operator on
`L²(S¹, ℝ²ⁿ)`: the partially defined linear map whose graph is `graphSet S` (chosen,
with fallback `0` if no such map exists). -/
def asymptoticOperator (S : C(UnitAddCircle, Mat n)) : L2 n →ₗ.[ℝ] L2 n :=
  if h : ∃ A : L2 n →ₗ.[ℝ] L2 n, (A.graph : Set (L2 n × L2 n)) = graphSet S then h.choose
  else 0

/-- `A` has an orthonormal basis of eigenvectors in its domain with real eigenvalues
`ev i`, and `|ev i| → ∞` along the cofinite filter (each bounded set of eigenvalues is
attained by finitely many basis vectors). -/
def HasDiscreteEigenbasis (A : L2 n →ₗ.[ℝ] L2 n) : Prop :=
  ∃ (ι : Type) (b : HilbertBasis ι ℝ (L2 n)) (ev : ι → ℝ),
    (∀ i, ∃ h : b i ∈ A.domain, A ⟨b i, h⟩ = ev i • b i) ∧
      Filter.Tendsto (fun i => |ev i|) Filter.cofinite Filter.atTop

/-- The eigenspace `ker(A - μ)`, as a subspace of the domain of `A`. -/
def eigenspace (A : L2 n →ₗ.[ℝ] L2 n) (μ : ℝ) : Submodule ℝ A.domain :=
  LinearMap.ker (A.toFun - μ • A.domain.subtype)

/-- `Ψ : ℝ → ℝ^{2n×2n}` is the fundamental solution of `S`: `Ψ(0) = Id` and
`Ψ'(t) = J₀ S(t) Ψ(t)` for all `t`. -/
def IsFundamentalSolution (S : C(UnitAddCircle, Mat n)) (Ψ : ℝ → Mat n) : Prop :=
  Ψ 0 = 1 ∧ ∀ t : ℝ, HasDerivAt Ψ (J₀ n * S (t : UnitAddCircle) * Ψ t) t

end

end AsymptoticOperator


