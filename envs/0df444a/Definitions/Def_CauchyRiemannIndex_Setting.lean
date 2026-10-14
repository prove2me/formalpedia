-- Prove2me | Definitions.Def_CauchyRiemannIndex_Setting
-- name    : CauchyRiemannIndex_Setting
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-13T21:00:19.314023+00:00
-- url     : https://prove2.me/theorems/e41a88c2-f901-498f-91b0-c648055c3d64
-- title:
--   Sobolev spaces, Cauchy–Riemann operators and asymptotic operators on the cylinder
-- statement:
--   Basic objects for linear Cauchy–Riemann operators on the cylinder $\mathbb{R}\times S^1$, $S^1=\mathbb{R}/\mathbb{Z}$, with the trivial bundle $\mathbb{R}^{2n}=\mathbb{C}^n$ (C. Wendl, *Lectures on Symplectic Field Theory*, Lectures 3–5), and the Conley–Zehnder index of a path of symplectic matrices (J. Gutt, *Generalized Conley–Zehnder index*, Definition 7 and Corollary 12).
--
--   1. **Matrices.** $J_0=\begin{pmatrix}0&-\mathrm{Id}\\\mathrm{Id}&0\end{pmatrix}$ on $\mathbb{R}^{2n}$, multiplication by $i$ under $(x,y)\mapsto x+iy$; $C=\begin{pmatrix}\mathrm{Id}&0\\0&-\mathrm{Id}\end{pmatrix}$ is complex conjugation; for $\beta\in\mathbb{C}$, `antilinearMat β` is the real $2\times2$ matrix of $z\mapsto\beta\bar z$ on $\mathbb{C}=\mathbb{R}^2$.
--   2. **Conley–Zehnder index of a symplectic path** $\psi:[0,1]\to\mathrm{Sp}(2n)$: the integer $\mu_{CZ}(\psi)=\deg(\hat\rho^2\circ\tilde\psi)$, where $\hat\rho(A)=\det_{\mathbb{C}}C_A/|\det_{\mathbb{C}}C_A|$, $C_A=\tfrac12(A-J_0AJ_0)$, and $\tilde\psi$ is $\psi$ followed by a path in $\mathrm{Sp}^*$ (no eigenvalue $1$) ending at $W^+=-\mathrm{Id}$ or $W^-=\mathrm{diag}(2,-1,\dots,-1,\tfrac12,-1,\dots,-1)$ (Gutt). The value is chosen, with fallback $0$ when no such degree exists.
--   3. **Asymptotic operators.** A loop $S_\infty:S^1\to\mathbb{R}^{2n\times2n}$ of symmetric matrices defines $A=-J_0\partial_t-S_\infty(t)$ (Wendl (3.10)). Its fundamental solution is $\Psi:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ with $\Psi(0)=\mathrm{Id}$, $\Psi'=J_0S_\infty\Psi$. $A$ is **nondegenerate** if $\det(\mathrm{Id}-\Psi(1))\ne0$, i.e. $A\eta=0$ has no nonzero $1$-periodic solution, and $\mu_{CZ}(A)$ is the Conley–Zehnder index of the path $\Psi|_{[0,1]}$.
--   4. **Sobolev space.** $L^p(\mathbb{R}\times S^1,\mathbb{R}^{2n})$ is $L^p$ of the strip $\mathbb{R}\times[0,1)$ with Lebesgue measure. A test section is a smooth map $u:\mathbb{R}^2\to\mathbb{R}^{2n}$ with $u(s,t+1)=u(s,t)$ that vanishes for large $|s|$. $W^{1,p}$ is the closure in $L^p\times L^p\times L^p$ of the span of the triples $(u,\partial_su,\partial_tu)$ of test sections, and $\|u\|_{W^{1,p}}=\|u\|_p+\|\partial_su\|_p+\|\partial_tu\|_p$ for test sections.
--   5. **Cauchy–Riemann operators** (Wendl (4.2)). For a continuous $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$, $D_S=\partial_s+J_0\partial_t+S(s,t)$, acting on a triple by $(u,v,w)\mapsto v+J_0w+Su$. Its kernel is $\{w\in W^{1,p}:D_Sw=0\}$, its range is $\{D_Sw:w\in W^{1,p}\}\subset L^p$, it is **Fredholm** if the kernel is finite-dimensional and the range is closed of finite codimension, and its **index** is $\dim\ker D_S-\dim(L^p/\operatorname{im}D_S)$.
--   6. **Asymptotic convergence** (Wendl, Definition 4.2 and Remark 4.4). $S$ is asymptotic to loops $S^\pm$ if it is continuous, $1$-periodic in $t$, and $S(s,t)\to S^\pm(t)$ as $s\to\pm\infty$, uniformly in $t$.
--
--   **Formalization Note** $\mathbb{R}^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)` and matrices are `Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ`, acting by `Matrix.toEuclideanLin`; $J_0$ is `Matrix.J`. The definitions `IsSymplectic`, `SpStar`, `Wplus`, `Wminus`, `complexLinearPart`, `complexLinearDet`, `rhoHat`, `IsArgLift`, `IsSpStarExtension`, `IsCZValue` and `czIndex` repeat those of `ConleyZehnder_Setting` word for word, so that the mission is standalone. `asymptoticCZIndex S` is the chosen `k` with `IsAsymptoticCZValue S k` (fallback $0$). $\partial_su$, $\partial_tu$ are `fderiv ℝ u x (1, 0)` and `fderiv ℝ u x (0, 1)`, and smoothness is `ContDiff ℝ ∞`. `W1p p n` is `(Submodule.span ℝ (testTriples n p)).topologicalClosure` in `Lp × Lp × Lp` (with `Fact (1 ≤ p)`), so its elements are triples $(u,\partial_su,\partial_tu)$ with weak derivatives; its norm is the product (maximum) norm, equivalent to the $W^{1,p}$ norm. `crKernel` and `crRange` are the spans of the kernel and range sets, which are already subspaces. Convergence $S\to S^\pm$ is stated entrywise.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lectures 3–4, (3.10), (4.2), Definition 4.2, Remark 4.4; J. Gutt, Generalized Conley–Zehnder index, Ann. Fac. Sci. Toulouse Math. (6) 23 (2014), arXiv:1307.7239, Definition 7 and Corollary 12

import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Linear Cauchy–Riemann operators on the cylinder

C. Wendl, *Lectures on Symplectic Field Theory*, arXiv:1612.01009, Lectures 3–5, for the
punctured surface `ℝ × S¹` (the sphere with one positive and one negative puncture) and the
trivial bundle `ℝ × S¹ × ℝ²ⁿ`.

Conventions. `S¹ = ℝ/ℤ`; a map on the cylinder is a map `u : ℝ × ℝ → ℝ²ⁿ` of `(s, t)` with
`u(s, t + 1) = u(s, t)`, and `L^p(ℝ × S¹)` is `L^p` of the strip `ℝ × [0, 1)` with Lebesgue
measure. `ℝ²ⁿ` is `EuclideanSpace ℝ (Fin n ⊕ Fin n)` (first block `q`, second block `p`) and
`J₀ = [[0, -Id], [Id, 0]]` is Mathlib's `Matrix.J`, i.e. multiplication by `i` under
`(x, y) ↦ x + i y`.

* `W^{1,p}(ℝ × S¹, ℝ²ⁿ)` is the closure of the smooth maps that are `1`-periodic in `t` and
  vanish for large `|s|`, under `u ↦ (u, ∂ₛu, ∂ₜu)` in `L^p × L^p × L^p`
  (Wendl, Lecture 4, §4.1 and §A.4).
* For a continuous, `t`-periodic `S : ℝ × ℝ → ℝ^{2n×2n}`, the operator
  `D_S = ∂ₛ + J₀ ∂ₜ + S(s, t) : W^{1,p} → L^p` (Wendl (4.2)) acts on such a triple by
  `(u, v, w) ↦ v + J₀ w + S u`.
* The asymptotic operator `A = -J₀ ∂ₜ - S∞(t)` of a loop `S∞` of symmetric matrices
  (Wendl (3.10)) is encoded by the fundamental solution `Ψ' = J₀ S∞ Ψ`, `Ψ(0) = Id`, whose
  columns span the solutions of `A η = 0` on `ℝ`.
* The Conley–Zehnder index of a path of symplectic matrices is defined as in Gutt,
  *Generalized Conley–Zehnder index*, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239,
  Definition 7 with Corollary 12; the definitions `IsSymplectic` … `czIndex` below repeat
  those of the `ConleyZehnder` mission word for word.
-/

namespace CauchyRiemannIndex

noncomputable section

open MeasureTheory Matrix Classical
open scoped ContDiff ENNReal

/-! ### Symplectic matrices and the Conley–Zehnder index of a path -/

/-- Real `2n × 2n` matrices, indexed by `Fin n ⊕ Fin n`. -/
abbrev Mat (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ

/-- `J₀ = [[0, -Id], [Id, 0]]`. -/
abbrev J₀ (n : ℕ) : Mat n := Matrix.J (Fin n) ℝ

variable {n : ℕ}

/-- `A ∈ Sp(ℝ²ⁿ, Ω₀)`. -/
def IsSymplectic (A : Mat n) : Prop := A ∈ Matrix.symplecticGroup (Fin n) ℝ

/-- `Sp*(ℝ²ⁿ, Ω₀)`: symplectic matrices without eigenvalue `1`. -/
def SpStar (n : ℕ) : Set (Mat n) := {A | IsSymplectic A ∧ (1 - A).det ≠ 0}

/-- `W⁺ = -Id`. -/
def Wplus (n : ℕ) : Mat n := -1

/-- `W⁻ = diag(2, -1, …, -1, 1/2, -1, …, -1)`. -/
def Wminus (n : ℕ) : Mat n :=
  Matrix.diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (2 : ℝ) else -1)
    (fun j : Fin n => if j.val = 0 then (1 / 2 : ℝ) else -1))

/-- The `ℂ`-linear part `C_A = ½(A - J₀ A J₀)` of `A`. -/
def complexLinearPart (A : Mat n) : Mat n := (1 / 2 : ℝ) • (A - J₀ n * A * J₀ n)

/-- `det_ℂ C_A`: writing `C_A = [[X, -Y], [Y, X]]`, the determinant of the complex
`n × n` matrix `X + i Y`. -/
def complexLinearDet (A : Mat n) : ℂ :=
  ((complexLinearPart A).toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
    Complex.I • (complexLinearPart A).toBlocks₂₁.map (fun x : ℝ => (x : ℂ))).det

/-- Gutt (9): `ρ̂(A) = det_ℂ C_A / |det_ℂ C_A|`. -/
def rhoHat (A : Mat n) : ℂ := complexLinearDet A / (‖complexLinearDet A‖ : ℂ)

/-- `θ` is a continuous argument of `f : [0, 1] → S¹`: `f(t) = e^{i θ(t)}`. -/
def IsArgLift (f : unitInterval → ℂ) (θ : unitInterval → ℝ) : Prop :=
  Continuous θ ∧ ∀ t, f t = Complex.exp ((θ t : ℂ) * Complex.I)

/-- `χ` continues `ψ` as in Gutt §2: it starts at `ψ(1)`, stays in `Sp*`, and ends at
`W⁺` or `W⁻`. -/
def IsSpStarExtension (ψ χ : C(unitInterval, Mat n)) : Prop :=
  χ 0 = ψ 1 ∧ (∀ t, χ t ∈ SpStar n) ∧ (χ 1 = Wplus n ∨ χ 1 = Wminus n)

/-- `k = deg(ρ̂² ∘ ψ̃)` for some extension `ψ̃` of `ψ`: the total change of a continuous
argument of `ρ̂² ∘ ψ̃` along `ψ` followed by `χ` is `2π k`. -/
def IsCZValue (ψ : C(unitInterval, Mat n)) (k : ℤ) : Prop :=
  ∃ χ : C(unitInterval, Mat n), IsSpStarExtension ψ χ ∧
    ∃ θ₁ θ₂ : unitInterval → ℝ, IsArgLift (fun t => rhoHat (ψ t)) θ₁ ∧
      IsArgLift (fun t => rhoHat (χ t)) θ₂ ∧
      2 * ((θ₁ 1 - θ₁ 0) + (θ₂ 1 - θ₂ 0)) = 2 * Real.pi * k

/-- Gutt, Definition 7 / Corollary 12: the Conley–Zehnder index `μ_CZ(ψ) = deg(ρ̂² ∘ ψ̃)`. -/
def czIndex (ψ : C(unitInterval, Mat n)) : ℤ :=
  if h : ∃ k, IsCZValue ψ k then h.choose else 0

/-! ### Asymptotic operators -/

/-- A loop `S∞ : S¹ → ℝ^{2n×2n}` of symmetric matrices, as a continuous `1`-periodic map on
`ℝ`. -/
def IsSymLoop (S : ℝ → Mat n) : Prop :=
  Continuous S ∧ Function.Periodic S 1 ∧ ∀ t, (S t).IsSymm

/-- `Ψ` is the fundamental solution of `S∞`: `Ψ(0) = Id` and `Ψ'(t) = J₀ S∞(t) Ψ(t)`. -/
def IsFundamentalSolution (S : ℝ → Mat n) (Ψ : ℝ → Mat n) : Prop :=
  Ψ 0 = 1 ∧ ∀ t : ℝ, HasDerivAt Ψ (J₀ n * S t * Ψ t) t

/-- The asymptotic operator `-J₀ ∂ₜ - S∞` is nondegenerate: `1` is not an eigenvalue of
`Ψ(1)`, i.e. `-J₀ η' - S∞ η = 0` has no nonzero `1`-periodic solution. -/
def IsNondegenerate (S : ℝ → Mat n) : Prop :=
  ∀ Ψ, IsFundamentalSolution S Ψ → (1 - Ψ 1).det ≠ 0

/-- `k` is the Conley–Zehnder index of `-J₀ ∂ₜ - S∞`: the index of the path
`t ↦ Ψ(t)`, `t ∈ [0, 1]`, of its fundamental solution. -/
def IsAsymptoticCZValue (S : ℝ → Mat n) (k : ℤ) : Prop :=
  ∃ Ψ, IsFundamentalSolution S Ψ ∧
    ∃ ψ : C(unitInterval, Mat n), (∀ t : unitInterval, ψ t = Ψ t) ∧ IsCZValue ψ k

/-- Wendl, Definition 3.30, through the fundamental solution: the Conley–Zehnder index
`μ_CZ(-J₀ ∂ₜ - S∞)` (chosen, with fallback `0`). -/
def asymptoticCZIndex (S : ℝ → Mat n) : ℤ :=
  if h : ∃ k, IsAsymptoticCZValue S k then h.choose else 0

/-! ### Sobolev spaces on the cylinder and Cauchy–Riemann operators -/

/-- `ℝ²ⁿ` with its Euclidean norm. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n ⊕ Fin n)

/-- Lebesgue measure on the strip `ℝ × [0, 1)`, a fundamental domain of `ℝ × S¹`. -/
def cylMeasure : Measure (ℝ × ℝ) := volume.restrict (Set.univ ×ˢ Set.Ico 0 1)

/-- `L^p(ℝ × S¹, ℝ²ⁿ)`. -/
abbrev LpCyl (n : ℕ) (p : ℝ≥0∞) := Lp (Vec n) p cylMeasure

/-- Triples `(u, ∂ₛu, ∂ₜu)` in `L^p × L^p × L^p`. -/
abbrev Triple (n : ℕ) (p : ℝ≥0∞) := LpCyl n p × LpCyl n p × LpCyl n p

/-- `u` is a test section: smooth, `1`-periodic in `t`, and zero for large `|s|`. -/
def IsTestSection (u : ℝ × ℝ → Vec n) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ s t, u (s, t + 1) = u (s, t)) ∧ ∃ R : ℝ, ∀ s t, R < |s| → u (s, t) = 0

/-- `∂ₛu`. -/
def partialS (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n := fderiv ℝ u x (1, 0)

/-- `∂ₜu`. -/
def partialT (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n := fderiv ℝ u x (0, 1)

/-- The triples `(u, ∂ₛu, ∂ₜu)` of test sections `u`. -/
def testTriples (n : ℕ) (p : ℝ≥0∞) : Set (Triple n p) :=
  {w | ∃ u, IsTestSection u ∧ (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u ∧
    (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u ∧
    (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u}

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- `W^{1,p}(ℝ × S¹, ℝ²ⁿ)`, as the closed subspace of `L^p × L^p × L^p` spanned by the
triples `(u, ∂ₛu, ∂ₜu)` of test sections; its norm is the product norm. -/
def W1p (n : ℕ) : Submodule ℝ (Triple n p) :=
  (Submodule.span ℝ (testTriples n p)).topologicalClosure

variable {p}

/-- `D_S (u, v, w) = v + J₀ w + S u`, pointwise on the cylinder; on `(u, ∂ₛu, ∂ₜu)` this is
`∂ₛu + J₀ ∂ₜu + S(s, t) u`. -/
def crApply (S : ℝ × ℝ → Mat n) (w : Triple n p) (x : ℝ × ℝ) : Vec n :=
  w.2.1 x + Matrix.toEuclideanLin (J₀ n) (w.2.2 x) + Matrix.toEuclideanLin (S x) (w.1 x)

variable (p)

/-- `ker D_S ⊆ W^{1,p}`. -/
def crKernel (S : ℝ × ℝ → Mat n) : Submodule ℝ (Triple n p) :=
  Submodule.span ℝ {w | w ∈ W1p p n ∧ crApply S w =ᵐ[cylMeasure] 0}

/-- `im D_S ⊆ L^p`. -/
def crRange (S : ℝ × ℝ → Mat n) : Submodule ℝ (LpCyl n p) :=
  Submodule.span ℝ {f | ∃ w ∈ W1p p n, (f : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] crApply S w}

/-- `D_S : W^{1,p} → L^p` is Fredholm: finite-dimensional kernel, closed range of finite
codimension. -/
def IsFredholmCR (S : ℝ × ℝ → Mat n) : Prop :=
  FiniteDimensional ℝ (crKernel p S) ∧ IsClosed (crRange p S : Set (LpCyl n p)) ∧
    FiniteDimensional ℝ (LpCyl n p ⧸ crRange p S)

/-- The Fredholm index `dim ker D_S - dim coker D_S`. -/
def crIndex (S : ℝ × ℝ → Mat n) : ℤ :=
  (Module.finrank ℝ (crKernel p S) : ℤ) - Module.finrank ℝ (LpCyl n p ⧸ crRange p S)

variable {p}

/-- `D_S u = ∂ₛu + J₀ ∂ₜu + S(s, t) u` for a differentiable map `u` on the cylinder. -/
def crOp (S : ℝ × ℝ → Mat n) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n :=
  partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x) + Matrix.toEuclideanLin (S x) (u x)

/-- The `W^{1,p}(ℝ × S¹)` norm `‖u‖_p + ‖∂ₛu‖_p + ‖∂ₜu‖_p`, with values in `[0, ∞]`. -/
def w1pNorm (p : ℝ≥0∞) (u : ℝ × ℝ → Vec n) : ℝ≥0∞ :=
  eLpNorm u p cylMeasure + eLpNorm (partialS u) p cylMeasure + eLpNorm (partialT u) p cylMeasure

/-- Complex conjugation `(x, y) ↦ (x, -y)` on `ℝ²ⁿ = ℂⁿ`. -/
def conjMat (n : ℕ) : Mat n :=
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1)

/-- The real `2 × 2` matrix of `z ↦ β z̄` on `ℂ = ℝ²`: `[[Re β, Im β], [Im β, -Re β]]`. -/
def antilinearMat (β : ℂ) : Mat 1 :=
  Matrix.fromBlocks (Matrix.of fun _ _ => β.re) (Matrix.of fun _ _ => β.im)
    (Matrix.of fun _ _ => β.im) (Matrix.of fun _ _ => -β.re)

/-- `S : ℝ × ℝ → ℝ^{2n×2n}` is a continuous `t`-periodic coefficient with
`S(s, ·) → S⁺` as `s → +∞` and `S(s, ·) → S⁻` as `s → -∞`, uniformly in `t` and entrywise
(Wendl, Definition 4.2 with Remark 4.4). -/
def IsAsymptoticTo (S : ℝ × ℝ → Mat n) (Splus Sminus : ℝ → Mat n) : Prop :=
  Continuous S ∧ (∀ s t, S (s, t + 1) = S (s, t)) ∧
    ∀ ε > 0, ∃ R : ℝ, ∀ s t, ∀ i j,
      (R ≤ s → |S (s, t) i j - Splus t i j| ≤ ε) ∧ (s ≤ -R → |S (s, t) i j - Sminus t i j| ≤ ε)

end

end CauchyRiemannIndex


