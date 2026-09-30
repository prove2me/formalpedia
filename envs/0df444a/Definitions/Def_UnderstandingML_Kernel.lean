-- Prove2me | Definitions.Def_UnderstandingML_Kernel
-- name    : UnderstandingML_Kernel
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T04:45:56.195169+00:00
-- url     : https://prove2.me/theorems/3589dbc6-851e-4b24-9a94-b4f3b2f12d7f
-- title:
--   Chapter 16: kernels and kernel functions, Gram matrices, the objective (16.2), polynomial and Gaussian kernels, kernel ridge regression, SGD for Soft-SVM in feature space and with kernels
-- statement:
--   Chapter 16 of Shalev-Shwartz and Ben-David. For a feature map $\psi : X \to F$ into a real Hilbert space, the **kernel** is $K(x, x') = \langle\psi(x), \psi(x')\rangle$ (`kernelOf`); a function $K : X \times X \to \mathbb{R}$ **implements an inner product in some Hilbert space** if it is of this form for some Hilbert space (in the universe of $X$) and feature map (`IsKernel`); the **Gram matrix** of a sample is $G_{ij} = K(x_i, x_j)$ (`gramMatrix`). The objective of the general problem (16.2), $f(\langle w, \psi(x_1)\rangle, \dots, \langle w, \psi(x_m)\rangle) + R(\|w\|)$ (`kernelObjective`). The **polynomial kernel** $(1 + \langle x, x'\rangle)^k$ (`polynomialKernel`) and the **Gaussian kernel** $e^{-\|x - x'\|^2/(2\sigma)}$ (`gaussianKernel`). Kernel ridge regression: the objectives (16.8) in $w$ and (16.9) in the coefficients (`kernelRidgeObjective`, `kernelRidgeCoeffObjective`). **SGD for Soft-SVM** (§15.5) in the feature space, maintaining $\theta^{(t)}$ with $w^{(t)} = \theta^{(t)}/(\lambda(t+1))$ (`svmSgdTheta`, `svmSgdAverage`), and **with kernels** (§16.3), maintaining coefficients $\beta^{(t)}$ with $\alpha^{(t)} = \beta^{(t)}/(\lambda(t+1))$ (`kernelSgdBeta`, `kernelSgdAlphaBar`); both are driven by a sequence of chosen indices and indexed from $0$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.2 pp. 217-222 (Equation (16.2), Examples 16.1-16.2, Lemma 16.2's notion), §16.3 pp. 222-223, Exercise 16.3 p. 225

import Definitions.Def_UnderstandingML_SVM
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 16: kernel methods

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.1–§16.3.

**Feature maps and kernels (§16.1–§16.2).** A feature map `ψ : X → F` into a Hilbert space `F`
defines the kernel `K(x, x') = ⟨ψ(x), ψ(x')⟩`; a function `K : X × X → ℝ` is a kernel if it is
of this form for some Hilbert space and feature map. The Gram matrix of a sample is
`Gᵢⱼ = K(xᵢ, xⱼ)`.

**The general problem (16.2).** `min_w f(⟨w, ψ(x₁)⟩, …, ⟨w, ψ(x_m)⟩) + R(‖w‖)` for an arbitrary
`f : ℝ^m → ℝ` and a nondecreasing `R : ℝ₊ → ℝ`; the representer theorem says an optimal
solution lies in the span of the `ψ(xᵢ)`, and (16.3) rewrites the objective in terms of the
coefficients and the Gram matrix.

**SGD for Soft-SVM with kernels (§16.3).** The procedure of §15.5 maintains `θ⁽ᵗ⁾`,
`w⁽ᵗ⁾ = θ⁽ᵗ⁾/(λt)`; the kernelized version maintains coefficients `β⁽ᵗ⁾`, `α⁽ᵗ⁾ = β⁽ᵗ⁾/(λt)` with
`θ⁽ᵗ⁾ = ∑ⱼ βⱼ⁽ᵗ⁾ ψ(xⱼ)`.

**Conventions.** Hilbert spaces are real inner product spaces that are complete. A kernel's
feature space is quantified existentially in the same universe as the domain (the reproducing
kernel Hilbert space of Lemma 16.2 lives there). The SGD procedures are driven by a given
sequence of indices `idx : ℕ → Fin m` (the uniformly random choices of §15.5), with iterates
indexed from `0` so that the book's `w⁽ᵗ⁾ = θ⁽ᵗ⁾/(λt)` reads `w⁽ᵗ⁾ = θ⁽ᵗ⁾/(λ(t+1))`. `R` is required
to be nondecreasing on `[0, ∞)`.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

universe u

section Kernels

variable {X : Type u} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The **kernel** of a feature map, `K(x, x') = ⟨ψ(x), ψ(x')⟩` (§16.2). -/
noncomputable def kernelOf (ψ : X → F) (x x' : X) : ℝ := ⟪ψ x, ψ x'⟫_ℝ

/-- `K` **implements an inner product in some Hilbert space**: `K(x, x') = ⟨ψ(x), ψ(x')⟩` for a
feature map `ψ` into a real Hilbert space (§16.2, Lemma 16.2). -/
def IsKernel (K : X → X → ℝ) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F) (_ : CompleteSpace F)
    (ψ : X → F), ∀ x x', K x x' = ⟪ψ x, ψ x'⟫_ℝ

/-- The **Gram matrix** `Gᵢⱼ = K(xᵢ, xⱼ)` of a sample under `K` (§16.2). -/
def gramMatrix {m : ℕ} (K : X → X → ℝ) (x : Fin m → X) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j ↦ K (x i) (x j)

/-- The objective of the general problem (16.2), `f(⟨w, ψ(x₁)⟩, …, ⟨w, ψ(x_m)⟩) + R(‖w‖)`. -/
noncomputable def kernelObjective {m : ℕ} (ψ : X → F) (x : Fin m → X) (f : (Fin m → ℝ) → ℝ)
    (R : ℝ → ℝ) (w : F) : ℝ :=
  f (fun i ↦ ⟪w, ψ (x i)⟫_ℝ) + R ‖w‖

/-- The **polynomial kernel** of degree `k`, `K(x, x') = (1 + ⟨x, x'⟩)^k` (Example 16.1). -/
noncomputable def polynomialKernel {n : ℕ} (k : ℕ) (x x' : Vec n) : ℝ := (1 + ⟪x, x'⟫_ℝ) ^ k

/-- The **Gaussian (RBF) kernel** `K(x, x') = exp(−‖x − x'‖²/(2σ))` (Example 16.2). -/
noncomputable def gaussianKernel {n : ℕ} (σ : ℝ) (x x' : Vec n) : ℝ :=
  Real.exp (-(‖x - x'‖ ^ 2) / (2 * σ))

/-- The kernel ridge regression objective (16.8): `λ‖w‖² + (1/(2m)) ∑ᵢ (⟨w, ψ(xᵢ)⟩ − yᵢ)²`. -/
noncomputable def kernelRidgeObjective {m : ℕ} (ψ : X → F) (x : Fin m → X) (y : Fin m → ℝ)
    (lam : ℝ) (w : F) : ℝ :=
  lam * ‖w‖ ^ 2 + (1 / (2 * m)) * ∑ i, (⟪w, ψ (x i)⟫_ℝ - y i) ^ 2

/-- The kernel ridge regression objective in the coefficients (16.9):
`λ αᵀGα + (1/(2m)) ∑ᵢ (⟨α, G_{·,i}⟩ − yᵢ)²`. -/
noncomputable def kernelRidgeCoeffObjective {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ)
    (y : Fin m → ℝ) (lam : ℝ) (α : Fin m → ℝ) : ℝ :=
  lam * dotProduct α (G.mulVec α) + (1 / (2 * m)) * ∑ i, ((∑ j, α j * G j i) - y i) ^ 2

end Kernels

/-! ### SGD for Soft-SVM in the feature space and with kernels (§15.5, §16.3) -/

section KernelSGD

variable {X : Type u} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The vectors `θ⁽ᵗ⁾` of the SGD procedure of §15.5 run in the feature space (indexed from `0`,
`w⁽ᵗ⁾ = θ⁽ᵗ⁾/(λ(t+1))`), driven by the index sequence `idx`: if `yᵢ⟨w⁽ᵗ⁾, ψ(xᵢ)⟩ < 1` for
`i = idx t` then `θ⁽ᵗ⁺¹⁾ = θ⁽ᵗ⁾ + yᵢ ψ(xᵢ)`, else `θ⁽ᵗ⁺¹⁾ = θ⁽ᵗ⁾`. -/
noncomputable def svmSgdTheta {m : ℕ} (ψ : X → F) (x : Fin m → X) (y : Fin m → ℝ) (lam : ℝ)
    (idx : ℕ → Fin m) : ℕ → F
  | 0 => 0
  | t + 1 =>
    let θ := svmSgdTheta ψ x y lam idx t
    let i := idx t
    if y i * ⟪(1 / (lam * (t + 1))) • θ, ψ (x i)⟫_ℝ < 1 then θ + y i • ψ (x i) else θ

/-- The output `w̄ = (1/T) ∑ₜ w⁽ᵗ⁾` of the feature-space SGD procedure of §15.5. -/
noncomputable def svmSgdAverage {m : ℕ} (ψ : X → F) (x : Fin m → X) (y : Fin m → ℝ) (lam : ℝ)
    (idx : ℕ → Fin m) (T : ℕ) : F :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (1 / (lam * (t + 1))) • svmSgdTheta ψ x y lam idx t

/-- The coefficient vectors `β⁽ᵗ⁾` of **SGD for Soft-SVM with kernels** (§16.3): with
`α⁽ᵗ⁾ = β⁽ᵗ⁾/(λ(t+1))` and `i = idx t`, if `yᵢ ∑ⱼ αⱼ⁽ᵗ⁾ K(xⱼ, xᵢ) < 1` then `βᵢ⁽ᵗ⁺¹⁾ = βᵢ⁽ᵗ⁾ + yᵢ`
(other coordinates unchanged), else `β⁽ᵗ⁺¹⁾ = β⁽ᵗ⁾`. -/
noncomputable def kernelSgdBeta {m : ℕ} (K : X → X → ℝ) (x : Fin m → X) (y : Fin m → ℝ)
    (lam : ℝ) (idx : ℕ → Fin m) : ℕ → Fin m → ℝ
  | 0 => 0
  | t + 1 =>
    let β := kernelSgdBeta K x y lam idx t
    let i := idx t
    if y i * ∑ j, (1 / (lam * (t + 1))) * β j * K (x j) (x i) < 1 then
      Function.update β i (β i + y i)
    else β

/-- The output coefficients `ᾱ = (1/T) ∑ₜ α⁽ᵗ⁾` of SGD with kernels, so that
`w̄ = ∑ⱼ ᾱⱼ ψ(xⱼ)`. -/
noncomputable def kernelSgdAlphaBar {m : ℕ} (K : X → X → ℝ) (x : Fin m → X) (y : Fin m → ℝ)
    (lam : ℝ) (idx : ℕ → Fin m) (T : ℕ) : Fin m → ℝ :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (1 / (lam * (t + 1))) • kernelSgdBeta K x y lam idx t

end KernelSGD

end UnderstandingML


