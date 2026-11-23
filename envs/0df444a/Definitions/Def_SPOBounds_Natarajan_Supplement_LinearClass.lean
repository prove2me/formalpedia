-- Prove2me | Definitions.Def_SPOBounds_Natarajan_Supplement_LinearClass
-- name    : SPOBounds_Natarajan_Supplement_LinearClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:35:43.431676+00:00
-- url     : https://prove2.me/theorems/791a59fb-89f6-4a7e-bb47-64b8c36e8fa4
-- title:
--   Constrained linear class $\mathcal H_{\mathcal B}$, matrix norms, dual norm and strong convexity (§4.4)
-- statement:
--   These are the objects of §4.4 and Theorem 6, on the space $\mathbb R^{d\times p}$ of real $d\times p$ matrices.
--
--   1. The **trace pairing** $\langle B, A\rangle := \sum_{i,j} B_{ij}A_{ij} = \operatorname{Tr}(BA^\top)$.
--   2. A **matrix norm** $\|\cdot\|$ on $\mathbb R^{d\times p}$: a seminorm that vanishes only at the zero matrix. The norm is arbitrary; it is not fixed to the Frobenius norm.
--   3. The **dual norm** with respect to the trace pairing,
--   $$\|A\|_* := \sup\{\langle B, A\rangle : \|B\|\le 1\}.$$
--   4. **Strong convexity**: $F$ is $\alpha$-strongly convex on $\mathcal S$ with respect to a function $M$ (used with $M=\|\cdot\|_*$) if for all $A,B\in\mathcal S$ and $t\in[0,1]$
--   $$F(tA+(1-t)B)\le tF(A)+(1-t)F(B)-\frac{\alpha}{2}\,t(1-t)\,M(A-B)^2 .$$
--   5. The **outer product** $\sigma x^\top\in\mathbb R^{d\times p}$ of a sign vector $\sigma\in\{\pm1\}^d$ and a feature $x\in\mathbb R^p$.
--   6. The **constrained linear class** $\mathcal H_{\mathcal B} := \{f : f(x) = Bx \text{ for some } B\in\mathcal B\}$ for $\mathcal B\subseteq\mathbb R^{d\times p}$.
--
--   Theorem 6 bounds the multivariate Rademacher complexity of $\mathcal H_{\mathcal B}$ when $\mathcal B$ lies in a level set of a function that is strongly convex with respect to the dual norm.
--
--   **Formalization Note** Signs are encoded by `Bool` (`true ↦ +1`, `false ↦ −1`). The prediction $Bx$ is represented as the continuous linear functional $c\mapsto c^\top(Bx)$ on the Euclidean space $\mathbb R^d$, so that the published multivariate Rademacher complexity of `SPOBounds.Margin.Rademacher` applies to $\mathcal H_{\mathcal B}$ without change.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 21, §4.4 (H_B and the matrix norms of Theorem 6); p. 34, Appendix C.2 (trace pairing)

import Mathlib

namespace SPOBounds.Natarajan.Supplement

/-- The trace pairing `⟨B, A⟩ = ∑_{i,j} B_{ij} A_{ij} = Tr(B Aᵀ)` on `d × p` real matrices
(arXiv:1905.11488v3, Appendix C.2, p. 34). -/
def matInner {d p : ℕ} (B A : Matrix (Fin d) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, B i j * A i j

/-- `N` is a norm on `ℝ^{d×p}`: a seminorm that vanishes only at the zero matrix (§4.4, p. 21:
"in Theorem 6 only we use `‖·‖` … to refer to a norm … on the space of matrices"). -/
def IsMatrixNorm {d p : ℕ} (N : Seminorm ℝ (Matrix (Fin d) (Fin p) ℝ)) : Prop :=
  ∀ A : Matrix (Fin d) (Fin p) ℝ, N A = 0 → A = 0

/-- The dual norm `‖A‖_* = sup {⟨B, A⟩ : ‖B‖ ≤ 1}` of a matrix norm `N` with respect to the trace
pairing (§4.4, p. 21, and p. 34). For a norm on the finite-dimensional space `ℝ^{d×p}` the unit
ball is compact, so the supremum is attained and finite. -/
noncomputable def dualNorm {d p : ℕ} (N : Seminorm ℝ (Matrix (Fin d) (Fin p) ℝ))
    (A : Matrix (Fin d) (Fin p) ℝ) : ℝ :=
  sSup ((fun B => matInner B A) '' {B | N B ≤ 1})

/-- `F` is `α`-strongly convex on `𝒮` with respect to the function `M` (used with `M = ‖·‖_*`):
for all `A, B ∈ 𝒮` and `t ∈ [0, 1]`,
`F(tA + (1−t)B) ≤ t F(A) + (1−t) F(B) − (α/2) t (1−t) M(A − B)²`
(the definition of Kakade, Sridharan and Tewari (2008) used in Theorem 6). -/
def StronglyConvexWrt {d p : ℕ} (M : Matrix (Fin d) (Fin p) ℝ → ℝ)
    (𝒮 : Set (Matrix (Fin d) (Fin p) ℝ)) (α : ℝ) (F : Matrix (Fin d) (Fin p) ℝ → ℝ) : Prop :=
  ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    F (t • A + (1 - t) • B) ≤ t * F A + (1 - t) * F B - α / 2 * t * (1 - t) * M (A - B) ^ 2

/-- The `d × p` outer product `σ xᵀ` of the sign vector `σ ∈ {±1}^d` encoded by
`b : Fin d → Bool` (`true ↦ +1`, `false ↦ −1`) and the feature `x ∈ ℝ^p`. -/
def signOuter {d p : ℕ} (b : Fin d → Bool) (x : EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin d) (Fin p) ℝ :=
  Matrix.of fun i j => (if b i then (1 : ℝ) else -1) * x j

/-- The prediction of the linear model `x ↦ Bx`, as a cost functional on `ℝ^d`:
`c ↦ cᵀ(Bx) = ⟪Bx, c⟫`. Costs and predictions are continuous linear functionals on the Euclidean
space `ℝ^d`, as in the published `SPOBounds.Margin` model, so `σᵀ f(x)` is `linPred B x σ`. -/
noncomputable def linPred {d p : ℕ} (B : Matrix (Fin d) (Fin p) ℝ)
    (x : EuclideanSpace ℝ (Fin p)) : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) :=
  innerSL ℝ (WithLp.toLp 2 (B.mulVec (WithLp.ofLp x)))

/-- The constrained linear class `𝓗_ℬ = {f : f(x) = Bx for some B ∈ ℬ}` (§4.4, p. 21). -/
def linearClass {d p : ℕ} (ℬ : Set (Matrix (Fin d) (Fin p) ℝ)) :
    Set (EuclideanSpace ℝ (Fin p) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :=
  {f | ∃ B ∈ ℬ, f = linPred B}

end SPOBounds.Natarajan.Supplement


