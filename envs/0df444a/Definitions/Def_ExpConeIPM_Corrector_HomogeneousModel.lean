-- Prove2me | Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel
-- name    : ExpConeIPM_Corrector_HomogeneousModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:48.403746+00:00
-- url     : https://prove2.me/theorems/9ca66412-38fc-43f9-baf4-e39deefd940e
-- title:
--   The homogeneous model (3): $K = \hat K \times \mathbb R_+$, $F = \hat F - \log\tau$, $\vartheta = \hat\vartheta + 1$, the residual $G(z)$, $\operatorname{int}(D)$ and $\mu$
-- statement:
--   This file fixes the homogeneous model of Dahl and Andersen's primal-dual interior-point method for nonsymmetric cones.
--
--   Let $A\colon\mathbb R^n\to\mathbb R^m$ be linear, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and let $\hat K\subseteq\mathbb R^n$ be a proper cone with a $\hat\vartheta$-logarithmically homogeneous self-concordant barrier $\hat F$. The conic pair is (P) minimize $\langle c,\hat x\rangle$ subject to $A\hat x=b$, $\hat x\in\hat K$, and (D) maximize $\langle b,y\rangle$ subject to $c-A^Ty=\hat s$, $\hat s\in\hat K^*$.
--
--   The model augments the variables by a homogenizing pair $\tau,\kappa\ge0$:
--   $$x=(\hat x,\tau)\in\mathbb R^{n+1},\qquad s=(\hat s,\kappa)\in\mathbb R^{n+1},\qquad K:=\hat K\times\mathbb R_+,\qquad F(x):=\hat F(\hat x)-\log\tau,\qquad \vartheta:=\hat\vartheta+1 .$$
--   With $z:=(x,s,y)$ the **residual** of the homogeneous self-dual embedding is
--   $$G(z):=\begin{bmatrix}0&A&-b\\-A^T&0&c\\b^T&-c^T&0\end{bmatrix}\begin{bmatrix}y\\\hat x\\\tau\end{bmatrix}-\begin{bmatrix}0\\\hat s\\\kappa\end{bmatrix}=\begin{bmatrix}A\hat x-b\tau\\-A^Ty+c\tau-\hat s\\b^Ty-c^T\hat x-\kappa\end{bmatrix}\in\mathbb R^m\times\mathbb R^n\times\mathbb R ,$$
--   and the KKT conditions read $G(z)=0$, $z\in D:=K\times K^*\times\mathbb R^m$. An **iterate** is a point $z\in\operatorname{int}(D)$, that is, $x\in\operatorname{int}K$ and $s\in\operatorname{int}K^*$. Its **centrality measure** is $\mu:=\langle x,s\rangle/\vartheta$, where $\langle x,s\rangle=\langle\hat x,\hat s\rangle+\tau\kappa$.
--
--   $G$ is linear in $z$, and the same map is applied to search directions $\Delta z=(\Delta x,\Delta s,\Delta y)$. The middle block matrix is skew-symmetric. These objects are the setting of Lemmas 2–4.
--
--   **Formalization Note** Vectors in $\mathbb R^{n+1}$ are `EuclideanSpace ℝ (Fin (n + 1))`; the paper's $\hat x$ is the first $n$ coordinates (`hatPart`, indices `Fin.castSucc i`), and $\tau$ (resp. $\kappa$) is the last coordinate `Fin.last n` (`lastCoord`). $A^T$ is the Hilbert adjoint of `A`. The paper's product $K_1\times\dots\times K_k$ with the sum barrier is represented by a single proper cone $\hat K$ with one barrier $\hat F$; a product of proper cones with the sum barrier is such a cone (p. 345), so this covers the paper's case. The barrier `augBarrier` is a function on all of $\mathbb R^{n+1}$ and is only meaningful on $\operatorname{int}K$, where $\tau>0$. The cone, the barrier and the dual cone are the published `SelfScaledIPM.ShortStep` and `ConvexOptimization.dualCone` notions.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), pp. 344–349, (P), (D), (3), G(z) and D (p. 348), μ (p. 349)

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting

open scoped InnerProductSpace

namespace ExpConeIPM.Corrector

/-! # The homogeneous model (3) of Dahl–Andersen (Math. Program. 194 (2022), pp. 347–349)

A single proper cone `K̂ ⊆ ℝⁿ` with a `ϑ̂`-LHSCB `F̂` stands for the paper's product
`K₁ × ⋯ × K_k` with the sum barrier. The augmented variables `x = (x̂, τ)` and `s = (ŝ, κ)` live
in `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))`: the paper's coordinates of `x̂` are the indices
`Fin.castSucc i`, `i : Fin n`, and the last coordinate `Fin.last n` holds `τ` (resp. `κ`). -/

/-- The cone block `x̂ ∈ ℝⁿ` of an augmented vector `x = (x̂, τ) ∈ ℝⁿ⁺¹` (its first `n`
coordinates). -/
def hatPart {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => x (Fin.castSucc i))

/-- The homogenizing coordinate `τ` (for `x`) or `κ` (for `s`): the last coordinate of an
augmented vector in `ℝⁿ⁺¹`. -/
def lastCoord {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  x (Fin.last n)

/-- The augmented cone `K := K̂ × ℝ₊` (p. 347, `K_{k+1} := ℝ₊`): `x = (x̂, τ)` with `x̂ ∈ K̂` and
`τ ≥ 0`. -/
def augCone {n : ℕ} (Khat : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | hatPart x ∈ Khat ∧ 0 ≤ lastCoord x}

/-- The augmented barrier `F(x) := F̂(x̂) − log τ` (pp. 347–348, `F_{k+1}(x_{k+1}) := −log x_{k+1}`).
Only evaluated on `int K`, where `τ > 0`. -/
noncomputable def augBarrier {n : ℕ} (Fhat : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
  fun x => Fhat (hatPart x) - Real.log (lastCoord x)

/-- The residual map `G` of the homogeneous model (p. 348):
`G(z) = [[0, A, −b], [−Aᵀ, 0, c], [bᵀ, −cᵀ, 0]] (y, x̂, τ) − (0, ŝ, κ)
      = (A x̂ − b τ, −Aᵀ y + c τ − ŝ, bᵀ y − cᵀ x̂ − κ) ∈ ℝᵐ × ℝⁿ × ℝ`
for `z = (x, s, y)`, `x = (x̂, τ)`, `s = (ŝ, κ)`. `Aᵀ` is the adjoint of `A`. `G` is linear in `z`
and is applied unchanged to directions `Δz = (Δx, Δs, Δy)`. -/
noncomputable def residual {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × ℝ :=
  (A (hatPart x) - lastCoord x • b,
   -(ContinuousLinearMap.adjoint A y) + lastCoord x • c - hatPart s,
   ⟪b, y⟫_ℝ - ⟪c, hatPart x⟫_ℝ - lastCoord s)

/-- An iterate `z = (x, s, y) ∈ int(D)`, `D := K × K* × ℝᵐ` (p. 348, p. 350): `x ∈ int K` and
`s ∈ int K*` for the augmented cone `K = K̂ × ℝ₊` (`y ∈ ℝᵐ` is free). -/
def IsInteriorIterate {n : ℕ} (Khat : Set (EuclideanSpace ℝ (Fin n)))
    (x s : EuclideanSpace ℝ (Fin (n + 1))) : Prop :=
  x ∈ interior (augCone Khat) ∧ s ∈ interior (ConvexOptimization.dualCone (augCone Khat))

/-- The complexity `ϑ = ϑ̂ + 1` of the augmented barrier (p. 347, `ϑ_{k+1} = 1`; p. 348). -/
def augParam (ϑhat : ℝ) : ℝ :=
  ϑhat + 1

/-- The centrality measure `μ := ⟨x, s⟩ / ϑ` of an iterate (p. 349), with `ϑ = ϑ̂ + 1`; the inner
product includes the `τκ` term. -/
noncomputable def mu (ϑhat : ℝ) {n : ℕ} (x s : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  ⟪x, s⟫_ℝ / augParam ϑhat

end ExpConeIPM.Corrector


