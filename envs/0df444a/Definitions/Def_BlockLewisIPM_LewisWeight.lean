-- Prove2me | Definitions.Def_BlockLewisIPM_LewisWeight
-- name    : BlockLewisIPM_LewisWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:19.227586+00:00
-- url     : https://prove2.me/theorems/cfbd5ddb-75c0-4ae2-ac16-455f25710954
-- title:
--   Smoothed preconditioners and regularized block Lewis weights
-- statement:
--   Fix a barrier $\phi$ on $K\subset\mathbb R^k$, a smoothing scale $\sigma>0$ and a positive definite $M$. The **smoothed preconditioner** of Definition 11 is
--
--   $$\widetilde C(y,M)=\widetilde S(y,M)^{1/2},\qquad \widetilde S(y,M)=\mathbb E_{u\sim\mathrm{Unif}(B_k)}\Bigl[\nabla^2\phi\bigl(y+\sigma M^{-1/2}u\bigr)^{-1}\Bigr].$$
--
--   The **$p$-th order regularized block Lewis weight** $w_p(B)\in\mathbb R^m_{>0}$ of a matrix $B\in\mathbb R^{n\times d}$, with regularization $v\in\mathbb R^m_{>0}$, is the solution of
--
--   $$w=\operatorname{tr}_G\bigl(P(W^{1/2-1/p}B)\bigr)+v,\qquad W=\operatorname{diag}_G(w).$$
--
--   For a block diagonal $C$, $w(C)=w_p(CA)$ with $v=\frac dm\mathbf 1_m$, and for $x\in K$,
--
--   $$\tau(x)=w\bigl(\widetilde C(x,\nabla^2\Phi(x))\bigr).$$
--
--   These weights define the weighted central path followed by the method.
--
--   **Formalization Note** Unif$(B_k)$ is the published `RegretBandits.Nonlinear.uniformBall`. The expectation is entrywise. The Lewis weight is chosen among the solutions and is $0$ if there is none; Lemma 57 gives a unique solution for $p\in(0,2)$ and full column rank, and $p=2$ makes the system explicit, so statements assume full column rank.
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Definitions 11–13, p.13; Lemma 57, p.58

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_BlockLewisIPM_Instance

namespace BlockLewisIPM

/-!
# Smoothed preconditioners and regularized block Lewis weights

Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization over
Product-Domain* (manuscript, sha256 66072000…), Definitions 11–13, p.13.

**Formalization Note.**
* `Unif(B_k)` is the published `RegretBandits.Nonlinear.uniformBall`: Lebesgue measure on the closed
  unit ball, normalized.
* The matrix expectation of Definition 11 is entrywise. A Bochner integral of a non-integrable
  entry is `0`, so statements about `S̃` carry well-definedness (Lemma 23's first conclusion).
* `C̃(x, M)` is the block diagonal matrix of the block roots `C̃_i`, which is `S̃(x, M)^{1/2}` when each
  `S̃_i` is positive definite.
* Definition 12 prints "the solution" of the system. Lemma 57, p.58, gives existence and uniqueness
  for `p ∈ (0, 2)` and full column rank (and `p = 2` makes the system explicit). `lewisWeight` picks a
  solution by choice, and is `0` when none exists, so the equation of Definition 12 holds for it when
  a solution exists; statements about it assume full column rank (reading R10).
* `W^{1/2-1/p}` is the real power of the positive entries of `w`.
-/

open Matrix MeasureTheory

/-- `S̃(y, M) = E_{u∼Unif(B_k)} [∇²ϕ(y + σ M^{-1/2} u)⁻¹]`, entrywise (Definition 11, p.13, and
Lemma 23, p.18). -/
noncomputable def smoothedS {k : ℕ} (φ : Eu k → ℝ) (σ : ℝ) (M : Matrix (Fin k) (Fin k) ℝ)
    (y : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a b =>
    ∫ u : Eu k, (hessMat φ (y + σ • (matInvSqrt M *ᵥ (u : Fin k → ℝ))))⁻¹ a b
      ∂(RegretBandits.Nonlinear.uniformBall k)

/-- `C̃(y, M) = S̃(y, M)^{1/2}` (Definition 11, p.13). -/
noncomputable def smoothedC {k : ℕ} (φ : Eu k → ℝ) (σ : ℝ) (M : Matrix (Fin k) (Fin k) ℝ)
    (y : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  matSqrt (smoothedS φ σ M y)

/-- The derivative `DC̃(y, M)[h]`, entrywise, of the map `y ↦ C̃(y, M)` (Lemma 23, p.18). -/
noncomputable def dSmoothedC {k : ℕ} (φ : Eu k → ℝ) (σ : ℝ) (M : Matrix (Fin k) (Fin k) ℝ)
    (y : Fin k → ℝ) (h : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fderiv ℝ (fun y' : Eu k => (smoothedC φ σ M y' : Fin k → Fin k → ℝ))
    (WithLp.toLp 2 y) (WithLp.toLp 2 h))

section Lewis

variable {ι : Type} [Fintype ι] [DecidableEq ι] {dim : ι → ℕ} {d : ℕ}

/-- `w` solves the system of Definition 12, p.13: `w > 0` and
`w = tr_G(P(W^{1/2-1/p} B)) + v` with `W = diag_G(w)`. -/
def IsLewisWeight (p : ℝ) (v : ι → ℝ) (B : Matrix (BIdx dim) (Fin d) ℝ) (w : ι → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧
    ∀ i, w i = blockTrace (projMat (diagG (dim := dim) (fun i => w i ^ ((1 : ℝ) / 2 - 1 / p)) * B)) i + v i

open Classical in
/-- The `p`-th order regularized block Lewis weight `w_p(B)` with regularization `v` (Definition 12,
p.13). -/
noncomputable def lewisWeight (p : ℝ) (v : ι → ℝ) (B : Matrix (BIdx dim) (Fin d) ℝ) : ι → ℝ :=
  if h : ∃ w, IsLewisWeight p v B w then h.choose else 0

/-- `w(C) = w_p(CA)` with regularization `v = (d/m) 1_m` (Definition 13, p.13). -/
noncomputable def lewisC (p : ℝ) (A : Matrix (BIdx dim) (Fin d) ℝ)
    (C : Matrix (BIdx dim) (BIdx dim) ℝ) : ι → ℝ :=
  lewisWeight p (fun _ => (d : ℝ) / Fintype.card ι) (C * A)

end Lewis

namespace Instance

variable {ι : Type} (I : Instance ι)

/-- `∇ϕ_i(x_i)`. -/
noncomputable def grad (x : I.Vec) (i : ι) : Fin (I.dim i) → ℝ :=
  gradVec (I.φ i) (block x i)

/-- `∇²ϕ_i(x_i)`. -/
noncomputable def hess (x : I.Vec) (i : ι) : Matrix (Fin (I.dim i)) (Fin (I.dim i)) ℝ :=
  hessMat (I.φ i) (block x i)

/-- `C̃_i(x_i, ∇²ϕ_i(x_i))`, the block of `C̃(x, ∇²Φ(x))`. -/
noncomputable def cBlock (σ : ℝ) (x : I.Vec) (i : ι) : Matrix (Fin (I.dim i)) (Fin (I.dim i)) ℝ :=
  smoothedC (I.φ i) σ (I.hess x i) (block x i)

variable [DecidableEq ι]

/-- `∇²Φ(x)⁻¹`, block diagonal. -/
noncomputable def hessInv (x : I.Vec) : Matrix (BIdx I.dim) (BIdx I.dim) ℝ :=
  Matrix.blockDiagonal' fun i => (I.hess x i)⁻¹

/-- `∇²Φ(x)^{1/2}`, block diagonal. -/
noncomputable def hessSqrt (x : I.Vec) : Matrix (BIdx I.dim) (BIdx I.dim) ℝ :=
  Matrix.blockDiagonal' fun i => matSqrt (I.hess x i)

/-- `∇²Φ(x)^{-1/2}`, block diagonal. -/
noncomputable def hessInvSqrt (x : I.Vec) : Matrix (BIdx I.dim) (BIdx I.dim) ℝ :=
  Matrix.blockDiagonal' fun i => matInvSqrt (I.hess x i)

/-- `C̃(x, ∇²Φ(x))`, block diagonal. -/
noncomputable def cTilde (σ : ℝ) (x : I.Vec) : Matrix (BIdx I.dim) (BIdx I.dim) ℝ :=
  Matrix.blockDiagonal' (I.cBlock σ x)

variable [Fintype ι]

/-- `τ(x) = w(C̃(x, ∇²Φ(x)))` (Definition 13, p.13), for the exponent `p` and smoothing scale `σ`. -/
noncomputable def tauAt (p σ : ℝ) (x : I.Vec) : ι → ℝ :=
  lewisC p I.A (I.cTilde σ x)

end Instance

end BlockLewisIPM


