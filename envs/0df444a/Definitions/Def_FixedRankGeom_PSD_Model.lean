-- Prove2me | Definitions.Def_FixedRankGeom_PSD_Model
-- name    : FixedRankGeom_PSD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:51.613991+00:00
-- url     : https://prove2.me/theorems/4baac06f-2922-42a3-8ab9-fa61f1929435
-- title:
--   §2, §4.1, §4.2.1, App. A — fixed-rank PSD matrices, the total space ℝ_*^{p×r} with metric tr(W_Y ηᵀθ), vertical/horizontal spaces, Riemannian gradients and Hessians, L(θ) = Yθᵀ + θYᵀ, k-th eigenvalues
-- statement:
--   This file sets up the two geometries on fixed-rank positive semidefinite matrices compared by Luo, Li and Zhang, and the spectral notions used to compare them.
--
--   **Ambient spaces.** For $a,b\in\mathbb N$, $\mathbb R^{a\times b}$ carries the Frobenius inner product $\langle A,B\rangle=\operatorname{tr}(A^\top B)$. Fix $0<r\le p$.
--
--   **Embedded geometry.** The set of rank-$r$ PSD matrices is
--   $$\mathcal M_{r+}=\{X\in\mathbb S^{p\times p}: X\succeq 0,\ \operatorname{rank}X=r\}.$$
--   Its tangent space $T_X\mathcal M^e_{r+}$ is the span of the tangent cone of $\mathcal M_{r+}$ at $X$, and the Riemannian gradient of $f:\mathbb R^{p\times p}\to\mathbb R$ for the induced metric is $\operatorname{grad} f(X)=P_{T_X\mathcal M^e_{r+}}(\nabla f(X))$ (both from published definitions). The Riemannian Hessian quadratic form at $X$ is characterised along curves: a function $q$ is *the Hessian quadratic form of $f$ at $X$* if for every $\xi\in T_X\mathcal M^e_{r+}$ and every $C^1$ curve $c$ with $c(0)=X$, $c'(0)=\xi$ and $c(t)\in\mathcal M_{r+}$ for $t$ near $0$,
--   $$q(\xi)=\frac{d}{dt}\Big|_{t=0}\big\langle \operatorname{grad} f(c(t)),\xi\big\rangle .$$
--   This is $\langle P_{T_X}(\mathrm D\operatorname{grad} f(X)[\xi]),\xi\rangle=\operatorname{Hess} f(X)[\xi,\xi]$, by definition (3) of the Hessian and the formula $\bar\nabla_\xi\eta=P_{T_X}(\bar\nabla'_\xi\eta)$ for the connection of an embedded submanifold.
--
--   **Quotient geometry.** The total space is $\mathbb R_*^{p\times r}$, the $p\times r$ matrices of full column rank, with $X=YY^\top$ and the objective $\bar h_{r+}(Y)=f(YY^\top)$ of (18a). A weight $W:\mathbb R^{p\times r}\to\mathbb R^{r\times r}$ defines the metric
--   $$\bar g_Y(\eta,\theta)=\operatorname{tr}(W_Y\,\eta^\top\theta).$$
--   The vertical space is $\mathcal V_Y=\{Y\Omega:\Omega=-\Omega^\top\in\mathbb R^{r\times r}\}$ and the horizontal space $\mathcal H_Y$ is its $\bar g_Y$-orthogonal complement in $\mathbb R^{p\times r}$. $P^{\mathcal H}_Y(v)$ is the horizontal component of $v$ in $\mathcal V_Y\oplus\mathcal H_Y$. The total-space gradient of $\bar h$ is the vector $G$ with $\bar g_Y(G,\theta)=\langle\nabla\bar h(Y),\theta\rangle$ for all $\theta$, namely $G=\nabla\bar h(Y)W_Y^{-1}$, and the horizontal lift of the quotient gradient is $\overline{\operatorname{grad} h([Y])}=P^{\mathcal H}_Y(G)$, equation (4). The Hessian quadratic form of $\bar h$ in the total space is
--   $$\bar g_Y(\bar\nabla_\theta G,\theta)=\bar g_Y(\mathrm DG(Y)[\theta],\theta)+\tfrac12\,\mathrm D\big(Z\mapsto\bar g_Z(\theta,\theta)\big)(Y)[G],$$
--   which is the Koszul formula (71)–(72) for the Levi-Civita connection of $\bar g$ on an open subset of a vector space, with $\theta$ a constant field. On horizontal $\theta$ it equals the bilinear form $\overline{\operatorname{Hess} h([Y])}[\theta,\theta]$ of the horizontal lift of the quotient Hessian.
--
--   **Comparison map and spectra.** $\mathcal L^{r+}_Y(\theta)=Y\theta^\top+\theta Y^\top$. For a quadratic form $q$ on a subspace $V$ with inner product $g$, its $k$-th largest eigenvalue is the max–min value of Lemma 13,
--   $$\lambda_k=\max_{C\le V,\ \dim C=k}\ \min_{u\in C,\,u\ne0}\frac{q(u)}{g(u,u)}\qquad(1\le k\le\dim V).$$
--   A number $\mu$ is *sandwiched between* $a$ and $b$ if $\min(a,b)\le\mu\le\max(a,b)$. For a symmetric positive definite $r\times r$ matrix $A$, $\sigma_1(A)$ and $\sigma_r(A)$ are its largest and smallest Rayleigh quotients $v^\top Av/v^\top v$, i.e. its largest and smallest singular values.
--
--   These objects are the vocabulary of every statement in the mission: the gradients, Hessians and eigenvalues are defined intrinsically, so the paper's explicit formulas (19), (20) and (34) are theorems about them, not definitions.
--
--   **Formalization Note** $\mathbb R^{a\times b}$ is `EuclideanSpace ℝ (Fin a × Fin b)` with a matrix view `toMat`/`ofMat`; its inner product is the Frobenius one. The weight $W$ takes values in this Euclidean space, so that its derivative $\mathrm DW_Y$ is defined. The horizontal projection is chosen with `Classical.epsilon`; it is the unique decomposition when $W_Y$ is positive definite. The embedded Hessian is a predicate on $q$, not a function: it determines $q$ on $T_X\mathcal M^e_{r+}$ because derivatives are unique. The vertical space is defined by its first description in Lemma 4 (i), which is the tangent space of the fiber $\{YO: O\in\mathbb O_r\}$.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, pp. 5–7, 10–13, 17–18, 35–37, 54: §1.3, §2 (3), §2.1 (4)–(5), Lemma 1, §4.1, §4.2.1, Table 1, Remark 1, (18a), Proposition 2 (L^{r+}_Y), App. A (71)–(72), Lemma 13

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad

open scoped RealInnerProductSpace Matrix
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- `ℝ^{a×b}` with the Frobenius inner product `⟨A, B⟩ = tr(AᵀB)` (§1.3, p. 5; §4.1, p. 11): the
Euclidean space indexed by the entries `(i, j)`. -/
abbrev Mat (a b : ℕ) := EuclideanSpace ℝ (Fin a × Fin b)

/-- The matrix view of an element of `Mat a b`. -/
def toMat {a b : ℕ} (x : Mat a b) : Matrix (Fin a) (Fin b) ℝ := Matrix.of fun i j => x (i, j)

/-- The element of `Mat a b` with the given entries (inverse of `toMat`). -/
def ofMat {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) : Mat a b :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

@[simp] lemma toMat_add {a b : ℕ} (x y : Mat a b) : toMat (x + y) = toMat x + toMat y := by
  ext i j; simp [toMat]

@[simp] lemma toMat_smul {a b : ℕ} (c : ℝ) (x : Mat a b) : toMat (c • x) = c • toMat x := by
  ext i j; simp [toMat]

@[simp] lemma toMat_zero {a b : ℕ} : toMat (0 : Mat a b) = 0 := by
  ext i j; simp [toMat]

/-- `M_{r+} = {X ∈ S^{p×p} | rank(X) = r, X ⪰ 0}`, the `p × p` PSD matrices of rank `r` (p. 10).
`Matrix.PosSemidef` includes symmetry. -/
def psdRankSet (p r : ℕ) : Set (Mat p p) := {X | (toMat X).PosSemidef ∧ (toMat X).rank = r}

/-- `ℝ_*^{p×r}`, the real `p × r` matrices of full column rank (§4.2, p. 11). -/
def fullRankSet (p r : ℕ) : Set (Mat p r) := {Y | (toMat Y).rank = r}

/-- The factorization map `Y ↦ YYᵀ` (§4.2.1, p. 12). -/
def gram {p r : ℕ} (Y : Mat p r) : Mat p p := ofMat (toMat Y * (toMat Y)ᵀ)

/-- `h̄_{r+}(Y) := f(YYᵀ)`, the objective (18a) on the total space `ℝ_*^{p×r}` (p. 17). -/
def hbarOf {p r : ℕ} (f : Mat p p → ℝ) (Y : Mat p r) : ℝ := f (gram Y)

/-- The metric `ḡ^{r+}_Y(η, θ) = tr(W_Y ηᵀ θ)` on `T_Y ℝ_*^{p×r} = ℝ^{p×r}` (Table 1, p. 12; §4.2.1, p. 12).
The weight `W_Y` is the matrix `toMat (W Y)`; `W` takes values in `Mat r r` so that its derivative
`DW_Y` makes sense. -/
noncomputable def qmetric {p r : ℕ} (W : Mat p r → Mat r r) (Y η θ : Mat p r) : ℝ :=
  Matrix.trace (toMat (W Y) * (toMat η)ᵀ * toMat θ)

/-- The vertical space `V_Y M̄^{q1}_{r+} = {YΩ : Ω = −Ωᵀ ∈ ℝ^{r×r}}`, the tangent directions of the
fiber `[Y] = {YO : O ∈ O_r}` (§2.1, p. 7; Lemma 4 (i), first description, p. 13). -/
def verticalSpace {p r : ℕ} (Y : Mat p r) : Submodule ℝ (Mat p r) where
  carrier := {θ | ∃ Ω : Matrix (Fin r) (Fin r) ℝ, Ωᵀ = -Ω ∧ toMat θ = toMat Y * Ω}
  add_mem' := by
    rintro a b ⟨Ω₁, h₁, e₁⟩ ⟨Ω₂, h₂, e₂⟩
    refine ⟨Ω₁ + Ω₂, ?_, ?_⟩
    · rw [Matrix.transpose_add, h₁, h₂, neg_add]
    · rw [toMat_add, e₁, e₂, Matrix.mul_add]
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro c a ⟨Ω, h, e⟩
    refine ⟨c • Ω, ?_, ?_⟩
    · rw [Matrix.transpose_smul, h, smul_neg]
    · rw [toMat_smul, e, Matrix.mul_smul]

/-- The canonical horizontal space `H_Y M̄^{q1}_{r+}`: the `ḡ_Y`-orthogonal complement of the vertical
space in `T_Y ℝ_*^{p×r} = ℝ^{p×r}` (Lemma 1, p. 7). -/
def horizontalSpace {p r : ℕ} (W : Mat p r → Mat r r) (Y : Mat p r) : Submodule ℝ (Mat p r) where
  carrier := {θ | ∀ v ∈ verticalSpace Y, qmetric W Y v θ = 0}
  add_mem' := by
    intro a b ha hb v hv
    have h1 := ha v hv
    have h2 := hb v hv
    simp only [qmetric, toMat_add, Matrix.mul_add, Matrix.trace_add] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' := by
    intro v _
    simp [qmetric]
  smul_mem' := by
    intro c a ha v hv
    have h1 := ha v hv
    simp only [qmetric, toMat_smul, Matrix.mul_smul, Matrix.trace_smul] at h1 ⊢
    rw [h1, smul_zero]

/-- `P^H_Y(v)`: the horizontal component of `v` in the decomposition `T_Y = V_Y ⊕ H_Y` (§2.1, p. 7).
Chosen by `Classical.epsilon`; when `W_Y` is positive definite the decomposition exists and is unique. -/
noncomputable def horizontalPart {p r : ℕ} (W : Mat p r → Mat r r) (Y v : Mat p r) : Mat p r :=
  Classical.epsilon fun h => h ∈ horizontalSpace W Y ∧ v - h ∈ verticalSpace Y

/-- `grad h̄(Y)`, the Riemannian gradient of `h̄` on `ℝ_*^{p×r}` for the metric `ḡ`: the vector `G` with
`ḡ_Y(G, θ) = Dh̄(Y)[θ] = ⟨∇h̄(Y), θ⟩` for all `θ`, i.e. `G = ∇h̄(Y) W_Y^{-1}` (§2, p. 6; `W_Y` symmetric). -/
noncomputable def totalGrad {p r : ℕ} (W : Mat p r → Mat r r) (hbar : Mat p r → ℝ) (Y : Mat p r) :
    Mat p r :=
  ofMat (toMat (gradient hbar Y) * (toMat (W Y))⁻¹)

/-- The horizontal lift of the Riemannian gradient of the induced function `h([Y])` on the quotient,
`P^H_Y(grad h̄(Y))`, equation (4), p. 7. -/
noncomputable def quotGrad {p r : ℕ} (W : Mat p r → Mat r r) (hbar : Mat p r → ℝ) (Y : Mat p r) :
    Mat p r :=
  horizontalPart W Y (totalGrad W hbar Y)

/-- `ḡ_Y(∇̄_θ grad h̄, θ)`: the quadratic form of the Riemannian Hessian of `h̄` on the open set
`ℝ_*^{p×r}` for the metric `ḡ` (definition (3), p. 6). The Levi-Civita connection is given by the Koszul
formula (71) with the Lie bracket (72) (App. A, p. 35); taking `ξ = θ` a constant field and
`η = G = grad h̄` gives `2ḡ_Y(∇̄_θ G, θ) = 2ḡ_Y(DG(Y)[θ], θ) + Dḡ_·(θ, θ)(Y)[G]`. On a horizontal `θ` this
is the bilinear form of the horizontal lift of `Hess h([Y])` ((5), p. 7, with Lemma 12, p. 54). -/
noncomputable def totalHessQuad {p r : ℕ} (W : Mat p r → Mat r r) (hbar : Mat p r → ℝ)
    (Y θ : Mat p r) : ℝ :=
  qmetric W Y (fderiv ℝ (totalGrad W hbar) Y θ) θ
    + (1 / 2 : ℝ) * fderiv ℝ (fun Z => qmetric W Z θ θ) Y (totalGrad W hbar Y)

/-- `q` is the quadratic form of the Riemannian Hessian of `f` on the embedded set `M ⊆ E` (metric induced
by the inner product of `E`) at `X`: for every tangent vector `ξ ∈ T_X M` and every `C¹` curve `c` with
`c 0 = X`, `c'(0) = ξ` and `c t ∈ M` for `t` near `0`,
`q ξ = d/dt ⟨grad f(c t), ξ⟩ |_{t=0}`. This is `⟨P_{T_X M}(D grad f(X)[ξ]), ξ⟩ = Hess f(X)[ξ, ξ]` by (3) and
`∇̄_ξ η = P_{T_X M}(∇̄'_ξ η)` for embedded submanifolds (p. 6). -/
def IsEmbHessQuad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Set E) (f : E → ℝ) (X : E) (q : E → ℝ) : Prop :=
  ∀ ξ ∈ tangentSpace M X, ∀ c : ℝ → E, ContDiff ℝ 1 c → (∀ᶠ t in nhds (0 : ℝ), c t ∈ M) →
    c 0 = X → HasDerivAt c ξ 0 →
      HasDerivAt (fun t => ⟪ZORiem.RGD.rgrad M f (c t), ξ⟫) (q ξ) 0

/-- `L^{r+}_Y(θ) = Yθᵀ + θYᵀ` (Proposition 2, p. 18). -/
def Lmap {p r : ℕ} (Y θ : Mat p r) : Mat p p :=
  ofMat (toMat Y * (toMat θ)ᵀ + toMat θ * (toMat Y)ᵀ)

/-- `λ_k`, the `k`-th largest eigenvalue of the quadratic form `q` on the subspace `V` with respect to the
inner product `g`, as the max–min value of Lemma 13 (p. 54):
`λ_k = max_{C ≤ V, dim C = k} min_{u ∈ C, u ≠ 0} q(u)/g(u, u)`. Meaningful for `1 ≤ k ≤ dim V`. -/
noncomputable def kthEig {E : Type*} [AddCommGroup E] [Module ℝ E] (g : E → E → ℝ) (q : E → ℝ)
    (V : Submodule ℝ E) (k : ℕ) : ℝ :=
  ⨆ C : {C : Submodule ℝ E // C ≤ V ∧ Module.finrank ℝ C = k},
    ⨅ u : {u : E // u ∈ C.1 ∧ u ≠ 0}, q u / g u u

/-- "`μ` is sandwiched between `a` and `b`": `min(a, b) ≤ μ ≤ max(a, b)`. -/
def IsSandwiched (μ a b : ℝ) : Prop := min a b ≤ μ ∧ μ ≤ max a b

/-- `σ_1(A)` for a symmetric positive definite `r × r` matrix `A` (where singular values and eigenvalues
coincide): the largest Rayleigh quotient `max_{v ≠ 0} vᵀAv / vᵀv`. -/
noncomputable def sigmaMax {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ⨆ v : {v : Fin r → ℝ // v ≠ 0}, (v.1 ⬝ᵥ (A *ᵥ v.1)) / (v.1 ⬝ᵥ v.1)

/-- `σ_r(A)` for a symmetric positive definite `r × r` matrix `A`: the smallest Rayleigh quotient
`min_{v ≠ 0} vᵀAv / vᵀv`. -/
noncomputable def sigmaMin {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ⨅ v : {v : Fin r → ℝ // v ≠ 0}, (v.1 ⬝ᵥ (A *ᵥ v.1)) / (v.1 ⬝ᵥ v.1)

end FixedRankGeom.PSD


