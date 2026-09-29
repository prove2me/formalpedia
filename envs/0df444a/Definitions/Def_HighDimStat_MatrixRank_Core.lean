-- Prove2me | Definitions.Def_HighDimStat_MatrixRank_Core
-- name    : HighDimStat_MatrixRank_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:18:32.089733+00:00
-- url     : https://prove2.me/theorems/a0969b48-cb1f-40f4-b4f5-1720c02243b8
-- title:
--   Matrix regression objects — nuclear/Frobenius/operator norms, observation operator, RSC
-- statement:
--   This file collects Chapter 10's core vocabulary for nuclear-norm-regularized matrix
--   regression, restating locally (per this chunk's convention: never import another chunk's
--   draft) the instantiation of chunk `09-decomposability`'s framework needed for Propositions
--   10.6 and 10.7.
--
--   - **`traceInner A B`**: the trace inner product $\langle\!\langle A,B\rangle\!\rangle :=
--     \mathrm{trace}(A^TB) = \sum_{j_1,j_2}A_{j_1j_2}B_{j_1j_2}$ on $\mathbb R^{d_1\times d_2}$
--     (Eq. 10.1).
--   - **`frobeniusNorm A`**: the Frobenius norm $\|\!|A|\!\|_F := \sqrt{\sum_{j_1,j_2}(A_{j_1j_2})^2}$.
--   - **`opNorm A`**: the $\ell_2$-operator (spectral) norm $\|\!|A|\!\|_2 :=
--     \sup_{\|v\|_2=1}\|Av\|_2$ of a (possibly rectangular) matrix — the dual norm of the
--     nuclear norm (Table 9.1).
--   - **`singularValues Θ`**: the singular values of $\Theta$, indexed by `Fin d2`, given by
--     the square roots of the eigenvalues of the Gram matrix $\Theta^T\Theta$, in decreasing
--     order.
--   - **`nuclearNorm Θ`**: $\|\!|\Theta|\!\|_{\mathrm{nuc}} := \sum_j\sigma_j(\Theta)$ (Eq. 10.5).
--   - **`tailSingularSum Θ r`**: $\sum_{j=r+1}^{d'}\sigma_j(\Theta)$, the singular-value mass
--     of $\Theta$ beyond the top $r$.
--   - **`observationOp Xs Θ`** / **`observationOpAdjoint Xs u`**: the observation operator
--     $\mathcal X_n(\Theta) := (\langle\!\langle X_i,\Theta\rangle\!\rangle)_{i=1}^n$ and its
--     adjoint $\mathcal X_n^*(u) := \sum_iu_iX_i$ (Eqs. 10.2-10.3, p. 312).
--   - **`RSCNuclear Xs κ c0`**: the restricted strong convexity condition (10.17):
--     $\|\mathcal X_n(\Delta)\|_2^2/(2n) \ge \kappa/2\|\!|\Delta|\!\|_F^2 -
--     c_0\frac{d_1+d_2}{n}\|\!|\Delta|\!\|_{\mathrm{nuc}}^2$ for all $\Delta$.
--   - **`DualCurvatureNuclear Xs κ τn`**: the $\Phi^*$-curvature condition (10.20):
--     $\|\!|\frac1n\mathcal X_n^*\mathcal X_n(\Delta)|\!\|_2 \ge \kappa\|\!|\Delta|\!\|_2 -
--     \tau_n\|\!|\Delta|\!\|_{\mathrm{nuc}}$ for all $\Delta$.
--   - **`IsNuclearNormLSSolution Xs y λn Θ̂`**: $\hat\Theta$ solves the nuclear-norm-regularized
--     least-squares program (10.16).
--
--   **Formalization Note** `singularValues` uses `Θᵀ Θ` (a `Fin d2 × Fin d2` Gram matrix)
--   regardless of whether $d_1\le d_2$ or $d_1>d_2$; when $d_2>d'=\min(d_1,d_2)$, the indices
--   beyond $d'$ carry eigenvalue (hence singular value) exactly zero, so `tailSingularSum`'s
--   sum over `Fin d2` agrees numerically with the book's own sum up to $d'$ for every `r`.
--   Unlike chunk `09-decomposability`'s abstract `Ψ(·)`/`errorCone`/`epsilonSq` framework
--   (parameterized by an arbitrary subspace pair $(\mathcal M,\bar{\mathcal M})$), Propositions
--   10.6 and 10.7's own printed *statements* never mention the subspace pair
--   $(\mathcal M(U_r,V_r),\bar{\mathcal M}(U_r,V_r))$ directly (only their *proofs*, which
--   instantiate chunk `09`'s Theorem 9.19/9.24 against it) — so this file does not construct
--   those subspaces explicitly; the two draft theorems below are stated exactly at the level
--   of generality the book's own numbered statements use.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, pp. 312-313, 318, 320 (PDF pp. 332-333, 338, 340), Eqs. (10.1)-(10.3), (10.5), (10.17), (10.20)

import Mathlib

namespace HighDimStat.MatrixRank

/-- The trace inner product `⟨⟨A, B⟩⟩ := trace(Aᵀ B) = Σⱼ₁ⱼ₂ Aⱼ₁ⱼ₂ Bⱼ₁ⱼ₂` on the matrix space
`ℝ^{d1×d2}` (Eq. (10.1), p. 312). -/
def traceInner {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The Frobenius norm `|||A|||_F := sqrt(Σⱼ₁ⱼ₂ (Aⱼ₁ⱼ₂)²)` induced by the trace inner product
(p. 312), the Euclidean norm on the vectorized matrix. -/
noncomputable def frobeniusNorm {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

/-- The `ℓ2`-operator (spectral) norm `|||A|||₂ := sup_{‖v‖₂=1} ‖Av‖₂` of a (possibly
rectangular) real matrix, the dual norm of the nuclear norm (Table 9.1). Realized via the
Rayleigh-type variational characterization, matching the pattern of `HighDimStat.Pca.opNormSymm`
for the symmetric case (chunk `08-pca`), generalized here to a rectangular domain/codomain. -/
noncomputable def opNorm {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  ⨆ v : {v : Fin d2 → ℝ // ∑ j, (v j) ^ 2 = 1}, Real.sqrt (∑ i, (A.mulVec v.1 i) ^ 2)

/-- The singular values of a real matrix `Θ : ℝ^{d1×d2}`, indexed by `Fin d2` and given (in
decreasing order) by the square roots of the eigenvalues of the positive semidefinite Gram
matrix `Θᵀ Θ`. Indexed through `eigenvalues₀` directly via `finCongr (Fintype.card_fin d2)`
rather than Mathlib's `Matrix.IsHermitian.eigenvalues` (which reindexes `eigenvalues₀` along
`Fintype.equivOfCardEq`, a classically-chosen bijection Mathlib proves no order relationship
for): `finCongr (Fintype.card_fin d2) : Fin (Fintype.card (Fin d2)) ≃ Fin d2` is definitionally
`Fin.cast` under the proof `Fintype.card_fin d2 : Fintype.card (Fin d2) = d2`, hence trivially
order-preserving, so the antitonicity of `eigenvalues₀`
(`Matrix.IsHermitian.eigenvalues₀_antitone`) transfers to `singularValues` by construction. When
`d2 > d1`, the indices beyond `d' := min d1 d2` carry the (correct) value zero, so any sum over a
suffix of indices agrees with the book's own sum over `j = r+1, ..., d'`. -/
noncomputable def singularValues {d1 d2 : ℕ} (Θ : Matrix (Fin d1) (Fin d2) ℝ) : Fin d2 → ℝ :=
  fun j => Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self Θ).1.eigenvalues₀
    ((finCongr (Fintype.card_fin d2)).symm j))

/-- The nuclear norm `|||Θ|||_nuc := Σⱼ σⱼ(Θ)` (Eq. (10.5), p. 313), the sum of the singular
values of `Θ`. -/
noncomputable def nuclearNorm {d1 d2 : ℕ} (Θ : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  ∑ j, singularValues Θ j

/-- The tail sum `Σ_{j=r+1}^{d'} σⱼ(Θ)` of singular values of `Θ` beyond the top `r`, as used
in Proposition 10.6's approximation-error term: the sum of `singularValues Θ j` over indices
`j` (0-indexed) with `r ≤ j`, i.e. the book's 1-indexed `j = r+1, ..., d'`. -/
noncomputable def tailSingularSum {d1 d2 : ℕ} (Θ : Matrix (Fin d1) (Fin d2) ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ (Finset.univ : Finset (Fin d2)).filter (fun j : Fin d2 => r ≤ (j : ℕ)), singularValues Θ j

/-- The observation operator `Xn(Θ) := (⟨⟨Xᵢ, Θ⟩⟩)ᵢ` of Eq. (10.2)-(10.3), p. 312: given the
design matrices `Xs : Fin n → ℝ^{d1×d2}`, `Xn Xs Θ` is the `n`-vector of trace-inner-product
observations. -/
def observationOp {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (Θ : Matrix (Fin d1) (Fin d2) ℝ) : Fin n → ℝ :=
  fun i => traceInner (Xs i) Θ

/-- The adjoint observation operator `X*ₙ(u) := Σᵢ uᵢXᵢ` of p. 312: the linear map from `ℝⁿ`
to `ℝ^{d1×d2}` adjoint to `observationOp`. -/
def observationOpAdjoint {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (u : Fin n → ℝ) : Matrix (Fin d1) (Fin d2) ℝ :=
  ∑ i, u i • Xs i

/-- The restricted strong convexity condition (10.17), p. 318, for the least-squares cost
under nuclear norm regularization, with curvature `κ` and tolerance parameter `c0`:
`‖Xn(Δ)‖₂²/(2n) ≥ κ/2 |||Δ|||_F² − c0(d1+d2)/n |||Δ|||_nuc²` for all `Δ`. -/
def RSCNuclear {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (κ c0 : ℝ) : Prop :=
  ∀ Δ : Matrix (Fin d1) (Fin d2) ℝ,
    (∑ i, (observationOp Xs Δ i) ^ 2) / (2 * (n : ℝ)) ≥
      κ / 2 * (frobeniusNorm Δ) ^ 2 - c0 * ((d1 : ℝ) + d2) / (n : ℝ) * (nuclearNorm Δ) ^ 2

/-- The `Φ*`-curvature condition (10.20), p. 320, with curvature `κ` and tolerance `τn`, for
the least-squares cost under nuclear norm regularization (dual norm = operator norm):
`|||(1/n) X*ₙXn(Δ)|||₂ ≥ κ|||Δ|||₂ − τn|||Δ|||_nuc` for all `Δ`. -/
def DualCurvatureNuclear {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (κ τn : ℝ) : Prop :=
  ∀ Δ : Matrix (Fin d1) (Fin d2) ℝ,
    opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs (observationOp Xs Δ)) ≥
      κ * opNorm Δ - τn * nuclearNorm Δ

/-- `Θhat` solves the nuclear-norm regularized least-squares program (10.16), p. 319:
`argmin_Θ (1/2n)‖y − Xn(Θ)‖₂² + λₙ|||Θ|||_nuc`. -/
def IsNuclearNormLSSolution {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (y : Fin n → ℝ) (lamN : ℝ) (Θhat : Matrix (Fin d1) (Fin d2) ℝ) : Prop :=
  ∀ Θ : Matrix (Fin d1) (Fin d2) ℝ,
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - observationOp Xs Θhat i) ^ 2) + lamN * nuclearNorm Θhat ≤
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - observationOp Xs Θ i) ^ 2) + lamN * nuclearNorm Θ

end HighDimStat.MatrixRank


