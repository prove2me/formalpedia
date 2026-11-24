-- Prove2me | Definitions.Def_RobustSDP_FullPert_Supplement_StructuredNorm
-- name    : RobustSDP_FullPert_Supplement_StructuredNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:44:43.108517+00:00
-- url     : https://prove2.me/theorems/4d137fe8-4c27-4048-91f5-b839f50bd567
-- title:
--   §5.6, pp. 45–46 — structured norm perturbations: the set 𝒟, the scalings 𝒮, problem (30) and the SDP of Theorem 5.5
-- statement:
--   This entry fixes the objects of the structured robust norm-minimization problem (30) of El Ghaoui, Oustry and Lebret and the SDP of Theorem 5.5. Let $n \ge 1$, $N = 1 + 2 + \dots + n$, $H_0, \dots, H_m \in \mathbb{R}^{n\times n}$, $H(x) = H_0 + \sum_i x_i H_i$, $L \in \mathbb{R}^{n\times N}$, $R \in \mathbb{R}^{N\times n}$ and $\rho \in \mathbb{R}$. Matrix norms are spectral norms.
--
--   1. **Perturbation set.** $\mathcal{D} = \{\mathrm{diag}(\delta_1 I_1, \dots, \delta_n I_n) : \delta_i \in \mathbb{R}\}$, where $I_i$ is the $i\times i$ identity.
--
--   2. **Scaling set.** $\mathcal{S} = \{\mathrm{diag}(S_1,\dots,S_n) : S_i \in \mathbb{R}^{i\times i}\}$.
--
--   3. **Problem (30).** The worst-case objective at $x$ and the objective value are
--   $$\phi(x) = \max_{\Delta \in \mathcal{D},\ \|\Delta\| \le \rho} \|H(x) + L\Delta R\|, \qquad \inf_{x \in \mathbb{R}^m} \phi(x).$$
--
--   4. **The SDP of Theorem 5.5.** A tuple $(x, \lambda, S, G)$ is feasible when $S = S^T \in \mathcal{S}$, $G = -G^T \in \mathcal{S}$ and
--   $$\begin{bmatrix} \lambda I - LSL^T & H(x) & LG \\ H(x)^T & \lambda I & \rho R^T \\ G^T L^T & \rho R & S \end{bmatrix} \succ 0 .$$
--   The SDP value is the infimum of $\lambda$ over feasible tuples.
--
--   These objects are used by Theorem 5.5, which bounds the value of (30) by the SDP value.
--
--   **Formalization Note** The index set of the block structure is the dependent pair type $\Sigma\, i : \mathrm{Fin}\, n,\ \mathrm{Fin}(i+1)$; block-diagonal matrices are Mathlib's `blockDiagonal'`. The paper prints $\rho R$ in position (2,3) and $\rho R^T$ in position (3,2) of the block matrix. Since $R$ is $N \times n$ (it multiplies $L\Delta$ in $H_0 + L\Delta R$), those blocks have the right sizes only when transposed, so the matrix here has $\rho R^T$ in position (2,3) and $\rho R$ in position (3,2). The worst-case objective, the value of (30) and the SDP value are extended-real suprema and infima; the SDP value is $+\infty$ when no tuple is feasible. The affine map $H(x)$ is the published `RobustSDP.FullPert.affineMap`.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 45, display of H₀(Δ), the set 𝒟 and Eq. (30); p. 46, the set 𝒮 and Theorem 5.5

import Mathlib
import Definitions.Def_RobustSDP_FullPert_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert.Supplement

open RobustSDP.FullPert

/-- Index set `{(i, k) : 1 ≤ i ≤ n, 1 ≤ k ≤ i}` of the block structure of §5.6, p. 45: block `i`
(0-based `i : Fin n`) has size `i + 1`, so the total size is `N = 1 + 2 + ⋯ + n`. -/
abbrev BlkIdx (n : ℕ) : Type := Σ i : Fin n, Fin (i.val + 1)

/-- The perturbation structure `𝒟 = {diag(δ₁I₁, …, δₙIₙ) | δᵢ ∈ ℝ}` of §5.6, p. 45, where `Iᵢ` is
the `i × i` identity: block-diagonal `N × N` matrices whose `i`-th block is a real multiple of the
identity of size `i`. -/
def blockScalarSet (n : ℕ) : Set (Matrix (BlkIdx n) (BlkIdx n) ℝ) :=
  {Δ | ∃ δ : Fin n → ℝ,
    Δ = blockDiagonal' fun i => δ i • (1 : Matrix (Fin (i.val + 1)) (Fin (i.val + 1)) ℝ)}

/-- The scaling set `𝒮 = {diag(S₁, …, Sₙ) | Sᵢ ∈ ℝ^{i×i}}` of §5.6, p. 46: block-diagonal `N × N`
matrices with blocks of sizes `1, …, n`. -/
def scalingSpace (n : ℕ) : Set (Matrix (BlkIdx n) (BlkIdx n) ℝ) :=
  {S | ∃ Ss : (i : Fin n) → Matrix (Fin (i.val + 1)) (Fin (i.val + 1)) ℝ, S = blockDiagonal' Ss}

/-- The `(n + n + N)`-square block matrix of the SDP of Theorem 5.5, p. 46, for `Hx = H(x)`:
`[[λI − LSLᵀ, H(x), LG], [H(x)ᵀ, λI, ρRᵀ], [GᵀLᵀ, ρR, S]]`, with `L : n × N` and `R : N × n`.
The index set is `(Fin n ⊕ Fin n) ⊕ BlkIdx n`. (The printed matrix has `ρR` in position (2,3) and
`ρRᵀ` in position (3,2); with `R : N × n` these blocks have the sizes `n × N` and `N × n` only
when transposed, so the dimensionally consistent symmetric matrix is the one written here.) -/
def structuredNormLMI {n : ℕ} (Hx : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin n) (BlkIdx n) ℝ)
    (R : Matrix (BlkIdx n) (Fin n) ℝ) (ρ lam : ℝ) (S G : Matrix (BlkIdx n) (BlkIdx n) ℝ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ BlkIdx n) ((Fin n ⊕ Fin n) ⊕ BlkIdx n) ℝ :=
  fromBlocks
    (fromBlocks (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - L * S * Lᵀ) Hx Hxᵀ
      (lam • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (fromRows (L * G) (ρ • Rᵀ))
    (fromCols (Gᵀ * Lᵀ) (ρ • R))
    S

/-- Feasibility of `(x, λ, S, G)` for the SDP of Theorem 5.5, p. 46: `S = Sᵀ ∈ 𝒮`,
`G = −Gᵀ ∈ 𝒮`, and the block matrix `structuredNormLMI` is positive definite (`≻ 0`), where
`H(x) = H₀ + ∑ᵢ xᵢHᵢ`. -/
def StructuredNormFeasible {m n : ℕ} (Hs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (BlkIdx n) ℝ) (R : Matrix (BlkIdx n) (Fin n) ℝ) (ρ : ℝ)
    (x : Fin m → ℝ) (lam : ℝ) (S G : Matrix (BlkIdx n) (BlkIdx n) ℝ) : Prop :=
  S ∈ scalingSpace n ∧ Sᵀ = S ∧ G ∈ scalingSpace n ∧ Gᵀ = -G ∧
    (structuredNormLMI (affineMap Hs x) L R ρ lam S G).PosDef

/-- The worst-case objective of the min-max problem (30), p. 45, at `x`:
`max_{Δ ∈ 𝒟, ‖Δ‖ ≤ ρ} ‖H(x) + LΔR‖` (spectral norms), as an extended-real supremum. -/
noncomputable def structuredRobustObj {m n : ℕ} (Hs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (BlkIdx n) ℝ) (R : Matrix (BlkIdx n) (Fin n) ℝ) (ρ : ℝ)
    (x : Fin m → ℝ) : EReal :=
  ⨆ (Δ : Matrix (BlkIdx n) (BlkIdx n) ℝ) (_ : Δ ∈ blockScalarSet n) (_ : ‖Δ‖ ≤ ρ),
    ((‖affineMap Hs x + L * Δ * R‖ : ℝ) : EReal)

/-- The objective value of the min-max problem (30), p. 45: the infimum over `x ∈ ℝ^m` of the
worst-case objective, in `EReal`. -/
noncomputable def structuredRobustValue {m n : ℕ} (Hs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (BlkIdx n) ℝ) (R : Matrix (BlkIdx n) (Fin n) ℝ) (ρ : ℝ) : EReal :=
  ⨅ x : Fin m → ℝ, structuredRobustObj Hs L R ρ x

/-- The value `inf λ` of the SDP of Theorem 5.5, p. 46, over all feasible `(x, λ, S, G)`, in
`EReal` (`⊤` if the SDP is infeasible). -/
noncomputable def structuredSDPValue {m n : ℕ} (Hs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (BlkIdx n) ℝ) (R : Matrix (BlkIdx n) (Fin n) ℝ) (ρ : ℝ) : EReal :=
  ⨅ (x : Fin m → ℝ) (lam : ℝ) (S : Matrix (BlkIdx n) (BlkIdx n) ℝ)
    (G : Matrix (BlkIdx n) (BlkIdx n) ℝ) (_ : StructuredNormFeasible Hs L R ρ x lam S G),
    (lam : EReal)

end RobustSDP.FullPert.Supplement


