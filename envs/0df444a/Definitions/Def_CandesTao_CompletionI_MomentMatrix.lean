-- Prove2me | Definitions.Def_CandesTao_CompletionI_MomentMatrix
-- name    : CandesTao_CompletionI_MomentMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:41:13.164985+00:00
-- url     : https://prove2.me/theorems/74a415a7-64fb-4ec4-a03f-0e9e007b0916
-- title:
--   Centered operators $\mathcal Q_T$ and the matrix $A = (\mathcal Q_\Omega\mathcal Q_T)^k\mathcal Q_\Omega(E)$ (Eqs. (III.12), (III.16), (III.17))
-- statement:
--   Fix a real $n\times n$ matrix $M$ with a rank-$r$ SVD, projections $P_U, P_V$ and sign matrix $E$ as in the strong incoherence definition. Let $T$ be the tangent space at $M$ and
--   $$\mathcal P_T(X) = P_U X + X P_V - P_U X P_V$$
--   the orthogonal projection onto it (III.3). Let $\Omega \subset [n]\times[n]$ be a set of observed entries, $\mathcal P_\Omega$ the operator keeping the entries in $\Omega$ and zeroing the others, and $p \in (0,1]$ the sampling probability. This file defines three objects.
--
--   1. The **normalized sampling operator** (III.12), $\mathcal Q_\Omega := p^{-1}\mathcal P_\Omega - \mathcal I$, where $\mathcal I$ is the identity on $\mathbb R^{n\times n}$. It is the platform's `centeredSamplingFluctuation`.
--   2. The numbers $\rho := r/n$ and $\rho' := 2\rho - \rho^2$ (III.16), which is $\operatorname{trace}(\mathcal P_T)/n^2$, and the **centered tangent projection** (III.17)
--   $$\mathcal Q_T := \mathcal P_T - \rho'\,\mathcal I .$$
--   3. For $k \ge 0$, the random matrix of the moment bounds (Theorems 3.4 and 3.6)
--   $$A := (\mathcal Q_\Omega \mathcal Q_T)^k\, \mathcal Q_\Omega(E),$$
--   obtained by applying $\mathcal Q_\Omega$ to $E$ and then the map $X \mapsto \mathcal Q_\Omega(\mathcal Q_T(X))$ exactly $k$ times.
--
--   Under the Bernoulli model $\mathcal Q_\Omega$ has mean zero, and $\mathcal Q_T$ has eigenvalues centered around zero. The spectral norms of the matrices $A$ for $k = 0,1,\dots,\lfloor\log n\rfloor$ control the norm of $\mathcal P_{T^\perp}(Y)$ for the candidate dual certificate $Y$, which is why their moments $\mathbb E\operatorname{trace}(A^*A)^j$ are the central quantities of the paper.
--
--   **Formalization Note** $A$ is `momentMatrix S Ω p k`, defined with `Nat.iterate`; $\mathcal Q_T$ is `centeredTangentProjection S`. Only the square case $n_1 = n_2 = n$ is defined, as in the paper (Section I-H). With the Lean convention $0^{-1} = 0$, $\mathcal Q_\Omega$ at $p = 0$ is the zero operator; every statement using it takes $p = m/n^2$ with the hypotheses of the paper.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, pp. 2061–2063, Eqs. (III.12), (III.16), (III.17) and the definition of A in Theorem 3.4

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

namespace CandesTao.CompletionI

/-- `ρ' := 2ρ - ρ²` with `ρ := r/n` (Candès–Tao, Eq. (III.16)); it equals
`trace(P_T)/n²`, the mean eigenvalue of the tangent projection. -/
noncomputable def rhoPrime (n r : ℕ) : ℝ :=
  2 * ((r : ℝ) / (n : ℝ)) - ((r : ℝ) / (n : ℝ)) ^ 2

/-- The centered tangent projection `Q_T := P_T - ρ' 𝓘` (Candès–Tao, Eq. (III.17)),
acting on `n × n` real matrices. -/
noncomputable def centeredTangentProjection {n r : ℕ} {M : RealMatrix n n}
    (S : SVD M r) (X : RealMatrix n n) : RealMatrix n n :=
  tangentProjection S X - rhoPrime n r • X

/-- The random matrix `A := (Q_Ω Q_T)^k Q_Ω(E)` of Theorems 3.4 and 3.6 of Candès–Tao,
where `Q_Ω := p⁻¹ P_Ω - 𝓘` (Eq. (III.12), the platform's
`centeredSamplingFluctuation Ω p`), `Q_T` is `centeredTangentProjection`, and
`E = signMatrix S`.  `Q_Ω` is applied to `E` first, then the map `X ↦ Q_Ω(Q_T(X))`
is applied `k` times. -/
noncomputable def momentMatrix {n r : ℕ} {M : RealMatrix n n} (S : SVD M r)
    (Ω : Finset (Fin n × Fin n)) (p : ℝ) (k : ℕ) : RealMatrix n n :=
  (fun X => centeredSamplingFluctuation Ω p (centeredTangentProjection S X))^[k]
    (centeredSamplingFluctuation Ω p (signMatrix S))

end CandesTao.CompletionI


