-- Prove2me | Definitions.Def_CandesTao_CompletionII_CenteredOperators
-- name    : CandesTao_CompletionII_CenteredOperators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:53:21.807979+00:00
-- url     : https://prove2.me/theorems/c8d10b2f-758c-439b-abec-afdaabcc0272
-- title:
--   Centered operators $\mathcal{Q}_T$, powers of $\mathcal{Q}_\Omega\mathcal{Q}_T$ and $\mathcal{Q}_\Omega\mathcal{P}_T$ (Eqs. (III.12), (III.16), (III.17))
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ have a rank-$r$ SVD with column and row projections $P_U, P_V$ and sign matrix $E$, and let $\mathcal{P}_T(X) = P_U X + X P_V - P_U X P_V$ be the orthogonal projection onto the tangent space $T$ (III.3). For an observation set $\Omega \subseteq [n]\times[n]$ let $\mathcal{P}_\Omega$ keep the entries in $\Omega$ and zero the others, and for a sampling parameter $p$ put
--   $$\mathcal{Q}_\Omega := \frac1p\mathcal{P}_\Omega - \mathcal{I} \qquad \text{(III.12)}.$$
--   With $\rho := r/n$ define
--   $$\rho' := 2\rho - \rho^2 \quad \text{(III.16)}, \qquad \mathcal{Q}_T := \mathcal{P}_T - \rho'\mathcal{I} \quad \text{(III.17)}.$$
--   This file defines:
--
--   1. $\rho'$ as a function of $n$ and $r$;
--   2. the centered tangent projection $\mathcal{Q}_T$;
--   3. the powers $(\mathcal{Q}_\Omega\mathcal{Q}_T)^j(X)$ and $(\mathcal{Q}_\Omega\mathcal{P}_T)^j(X)$, meaning that the composite operator $\mathcal{Q}_\Omega\mathcal{Q}_T$ (respectively $\mathcal{Q}_\Omega\mathcal{P}_T$) is applied $j$ times to $X$, the rightmost factor first;
--   4. the random matrix
--   $$A := (\mathcal{Q}_\Omega\mathcal{Q}_T)^k\mathcal{Q}_\Omega(E),$$
--   in which $\mathcal{Q}_\Omega$ is applied to $E$ first.
--
--   The operator $\mathcal{Q}_\Omega$ has mean zero under the Bernoulli model with parameter $p$, and $\mathcal{Q}_T$ has eigenvalues centered around zero, since $\rho' = \operatorname{trace}(\mathcal{P}_T)/n^2$. The matrices $(\mathcal{Q}_\Omega\mathcal{P}_T)^k\mathcal{Q}_\Omega(E)$ are the terms of the Neumann series for the candidate dual certificate, and $A$ is the matrix whose moments are bounded in Theorem 3.6.
--
--   **Formalization Note** $\mathcal{Q}_\Omega$ is the platform's `centeredSamplingFluctuation Ω p`, i.e. $p^{-1}(\mathcal{P}_\Omega X - pX)$. Matrices are indexed by `Fin n`, and $\rho$ is the real quotient $r/n$.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, pp. 2061–2063, Eqs. (III.12), (III.16), (III.17), and the matrix A of Theorem 3.6

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

namespace CandesTao.CompletionII

/-- `ρ' := 2ρ - ρ²` with `ρ := r/n` (Candès–Tao, Eq. (III.16)); for a rank-`r` SVD it
equals `trace(P_T)/n²`. -/
noncomputable def rhoPrime (n r : ℕ) : ℝ :=
  2 * ((r : ℝ) / (n : ℝ)) - ((r : ℝ) / (n : ℝ)) ^ 2

/-- The centered tangent projection `Q_T := P_T - ρ' 𝓘` (Candès–Tao, Eq. (III.17)),
acting on `n × n` real matrices. -/
noncomputable def centeredTangentProjection {n r : ℕ} {M : RealMatrix n n}
    (S : SVD M r) (X : RealMatrix n n) : RealMatrix n n :=
  tangentProjection S X - rhoPrime n r • X

/-- `(Q_Ω Q_T)^j (X)`: the map `Y ↦ Q_Ω(Q_T(Y))` applied `j` times to `X`, where
`Q_Ω := p⁻¹ P_Ω - 𝓘` (Eq. (III.12), the platform's `centeredSamplingFluctuation Ω p`). -/
noncomputable def centeredPower {n r : ℕ} {M : RealMatrix n n} (S : SVD M r)
    (Ω : Finset (Fin n × Fin n)) (p : ℝ) (j : ℕ) (X : RealMatrix n n) :
    RealMatrix n n :=
  (fun Y => centeredSamplingFluctuation Ω p (centeredTangentProjection S Y))^[j] X

/-- `(Q_Ω P_T)^j (X)`: the map `Y ↦ Q_Ω(P_T(Y))` applied `j` times to `X`. -/
noncomputable def tangentPower {n r : ℕ} {M : RealMatrix n n} (S : SVD M r)
    (Ω : Finset (Fin n × Fin n)) (p : ℝ) (j : ℕ) (X : RealMatrix n n) :
    RealMatrix n n :=
  (fun Y => centeredSamplingFluctuation Ω p (tangentProjection S Y))^[j] X

/-- The random matrix `A := (Q_Ω Q_T)^k Q_Ω(E)` of Theorem 3.6 of Candès–Tao, with
`E = signMatrix S`: `Q_Ω` is applied to `E` first, then `Y ↦ Q_Ω(Q_T(Y))` `k` times. -/
noncomputable def momentMatrix {n r : ℕ} {M : RealMatrix n n} (S : SVD M r)
    (Ω : Finset (Fin n × Fin n)) (p : ℝ) (k : ℕ) : RealMatrix n n :=
  centeredPower S Ω p k (centeredSamplingFluctuation Ω p (signMatrix S))

end CandesTao.CompletionII


