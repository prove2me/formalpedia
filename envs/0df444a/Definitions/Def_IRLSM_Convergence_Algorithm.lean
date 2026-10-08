-- Prove2me | Definitions.Def_IRLSM_Convergence_Algorithm
-- name    : IRLSM_Convergence_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:47.113929+00:00
-- url     : https://prove2.me/theorems/9f989f6d-b690-4da5-aee3-bc3bbefe179e
-- title:
--   The IRLS-M weights $W=U\Sigma_\varepsilon^{-1}U^*$, the functionals $\mathcal J(X,W)$ and $\mathcal J_\varepsilon(X)$, the IRLS-M run (2.9)–(2.12), and the constant $\Lambda$
-- statement:
--   Let $X$ be a real $n\times p$ matrix with $XX^{\mathsf T}=U\Sigma^2U^{\mathsf T}$, $\Sigma=\operatorname{diag}(\sigma_1,\dots,\sigma_n)$. For $\varepsilon>0$ the **$\varepsilon$-stabilization** is $\Sigma_\varepsilon=\operatorname{diag}(\max\{\sigma_j,\varepsilon\})$ (2.3), and the **IRLS-M weight** is
--   $$W=U\Sigma_\varepsilon^{-1}U^{\mathsf T}=\big[((XX^{\mathsf T})^{1/2})_\varepsilon\big]^{-1},$$
--   the function $t\mapsto1/\max\{\sqrt t,\varepsilon\}$ applied to the symmetric matrix $XX^{\mathsf T}$; it does not depend on the choice of $U$.
--
--   For $W=W^{\mathsf T}\succ0$ the functional (5.1) is
--   $$\mathcal J(X,W)=\tfrac12\big(\|W^{1/2}X\|_F^2+\|W^{-1/2}\|_F^2\big).$$
--   The scalar smoothing is $j^\varepsilon(u)=|u|$ for $|u|\ge\varepsilon$ and $j^\varepsilon(u)=(u^2+\varepsilon^2)/(2\varepsilon)$ otherwise, and $\mathcal J_\varepsilon(X)=\sum_{i=1}^n j^\varepsilon(\sigma_i(X))$ (6.8).
--
--   **The IRLS-M algorithm.** Given measurement matrices defining $\mathcal S$, data $\mathscr M\in\mathbb R^m$, $K\in\mathbb N$ and $\gamma>0$: $W^0=I$, $\varepsilon_0=1$, and for $\ell=1,2,\dots$
--   $$X^\ell\in\arg\min_{\mathcal S(X)=\mathscr M}\|(W^{\ell-1})^{1/2}X\|_F^2,\qquad \varepsilon_\ell=\min\{\varepsilon_{\ell-1},\gamma\sigma_{K+1}(X^\ell)\},\qquad W^\ell=U^\ell(\Sigma^\ell_{\varepsilon_\ell})^{-1}(U^\ell)^{\mathsf T};$$
--   the algorithm stops when $\varepsilon_\ell=0$, after which $X^j:=X^\ell$. A pair of sequences $(X^\ell),(\varepsilon_\ell)$ satisfying these rules is a **run**.
--
--   Finally, $\Lambda(\eta,K,k)=\dfrac{4(1+\eta)^2}{(1-\eta)^2((K-k)(1-\eta)-2\eta)}+\dfrac{2(1+\eta)}{1-\eta}$ is the constant of Theorem 6.11(ii).
--
--   These objects describe the algorithm whose convergence the mission's goal theorem establishes.
--
--   **Formalization Note** The weight uses Mathlib's continuous functional calculus `cfc`; $W^{1/2}$ is `cfc Real.sqrt W` and $W^{-1/2}$ its matrix inverse. For $\varepsilon\le0$ the weight formula is junk, and no statement uses it there. The run is a relation (`IsRun`): $X^{\ell+1}$ is *a* minimizer (no choice function, no uniqueness assumed); after a stop, $\varepsilon_j:=0$ (the page leaves it undefined); $X^0$ is unconstrained (the algorithm never defines it). The page's second case of $j^\varepsilon$ reads "$u<\varepsilon$", a slip for $|u|<\varepsilon$, immaterial on singular values. $\mathcal J_\varepsilon$ sums the $n$ singular values $\sigma_1,\dots,\sigma_n$.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), (2.3), p. 4; IRLS-M algorithm (2.9)–(2.12), p. 6; (5.1), p. 12; (6.8), p. 20; Theorem 6.11 (Λ), p. 21

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- The IRLS-M weight `W = U Σ_ε⁻¹ Uᵀ`, where `X Xᵀ = U Σ² Uᵀ` and `Σ_ε = diag(max{σ_j, ε})` is the
`ε`-stabilization (2.3): the function `t ↦ (max{√t, ε})⁻¹` applied to the symmetric matrix `X Xᵀ`
by the continuous functional calculus.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, (2.3), p. 4; (2.11)–(2.12), p. 6; Proposition 5.3,
p. 14 (`W̄ = U Σ_ε⁻¹ Uᵀ`); p. 22 (`W = [((X Xᵀ)^{1/2})_ε]⁻¹`).

Formalization Notes: real matrices. The functional calculus does not depend on the choice of the
eigenbasis `U`. For `ε ≤ 0` the formula is junk (`0⁻¹ = 0` in Lean); every statement using it
assumes `0 < ε`. -/
noncomputable def weight {n p : ℕ} (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  cfc (fun t : ℝ => (max (Real.sqrt t) ε)⁻¹) (X * Xᵀ)

/-- The functional `𝒥(X, W) := ½ (‖W^{1/2} X‖²_F + ‖W^{−1/2}‖²_F)` (5.1).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, (5.1), p. 12.

Formalization Note: `W^{1/2}` is `cfc Real.sqrt W`, the real square root applied to the symmetric
matrix `W` by the continuous functional calculus (for `W ≻ 0` it is the unique positive definite
square root), and `W^{−1/2}` is its matrix inverse. The page defines `𝒥` for `W = Wᵀ ≻ 0`; every
statement about `J` assumes `W.PosDef`. -/
noncomputable def J {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2) * (frobeniusNorm (cfc Real.sqrt W * X) ^ 2 + frobeniusNorm (cfc Real.sqrt W)⁻¹ ^ 2)

/-- The scalar smoothing `j^ε(u) = |u|` for `|u| ≥ ε` and `(u² + ε²)/(2ε)` otherwise (6.8).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, (6.8), p. 20.

Formalization Note: the page's second case reads "`u < ε`", a slip for `|u| < ε`; the two agree on
singular values (`u ≥ 0`), which is the only use. -/
noncomputable def jε (ε u : ℝ) : ℝ :=
  if ε ≤ |u| then |u| else (u ^ 2 + ε ^ 2) / (2 * ε)

/-- The smoothed functional `𝒥_ε(X) := Σ_{i=1}^n j^ε(σ_i(X))` (6.8).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, (6.8), p. 20.

Formalization Note: the sum runs over the **n** singular values `σ_1, …, σ_n` (`sv X 0, …,
sv X (n-1)`), as on the page; the extra zero entries of `singularValues` beyond `n` are not
summed (`j^ε(0) = ε/2 ≠ 0`). -/
noncomputable def Jeps {n p : ℕ} (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, jε ε (sv X i)

/-- The weight sequence of the IRLS-M algorithm: `W⁰ = I` and `W^ℓ = U^ℓ (Σ^ℓ_{ε_ℓ})⁻¹ (U^ℓ)ᵀ`
for `ℓ ≥ 1`, computed from the iterate `X^ℓ` and the parameter `ε_ℓ`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, algorithm box, (2.11)–(2.12), p. 6. -/
noncomputable def Wseq {n p : ℕ} (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (ε : ℕ → ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | ℓ + 1 => weight (ε (ℓ + 1)) (X (ℓ + 1))

/-- `(X, ε)` is a run of the IRLS-M algorithm with data `S` (measurement matrices `A`), `𝓜 = M`,
parameters `K` and `γ`: `ε₀ = 1`, and for every `ℓ`, if `ε_ℓ ≠ 0` then `X^{ℓ+1}` is a minimizer of
`‖(W^ℓ)^{1/2} X‖²_F` subject to `S(X) = 𝓜` (2.9) and `ε_{ℓ+1} = min{ε_ℓ, γ σ_{K+1}(X^{ℓ+1})}`
(2.10), with `W^ℓ = Wseq X ε ℓ`; if `ε_ℓ = 0` the algorithm has stopped and `X^{ℓ+1} = X^ℓ`,
`ε_{ℓ+1} = 0`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, IRLS-M algorithm, (2.9)–(2.12), p. 6.

Formalization Notes: the run is a relation, not a function: `X^{ℓ+1}` is *a* minimizer of (2.9)
(no choice function; uniqueness is Lemma 5.1, not assumed). After the stop the page sets
`X^j := X^ℓ` and leaves `ε_j` undefined; here `ε_j := 0`. `X 0` is unconstrained (the algorithm
never defines `X⁰`). `σ_{K+1}` is the 0-based `sv _ K`. `(W^ℓ)^{1/2}` is `cfc Real.sqrt (Wseq X ε ℓ)`. The page's "`K ≥ k`" refers to the target
rank `k` of the analysis and does not constrain the run. -/
structure IsRun {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (K : ℕ)
    (γ : ℝ) (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (ε : ℕ → ℝ) : Prop where
  eps_zero : ε 0 = 1
  step : ∀ ℓ : ℕ,
    (ε ℓ = 0 → X (ℓ + 1) = X ℓ ∧ ε (ℓ + 1) = 0) ∧
    (ε ℓ ≠ 0 →
      (observationOp A (X (ℓ + 1)) = M ∧
        ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M →
          frobeniusNorm (cfc Real.sqrt (Wseq X ε ℓ) * X (ℓ + 1)) ^ 2 ≤
            frobeniusNorm (cfc Real.sqrt (Wseq X ε ℓ) * Y) ^ 2) ∧
      ε (ℓ + 1) = min (ε ℓ) (γ * sv (X (ℓ + 1)) K))

/-- The constant `Λ := 4(1 + η)² / ((1 − η)²((K − k)(1 − η) − 2η)) + 2(1 + η)/(1 − η)` of
Theorem 6.11(ii).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Theorem 6.11(ii), p. 21.

Formalization Note: computed in `ℝ` with `K` and `k` cast; under the theorem's hypotheses
`η < 1` and `k < K − 2η/(1 − η)` the denominators are positive. -/
noncomputable def Lambda (η : ℝ) (K k : ℕ) : ℝ :=
  4 * (1 + η) ^ 2 / ((1 - η) ^ 2 * (((K : ℝ) - k) * (1 - η) - 2 * η)) + 2 * (1 + η) / (1 - η)

end IRLSM.Convergence


