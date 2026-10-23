-- Prove2me | Definitions.Def_StaggeredRollout_TOpt_Setting
-- name    : StaggeredRollout_TOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:56.99014+00:00
-- url     : https://prove2.me/theorems/0faaa50a-ca51-444b-8df1-c24327012361
-- title:
--   §2–§3, (3.1), (3.4), (EC.1.1)–(EC.1.3), (EC.2.1)–(EC.2.2) — staggered designs, the GLS precision trace tr Prec(τ̂; A), the S-shaped fraction ω*, the design sets 𝔸_ℓ, 𝔸_X, 𝔸_U
-- statement:
--   This file sets up the non-adaptive staggered-rollout design problem of Xiong, Athey, Bayati and Imbens.
--
--   **Designs and treatment paths.** There are $N$ units and $T$ periods. A *staggered design* assigns to each unit $i$ an adoption time $A_i\in[T]\cup\{\infty\}$ ($A_i=\infty$: never treated). Treatment is irreversible, and coded $\pm1$:
--   $$
--   z_{it}=\begin{cases}+1 & A_i\le t,\\ -1 & \text{otherwise.}\end{cases}
--   $$
--
--   **The estimator and its precision.** With $\ell\ge 0$ known lags, the outcome model (3.1) is
--   $$
--   Y_{it}=\alpha_i+\beta_t+X_i^\top\theta_t+\tau_0z_{it}+\tau_1z_{i,t-1}+\dots+\tau_\ell z_{i,t-\ell}+u_i^\top v_t+\varepsilon_{it},
--   $$
--   with observed covariates $X\in\mathbb R^{N\times d_x}$ and latent covariates $U=[u_i]\in\mathbb R^{N\times d_u}$. It is fitted by generalized least squares on the periods $t=\ell+1,\dots,T$. The errors $e_{it}=u_i^\top v_t+\varepsilon_{it}$ have per-period covariance $\Psi=U\Sigma_vU^\top+\sigma_\varepsilon^2I_N$ and are uncorrelated across periods, so $\Sigma_e=\mathrm{diag}(\Psi,\dots,\Psi)$. For $j=0,\dots,\ell$ let $D_j$ be the lag-$j$ treatment column, with entry $z_{i,s-j}$ at observation $(s,i)$, $s=\ell+1,\dots,T$. The nuisance columns $G$ are a unit effect for every unit, and for every observed period $s$ a time effect and a slope on $X_i$. The trace of the precision of $\hat\tau=(\hat\tau_0,\dots,\hat\tau_\ell)$ under $A$ is
--   $$
--   \operatorname{tr}\operatorname{Prec}(\hat\tau;A)=\sum_{j=0}^{\ell}\ \min_{\gamma}\ \sum_{s=\ell+1}^{T}(D_j-G\gamma)_s^\top\,\Psi^{-1}\,(D_j-G\gamma)_s ,
--   $$
--   the sum of the diagonal entries of the Schur complement $Z_\ell^\top\Sigma_e^{-1}Z_\ell-Z_\ell^\top\Sigma_e^{-1}G(G^\top\Sigma_e^{-1}G)^{-1}G^\top\Sigma_e^{-1}Z_\ell$ of (EC.2.2).
--
--   **The S-shaped fraction.** With $h=\lfloor\ell/2\rfloor$ and $K=\ell-h$, the $K\times K$ matrix $M^{(\ell)}$ and vector $b^{(\ell)}$ of (EC.1.2)–(EC.1.3) are, for $r,c=1,\dots,K$,
--   $$
--   M^{(\ell)}_{rc}=(h+r)\,\mathbf 1[r=c]-\frac{K+1-\max(r,c)}{T-\ell},\qquad
--   b^{(\ell)}_r=-(h+r)+\frac{(h+r)^2}{T-\ell}-\frac{1}{T-\ell}\sum_{l=1}^{K+1-r}(h+1-l),
--   $$
--   and $a^{(\ell)}=(M^{(\ell)})^{-1}b^{(\ell)}$. The treated fraction (3.4) is
--   $$
--   \omega^*_{\ell,t}=\begin{cases}-1 & t\le h\\ a^{(\ell)}_{t-h} & h<t\le\ell\\ -1+\dfrac{2t-(\ell+1)}{T-\ell} & \ell<t\le T-\ell\\ -\omega^*_{\ell,T+1-t} & T-\ell<t\le T-h\\ 1 & T-h<t.\end{cases}
--   $$
--
--   **Design sets** (p. 13):
--   $$
--   \mathbb A_\ell=\Big\{A:\ N^{-1}\sum_{i=1}^N\mathbf 1_{A_i\le t}=\tfrac{1+\omega^*_{\ell,t}}{2}\ \forall t\Big\},\qquad
--   \mathbb A_X=\Big\{A:\ N^{-1}\sum_{i=1}^N X_i\mathbf 1_{A_i=t}=0_{d_x}\ \forall t\in\{2,\dots,T\}\Big\},
--   $$
--   and $\mathbb A_U$ is $\mathbb A_X$ with $u_i$ in place of $X_i$. For $d_x=0$ the condition defining $\mathbb A_X$ is empty.
--
--   These objects are shared by Theorem 3.1 and the milestones of its proof.
--
--   **Formalization Note** Periods are 0-based (`Fin T`; the paper's period $t$ is index $t-1$) and $\infty$ is the top element of `WithTop (Fin T)`, which keeps "larger means later". The minimum over $\gamma$ is a real infimum `⨅` of a quadratic that is nonnegative whenever $\Psi\succ0$ and attains its infimum, so under the theorems' hypotheses ($\sigma_\varepsilon^2>0$, $\Sigma_v=\sigma_\varepsilon^2I$) it is the true minimum. All $N$ unit dummies are used instead of the paper's normalization $\alpha_{N-p+1:N}=0$: the column span is the same, so the value agrees with (EC.2.2) wherever that formula is defined, and it needs no invertibility side condition. $\Psi^{-1}$ is Lean's matrix inverse, invertible under $\sigma_\varepsilon^2>0$, $\Sigma_v=\sigma_\varepsilon^2I$. $a^{(\ell)}$ uses Lean's inverse of $M^{(\ell)}$; its invertibility under the threshold of Theorem 3.1 is a conclusion of the milestone on $a^{(\ell)}$. In $\mathbb A_\ell$ and $\mathbb A_X$ the factor $N^{-1}$ is Lean's (`0⁻¹ = 0` at $N=0$).
-- source:
--   Xiong, Athey, Bayati, Imbens, Optimal Experimental Design for Staggered Rollouts, arXiv:1911.03764v6, pp. 5–13, ec4–ec5, ec14, (3.1), (3.2), (3.4), (EC.1.1)–(EC.1.3), (EC.2.1)–(EC.2.2); design sets 𝔸_ℓ, 𝔸_X, 𝔸_U on p. 13

import Mathlib

namespace StaggeredRollout.TOpt
open Matrix

/-- Treatment indicator `z_it ∈ {−1, +1}` of a staggered design (p. 5, p. 11). A design assigns to every
unit `i` its adoption period `A i ∈ [T] ∪ {∞}`, encoded as `WithTop (Fin T)` (periods are 0-based: the
paper's period `t` is `Fin T` index `t − 1`; `⊤` is `∞`, never treated). Unit `i` is treated in period
`t` (`z_it = +1`) iff it adopted by then, `A i ≤ t`; otherwise `z_it = −1`. -/
def z {N T : ℕ} (A : Fin N → WithTop (Fin T)) (i : Fin N) (t : Fin T) : ℝ :=
  if A i ≤ (t : WithTop (Fin T)) then 1 else -1

/-- The lag-`j` regressor of (3.1) over the observed periods `ℓ+1, …, T` (EC.1.1): at observation
`(s, i)`, with `s : Fin (T − ℓ)` standing for the (0-based) period `s + ℓ`, its value is
`z_{i, s + ℓ − j}`. The columns `j = 0, …, ℓ` form the matrix `Z_ℓ` of (EC.2.1). -/
def lagCol {N T : ℕ} (ℓ : ℕ) (A : Fin N → WithTop (Fin T)) (j : Fin (ℓ + 1))
    (s : Fin (T - ℓ)) (i : Fin N) : ℝ :=
  z A i ⟨s.val + ℓ - j.val, by have := s.isLt; have := j.isLt; omega⟩

/-- The error covariance of one period, `Ψ = U Σ_v Uᵀ + σ²_ε I_N` (Assumption 3.1, (EC.2.1)). -/
def Psi {N du : ℕ} (sig2 : ℝ) (U : Matrix (Fin N) (Fin du) ℝ) (Sv : Matrix (Fin du) (Fin du) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  U * Sv * Uᵀ + sig2 • (1 : Matrix (Fin N) (Fin N) ℝ)

/-- Fitted value of the nuisance part of (3.1) at observation `(s, i)` (period `s + ℓ`, 0-based):
`α_i + β_s + X_iᵀ θ_s`, with a unit effect for every unit and a time effect and a covariate slope
vector for every observed period. -/
def nuisanceFit {N T dx : ℕ} (ℓ : ℕ) (X : Matrix (Fin N) (Fin dx) ℝ)
    (γ : (Fin N → ℝ) × (Fin (T - ℓ) → ℝ) × (Fin (T - ℓ) → Fin dx → ℝ))
    (s : Fin (T - ℓ)) (i : Fin N) : ℝ :=
  γ.1 i + γ.2.1 s + ∑ k, X i k * γ.2.2 s k

/-- The trace of the GLS precision of `τ̂ = (τ_0, …, τ_ℓ)` under the design `A`, (EC.2.1)–(EC.2.2),
with error covariance `Σ_e = diag(Ψ, …, Ψ)` over the observed periods `ℓ+1, …, T`:
`tr Prec(τ̂; A) = Σ_{j=0}^{ℓ} min_γ Σ_s (D_j − Gγ)_sᵀ Ψ⁻¹ (D_j − Gγ)_s`,
the `j`-th diagonal entry of the Schur complement of the nuisance block in the information matrix
being the minimal `Σ_e⁻¹`-weighted residual sum of squares of the lag-`j` column regressed on the
nuisance columns. -/
noncomputable def traceT {N T dx du : ℕ} (ℓ : ℕ) (sig2 : ℝ) (X : Matrix (Fin N) (Fin dx) ℝ)
    (U : Matrix (Fin N) (Fin du) ℝ) (Sv : Matrix (Fin du) (Fin du) ℝ)
    (A : Fin N → WithTop (Fin T)) : ℝ :=
  ∑ j : Fin (ℓ + 1),
    ⨅ γ : (Fin N → ℝ) × (Fin (T - ℓ) → ℝ) × (Fin (T - ℓ) → Fin dx → ℝ),
      ∑ s : Fin (T - ℓ),
        (fun i => lagCol ℓ A j s i - nuisanceFit ℓ X γ s i) ⬝ᵥ
          ((Psi sig2 U Sv)⁻¹ *ᵥ (fun i => lagCol ℓ A j s i - nuisanceFit ℓ X γ s i))

/-- The matrix `M^{(ℓ)}` of (EC.1.2), of size `K = ℓ − ⌊ℓ/2⌋`. With 0-based indices `r, c` and
`h = ⌊ℓ/2⌋`: `M_{rc} = (h + r + 1)·[r = c] − (K − max(r, c))/(T − ℓ)`. -/
noncomputable def Mmat (ℓ T : ℕ) : Matrix (Fin (ℓ - ℓ / 2)) (Fin (ℓ - ℓ / 2)) ℝ :=
  Matrix.of fun r c =>
    (if r = c then ((ℓ / 2 : ℕ) : ℝ) + r.val + 1 else 0)
      - (((ℓ - ℓ / 2 : ℕ) : ℝ) - (max r.val c.val : ℕ)) / ((T : ℝ) - ℓ)

/-- The vector `b^{(ℓ)}` of (EC.1.3). With 0-based index `r` and `h = ⌊ℓ/2⌋`, `K = ℓ − h`:
`b_r = −(h + r + 1) + (h + r + 1)²/(T − ℓ) − (1/(T − ℓ)) Σ_{l=1}^{K−r} (h + 1 − l)`. -/
noncomputable def bvec (ℓ T : ℕ) : Fin (ℓ - ℓ / 2) → ℝ :=
  fun r =>
    -(((ℓ / 2 : ℕ) : ℝ) + r.val + 1) + (((ℓ / 2 : ℕ) : ℝ) + r.val + 1) ^ 2 / ((T : ℝ) - ℓ)
      - (1 / ((T : ℝ) - ℓ)) *
          ∑ l ∈ Finset.Icc 1 (ℓ - ℓ / 2 - r.val), (((ℓ / 2 : ℕ) : ℝ) + 1 - (l : ℝ))

/-- `a^{(ℓ)} = (M^{(ℓ)})⁻¹ b^{(ℓ)}` (Section EC.1.2, p. ec5). -/
noncomputable def avec (ℓ T : ℕ) : Fin (ℓ - ℓ / 2) → ℝ :=
  (Mmat ℓ T)⁻¹ *ᵥ bvec ℓ T

/-- The S-shaped treated fraction `ω*_{ℓ,t}` of (3.4), at the 0-based period `t` (paper's period
`τ = t + 1`), with `h = ⌊ℓ/2⌋`; the five cases are tried in the page's order:
`−1` for `τ ≤ h`; `a^{(ℓ)}_{τ−h}` for `h < τ ≤ ℓ`; `−1 + (2τ − (ℓ+1))/(T − ℓ)` for `ℓ < τ ≤ T − ℓ`;
`−ω*_{T+1−τ} = −a^{(ℓ)}_{T+1−τ−h}` for `T − ℓ < τ ≤ T − h`; and `1` otherwise. -/
noncomputable def omegaStar (ℓ T : ℕ) (t : Fin T) : ℝ :=
  if h1 : t.val + 1 ≤ ℓ / 2 then -1
  else if h2 : t.val + 1 ≤ ℓ then avec ℓ T ⟨t.val - ℓ / 2, by omega⟩
  else if h3 : t.val + 1 ≤ T - ℓ then
    -1 + (2 * ((t.val : ℝ) + 1) - ((ℓ : ℝ) + 1)) / ((T : ℝ) - ℓ)
  else if h4 : t.val + 1 ≤ T - ℓ / 2 then
    -avec ℓ T ⟨T - (t.val + 1) - ℓ / 2, by have := t.isLt; omega⟩
  else 1

/-- `𝔸_ℓ` (p. 13): designs whose treated fraction follows `ω*`, i.e.
`N⁻¹ Σ_i 1{A_i ≤ t} = (1 + ω*_{ℓ,t})/2` for every period `t`. -/
def Aell {N T : ℕ} (ℓ : ℕ) : Set (Fin N → WithTop (Fin T)) :=
  {A | ∀ t : Fin T,
    (N : ℝ)⁻¹ * ((Finset.univ.filter fun i => A i ≤ (t : WithTop (Fin T))).card : ℝ)
      = (1 + omegaStar ℓ T t) / 2}

/-- `𝔸_X` (p. 13): covariate-balanced designs, `N⁻¹ Σ_i X_i 1{A_i = t} = 0` for every period
`t ∈ {2, …, T}` (0-based: `1 ≤ t`). For `dx = 0` the condition is empty, so `𝔸_X` is all designs. -/
def AX {N T dx : ℕ} (X : Matrix (Fin N) (Fin dx) ℝ) : Set (Fin N → WithTop (Fin T)) :=
  {A | ∀ t : Fin T, 1 ≤ t.val → ∀ k : Fin dx,
    (N : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i => A i = (t : WithTop (Fin T))), X i k = 0}

/-- `𝔸_U` (p. 13), defined like `𝔸_X` with the latent covariates `u_i` (rows of `U`). -/
def AU {N T du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) : Set (Fin N → WithTop (Fin T)) :=
  {A | ∀ t : Fin T, 1 ≤ t.val → ∀ k : Fin du,
    (N : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i => A i = (t : WithTop (Fin T))), U i k = 0}

end StaggeredRollout.TOpt


