-- Prove2me | Definitions.Def_RobustSAA_Discrete_Supplement_UnivStat
-- name    : RobustSAA_Discrete_Supplement_UnivStat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:37:38.540877+00:00
-- url     : https://prove2.me/theorems/ca77821a-5deb-4990-9ea9-7ac12a8c9fcc
-- title:
--   (8), Theorem 10 — the five univariate statistics as functions of $\zeta_i=F_0(\xi^{(i)})$ and their cone data
-- statement:
--   Let $N\ge1$ and $\zeta=(\zeta_1,\dots,\zeta_N)\in\mathbb R^N$, where in the tests $\zeta_i=F_0(\xi^{(i)})$ is the hypothesized cdf at the $i$-th order statistic. The statistics (8) of p. 9 are
--
--   $$D_N=\max_i\max\Big\{\tfrac iN-\zeta_i,\ \zeta_i-\tfrac{i-1}N\Big\},\qquad V_N=\max_i\Big(\zeta_i-\tfrac{i-1}N\Big)+\max_i\Big(\tfrac iN-\zeta_i\Big),$$
--
--   $$W_N=\Big(\tfrac1{12N^2}+\tfrac1N\sum_i\big(\tfrac{2i-1}{2N}-\zeta_i\big)^2\Big)^{1/2},\qquad U_N=\Big(W_N^2-\big(\tfrac1N\sum_i\zeta_i-\tfrac12\big)^2\Big)^{1/2},$$
--
--   $$A_N=\Big(-1-\sum_i\tfrac{2i-1}{N^2}\big(\log\zeta_i+\log(1-\zeta_{N+1-i})\big)\Big)^{1/2},$$
--
--   with $A_N=+\infty$ when some $\zeta_i\notin(0,1)$. They agree with the published statistics `RobustSAA.Univariate.ksStat`, … evaluated at $\zeta_i=F_0(\xi^{(i)})$.
--
--   The file also defines the cones $K_{S_N}$, matrices $A_{S_N}$ and vectors $b_{S_N,\alpha}$ of Theorem 10 (pp. 17–18), with threshold $Q=Q_{S_N}(\alpha)$:
--
--   1. $K_{D_N}=\mathbb R_+^{2N}$, $A_{D_N}=A_{V_N}=[I_N;-I_N]$, $b_{D_N,\alpha}=(\tfrac1N-Q,\dots,\tfrac NN-Q,-\tfrac0N-Q,\dots,-\tfrac{N-1}N-Q)$.
--   2. $K_{V_N}=\{(x,y): \min_i x_i+\min_i y_i\ge0\}$, $b_{V_N,\alpha}$ as $b_{D_N,\alpha}$ with $Q/2$ in place of $Q$.
--   3. $K_{W_N}=C^{N+1}_{SOC}$, $A_{W_N}=[0\cdots0;I_N]$, $b_{W_N,\alpha}=\big(-\sqrt{NQ^2-\tfrac1{12N}},\tfrac1{2N},\tfrac3{2N},\dots,\tfrac{2N-1}{2N}\big)$.
--   4. $K_{U_N}=C^{N+2}_{SOC}$, $A_{U_N}$ with rows $\big(\tfrac{2i-1-N}{2N}\big)_i$, its negative, and $I_N-\tfrac1NE_N$; $b_{U_N,\alpha}=\big(-\tfrac12+(\tfrac N{24}-\tfrac N2Q^2),-\tfrac12-(\tfrac N{24}-\tfrac N2Q^2),0,\dots,0\big)$.
--   5. $K_{A_N}=\{(z,x,y)\in\mathbb R\times\mathbb R^{2N}_+: |z|\le\prod_i(x_iy_i)^{(2i-1)/(2N^2)}\}$, $A_{A_N}=[0\cdots0;I_N;-\tilde I_N]$ with $[\tilde I_N]_{ij}=\mathbb 1[i+j=N+1]$, $b_{A_N,\alpha}=(e^{-(Q^2+1)/2},0,\dots,0,-1,\dots,-1)$.
--
--   **Formalization Note** Two entries are corrected relative to the printed page: the leading entry of $b_{W_N,\alpha}$ (printed $+\sqrt{NQ^2-1/(2N)}$) and the leading entry of $b_{A_N,\alpha}$ (printed $e^{-Q^2-1}$); the reversal $\tilde I_N$ is printed $\mathbb 1[i=N-j]$, which is off by one. The corrections and their evidence are given with Theorem 10. Stacked vectors are indexed by sum and option types rather than by $\{1,\dots,2N\}$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, (8) p. 9; Theorem 10, pp. 17–18

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones

namespace RobustSAA.Discrete.Supplement

open scoped BigOperators

/-! The five univariate statistics (8), p. 9, as functions of `ζᵢ = F₀(ξ^(i))`, and the cone data
of Theorem 10, pp. 17–18. Vectors are indexed by `Fin N`; index `i : Fin N` is the paper's `i + 1`.
-/

/-- `D_N(ζ) = max_i max{i/N − ζᵢ, ζᵢ − (i−1)/N}`. -/
noncomputable def ksZ {N : ℕ} (ζ : Fin N → ℝ) : ℝ :=
  ⨆ i : Fin N, max (((i : ℕ) + 1 : ℝ) / N - ζ i) (ζ i - ((i : ℕ) : ℝ) / N)

/-- `V_N(ζ) = max_i (ζᵢ − (i−1)/N) + max_i (i/N − ζᵢ)`. -/
noncomputable def kuiperZ {N : ℕ} (ζ : Fin N → ℝ) : ℝ :=
  (⨆ i : Fin N, (ζ i - ((i : ℕ) : ℝ) / N)) + (⨆ i : Fin N, (((i : ℕ) + 1 : ℝ) / N - ζ i))

/-- `W_N(ζ) = (1/(12N²) + (1/N) Σᵢ ((2i−1)/(2N) − ζᵢ)²)^{1/2}`. -/
noncomputable def cvmZ {N : ℕ} (ζ : Fin N → ℝ) : ℝ :=
  Real.sqrt (1 / (12 * (N : ℝ) ^ 2) +
    (1 / (N : ℝ)) * ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - ζ i) ^ 2)

/-- `U_N(ζ) = (W_N(ζ)² − ((1/N) Σᵢ ζᵢ − 1/2)²)^{1/2}`. -/
noncomputable def watsonZ {N : ℕ} (ζ : Fin N → ℝ) : ℝ :=
  Real.sqrt (cvmZ ζ ^ 2 - ((1 / (N : ℝ)) * ∑ i : Fin N, ζ i - 1 / 2) ^ 2)

/-- `A_N(ζ)² = −1 − Σᵢ ((2i−1)/N²)(log ζᵢ + log(1 − ζ_{N+1−i}))` (`Fin.rev i` is `N + 1 − i`). -/
noncomputable def adSqZ {N : ℕ} (ζ : Fin N → ℝ) : ℝ :=
  -1 - ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (N : ℝ) ^ 2) *
    (Real.log (ζ i) + Real.log (1 - ζ (Fin.rev i)))

/-- `A_N(ζ)` in `[0, ∞]`: `(A_N²)^{1/2}` when every `ζᵢ ∈ (0, 1)`, and `+∞` otherwise (a logarithm
of a nonpositive number). -/
noncomputable def adZ {N : ℕ} (ζ : Fin N → ℝ) : ENNReal :=
  if ∀ i, 0 < ζ i ∧ ζ i < 1 then ENNReal.ofReal (Real.sqrt (adSqZ ζ)) else ⊤

/-! ### Cone data of Theorem 10 -/

/-- `A_{D_N} = A_{V_N} = [I_N; −I_N]`, rows indexed by `Fin N ⊕ Fin N`. -/
def A_KS (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N) ℝ :=
  Matrix.fromRows (1 : Matrix (Fin N) (Fin N) ℝ) (-1)

/-- `b_{D_N,α} = (1/N − Q, …, N/N − Q, −0/N − Q, …, −(N−1)/N − Q)`. -/
noncomputable def b_KS (N : ℕ) (Q : ℝ) : Fin N ⊕ Fin N → ℝ
  | Sum.inl i => ((i : ℕ) + 1 : ℝ) / N - Q
  | Sum.inr i => -(((i : ℕ) : ℝ) / N) - Q

/-- `K_{D_N} = ℝ₊^{2N}`. -/
def K_KS (N : ℕ) : Set (Fin N ⊕ Fin N → ℝ) :=
  {v | ∀ j, 0 ≤ v j}

/-- `b_{V_N,α} = (1/N − Q/2, …, N/N − Q/2, −0/N − Q/2, …, −(N−1)/N − Q/2)`. -/
noncomputable def b_Kuiper (N : ℕ) (Q : ℝ) : Fin N ⊕ Fin N → ℝ
  | Sum.inl i => ((i : ℕ) + 1 : ℝ) / N - Q / 2
  | Sum.inr i => -(((i : ℕ) : ℝ) / N) - Q / 2

/-- `K_{V_N} = {(x, y) ∈ ℝ^{2N} : minᵢ xᵢ + minᵢ yᵢ ≥ 0}`. -/
noncomputable def K_Kuiper (N : ℕ) : Set (Fin N ⊕ Fin N → ℝ) :=
  {v | 0 ≤ (⨅ i : Fin N, v (Sum.inl i)) + (⨅ i : Fin N, v (Sum.inr i))}

/-- `A_{W_N} = [0 ⋯ 0; I_N]`; row `none` is the zero row. -/
def A_CvM (N : ℕ) : Matrix (Option (Fin N)) (Fin N) ℝ
  | none, _ => 0
  | some i, j => if i = j then 1 else 0

/-- `b_{W_N,α}` with the corrected leading entry `−√(N Q² − 1/(12N))` (printed:
`+√(N Q² − 1/(2N))`), followed by `1/(2N), 3/(2N), …, (2N−1)/(2N)`. -/
noncomputable def b_CvM (N : ℕ) (Q : ℝ) : Option (Fin N) → ℝ
  | none => -Real.sqrt ((N : ℝ) * Q ^ 2 - 1 / (12 * (N : ℝ)))
  | some i => (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N)

/-- `K_{W_N} = C^{N+1}_SOC`. -/
def K_CvM (N : ℕ) : Set (Option (Fin N) → ℝ) :=
  soc (Fin N)

/-- `A_{U_N}`: first row `((1−N)/(2N), (3−N)/(2N), …, (N−1)/(2N))`, second row its negative,
then `I_N − E_N/N`. Row `none` is the first row, `some none` the second, `some (some i)` row `i`
of `I_N − E_N/N`. -/
noncomputable def A_Watson (N : ℕ) : Matrix (Option (Option (Fin N))) (Fin N) ℝ
  | none, j => (2 * ((j : ℕ) + 1 : ℝ) - 1 - N) / (2 * N)
  | some none, j => (N - (2 * ((j : ℕ) + 1 : ℝ) - 1)) / (2 * N)
  | some (some i), j => (if i = j then 1 else 0) - 1 / (N : ℝ)

/-- `b_{U_N,α} = (−1/2 + (N/24 − N Q²/2), −1/2 − (N/24 − N Q²/2), 0, …, 0)`. -/
noncomputable def b_Watson (N : ℕ) (Q : ℝ) : Option (Option (Fin N)) → ℝ
  | none => -1 / 2 + ((N : ℝ) / 24 - (N : ℝ) * Q ^ 2 / 2)
  | some none => -1 / 2 - ((N : ℝ) / 24 - (N : ℝ) * Q ^ 2 / 2)
  | some (some _) => 0

/-- `K_{U_N} = C^{N+2}_SOC`. -/
def K_Watson (N : ℕ) : Set (Option (Option (Fin N)) → ℝ) :=
  soc (Option (Fin N))

/-- `A_{A_N} = [0 ⋯ 0; I_N; −Ĩ_N]` with the reversal `Ĩ_N` read as `[Ĩ_N]_{ij} = 𝕀[i + j = N + 1]`
(1-based; printed `𝕀[i = N − j]`). Row `none` is the zero row. -/
def A_AD (N : ℕ) : Matrix (Option (Fin N ⊕ Fin N)) (Fin N) ℝ
  | none, _ => 0
  | some (Sum.inl i), j => if i = j then 1 else 0
  | some (Sum.inr i), j => if Fin.rev i = j then -1 else 0

/-- `b_{A_N,α}` with the corrected leading entry `e^{−(Q² + 1)/2}` (printed `e^{−Q²−1}`), then
`N` zeros and `N` entries `−1`. -/
noncomputable def b_AD (N : ℕ) (Q : ℝ) : Option (Fin N ⊕ Fin N) → ℝ
  | none => Real.exp (-(Q ^ 2 + 1) / 2)
  | some (Sum.inl _) => 0
  | some (Sum.inr _) => -1

/-- `K_{A_N} = {(z, x, y) ∈ ℝ × ℝ₊^{2N} : |z| ≤ ∏ᵢ (xᵢ yᵢ)^{(2i−1)/(2N²)}}`. -/
noncomputable def K_AD (N : ℕ) : Set (Option (Fin N ⊕ Fin N) → ℝ) :=
  {v | (∀ i, 0 ≤ v (some (Sum.inl i))) ∧ (∀ i, 0 ≤ v (some (Sum.inr i))) ∧
    |v none| ≤ ∏ i : Fin N, (v (some (Sum.inl i)) * v (some (Sum.inr i))) ^
      ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2))}

end RobustSAA.Discrete.Supplement


