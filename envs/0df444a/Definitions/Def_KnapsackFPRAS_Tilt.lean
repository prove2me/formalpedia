-- Prove2me | Definitions.Def_KnapsackFPRAS_Tilt
-- name    : KnapsackFPRAS_Tilt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:52.536094+00:00
-- url     : https://prove2.me/theorems/8a4a498a-f790-4c65-bad8-6253ec727181
-- title:
--   The exponentially tilted distribution $Q^\lambda_v$ and its normalizers
-- statement:
--   Let $v=(v_1,\dots,v_n)$ be real weights and $\lambda$ a real tilt. Define
--
--   $$
--   Z^\lambda_v := \prod_{i=1}^n\bigl(1+e^{-\lambda v_i}\bigr)=\sum_{X\subseteq[n]}e^{-\lambda v(X)},\qquad Q^\lambda_v(X):=\frac{e^{-\lambda v(X)}}{Z^\lambda_v}\quad(X\subseteq[n]),
--   $$
--
--   so that $Q^\lambda_v$ is the product distribution on subsets in which item $i$ is included independently with probability
--
--   $$
--   p^{v,\lambda}_i := \frac{1}{1+e^{\lambda v_i}}.
--   $$
--
--   For a family $\mathcal A$ of subsets, $Q^\lambda_v(\mathcal A)=\sum_{X\in\mathcal A}Q^\lambda_v(X)$. For a capacity $T$ the **rescaled normalizer** is $C^\lambda_v:=e^{\lambda T}Z^\lambda_v=\sum_{X\subseteq[n]}e^{\lambda(T-v(X))}$, and the expected weight of a tilted subset is
--
--   $$
--   \mathbb E_{X\sim Q^\lambda_v}[v(X)] = \sum_{X\subseteq[n]}Q^\lambda_v(X)\,v(X).
--   $$
--
--   These are used with the original weights $v=w$ (Section 3) and with the rounded weights $v=a$ (Section 4).
--
--   **Formalization Note** $Z^\lambda_v$ is defined as the product; it is positive, so $Q^\lambda_v$ is a genuine division. The expectation is the finite sum over all $2^n$ subsets.
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), §3.1, pp.10–11 (PDF pp.11–12); Eq. (13), p.12 (PDF p.13); §4.2, p.16 (PDF p.17)

import Mathlib

set_option autoImplicit false

namespace KnapsackFPRAS

/-! # The tilted distribution

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), §3.1, pp.10–11 (PDF pp.11–12), Eq. (13), p.12 (PDF p.13), and
§4.2 "Exponential tilting of the rounded instance", p.16 (PDF p.17).

**Formalization Note.** All quantities are defined for a real weight vector `v : Fin n → ℝ` and a
real tilt `λ`, so that the same definitions serve the original weights (`fun i => (w i : ℝ)`)
and the rounded weights `a`. `Z` is defined as the product `∏ᵢ (1 + e^{−λvᵢ})`; the page's sum
over subsets equals it. `Z > 0`, so `Q` is a genuine division. The expectation
`E_{X∼Q}[v(X)]` is the finite sum over all subsets `∑_X Q(X) v(X)`. -/

namespace Tilt

/-- `Z^λ_v := ∏_{i=1}^n (1 + e^{−λ vᵢ})` (= `∑_{X ⊆ [n]} e^{−λ v(X)}`). -/
noncomputable def Z {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∏ i, (1 + Real.exp (-(lam * v i)))

/-- `Q^λ_v(X) := e^{−λ v(X)} / Z^λ_v`. -/
noncomputable def Q {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) (X : Finset (Fin n)) : ℝ :=
  Real.exp (-(lam * ∑ i ∈ X, v i)) / Z v lam

/-- `Q^λ_v(𝒜) := ∑_{X ∈ 𝒜} Q^λ_v(X)` for a family `𝒜` of subsets. -/
noncomputable def QFam {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) (𝒜 : Finset (Finset (Fin n))) : ℝ :=
  ∑ X ∈ 𝒜, Q v lam X

/-- `p^{v,λ}_i := 1 / (1 + e^{λ vᵢ})`, the probability that item `i` is included under `Q^λ_v`. -/
noncomputable def p {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) (i : Fin n) : ℝ :=
  1 / (1 + Real.exp (lam * v i))

/-- The rescaled normalizer `C^λ_v := e^{λT} Z^λ_v`. -/
noncomputable def Cnorm {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) (T : ℝ) : ℝ :=
  Real.exp (lam * T) * Z v lam

/-- `E_{X∼Q^λ_v}[v(X)] = ∑_{X ⊆ [n]} Q^λ_v(X) · v(X)`, the left side of (13). -/
noncomputable def expWeight {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ X : Finset (Fin n), Q v lam X * ∑ i ∈ X, v i

end Tilt

end KnapsackFPRAS


