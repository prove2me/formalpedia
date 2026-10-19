-- Prove2me | Definitions.Def_WFMFG_Conv_Simplex
-- name    : WFMFG_Conv_Simplex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:59.824006+00:00
-- url     : https://prove2.me/theorems/76219a92-c73f-4371-8611-6f3e2f56d0f8
-- title:
--   Notation, pp. 5–6 — interior of the simplex $\mathcal S_{d-1}$ and the intrinsic derivatives $\mathfrak d_i$, $\mathfrak d^2_{j,k}$
-- statement:
--   Let $d \ge 1$ and identify the probability measures on $[\![d]\!] = \{1, \dots, d\}$ with the simplex
--   $\mathcal S_{d-1} = \{p \in \mathbb R^d : p_i \ge 0,\ \sum_i p_i = 1\}$.
--
--   1. The **interior of the simplex** is $\{p \in \mathbb R^d : p_i > 0 \text{ for all } i,\ \sum_i p_i = 1\}$; it is relatively open in the affine hyperplane $\{q \in \mathbb R^d : \sum_i q_i = 1\}$, which is also recorded.
--   2. For a real function $h$ and a point $p$, the **intrinsic derivative** is
--   $$
--   \mathfrak d_i h(p) = \frac1d \sum_{m \in [\![d]\!]} \partial_{e_i - e_m} h(p),
--   $$
--   where $\partial_v h(p)$ is the derivative of $s \mapsto h(p + s v)$ at $s = 0$. Since $\partial_{e_j - e_i} h$ is the partial derivative $\partial_{p_j}\hat h^i$ of $h$ written in the chart that eliminates the coordinate $p_i$, this is the paper's $\mathfrak d_i h(p) = -\frac1d\sum_{j \ne i}\partial_{p_j}\hat h^i(p^{-i})$. When $h$ is differentiable on the simplex one has $\sum_i \mathfrak d_i h = 0$ and $\mathfrak d_i h - \mathfrak d_j h = \partial_{e_i - e_j} h$.
--   3. The **second-order intrinsic derivative** is $\mathfrak d^2_{j,k} h(p) = \mathfrak d_j(\mathfrak d_k h)(p)$.
--
--   These are the derivatives in which the master equation (2.3) is written. At interior points they depend only on the values of $h$ on the simplex.
--
--   **Formalization Note.** The derivative along a direction is Mathlib's `lineDeriv`, which returns $0$ where the derivative does not exist. The regularity class `WFReg` (in `WFMFG.Conv.Setting`) therefore requires differentiability explicitly.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, pp. 5–6, Notation, Derivatives on the simplex

import Mathlib

open Finset

namespace WFMFG.Conv

/-- The relative interior of the probability simplex `S_{d-1} ⊂ ℝ^d`: all coordinates are
positive and they sum to one (the paper's `Int(Ŝ_{d-1})`, in the full-coordinate chart). -/
def simplexInt (d : ℕ) : Set (Fin d → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

/-- The affine hyperplane `{q ∈ ℝ^d : ∑ q_i = 1}` that carries the simplex. Differentiability
"on `S_{d-1}`" (p. 6) is differentiability within this hyperplane. -/
def affPlane (d : ℕ) : Set (Fin d → ℝ) :=
  {q | ∑ i, q i = 1}

/-- The intrinsic derivative `𝔡_i h(p)` of pp. 5–6:
`𝔡_i h(p) = (1/d) ∑_m ∂_{e_i - e_m} h(p) = -(1/d) ∑_{j ≠ i} ∂_{p_j} ĥ^i(p^{-i})`. -/
noncomputable def sD {d : ℕ} (h : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ) (i : Fin d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ m, lineDeriv ℝ h p (Pi.single i 1 - Pi.single m 1)

/-- The second-order intrinsic derivative `𝔡²_{j,k} h(p) = 𝔡_j (𝔡_k h)(p)`. -/
noncomputable def sD2 {d : ℕ} (h : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ) (j k : Fin d) : ℝ :=
  sD (fun q => sD h q k) p j

end WFMFG.Conv


