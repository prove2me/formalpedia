-- Prove2me | Definitions.Def_MNLStability_greedyLengths
-- name    : MNLStability_greedyLengths
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:24.980016+00:00
-- url     : https://prove2.me/theorems/70ff29f4-1871-4c27-8650-0b4cf1e01fbd
-- title:
--   The interval-length estimates $\tilde m_\ell$ and the step vector $\tilde V^{\mathrm{step}}$
-- statement:
--   Let $r_1\ge\dots\ge r_m$ be the prices of $I$ in order, and $\tau_1,\tau_2,\dots$ thresholds (in §4.4, $\tau_\lambda=\tilde{\mathcal R}_{\ell_\lambda}/\tilde{\mathcal E}_{\ell_\lambda}$).
--
--   1. $\tilde m_{\ell_1}$ is the minimal index with $\sum_{i=1}^{\tilde m_{\ell_1}}r_i\ge\tau_1$; given it, $\tilde m_{\ell_2}$ is the minimal index with $\sum_{i=\tilde m_{\ell_1}+1}^{\tilde m_{\ell_1}+\tilde m_{\ell_2}}r_i\ge\tau_2$; and so on. The construction fails if some minimal index does not exist.
--   2. Given levels $H(\ell_1),H(\ell_2),\dots$ and lengths $\tilde m_{\ell_1},\tilde m_{\ell_2},\dots$, the **step vector** $\tilde V^{\mathrm{step}}$ stocks the first $\tilde m_{\ell_1}$ products of $I$ at level $H(\ell_1)$, the next $\tilde m_{\ell_2}$ at level $H(\ell_2)$, and so on, and $0$ on the remaining products (and outside $I$).
--
--   These are the objects of Lemmas 8 and 9 and of the enumeration of Theorem 3.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §4.4, p.22

import Mathlib

namespace MNLStability

variable {n : ℕ}

/-- The least `k` (with `k ≤ rs.length`) such that the first `k` entries of `rs` sum to at least `τ`,
or `none` if there is none. -/
noncomputable def leastPrefix (rs : List ℝ) (τ : ℝ) : Option ℕ :=
  (List.range (rs.length + 1)).find? fun k => decide (τ ≤ (rs.take k).sum)

/-- The interval-length estimates `m̃_{ℓ₁}, m̃_{ℓ₂}, …` of SSRN:3498325, §4.4, p.22: given the prices
`rs = (r₁, …, r_m)` of `I` in order and the thresholds `τ_λ = R̃_{ℓ_λ}/Ẽ_{ℓ_λ}`, `m̃_{ℓ₁}` is the
minimal index with `Σ_{i=1}^{m̃_{ℓ₁}} r_i ≥ τ₁`, `m̃_{ℓ₂}` the minimal one with
`Σ_{i=m̃_{ℓ₁}+1}^{m̃_{ℓ₁}+m̃_{ℓ₂}} r_i ≥ τ₂`, and so on. `none` when some minimal index does not exist
(the products of `I` run out). -/
noncomputable def greedyLengths : List ℝ → List ℝ → Option (List ℕ)
  | _, [] => some []
  | rs, τ :: τs =>
    match leastPrefix rs τ with
    | none => none
    | some k => (greedyLengths (rs.drop k) τs).map (k :: ·)

/-- The step vector `Ṽ^step` of §4.4, p.22: along `ord` (the products of `I` by non-increasing
price), the first `ks₁` products get level `levels₁`, the next `ks₂` get `levels₂`, and so on; the
remaining products of `ord`, and all products outside `ord`, get `0`. -/
def stepVec (ord : List (Fin n)) (levels ks : List ℕ) : Fin n → ℕ := fun i =>
  if i ∈ ord then
    ((levels.zip ks).flatMap fun p => List.replicate p.2 p.1).getD (ord.idxOf i) 0
  else 0

end MNLStability


