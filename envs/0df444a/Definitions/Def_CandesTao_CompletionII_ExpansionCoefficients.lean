-- Prove2me | Definitions.Def_CandesTao_CompletionII_ExpansionCoefficients
-- name    : CandesTao_CompletionII_ExpansionCoefficients
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:53:36.536067+00:00
-- url     : https://prove2.me/theorems/4b9a4b0a-3bdf-4c80-bfa5-f679c5188219
-- title:
--   Coefficient sequences $\alpha^{(k)}, \beta^{(k)}, \gamma^{(k)}, \delta^{(k)}$ of Lemma 8.1
-- statement:
--   Fix real numbers $p$ and $\rho'$. The sequences $\alpha^{(k)}_j, \beta^{(k)}_j, \gamma^{(k)}_j, \delta^{(k)}_j$ ($k, j \ge 0$) start from $\alpha^{(0)}_0 = 1$, with every other value at $k = 0$ equal to $0$, and satisfy
--   $$\alpha_j^{(k+1)} = \left[\alpha_{j-1}^{(k)} + (1-\rho')\gamma_{j-1}^{(k)}\right] + \frac{\rho'(1-2p)}{p}\left[\alpha_j^{(k)} + (1-\rho')\gamma_j^{(k)}\right] + 1_{j=0}\,\rho'\left[\beta_0^{(k)} + (1-\rho')\delta_0^{(k)}\right],$$
--   $$\beta_j^{(k+1)} = \left[\beta_{j-1}^{(k)} + (1-\rho')\delta_{j-1}^{(k)}\right] + \frac{\rho'(1-2p)}{p}\left[\beta_j^{(k)} + (1-\rho')\delta_j^{(k)}\right]1_{j>0} + 1_{j=0}\,\rho'\frac{1-p}{p}\left[\alpha_0^{(k)} + (1-\rho')\gamma_0^{(k)}\right],$$
--   $$\gamma_j^{(k+1)} = \frac{\rho'(1-p)}{p}\left[\alpha_{j+1}^{(k)} + (1-\rho')\gamma_{j+1}^{(k)}\right], \qquad \delta_j^{(k+1)} = \frac{\rho'(1-p)}{p}\left[\beta_{j+1}^{(k)} + (1-\rho')\delta_{j+1}^{(k)}\right],$$
--   where a term with index $j - 1 = -1$ is $0$.
--
--   These are the coefficients of the expansion (VIII.2) of $(\mathcal{Q}_\Omega\mathcal{P}_T)^k\mathcal{Q}_\Omega$ in powers of $\mathcal{Q}_\Omega\mathcal{Q}_T$ (Lemma 8.1). The recurrence keeps $\alpha^{(k)}_j$ zero for $j > k$, $\beta^{(k)}_j$ zero for $j > k-1$, $\gamma^{(k)}_j$ zero for $j > k-2$ and $\delta^{(k)}_j$ zero for $j > k-3$. This is the paper's convention that each sequence vanishes outside the index range of (VIII.2).
--
--   **Formalization Note** The four sequences at step $k$ are bundled in a structure with fields `α β γ δ : ℕ → ℝ`, and `expansionCoeffs p ρ' k` is defined by recursion on $k$. The definition is for arbitrary reals $p, \rho'$. The paper uses $p = m/n^2$ and $\rho' = 2r/n - (r/n)^2$, and the theorems that use it substitute those values. Division by $p = 0$ is Lean's $x/0 = 0$, but every theorem using the sequences assumes $p > 0$.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2078, Lemma 8.1 (recurrence relations and range convention)

import Mathlib.Data.Real.Basic

namespace CandesTao.CompletionII

/-- The four coefficient sequences `α^{(k)}, β^{(k)}, γ^{(k)}, δ^{(k)}` of Lemma 8.1
of Candès–Tao at a fixed `k`, each indexed by `j ∈ ℕ`. -/
structure ExpansionCoeffs where
  α : ℕ → ℝ
  β : ℕ → ℝ
  γ : ℕ → ℝ
  δ : ℕ → ℝ

/-- `f_{j-1}` with the convention `f_{-1} = 0`. -/
def shiftDown (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else f (j - 1)

/-- The recurrence of Lemma 8.1 (Candès–Tao, p. 2078), taking the sequences at `k`
to the sequences at `k + 1`, for sampling parameter `p` and `ρ'`:

* `α^{(k+1)}_j = [α_{j-1} + (1-ρ')γ_{j-1}] + ρ'(1-2p)/p [α_j + (1-ρ')γ_j]
    + 1_{j=0} ρ' [β_0 + (1-ρ')δ_0]`,
* `β^{(k+1)}_j = [β_{j-1} + (1-ρ')δ_{j-1}] + ρ'(1-2p)/p [β_j + (1-ρ')δ_j] 1_{j>0}
    + 1_{j=0} ρ'(1-p)/p [α_0 + (1-ρ')γ_0]`,
* `γ^{(k+1)}_j = ρ'(1-p)/p [α_{j+1} + (1-ρ')γ_{j+1}]`,
* `δ^{(k+1)}_j = ρ'(1-p)/p [β_{j+1} + (1-ρ')δ_{j+1}]`,

where the right-hand sides are at step `k` and index `-1` means `0`. -/
noncomputable def ExpansionCoeffs.step (p ρ' : ℝ) (c : ExpansionCoeffs) : ExpansionCoeffs where
  α := fun j =>
    (shiftDown c.α j + (1 - ρ') * shiftDown c.γ j) +
      ρ' * (1 - 2 * p) / p * (c.α j + (1 - ρ') * c.γ j) +
      (if j = 0 then ρ' * (c.β 0 + (1 - ρ') * c.δ 0) else 0)
  β := fun j =>
    (shiftDown c.β j + (1 - ρ') * shiftDown c.δ j) +
      (if 0 < j then ρ' * (1 - 2 * p) / p * (c.β j + (1 - ρ') * c.δ j) else 0) +
      (if j = 0 then ρ' * (1 - p) / p * (c.α 0 + (1 - ρ') * c.γ 0) else 0)
  γ := fun j => ρ' * (1 - p) / p * (c.α (j + 1) + (1 - ρ') * c.γ (j + 1))
  δ := fun j => ρ' * (1 - p) / p * (c.β (j + 1) + (1 - ρ') * c.δ (j + 1))

/-- The coefficient sequences of Lemma 8.1 at step `k`, starting from `α^{(0)}_0 = 1`
and every other value at `k = 0` equal to `0`.  The recurrence keeps every sequence
zero outside the index range of (VIII.2) (`α^{(k)}_j` for `j ≤ k`, `β^{(k)}_j` for
`j ≤ k-1`, `γ^{(k)}_j` for `j ≤ k-2`, `δ^{(k)}_j` for `j ≤ k-3`), which is the
paper's convention. -/
noncomputable def expansionCoeffs (p ρ' : ℝ) : ℕ → ExpansionCoeffs
  | 0 => ⟨fun j => if j = 0 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  | k + 1 => (expansionCoeffs p ρ' k).step p ρ'

end CandesTao.CompletionII


