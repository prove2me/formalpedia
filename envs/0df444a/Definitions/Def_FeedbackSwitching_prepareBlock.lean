-- Prove2me | Definitions.Def_FeedbackSwitching_prepareBlock
-- name    : FeedbackSwitching_prepareBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:37.687305+00:00
-- url     : https://prove2.me/theorems/bb641767-5b23-4bf5-9c14-d81e9cbcca43
-- title:
--   PrepareBlock (Algorithm 3): $q$, $p=(1-4\kappa)w+4\kappa q$, $x=(p+q)/2$, $\Psi_s=C_wQ_s/p_s$
-- statement:
--   Given smoothed weights $w$, a base rate $\kappa$ and an assignment $((Q_s)_s,\rho)$ (in the algorithm, a solution of the LP (19) with anchor $w$), PrepareBlock returns
--   $$
--   q=\rho\Big/\sum_j\rho_j,\qquad p=(1-4\kappa)w+4\kappa q,\qquad x=\frac{p+q}{2},\qquad \Psi_s=\frac{C_wQ_s}{p_s}.
--   $$
--   $p$ is the sampling law, $x$ the refresh law and $\Psi_s$ the estimation matrices of the block.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Algorithm 3, p.23 (PDF p.25); Eq. (20), p.20

import Mathlib
import Definitions.Def_FeedbackSwitching_centering
open Matrix

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

Normalized source weights `q = ρ / ∑_j ρ_j` (Definition 3; Algorithm 3, line 2). -/
noncomputable def prepQ {K : ℕ} (ρ : Fin K → ℝ) : Fin K → ℝ :=
  fun s => ρ s / ∑ j, ρ j

/-- Sampling law `p = (1 − 4κ) w + 4κ q` (Algorithm 3, line 3; Lemma 7). -/
noncomputable def prepP {K : ℕ} (κ : ℝ) (w ρ : Fin K → ℝ) : Fin K → ℝ :=
  fun s => (1 - 4 * κ) * w s + 4 * κ * prepQ ρ s

/-- Refresh law `x = (p + q)/2` (Algorithm 3, line 3; Lemma 7). -/
noncomputable def prepX {K : ℕ} (κ : ℝ) (w ρ : Fin K → ℝ) : Fin K → ℝ :=
  fun s => (prepP κ w ρ s + prepQ ρ s) / 2

/-- **PrepareBlock** (Algorithm 3, p.23 = PDF p.25; Eq. (20)): estimation matrices
`Ψ_s = C_w Q_s / p_s`, from an assignment `((Q_s)_s, ρ)` (in the algorithm, a solution of the LP
(19) with anchor `w`). Together with `prepP` and `prepX` this is the output `(p, x, (Ψ_s)_s)`. -/
noncomputable def prepareBlock {K : ℕ} (κ : ℝ) (w : Fin K → ℝ)
    (z : (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ)) : Fin K → Matrix (Fin K) (Fin K) ℝ :=
  fun s => (prepP κ w z.2 s)⁻¹ • (centering w * z.1 s)

end FeedbackSwitching


