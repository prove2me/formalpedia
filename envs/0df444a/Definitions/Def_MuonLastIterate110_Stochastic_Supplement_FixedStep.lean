-- Prove2me | Definitions.Def_MuonLastIterate110_Stochastic_Supplement_FixedStep
-- name    : MuonLastIterate110_Stochastic_Supplement_FixedStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:37:11.696783+00:00
-- url     : https://prove2.me/theorems/570f80f4-1804-444c-bc92-9e47d48f48d0
-- title:
--   Fixed-step Muon setting and computed Lyapunov potential
-- statement:
--   Let $S$ be a Muon run on real $m\times n$ matrices, with loss $F$, stabilizer $\varepsilon$, $J$ Newton–Schulz iterations, deterministic initial points $W_1,M_0$, and schedules $\beta_t,\theta_t,\eta_t$. Write $u_J$ for the maximum amplification of the published Newton–Schulz polynomial, and $L$ for the smoothness constant. The fixed-step setting comprises $J\ge1$, $\varepsilon>0$, $0\le\beta<1$, $0\le\theta\le1$ and
--
--   $$
--   0<\eta\le\frac{\varepsilon(1-\beta)}{4Lu_J},\qquad
--   (\beta_t,\theta_t,\eta_t)=(\beta,\theta,\eta)\quad(t\ge1).
--   $$
--
--   For any perturbation sequence $\zeta_t$ driving the published recursion, put $e_t=M_t-\nabla F(W_t)$, $\alpha=1-\beta$, and define
--
--   $$
--   \kappa=\varepsilon/u_J,\qquad V_t=F(W_t)+\frac{2\eta}{\kappa\alpha}\|e_t\|_F^2.
--   $$
--
--   The predicate records the standing setting and the imposed step condition (4.2). Objective regularity is a separate Assumption 3.1 hypothesis in every result. Exact gradients use $\zeta_t=0$; the predicate itself also serves the perturbed theorem. The potential is computed from the trajectory and contains no decrease or convergence assumption.
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.7, §4, (4.1)–(4.2); p.16, Lemma B.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Muon

open Filter Topology MeasureTheory
open scoped ENNReal

namespace MuonLastIterate110.Stochastic.Supplement

/-- The fixed-step setting of §4, p.7, including the imposed condition (4.2).
The perturbation sequence is supplied separately: exact gradients use the zero sequence. -/
def FixedStep {m n : ℕ} (S : Muon m n) (L β θ η : ℝ) : Prop :=
  1 ≤ S.J ∧ 0 < S.ε ∧ 0 ≤ β ∧ β < 1 ∧ 0 ≤ θ ∧ θ ≤ 1 ∧ 0 < η ∧
    η ≤ S.ε * (1 - β) / (4 * L * uJ S.J) ∧
    ∀ t : ℕ, 1 ≤ t → S.β t = β ∧ S.θ t = θ ∧ S.η t = η

/-- κ = ε/u_J, as in (4.1). -/
noncomputable def kappa {m n : ℕ} (S : Muon m n) : ℝ := S.ε / uJ S.J

/-- The computed potential of Lemma B.1, p.16, for a run driven by ζ.
Here α = 1 − β; this definition assumes no decrease or summability conclusion. -/
noncomputable def lyapunov {m n : ℕ} (S : Muon m n) (β η : ℝ)
    (ζ : ℕ → Mat m n) (t : ℕ) : ℝ :=
  S.F (S.W ζ t) + (2 * η / (kappa S * (1 - β))) * ‖S.e ζ t‖ ^ 2

end MuonLastIterate110.Stochastic.Supplement


