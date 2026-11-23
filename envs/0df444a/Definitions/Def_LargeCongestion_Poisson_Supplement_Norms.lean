-- Prove2me | Definitions.Def_LargeCongestion_Poisson_Supplement_Norms
-- name    : LargeCongestion_Poisson_Supplement_Norms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:29:59.010433+00:00
-- url     : https://prove2.me/theorems/f8853313-c5c5-458a-b2fb-5ffcf8b51c41
-- title:
--   §6 — Euclidean load distance, l1 demand distance, scalar L² error and exact theta in (31)
-- statement:
--   For resource vectors $v$ and demand vectors $d,d'$, use
--   $$\|v\|_2=\sqrt{\sum_ev_e^2},\qquad\|d'-d\|_1=\sum_t|d'_t-d_t|.$$
--   For a resource load induced by an independent weighted mixed profile, the scalar error is
--   $$\|X_e-\hat x_e\|_{L^2}=\sqrt{\mathbb E[(X_e-\hat x_e)^2]}.$$
--   The exact constant of Theorem 5 is
--   $$\theta=\sqrt{d_{\max}/4}+\sqrt{\kappa d_{\max}(2c'_{\max}+Ld_{\max}/4)/c'_{\min}}.$$
--   These definitions distinguish the Euclidean resource error from Lean's default sup norm on function spaces, and distinguish scalar random-variable L² error from a vector norm. All expectations here are finite outcome sums. The constant follows the theorem on p. 25 and its proof (41)–(44), rather than the inconsistent glossary entry.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 24–25, Proposition 2 and (31); pp. 33–34, (41)–(44)

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_Weighted

namespace LargeCongestion.Poisson.Supplement

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

/-- Euclidean resource norm, not the default sup norm on a function type. -/
noncomputable def loadNorm (x : E → ℝ) : ℝ := Real.sqrt (∑ e, (x e) ^ 2)

def demandDistance (d d' : T → ℝ) : ℝ := ∑ t, |d' t - d t|

/-- Exact constant in (31), p. 25 and (41)–(44), pp. 33–34. -/
noncomputable def theta (dmax cmin cmax L κ : ℝ) : ℝ :=
  Real.sqrt (dmax / 4) + Real.sqrt (κ * dmax * (2 * cmax + L * dmax / 4) / cmin)

/-- Scalar L² error, p. 25: sqrt(E[(X_e - xhat_e)^2]). The outcome space is finite. -/
noncomputable def wL2Error {N : ℕ} (w : Fin N → ℝ) (σ : Fin N → Finset E → ℝ)
    (e : E) (xhat : ℝ) : ℝ :=
  Real.sqrt (wExpect σ (fun a => (wLoad w a e - xhat) ^ 2))

end LargeCongestion.Poisson.Supplement


