-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_wy
-- name    : ParetoNCSched_Supplement_wy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:33:43.212791+00:00
-- url     : https://prove2.me/theorems/8da2292b-82bc-485f-8790-13c83cf6ab8e
-- title:
--   The predicted position $w_y(s)$
-- statement:
--   For predicted sizes $y\in(0,\infty)^n$ let $n_s=|\{j:y_j>s\}|$ and $\omega_s=n_s(n_s+1)/2$. Then
--
--   $$w_y(s)=\frac{1}{\Phi(y)}\int_0^s\omega_u\,du,$$
--
--   the fraction of the predicted optimum $\Phi(y)=\sum_j y_j+\sum_{i<j}\min(y_i,y_j)$ paid by the layers below $s$. It is continuous and non-decreasing, $w_y(0)=0$, $w_y(\max_j y_j)=1$, and strictly increasing on $[0,\max_j y_j]$.
--
--   **Formalization Note** $n_s$ and $\Phi$ are the base mission's `ns` and `Phi`, applied to $y$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 4.5, p.13; Appendix H, Notation, p.39

import Mathlib
import Definitions.Def_ParetoNCSched_ns
import Definitions.Def_ParetoNCSched_Phi

namespace ParetoNCSched.Supplement

/-- **The predicted position `w_y(s)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 4.5, p.13, and Appendix H, Notation, p.39:
"ns = |{j : yj > s}|, ωs = ns(ns + 1)/2 = Φs(y), wy(s) = (1/Φ(y)) ∫₀ˢ ωu du", the fraction of the
predicted optimum `Φ(y)` paid by the layers below `s`.

**Formalization Note.** `n_s` is the base mission's `ParetoNCSched.ns` applied to `y`, `Φ` the
base `ParetoNCSched.Phi`; the integral is an interval integral from `0` to `s`. -/
noncomputable def wy {n : ℕ} (y : Fin n → ℝ) (s : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..s, ((ns y u : ℝ) * ((ns y u : ℝ) + 1) / 2)) / Phi y

end ParetoNCSched.Supplement


