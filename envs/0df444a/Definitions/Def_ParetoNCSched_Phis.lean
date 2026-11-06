-- Prove2me | Definitions.Def_ParetoNCSched_Phis
-- name    : ParetoNCSched_Phis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:27.314018+00:00
-- url     : https://prove2.me/theorems/0a19433f-06de-44e9-a2f4-374d2ecdfae2
-- title:
--   The layer integrand $\Phi_s(e)=k_s(e)(k_s(e)+1)/2$
-- statement:
--   $$\Phi_s(e)=\frac{k_s(e)\,(k_s(e)+1)}{2}.$$
--   By Lemma A.1, $\Phi(e)=\int_0^\infty\Phi_s(e)\,ds$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma A.1, p.16

import Mathlib
import Definitions.Def_ParetoNCSched_ks

namespace ParetoNCSched

/-- **The layer integrand `Φ_s(e)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma A.1, p.16: "Φ_s(e) = k_s(e)(k_s(e)+1)/2". -/
noncomputable def Phis {n : ℕ} (e : Fin n → ℝ) (s : ℝ) : ℝ :=
  (ks e s : ℝ) * ((ks e s : ℝ) + 1) / 2

end ParetoNCSched


