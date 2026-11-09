-- Prove2me | Definitions.Def_TranspositionIID_Main_Stationary
-- name    : TranspositionIID_Main_Stationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:04.414892+00:00
-- url     : https://prove2.me/theorems/e2bea3bc-0449-4d69-a364-bf6c5da88ce3
-- title:
--   Transposition stationary weights and partition function
-- statement:
--   For strictly positive requests define
--   $$w_p(\sigma)=\prod_i p_i^{n-\operatorname{position}_\sigma(i)},\quad Z_p=\sum_\sigma w_p(\sigma),\quad \mu_p(\sigma)=w_p(\sigma)/Z_p.$$
--   The partition function is computed from $p$. Positivity, normalization and reversibility are consequences of this construction, not assumptions built into the definition. This stationary law is used only for positive request vectors. Zero-based positions give exponent $n-1-(\sigma i).\mathrm{val}$.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). §2.1, equation (2.1), printed p.3 = PDF p.3

import Definitions.Def_TranspositionIID_Main_ListModel

noncomputable section

namespace TranspositionIID.Main

/-- Explicit weight and normalizing partition function, equation (2.1), p.3. -/
def stationaryWeight {n : ℕ} (p : Fin n → ℝ) (σ : ListState n) : ℝ :=
  ∏ i, p i ^ (n - 1 - (σ i).val)

def partitionFunction {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ σ : ListState n, stationaryWeight p σ

def stationaryLaw {n : ℕ} (p : Fin n → ℝ) (σ : ListState n) : ℝ :=
  stationaryWeight p σ / partitionFunction p

end TranspositionIID.Main


