-- Prove2me | Definitions.Def_CompDesignBFM_pot
-- name    : CompDesignBFM_pot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:38.80072+00:00
-- url     : https://prove2.me/theorems/41a13cd0-2c32-4919-a755-9824272fd569
-- title:
--   Potential function
-- statement:
--   The **potential** is
--
--   $$\Phi^F_c(S)=F(S)\prod_{i\in S}\Bigl(1-\frac{c_i}{B}\Bigr)_+,$$
--
--   where $(x)_+=\max\{x,0\}$ and the empty product is one. Its maximizer is the allocation of the marginal-contribution branch.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §3.2, p.15 (PDF 17)

import Mathlib

namespace CompDesignBFM

/-- The potential `Φ^F_c(S) = F(S) ∏_(i ∈ S) (1 - cᵢ/B)₊` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §3.2, p.15, PDF 17).
**Formalization Note.** The positive part is `max _ 0`. The empty product is one, as on p.12. -/
noncomputable def pot {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  F S * ∏ i ∈ S, max (1 - c i / B) 0

end CompDesignBFM


