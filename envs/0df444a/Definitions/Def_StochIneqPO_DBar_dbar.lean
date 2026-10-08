-- Prove2me | Definitions.Def_StochIneqPO_DBar_dbar
-- name    : StochIneqPO_DBar_dbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:11.000776+00:00
-- url     : https://prove2.me/theorems/4259aba9-da3c-4cbb-b282-1bc8d7623323
-- title:
--   Sec. 8, p. 910 — Ornstein's d̄-distance
-- statement:
--   For laws $P,Q$ of real-valued two-sided paths, Ornstein's **$\bar d$-distance** is the least expected absolute difference at time zero among stationary joint laws with marginals $P,Q$:
--
--   $$\bar d(P,Q)=\inf_{\substack{\nu\in\mathcal S_S\\\nu_1=P,\,\nu_2=Q}}\int|\omega_1^0-\omega_2^0|\,\nu(d\omega_1,d\omega_2).$$
--
--   Stationarity of the joint law is essential: without it this would compare only the one-time marginals.
--
--   **Formalization Note** The definition has a real-valued infimum. For stationary $P,Q$ with integrable time-zero coordinates, the product coupling makes the defining set nonempty, every cost is integrable, and every cost is nonnegative. Outside that domain, Lean's total real infimum is not asserted to have the paper's meaning.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Sec. 8, p. 910, displayed definition of d̄ (PDF p. 12)

import Mathlib
import Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant

namespace StochIneqPO.DBar

open MeasureTheory

/-- Ornstein's `d̄`, as the infimum of the time-zero cost over stationary couplings. -/
noncomputable def dbar (P Q : Measure (ℤ → ℝ)) : ℝ :=
  sInf {c : ℝ | ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
    IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q ∧
    c = ∫ z, |z.1 0 - z.2 0| ∂ν}

end StochIneqPO.DBar


