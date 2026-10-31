-- Prove2me | Definitions.Def_DynTargetMV_Market_rho
-- name    : DynTargetMV_Market_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:19.154172+00:00
-- url     : https://prove2.me/theorems/ff3efb54-d6d5-40f3-9701-65bf26f2dd76
-- title:
--   $\rho(t)=b(t)^\top(\sigma(t)\sigma(t)^\top)^{-1}b(t)$, (2.1)
-- statement:
--   The squared market price of risk
--   $$
--   \rho(t):=b(t)^\top\bigl(\sigma(t)\sigma(t)^\top\bigr)^{-1}b(t).
--   $$
--   It enters the conditions (2.13) and (2.15) of Theorem 1 (iii).
--
--   **Formalization Note** Assumption 1 (ii) makes the matrix invertible, so Mathlib's matrix inverse takes no junk value here.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.1), p.6

import Definitions.Def_DynTargetMV_Market

open Matrix

namespace DynTargetMV

/-- `ρ(t) := b(t)⊤(σ(t)σ(t)⊤)⁻¹b(t)`, (2.1). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.1), p.6.

**Formalization Note** The matrix inverse is Mathlib's, whose junk value on singular matrices is
excluded by Assumption 1 (ii). -/
noncomputable def Market.rho {m d n : ℕ} (M : Market m d n) (t : ℝ) : ℝ :=
  M.b t ⬝ᵥ ((M.σ t * (M.σ t)ᵀ)⁻¹ *ᵥ M.b t)

end DynTargetMV


