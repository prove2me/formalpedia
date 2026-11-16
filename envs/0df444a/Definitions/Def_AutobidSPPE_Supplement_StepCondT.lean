-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_StepCondT
-- name    : AutobidSPPE_Supplement_StepCondT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:55:40.260027+00:00
-- url     : https://prove2.me/theorems/b9b107e9-d87e-4146-9f80-7052e0103d3d
-- title:
--   Separated step condition (63)
-- statement:
--   For a certificate value $m$, steps $\tau$ satisfy the **separated step condition** if, for some fixed ordering of the bidders,
--   $$
--   0<\tau_1\le b_0^{-1},\qquad 0<\tau_i\le\delta\,\tau_{i-1}\quad(2\le i\le n),
--   $$
--   with $b_0,\delta$ from (62).
--
--   **Formalization Note** "For any fixed bidder ordering" is a permutation $\sigma$ of the bidders: the $k$-th bidder in the order is $\sigma(k)$ (0-based).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (63), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_b0T
import Definitions.Def_AutobidSPPE_Supplement_deltaT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The separated step condition (63) for the throttling hierarchy: for some fixed ordering of
the bidders, `0 < τ₁ ≤ b₀⁻¹` and `0 < τᵢ ≤ δ τᵢ₋₁` (`2 ≤ i ≤ n`), with `b₀`, `δ` from (62) for the certificate
value `m` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (63), p.28).

**Formalization Note** "For any fixed bidder ordering" is an ordering `σ` of `Fin n` (a permutation); the
`k`-th bidder in the order is `σ k` (0-based). -/
def StepCondT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) (τ : Fin n → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), (∀ i, 0 < τ i) ∧
    (∀ i : Fin n, i.val = 0 → τ (σ i) ≤ 1 / b0T vhat ρ m) ∧
    ∀ i j : Fin n, i.val = j.val + 1 → τ (σ i) ≤ deltaT vhat ρ m * τ (σ j)

end AutobidSPPE.Supplement


