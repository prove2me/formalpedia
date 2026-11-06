-- Prove2me | Definitions.Def_BlockBochner_bochnerOp
-- name    : BlockBochner_bochnerOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:45.596185+00:00
-- url     : https://prove2.me/theorems/d893d70d-9f77-4596-b19b-971675b2abc6
-- title:
--   The Bochner operator $B=d_0d_0^*+d_1^*d_1$
-- statement:
--   The Bochner operator on $H_1=\bigoplus_iW_i$ is
--   $$B=d_0d_0^*+d_1^*d_1 .$$
--   Its diagonal blocks are $I+\sum_{k\ne i}P_{ik}$ and its off-diagonal $W_j\to W_i$ blocks are $P_iP_j-P_{ij}$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, p.23

import Mathlib
import Definitions.Def_BlockBochner_bochD1

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The Bochner operator `B = d₀ d₀* + d₁* d₁` on `⊕_i W_i`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3, p.23 (also Sec. 1.6,
p.10). Its diagonal blocks are `I + Σ_{k≠i} P_{ik}` and its off-diagonal `W_j → W_i` blocks are
`P_i P_j − P_{ij}`.

**Formalization Note** Adjoints are Hilbert-space adjoints (`ContinuousLinearMap.adjoint`). -/
noncomputable def bochnerOp {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) :
    PiLp 2 (fun i => (W i : Submodule ℝ H)) →L[ℝ] PiLp 2 (fun i => (W i : Submodule ℝ H)) :=
  bochD0 W ∘L ContinuousLinearMap.adjoint (bochD0 W) +
    ContinuousLinearMap.adjoint (bochD1 W) ∘L bochD1 W

end BlockBochner


