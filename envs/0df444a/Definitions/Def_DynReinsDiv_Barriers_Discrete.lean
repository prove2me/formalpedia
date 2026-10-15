-- Prove2me | Definitions.Def_DynReinsDiv_Barriers_Discrete
-- name    : DynReinsDiv_Barriers_Discrete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:53.299222+00:00
-- url     : https://prove2.me/theorems/139d9fb5-7d76-42c5-a5a1-8fce342a3cbc
-- title:
--   Discrete claim law ℙ(Z₁ = z_j) = p_j, 0 < z_1 < ⋯ < z_N, Σ p_j = 1 (p. 19)
-- statement:
--   A **discrete claim distribution** with $N\ge1$ atoms consists of claim sizes $0<z_1<z_2<\dots<z_N$ and probabilities $p_1,\dots,p_N>0$ with $\sum_{j=1}^N p_j=1$; the claim $Z_1$ satisfies $\mathbb P(Z_1=z_j)=p_j$. Its law is the measure
--   $$\sum_{j=1}^N p_j\,\delta_{z_j}.$$
--   Section 4 of the paper studies the reinsurance boundaries in this case, one boundary per atom.
--
--   **Formalization Note** Atoms are indexed by `j : Fin N`, starting at $0$, so `z 0` is the paper's $z_1$. The paper's index $i_0$ (the first atom above $1/\lambda$) is not part of the data; the theorems state its role directly.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 19 (discrete claim distribution before Theorem 4.5)

import Mathlib

namespace DynReinsDiv.Barriers

open MeasureTheory

/-- The discrete claim law of p. 19: `ℙ(Z₁ = z_j) = p_j > 0` for `N` atoms
`0 < z_1 < ⋯ < z_N` with `∑ p_j = 1`. Atoms are indexed by `j : Fin N` from `0`, so `z 0` is the
paper's `z₁`. -/
structure DiscreteClaims (N : ℕ) where
  z : Fin N → ℝ
  p : Fin N → ℝ
  N_pos : 0 < N
  z_strictMono : StrictMono z
  z_pos : ∀ j, 0 < z j
  p_pos : ∀ j, 0 < p j
  p_sum : ∑ j, p j = 1

/-- The law `∑_j p_j δ_{z_j}` of a discrete claim distribution. -/
noncomputable def DiscreteClaims.law {N : ℕ} (D : DiscreteClaims N) : Measure ℝ :=
  ∑ j, ENNReal.ofReal (D.p j) • Measure.dirac (D.z j)

end DynReinsDiv.Barriers


