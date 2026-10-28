-- Prove2me | Definitions.Def_MultPacing_Existence_Limit
-- name    : MultPacing_Existence_Limit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:54.271101+00:00
-- url     : https://prove2.me/theorems/c2aba5db-3985-4520-9684-bdd309f404bb
-- title:
--   Proof of Theorem 1, p. 12 — a sequence of equilibria of smoothed games (ϵ^l → 0, H^l → ∞) and its limit point
-- statement:
--   This packages the setting of the proof of Theorem 1. Fix a pacing game $(v,B)$. The data are
--
--   1. sequences $\epsilon^l>0$ and $H^l$ ($l\in\mathbb N$) and a number $M$ with $\sum_j v_{ij}+2\epsilon^l\le M$ for every buyer $i$ and every $l$, and $H^l>M/\epsilon^l$;
--   2. $\epsilon^l\to0$ and $H^l\to\infty$;
--   3. for every $l$, a pure-strategy Nash equilibrium $\alpha^l$ of the $(\epsilon^l,H^l)$-smoothed pacing game, with allocations $x^l_{ij}$, prices $p^l_{ij}$ and payments $s^l_{ij}=x^l_{ij}p^l_{ij}$;
--   4. limits $\alpha^*_i=\lim_l\alpha^l_i$, $x^*_{ij}=\lim_l x^l_{ij}$, $p^*_{ij}=\lim_l p^l_{ij}$ and $s^*_{ij}=\lim_l s^l_{ij}$.
--
--   The paper obtains such a convergent sequence by passing to a subsequence of the equilibria given by Theorem 2 (all the quantities lie in a compact set) and then shows, in four claims, that the limit point is a pacing equilibrium of the original game.
--
--   **Formalization Note** The proposition `IsSmoothedLimit` records the convergent sequence directly (the paper's "replace the sequence by this subsequence"). Limits are in $\mathbb R$; $\alpha^l\to\alpha^*$ is convergence in the product topology on $\mathbb R^N$. The limiting price is indexed by buyer and good, $p^*_{ij}$, like the smoothed price.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 12 (PDF 12), proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

open Filter Topology

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

/-- The setting of the proof of Theorem 1 (p. 12): a sequence of smoothed versions `(ε_l, H_l)` of the
pacing game `P` with `H_l > M/ε_l`, `ε_l → 0` and `H_l → ∞`, where `M` bounds every buyer's
`∑_j v_ij + 2ε_l`; a pure-strategy Nash equilibrium `α_l` of the `l`-th smoothed game; and limits
`αs`, `xs`, `ps`, `ss` of the multipliers, allocations `x^l_ij`, prices `p^l_ij` and payments
`s^l_ij` along the sequence. -/
structure IsSmoothedLimit (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ)
    (αs : N → ℝ) (xs ps ss : N → G → ℝ) : Prop where
  eps_pos : ∀ l, 0 < ε l
  M_bound : ∀ l i, ∑ j, P.v i j + 2 * ε l ≤ M
  H_gt : ∀ l, M / ε l < H l
  eps_tendsto : Tendsto ε atTop (𝓝 0)
  H_tendsto : Tendsto H atTop atTop
  equilibrium : ∀ l, IsSmoothedPNE P (ε l) (H l) (α l)
  alpha_tendsto : Tendsto α atTop (𝓝 αs)
  alloc_tendsto : ∀ i j, Tendsto (fun l => smAlloc P (ε l) (α l) i j) atTop (𝓝 (xs i j))
  price_tendsto : ∀ i j, Tendsto (fun l => smPrice P (ε l) (α l) i j) atTop (𝓝 (ps i j))
  pay_tendsto : ∀ i j, Tendsto (fun l => smPay P (ε l) (α l) i j) atTop (𝓝 (ss i j))

end MultPacing.Existence


