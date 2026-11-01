-- Prove2me | Definitions.Def_CongestionTaxes_IsCorrelatedEq
-- name    : CongestionTaxes_IsCorrelatedEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:03.928102+00:00
-- url     : https://prove2.me/theorems/4e71129b-b363-4ff8-9205-9a62d06e2498
-- title:
--   Correlated equilibrium of a cost-minimization game
-- statement:
--   In a game with players $i$, strategy sets $S_i$ and costs $C_i$, a **correlated equilibrium** is a probability distribution $\sigma$ over strategy profiles such that for every player $i$ and every deviation rule $\varphi:S_i\to S_i$,
--
--   $$
--   \mathbb E_{s\sim\sigma}\bigl[C_i(s)\bigr]\le\mathbb E_{s\sim\sigma}\bigl[C_i(\varphi(s_i),s_{-i})\bigr].
--   $$
--
--   A constant rule gives the coarse correlated condition, so correlated equilibria are coarse correlated.
--
--   **Formalization Note** Distributions are finitely supported weights of total mass $1$, with the published `RobustPoA.Static.IsDist` and `RobustPoA.Static.expect`, the same vocabulary as the published coarse correlated equilibrium `RobustPoA.Static.IsCCE`.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, p.4 and footnote 3, p.4 (citing Roughgarden 2015)

import Mathlib
import Definitions.Def_RobustPoA_Static_Distribution

namespace CongestionTaxes

/-- A **correlated equilibrium** of a cost-minimization game (Paccagnan, Gairing,
arXiv:2105.07480v2, p.4 and footnote 3, citing Roughgarden 2015): a probability distribution `σ`
over strategy profiles such that no player `i` lowers its expected cost by applying a fixed
deviation rule `φ : S_i → S_i` to the recommendation it receives,
`E_{s∼σ}[C_i(s)] ≤ E_{s∼σ}[C_i(φ(s_i), s_{−i})]`.

**Formalization Note** Distributions and expectations are the published
`RobustPoA.Static.IsDist` and `RobustPoA.Static.expect` (finitely supported weights of total mass
`1`), the same vocabulary as the published coarse correlated equilibrium `RobustPoA.Static.IsCCE`.
A constant rule `φ` is a coarse deviation, so every correlated equilibrium is coarse
correlated. -/
def IsCorrelatedEq {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (σ : (∀ i, S i) →₀ ℝ) : Prop :=
  RobustPoA.Static.IsDist σ ∧ ∀ (i : ι) (φ : S i → S i),
    RobustPoA.Static.expect σ (C i) ≤
      RobustPoA.Static.expect σ (fun s => C i (Function.update s i (φ (s i))))

end CongestionTaxes


