-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_GloballyAsymptoticallyStable
-- name    : IncentiveFinNet_Supplement_GloballyAsymptoticallyStable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:29:10.628907+00:00
-- url     : https://prove2.me/theorems/be64b54a-71a5-5055-b90b-f033b9d9e3ea
-- title:
--   Global asymptotic stability of pairwise negotiations (Definition 6)
-- statement:
--   Pairwise negotiations with dampening factor $\eta$ are **globally asymptotically stable** for a network setting (Definition 6) if for every skew-symmetric initial price matrix $P(0)$ there is a matrix $P^\star$ with
--
--   $$
--   \lim_{t\to\infty}\|P(t)-P^\star\|_F = 0,
--   $$
--
--   where $P(t)$ are the iterates of Algorithm 1 and $\|X\|_F = \bigl(\sum_{i,j}X_{ij}^2\bigr)^{1/2}$ is the Frobenius norm.
--
--   Theorem 4 gives a range of $\eta$ for which this holds.
--
--   **Formalization Note** Definition 6 says "for any initial price matrix $P(0)$"; Algorithm 1 starts from "any skew-symmetric matrix", and the text after Definition 6 uses that every $P(t)$ is skew-symmetric, so the initial matrices here are the skew-symmetric ones. The Frobenius norm is the published `DDROCS.frobNorm`.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Definition 6 (Global Asymptotic Stability), p.14; Algorithm 1, line 3, p.14

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_DDROCS_frobNorm
import Definitions.Def_IncentiveFinNet_Supplement_negotiate

open Matrix Filter Topology

namespace IncentiveFinNet.Supplement

/-- **Definition 6 (Global Asymptotic Stability)**, Jalan, Chakrabarti, Sarkar,
arXiv:2212.06808v3, p.14: "The pairwise negotiation process is globally asymptotically stable for a
given network setting and dampening factor `η` if, for any initial price matrix `P(0)`, there
exists a matrix `P⋆` such that the sequence of price matrices `P(t)` converges to `P⋆` in Frobenius
norm: `lim_{t→∞} ‖P(t) − P⋆‖_F = 0`."

**Formalization Note**
* `P(t)` is `negotiate S η P₀ t` (Algorithm 1). The initial price matrices are the skew-symmetric
  ones: Algorithm 1, line 3 (p.14), starts from "any skew-symmetric matrix", and the paragraph after
  Definition 6 uses that each `P(t)` is skew-symmetric.
* `‖·‖_F` is the published `DDROCS.frobNorm`, `√(Σ_{i,j} X_ij²)`. -/
def GloballyAsymptoticallyStable {n : ℕ} (S : NetworkSetting n) (η : ℝ) : Prop :=
  ∀ P₀ : Matrix (Fin n) (Fin n) ℝ, P₀ᵀ = -P₀ →
    ∃ Pstar : Matrix (Fin n) (Fin n) ℝ,
      Tendsto (fun t => DDROCS.frobNorm (negotiate S η P₀ t - Pstar)) atTop (𝓝 0)

end IncentiveFinNet.Supplement


