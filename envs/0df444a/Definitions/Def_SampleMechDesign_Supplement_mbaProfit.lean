-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_mbaProfit
-- name    : SampleMechDesign_Supplement_mbaProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:46:34.504559+00:00
-- url     : https://prove2.me/theorems/817919fa-8dcd-50ee-a585-be9273c31b88
-- title:
--   Appendix A.2 — mixed bundling auctions (MBAs)
-- statement:
--   The **γ-MBA** ($\gamma\ge0$) is the λ-auction whose boost is
--   $$
--   \lambda(Q)=\begin{cases}\gamma&\text{if some buyer receives the grand bundle (all } m \text{ items) under } Q,\\0&\text{otherwise.}\end{cases}
--   $$
--   Buyer $i$ pays $v_i(q^*_i)-\big[(\sum_jv_j(q^*_j)+\lambda(Q^*)-c(Q^*))-(\sum_{j\ne i}v_j(q^{-i}_j)+\lambda(Q^{-i})-c(Q^{-i}))\big]$ (p.33), which is the AMA payment with unit weights. $\mathrm{profit}_v(\gamma)$ is the profit of the γ-MBA on $v$, and the class of MBAs is $\{\mathrm{profit}_{\cdot}(\gamma):\gamma\ge0\}$.
--
--   **Formalization Note** The MBA is the AMA of `amaProfit` with unit weights and the boost above, so it uses the same conventions (allocations of single-unit items, profit = payments minus cost, ties for $Q^*$ broken by a rule).
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Appendix A.2, p.31 (PDF p.31); payments p.33

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_amaProfit

namespace SampleMechDesign.Supplement

open Finset

/-- **Mixed bundling auctions (MBAs).** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6,
Appendix A.2, p.31 (payments p.33).

The `γ`-MBA (`γ ≥ 0`) is the λ-auction (all weights `1`) whose boost is `λ(Q) = γ` if some buyer
receives the grand bundle (all `m` items) under `Q` and `λ(Q) = 0` otherwise. `mbaProfit c tb γ v`
is its profit on the valuation vector `v`: the VCG-style payments of p.33, which are the AMA
payments of Definition A.10 with unit weights, minus the cost of the allocation. `mbaClass c tb`
is the class of MBAs, `{mbaProfit c tb γ : γ ≥ 0}`.

**Formalization Note.** The MBA is the AMA `amaProfit` with `w = 1` and boost `mbaBoost γ`, so it
inherits that definition's conventions: allocations of single-unit items, "without buyer `i`" as
the allocations giving `i` nothing, ties for `Q*` broken by `tb`, and profit equal to the payments
minus the cost. -/
noncomputable def mbaBoost {n m : ℕ} (γ : ℝ) : Alloc n m → ℝ :=
  fun Q => if ∃ j, Q.bundle j = univ then γ else 0

/-- Profit of the `γ`-MBA on `v`. -/
noncomputable def mbaProfit {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) (γ : ℝ) (v : BVal n m) : ℝ :=
  amaProfit c tb (fun _ => 1) (mbaBoost γ) v

/-- The class of MBAs. -/
def mbaClass {n m : ℕ} (c : Bundles n m → ℝ) (tb : BVal n m → Finset (Alloc n m) → Alloc n m) :
    Set (BVal n m → ℝ) :=
  {f | ∃ γ : ℝ, 0 ≤ γ ∧ f = mbaProfit c tb γ}

end SampleMechDesign.Supplement


