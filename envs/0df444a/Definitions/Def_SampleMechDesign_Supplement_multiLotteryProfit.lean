-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_multiLotteryProfit
-- name    : SampleMechDesign_Supplement_multiLotteryProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:48:30.643808+00:00
-- url     : https://prove2.me/theorems/1cdae44c-9cd8-4993-8005-d689fded244a
-- title:
--   Appendix A.1 — lotteries for multiple unit-demand or additive buyers
-- statement:
--   There are $n$ units of each item and each buyer receives at most one unit of each item. The buyers arrive simultaneously and each buys, from one anonymous length-$\ell$ menu, the lottery that maximizes her expected utility. A point is $(v,z)=(v_1,\dots,v_n,z_1,\dots,z_n)$; buyer $j$ takes $(\varphi_{v_j},p_{v_j})$ and receives the bundle $\sum_{i:\,z_j[i]<\varphi_{v_j}[i]}e_i$, and
--   $$
--   \mathrm{profit}'_M(v,z)=\sum_{j=1}^np_{v_j}-c(Q),
--   $$
--   with $Q$ the profile of these bundles.
--
--   **Formalization Note** Each buyer's ties are broken by her own rule; $c$ is a function of the profile of bundles (which need not be disjoint, since there are $n$ units of each item); every $z_j\in\mathbb R^m$ is accepted.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Appendix A.1, p.31 (PDF p.31)

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_Alloc
import Definitions.Def_SampleMechDesign_Supplement_lotteryProfit

namespace SampleMechDesign.Supplement

open Finset

/-- **Lotteries for multiple unit-demand or additive buyers.** Balcan, Sandholm, Vitercik,
arXiv:1705.00243v6, Appendix A.1, p.31.

There are `n` units of each item and each buyer receives at most one unit of each item. The
buyers arrive simultaneously, and each buys from the same (anonymous) length-`ℓ` menu the lottery
that maximizes her expected utility. A point of the class `M′` is `(v, z)` with `v_j` and `z_j` the
values and the uniform draws of buyer `j`; buyer `j` takes entry `(φ_{v_j}, p_{v_j})` and receives
the bundle `∑_{i : z_j[i] < φ_{v_j}[i]} e_i`, and

`profit′_M(v, z) = ∑_j p_{v_j} − c(Q)`,

where `Q` is the profile of these bundles.

**Formalization Note.** Each buyer's ties are broken by her own rule `tb j`, which may depend on
her values. The cost `c` is a function of the profile of bundles (with `n` units of each item, the
bundles need not be disjoint). Every `z_j ∈ ℝ^m` is accepted, which contains `[0, 1]^m`. -/
noncomputable def multiLotteryProfit {n ℓ m : ℕ} (c : Bundles n m → ℝ)
    (tb : Fin n → (Fin m → ℝ) → Finset (Fin (ℓ + 1)) → Fin (ℓ + 1)) (p : Fin (ℓ * (m + 1)) → ℝ)
    (x : AVal n m × AVal n m) : ℝ :=
  ∑ j, lotteryPrice p (lotteryChoice (tb j) (x.1 j) p) -
    c (fun j => lotteryBundle (tb j) (x.1 j) (x.2 j) p)

end SampleMechDesign.Supplement


