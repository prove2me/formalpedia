-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_amaProfit
-- name    : SampleMechDesign_Supplement_amaProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:45:23.696483+00:00
-- url     : https://prove2.me/theorems/17c09888-7dee-50da-8b31-aef458b184f4
-- title:
--   Definition A.10 — affine maximizer auctions (AMAs) and their profit
-- statement:
--   An **affine maximizer auction** is a weight $w_j>0$ per buyer and a boost $\lambda(Q)\ge0$ per allocation. On the valuation vector $v$ its allocation $Q^*=(q^*_1,\dots,q^*_n)$ maximizes the weighted social welfare
--   $$
--   \sum_{j=1}^n w_jv_j(q_j)+\lambda(Q)-c(Q).
--   $$
--   Let $Q^{-j}$ maximize $\sum_{\ell\neq j}w_\ell v_\ell(q_\ell)+\lambda(Q)-c(Q)$ over the allocations without buyer $j$'s participation. Buyer $j$ pays
--   $$
--   \frac1{w_j}\Big[\sum_{\ell\ne j}w_\ell v_\ell(q^{-j}_\ell)+\lambda(Q^{-j})-c(Q^{-j})-\Big(\sum_{\ell\ne j}w_\ell v_\ell(q^*_\ell)+\lambda(Q^*)-c(Q^*)\Big)\Big],
--   $$
--   and the profit of the AMA on $v$ is the total payment minus the cost $c(Q^*)$.
--
--   AMAs contain the λ-auctions, the VVCAs and the mixed bundling auctions of this supplement.
--
--   **Formalization Note** "Without buyer $j$'s participation" is read as the allocations giving $j$ nothing, as in the proofs of Lemma A.15 (p.33) and Lemma A.18 (p.35). Only the maximum value enters the payment, so $Q^{-j}$ needs no tie-break; ties for $Q^*$ are broken by a tie-breaking rule that may depend on $v$.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Definition A.10, p.28 (PDF p.28); Section 3.4.3, p.14

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_Alloc

namespace SampleMechDesign.Supplement

open Finset

/-- **Affine maximizer auctions (AMAs).** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6,
Definition A.10, p.28 (and p.14).

An AMA is a weight `w j > 0` per buyer and a boost `λ Q ≥ 0` per allocation. On the valuation
vector `v` its allocation `Q*` maximizes the weighted social welfare
`∑_j w_j v_j(q_j) + λ(Q) − c(Q)` (`amaArgmax`; the tie-breaking rule `tb` picks one maximizer).
`amaWelfareWithout j` is the largest value of `∑_{ℓ ≠ j} w_ℓ v_ℓ(q_ℓ) + λ(Q) − c(Q)` over the
allocations `Q` without buyer `j`'s participation, and buyer `j` pays

`(1 / w_j) · [amaWelfareWithout j − (∑_{ℓ ≠ j} w_ℓ v_ℓ(q*_ℓ) + λ(Q*) − c(Q*))]`.

`amaProfit c tb w λ v` is the total payment minus the cost `c(Q*)` of the allocation.
`IsAMAParam w λ` is the parameter condition `w > 0`, `λ ≥ 0`, and `amaClass` is the class of all
AMAs over valuation vectors.

**Formalization Note.**
* Allocations range over all `(n + 1)^m` assignments of the single-unit items (`Alloc n m`).
* "Without buyer `j`'s participation" is read as the allocations that give `j` nothing
  (`Q.bundle j = ∅`), as in the proofs of Lemma A.15 (p.33, "excluding buyer i") and Lemma A.18
  (p.35, "bidder i receives the empty set"). The printed argmax of Definition A.10 does not say
  over which allocations it ranges.
* Only the value of the maximum enters the payment, so no tie-breaking is needed for `Q^{-j}`;
  ties for `Q*` are broken by `tb`, which may depend on the valuation vector.
* Profit is the payments collected minus the cost of the allocation. -/
noncomputable def amaScore {n m : ℕ} (c : Bundles n m → ℝ) (w : Fin n → ℝ)
    (lam : Alloc n m → ℝ) (v : BVal n m) (Q : Alloc n m) : ℝ :=
  ∑ j, w j * v j (Q.bundle j) + lam Q - c Q.bundles

/-- The maximizers of the weighted, boosted social welfare. -/
noncomputable def amaArgmax {n m : ℕ} (c : Bundles n m → ℝ) (w : Fin n → ℝ)
    (lam : Alloc n m → ℝ) (v : BVal n m) : Finset (Alloc n m) :=
  univ.filter fun Q => ∀ Q', amaScore c w lam v Q' ≤ amaScore c w lam v Q

/-- The AMA allocation `Q*`. -/
noncomputable def amaAllocation {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) (w : Fin n → ℝ) (lam : Alloc n m → ℝ)
    (v : BVal n m) : Alloc n m :=
  tb v (amaArgmax c w lam v)

/-- The weighted, boosted welfare of the buyers other than `j`. -/
noncomputable def amaScoreWithout {n m : ℕ} (c : Bundles n m → ℝ) (j : Fin n) (w : Fin n → ℝ)
    (lam : Alloc n m → ℝ) (v : BVal n m) (Q : Alloc n m) : ℝ :=
  ∑ ℓ ∈ univ.erase j, w ℓ * v ℓ (Q.bundle ℓ) + lam Q - c Q.bundles

/-- The allocation that gives nothing to anybody has no buyer's participation. -/
theorem nonempty_without {n m : ℕ} (j : Fin n) :
    (univ.filter fun Q : Alloc n m => Q.bundle j = ∅).Nonempty :=
  ⟨fun _ => none, by simp [Alloc.bundle]⟩

/-- The largest welfare of the other buyers over the allocations without buyer `j`. -/
noncomputable def amaWelfareWithout {n m : ℕ} (c : Bundles n m → ℝ) (j : Fin n)
    (w : Fin n → ℝ) (lam : Alloc n m → ℝ) (v : BVal n m) : ℝ :=
  (univ.filter fun Q : Alloc n m => Q.bundle j = ∅).sup' (nonempty_without j)
    (amaScoreWithout c j w lam v)

/-- Buyer `j`'s AMA payment. -/
noncomputable def amaPayment {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) (j : Fin n) (w : Fin n → ℝ)
    (lam : Alloc n m → ℝ) (v : BVal n m) : ℝ :=
  (1 / w j) * (amaWelfareWithout c j w lam v -
    amaScoreWithout c j w lam v (amaAllocation c tb w lam v))

/-- Profit of the AMA `(w, λ)` on `v`: total payment minus the cost of the allocation. -/
noncomputable def amaProfit {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) (w : Fin n → ℝ) (lam : Alloc n m → ℝ)
    (v : BVal n m) : ℝ :=
  ∑ j, amaPayment c tb j w lam v - c (amaAllocation c tb w lam v).bundles

/-- AMA parameters: positive weights and nonnegative boosts. -/
def IsAMAParam {n m : ℕ} (w : Fin n → ℝ) (lam : Alloc n m → ℝ) : Prop :=
  (∀ j, 0 < w j) ∧ ∀ Q, 0 ≤ lam Q

/-- The class of AMAs over valuation vectors. -/
def amaClass {n m : ℕ} (c : Bundles n m → ℝ) (tb : BVal n m → Finset (Alloc n m) → Alloc n m) :
    Set (BVal n m → ℝ) :=
  {f | ∃ (w : Fin n → ℝ) (lam : Alloc n m → ℝ), IsAMAParam w lam ∧ f = amaProfit c tb w lam}

end SampleMechDesign.Supplement


