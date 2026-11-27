-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_vvcaBoost
-- name    : SampleMechDesign_Supplement_vvcaBoost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:46:06.703811+00:00
-- url     : https://prove2.me/theorems/0762151c-2446-4895-9aea-23aaba782117
-- title:
--   Section 3.4.3 — VVCAs and λ-auctions
-- statement:
--   A **virtual valuation combinatorial auction (VVCA)** is an AMA whose boost splits into one term per buyer,
--   $$
--   \lambda(Q)=\sum_{j=1}^n\lambda_j(Q),\qquad \lambda_j(Q)=c_{j,q}\ \text{ for every allocation } Q \text{ that gives buyer } j \text{ exactly bundle } q .
--   $$
--   A **λ-auction** is an AMA with $w_1=\dots=w_n=1$. The definition also gives the classes of AMAs, λ-auctions and VVCAs as functions on additive valuation vectors, for a cost function and a tie-breaking rule; these are the classes of the sample-complexity lower bounds of Appendix A.3.
--
--   **Formalization Note** As an AMA, a VVCA has $\lambda(Q)\ge0$ for every $Q$; the constants $c_{j,q}$ are otherwise unconstrained.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Section 3.4.3, p.14 (PDF p.14); Appendix A.3, p.36

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_amaProfit

namespace SampleMechDesign.Supplement

open Finset

/-- **VVCAs and λ-auctions.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, Section 3.4.3,
p.14.

A virtual valuation combinatorial auction (VVCA) is an AMA whose boost splits into one term per
buyer, `λ(Q) = ∑_j λ_j(Q)`, where `λ_j(Q) = c_{j,q}` for every allocation `Q` giving buyer `j`
exactly bundle `q`; `vvcaBoost cc` is that boost for the constants `cc j q = c_{j,q}`. A
λ-auction is an AMA with `w_1 = ⋯ = w_n = 1`.

The classes below are the AMAs, the λ-auctions and the VVCAs as functions on additive valuation
vectors (`additiveVal`), for a cost function `c` and a tie-breaking rule `tb`.

**Formalization Note.** A VVCA is an AMA, so its boost satisfies `λ(Q) ≥ 0` for every `Q`
(`IsAMAParam`); the individual constants `c_{j,q}` are otherwise unconstrained. The classes are
restricted to additive valuations because the sample-complexity lower bounds of Appendix A.3
hold "even when the bidders' valuation functions are additive" (p.36). -/
def vvcaBoost {n m : ℕ} (cc : Fin n → Finset (Fin m) → ℝ) : Alloc n m → ℝ :=
  fun Q => ∑ j, cc j (Q.bundle j)

/-- AMAs as functions on additive valuation vectors. -/
def amaAdditiveClass {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) : Set (AVal n m → ℝ) :=
  {f | ∃ (w : Fin n → ℝ) (lam : Alloc n m → ℝ), IsAMAParam w lam ∧
    f = fun v => amaProfit c tb w lam (additiveVal v)}

/-- λ-auctions (all weights `1`) as functions on additive valuation vectors. -/
def lambdaAuctionClass {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) : Set (AVal n m → ℝ) :=
  {f | ∃ lam : Alloc n m → ℝ, (∀ Q, 0 ≤ lam Q) ∧
    f = fun v => amaProfit c tb (fun _ => 1) lam (additiveVal v)}

/-- VVCAs as functions on additive valuation vectors. -/
def vvcaClass {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) : Set (AVal n m → ℝ) :=
  {f | ∃ (w : Fin n → ℝ) (cc : Fin n → Finset (Fin m) → ℝ), IsAMAParam w (vvcaBoost cc) ∧
    f = fun v => amaProfit c tb w (vvcaBoost cc) (additiveVal v)}

end SampleMechDesign.Supplement


