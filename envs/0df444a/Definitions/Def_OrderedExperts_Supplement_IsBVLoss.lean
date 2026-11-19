-- Prove2me | Definitions.Def_OrderedExperts_Supplement_IsBVLoss
-- name    : OrderedExperts_Supplement_IsBVLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:43:18.080931+00:00
-- url     : https://prove2.me/theorems/f39d8bcf-d581-4288-be69-df4c2be8e168
-- title:
--   Bounded-variation loss on the active chain
-- statement:
--   A loss $\ell:A\to[0,1]$ is a **BV loss** on the current active chain $x_1<\cdots<x_m$ if
--
--   $$
--   \sum_{j=2}^{m}\left|\ell(x_j)-\ell(x_{j-1})\right|\le 1.
--   $$
--
--   This is the per-round loss class of the BV problem.
--
--   **Formalization Note** The range bound holds on the entire action space; total variation is computed only along the distinct active recommendations. The variation of a singleton chain is the empty sum, hence zero.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 2.1, p. 5

import Definitions.Def_OrderedExperts_chainPt

open Finset

namespace OrderedExperts.Supplement

/-- **A bounded-variation loss on the current active chain.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 2.1, p. 5.

The loss takes values in `[0,1]` on the action space and its total variation along the increasing
list of distinct current recommendations is at most one.

**Formalization Note.** The range condition is global, while total variation is imposed on the
finite active chain.  Ranks are the base mission's 1-based ranks, and the empty variation sum for a
singleton chain is zero. -/
def IsBVLoss {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ}
    (current : Fin n → A) (loss : A → ℝ) : Prop :=
  let rs : ℕ → Fin n → A := fun _ ↦ current
  let m := chainSize rs 0
  (∀ x, 0 ≤ loss x ∧ loss x ≤ 1) ∧
    ∑ j ∈ Icc 2 m, |loss (chainPt rs 0 j) - loss (chainPt rs 0 (j - 1))| ≤ 1

end OrderedExperts.Supplement


