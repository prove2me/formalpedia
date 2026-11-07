-- Prove2me | Definitions.Def_TIEMaximin_MechLottery
-- name    : TIEMaximin_MechLottery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:47.192005+00:00
-- url     : https://prove2.me/theorems/d8b720b5-47c0-448d-8fdd-c58612d2443d
-- title:
--   The lotteries the mechanism of §4.4 can produce
-- statement:
--   At a profile $v$, with $\alpha=1/6$, the mechanism proceeds in four steps.
--
--   1. **Reserve.** It samples a 0–1 point of (12), for an order of $D$ by decreasing $1/k_i$, from a lottery with mean exactly $(h,p)$.
--   2. **Compensate.** It forms the suballocation $b$ of that outcome.
--   3. **Round.** It samples an integral suballocation from a lottery with the properties of Lemma 4.3 for $b$.
--   4. **Complete.** It keeps every assignment and gives each unassigned good $g$ with $e_g>0$ to agent $i$ with conditional probability $e_{ig}/e_g$, where $e=x-\bar b$, $\bar b$ is the mean of the rounded suballocation, and $e_g=\sum_i e_{ig}$.
--
--   $L$ is a lottery of the mechanism if it arises from these four steps.
--
--   **Formalization Note** §4.4 fixes the lotteries only through their stated properties, so the mechanism is a relation and the results about it hold for every lottery it allows. The completion is pinned by the conditional probabilities and not by "$L$ implements $x$", so Proposition 5.1 is not true by definition. A separate milestone states that such an $L$ exists.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §4.4, p.22; proof of Lemma 4.4, p.22; Table 2, p.13

import Mathlib
import Definitions.Def_TIEMaximin_Reservation
import Definitions.Def_TIEMaximin_Rounding

namespace TIEMaximin

/-- The residual budget `e_ig = x_ig − b̄_ig` of the completion step (proof of Lemma 4.4, p.22), `b̄`
the mean of the lottery `μ` over integral suballocations (arXiv:2609.35670, version of 2026-11-03,
sha256 4e68de70…). -/
noncomputable def residual {n m : ℕ} (x : Fin n → Fin m → ℝ) (μ : PMF (SubAlloc n m))
    (i : Fin n) (g : Fin m) : ℝ :=
  x i g - subMarginal μ i g

/-- **`L` is a lottery the mechanism of §4.4 can produce at the profile `v`** (p.22), with `α = 1/6`:
1. *Reserve:* `μ₁` is a lottery over 0–1 points of (12), for some order of `D` by decreasing `1/k_i`,
   with mean exactly `(h, p)` (Lemma 4.1).
2. *Compensate, 3. round:* at every outcome `pt`, `μ₂ pt` is a lottery with the three properties of
   Lemma 4.3 for the suballocation `b` of `pt` and the parameters `k_i`.
4. *Complete:* at every supported integral suballocation `A'`, `κ A'` only extends `A'` and assigns each
   unassigned good `g` with `e_g > 0` to agent `i` with probability `e_ig/e_g`, where `e = x − b̄`.
`L` is the resulting composition.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §4.4, p.22; proof of Lemma 4.4, p.22: "Put
e_ig = x_ig − b̄_ig ≥ 0 and e_g = Σ_{i∈N} e_ig. … Whenever it is unassigned and e_g > 0, assign it to
agent i with conditional probability e_ig/e_g … Any finite joint distribution with these conditional
marginals completes the allocation".

**Formalization Note.** §4.4 fixes these lotteries only through their stated properties, so the
mechanism is a relation and the results about it hold for every lottery it allows. The completion is
pinned by the conditional probabilities, never by "`L` implements `x`", so Proposition 5.1 is not true by
definition; `TIEMaximin.mechanism_exists` states that such an `L` exists. `α = 1/6` is the paper's value
(Table 2, p.13). -/
def IsMechLottery {n m : ℕ} (v : Fin n → Fin m → ℝ) (L : PMF (Alloc n m)) : Prop :=
  ∃ (ord : List (Fin n)) (μ₁ : PMF (ResPt n m)) (μ₂ : ResPt n m → PMF (SubAlloc n m))
    (κ : SubAlloc n m → PMF (Alloc n m)),
    IsDOrder (1 / 6) v ord ∧
    (∀ pt ∈ μ₁.support, IsResPoint (1 / 6) v ord pt) ∧
    (∀ i g, expect μ₁ (fun pt => if pt.1 i g = true then 1 else 0) = hRet (1 / 6) v i g) ∧
    (∀ i, expect μ₁ (fun pt => if pt.2 i = true then 1 else 0) = pDef (1 / 6) v i) ∧
    (∀ pt ∈ μ₁.support, IsRounding v (bComp (1 / 6) v pt) (kDef (1 / 6) v) (μ₂ pt)) ∧
    (∀ A' ∈ (μ₁.bind μ₂).support, ∀ A ∈ (κ A').support, ∀ g i, A' g = some i → A g = i) ∧
    (∀ A' ∈ (μ₁.bind μ₂).support, ∀ g, A' g = none →
      0 < ∑ j, residual (xRule v) (μ₁.bind μ₂) j g →
      ∀ i, marginal (κ A') i g =
        residual (xRule v) (μ₁.bind μ₂) i g / ∑ j, residual (xRule v) (μ₁.bind μ₂) j g) ∧
    L = (μ₁.bind μ₂).bind κ

end TIEMaximin


