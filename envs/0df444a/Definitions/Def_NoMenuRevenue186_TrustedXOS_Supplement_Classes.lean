-- Prove2me | Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Classes
-- name    : NoMenuRevenue186_TrustedXOS_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:03:25.512298+00:00
-- url     : https://prove2.me/theorems/2b10dc5d-dbe9-4ca6-9b2d-757e1d0c1814
-- title:
--   Gross-substitutes and additive instances, finite-precision priors, seller-BIC
-- statement:
--   These predicates extend the published model of the mission (finite outer law $\mathcal D$ over finite seller priors $D$ on valuations of $n$ items; protocols given by a public binary tree, a seller strategy $s_D$ depending only on $D$ and a buyer strategy $b_v$ depending only on $v$).
--
--   1. **Gross-substitutes instance.** Section 2.1 fixes this class as "gross-substitutes valuations, and specifically positive multiples of matroid rank functions". An instance is gross-substitutes when every supported valuation $v$ is normalized, nonnegative and monotone and $v=c\cdot r$ for a real $c>0$ and the rank function $r$ of a matroid whose ground set is all $n$ items.
--   2. **Additive instance.** Every supported valuation has nonnegative item values $w_1,\dots,w_n$ with $v(T)=\sum_{a\in T}w_a$ for every bundle $T$.
--   3. **Finite-precision priors.** Every prior $D$ in the (finite) public class assigns a rational probability to every valuation in its support.
--   4. **Seller-BIC** (eq. (2.1)). For every prior $D\in\operatorname{supp}(\mathcal D)$ and every complete seller strategy $s$ on the fixed tree,
--
--   $$\mathbb E_{v\sim D}\bigl[p(s,b_v)\bigr]\le\mathbb E_{v\sim D}\bigl[p(s_D,b_v)\bigr].$$
--
--   The strategy $s$ may imitate the prescription of another prior, take off-path branches, or react adaptively to the buyer's bits; the buyer plays the prescribed $b_v$.
--
--   The first two predicates name the valuation classes of Theorems 3.2, 3.4 and 3.5; the last two are the strategic-seller requirements of Section 2.2.
--
--   **Formalization Note** The matroid rank predicate is the published `DSICHardRev.IsMatroidRankFn` and additivity is the published `FairShares.IsAdditive`. Expectations are finite sums over the finite supports.
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed pp.8, 10, PDF pp.10, 12, Sections 2.1–2.2, eq. (2.1)

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Auction
import Definitions.Def_FairShares_IsAdditive

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Gross-substitutes instances in the sense Section 2.1 fixes (printed p.8, PDF p.10):
    "Gross-substitutes valuations, and specifically positive multiples of matroid rank
    functions". Every supported valuation is a valuation and equals `c · r` for a real
    `c > 0` and the rank function `r` of a matroid on all `n` items. -/
def GSInstance {n : ℕ} (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support, ∀ v ∈ D.law.support, IsValuation v ∧
    ∃ c : ℝ, 0 < c ∧ ∃ r : Bundle n → ℝ, DSICHardRev.IsMatroidRankFn r ∧ ∀ T, v T = c * r T

/-- Additive instances (Section 2.1, printed p.8): every supported valuation has
    nonnegative item values `w` with `v T = ∑_{a ∈ T} w a` (published `FairShares.IsAdditive`). -/
def AdditiveInstance {n : ℕ} (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support, ∀ v ∈ D.law.support, FairShares.IsAdditive v

/-- Finite-precision seller priors (Section 2.2, printed p.10): every prior in the finite
    public class assigns a rational probability to every valuation in its support. -/
def FinitePrecisionPriors {n : ℕ} (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support, ∀ v ∈ D.law.support, ∃ q : ℚ, (D.law v).toReal = (q : ℝ)

/-- Seller Bayesian incentive compatibility, eq. (2.1), printed p.10 (PDF p.12): for every
    prior `D` in the public class and every complete seller strategy `s` on the fixed tree
    (imitation of another prior, off-path branches, adaptive reactions to buyer bits), the
    expected payment over `v ∼ D` under prescribed buyer play is at most that of `s_D`. -/
def SellerBIC {n : ℕ} (P : Protocol n) (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support, ∀ s : Strategy,
    D.expect (fun v => (P.tree.run s (P.buyer v) []).payment) ≤
      D.expect (fun v => (P.outcome D v).payment)

end NoMenuRevenue186.TrustedXOS.Supplement


