-- Prove2me | Definitions.Def_BassokSubstitution_Profit
-- name    : BassokSubstitution_Profit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:15:17.913486+00:00
-- url     : https://prove2.me/theorems/65873ae0-bd49-4fad-8a1c-497226d344a0
-- title:
--   Expected profit $P(x,y)$ (Eq. (2)) and the demand hypotheses
-- statement:
--   Let $x \in \mathbb R^N$ be the starting inventory, $y$ the inventory after ordering, and $F$ the joint law of the demand vector $D = (D_1,\dots,D_N)$. The expected single-period profit is
--   $$P(x, y) = -\sum_{k=1}^N c_k (y_k - x_k) + \int_{\mathbb R^N} G(y, d)\, dF(d),$$
--   the ordering cost plus the expected optimal allocation profit.
--
--   The demand laws used in the mission are products $F = \nu_1 \otimes \dots \otimes \nu_N$ of marginal laws $\nu_i$ (independent demand classes). The predicate **DemandLaw** asks that every $\nu_i$ gives zero mass to $(-\infty, 0)$ (demands are nonnegative), has a finite mean, and is absolutely continuous with respect to Lebesgue measure (class $i$ has a density $f_i$). The predicate **FullSupport** asks that $\nu_i((a,b)) > 0$ for all $0 \le a < b$, i.e. every nonempty open interval of $[0,\infty)$ has positive probability.
--
--   The profit $P$ is the objective of the ordering problem $I(x) = \max_{y \ge x} P(x,y)$ of Eq. (1).
--
--   **Formalization Note.** `profit M μ x y` takes the joint demand law `μ` as a parameter; the theorems instantiate it with `Measure.pi ν`. The paper states only that class $i$ has "marginal density $f_i$"; independence, nonnegativity, finite means and full support are hypotheses the paper's proofs use without stating (independence for the product formulas of Lemma 3 and the proof in Appendix B, finite means for $P$ to be finite, densities for differentiability, full support for the optimal level $\bar y(x)$ to be unique). Each theorem states which of them it assumes.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 633, §2.1 (marginal densities) and p. 634, Eqs. (1)–(2)

import Mathlib
import Definitions.Def_BassokSubstitution_Allocation

namespace BassokSubstitution

open MeasureTheory

variable {N : ℕ}

/-- Expected single-period profit, Eq. (2):
`P(x, y) = -∑_k c_k (y_k - x_k) + ∫ G(y, d) dF(d)`, where `x` is the starting inventory,
`y` the inventory after ordering, and `μ` the joint law of the demand vector. -/
noncomputable def Model.profit (M : Model N) (μ : Measure (Fin N → ℝ)) (x y : Fin N → ℝ) : ℝ :=
  -(∑ k, M.c k * (y k - x k)) + ∫ d, M.G y d ∂μ

/-- Standing hypotheses on the marginal demand laws `ν i` (the joint law is the product
`Measure.pi ν`, i.e. independent classes): each demand is nonnegative almost surely, has
finite mean, and has a density (is absolutely continuous w.r.t. Lebesgue measure). -/
def DemandLaw (ν : Fin N → Measure ℝ) : Prop :=
  ∀ i, ν i (Set.Iio 0) = 0 ∧ Integrable id (ν i) ∧ ν i ≪ volume

/-- Every marginal demand law charges every nonempty open interval of `[0, ∞)`:
`ν i (a, b) > 0` whenever `0 ≤ a < b`. -/
def FullSupport (ν : Fin N → Measure ℝ) : Prop :=
  ∀ i (a b : ℝ), 0 ≤ a → a < b → 0 < ν i (Set.Ioo a b)

end BassokSubstitution


