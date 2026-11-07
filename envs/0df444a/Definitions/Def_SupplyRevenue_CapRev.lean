-- Prove2me | Definitions.Def_SupplyRevenue_CapRev
-- name    : SupplyRevenue_CapRev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:24.80309+00:00
-- url     : https://prove2.me/theorems/5f2342af-7194-4dda-9233-85b0f21de8da
-- title:
--   The capped source benchmark $A_\delta$
-- statement:
--   An item-pricing **source** gives each buyer a finite mixture of offers, drawn independently of type. Let $X_i$ be buyer $i$'s full-stock demand and $s_i=p_i(X_i)$ its payment. The source has revenue $R=\sum_i E[s_i]$ and marginals $x_{ij}=\Pr[j\in X_i]$. It meets the aggregate caps $\delta$ when $\sum_i x_{ij}\le\delta$ for each item $j$. Then
--
--   $$A_\delta(D)=\sup\Bigl\{\sum_i E[s_i] : \text{sources with }\sum_i x_{ij}\le\delta\ \ \forall j\Bigr\}.$$
--
--   This is the relaxation whose revenue the mission compares with actual single-copy revenue.
--
--   **Formalization Note** The caps count actual demand, including free items taken by the residual order. The supremum is an extended nonnegative real.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, p.2

import Mathlib
import Definitions.Def_SupplyRevenue_Buyer

open scoped ENNReal

namespace SupplyRevenue

/-!
# The capped source benchmark `A_δ`

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§1.1, p.2: "A_δ(D) is the full-stock source item-pricing revenue supremum with aggregate item caps δ."

**Formalization Note** A source is one finite mixture of offers per buyer (reading R4), and all demand is full-stock
(`S = Finset.univ`). The caps count actual demand, including free items taken by the residual order. The supremum is in
`ℝ≥0∞` (R9); it is never over an empty set when `δ ≥ 0`, since the empty offer has zero marginals. Payments are
nonnegative, so `ENNReal.ofReal` loses nothing.
-/

/-- An item-pricing source: per buyer, a finite mixture of offers, independent of type. -/
abbrev Source (n m : ℕ) := Fin n → Mix (Offer m)

/-- The full-stock demand `X` of type `θ` at offer `o`. -/
noncomputable def fullDemand {m : ℕ} (tie : Tie m) (b : Buyer m) (o : Offer m)
    (θ : Fin b.numTypes) : Finset (Fin m) :=
  demand tie (b.val θ) o Finset.univ

/-- `E[f(s)]` over a single buyer's source draw and type, with `s = p(X)` the full-stock payment. -/
noncomputable def sourceStat {m : ℕ} (tie : Tie m) (b : Buyer m) (μ : Mix (Offer m))
    (f : ℝ → ℝ) : ℝ :=
  μ.E fun o => b.E fun θ => f (o.pay (fullDemand tie b o θ))

/-- The revenue `R = Σ_i E[s_i]` of a source. -/
noncomputable def sourceRev {n m : ℕ} (tie : Tie m) (D : Instance n m) (σ : Source n m) : ℝ :=
  ∑ i, sourceStat tie (D i) (σ i) id

/-- The source marginal `x_ij = P[j ∈ X_i]`, over source draw and type. -/
noncomputable def sourceMarginal {m : ℕ} (tie : Tie m) (b : Buyer m) (μ : Mix (Offer m))
    (j : Fin m) : ℝ :=
  μ.E fun o => b.E fun θ => if j ∈ fullDemand tie b o θ then 1 else 0

/-- The source meets the aggregate item caps `δ`: `Σ_i x_ij ≤ δ` for each item. -/
def FeasibleSource {n m : ℕ} (tie : Tie m) (D : Instance n m) (δ : ℝ) (σ : Source n m) : Prop :=
  ∀ j, ∑ i, sourceMarginal tie (D i) (σ i) j ≤ δ

/-- `A_δ(D)`: the supremum over cap-`δ` sources of the full-stock revenue (p.2). -/
noncomputable def capRev {n m : ℕ} (tie : Tie m) (D : Instance n m) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (σ : Source n m) (_ : FeasibleSource tie D δ σ), ENNReal.ofReal (sourceRev tie D σ)

end SupplyRevenue


