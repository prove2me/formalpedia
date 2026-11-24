-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_OpaqueAlgorithm
-- name    : OpaquePricing_Dominance_Supplement_OpaqueAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:34:42.843477+00:00
-- url     : https://prove2.me/theorems/703f6722-7c39-4029-b36c-ab701880aa24
-- title:
--   Appendix D: reduction of both customer classes to size-valued opaque types
-- statement:
--   For each supported valuation vector $v$ and each size $s=1,\ldots,N$, form its best pessimistic and risk-neutral opaque values by maximizing the published subset valuation over all subsets of size $s$. The two resulting types have weights $\alpha w_j$ and $(1-\alpha)w_j$:
--   $$z^{pess}_{j,s}=\max_{|S|=s}\min_{i\in S}v_{j,i},\qquad z^{rn}_{j,s}=\max_{|S|=s}\frac1s\sum_{i\in S}v_{j,i}.$$
--   Run the same backwards tree on these $2m$ weighted types. Its first returned coordinate is the common item price; later coordinates are the opaque prices by cardinality. Zero-weight types at $\alpha=0,1$ stay in the enumeration without changing revenue. Prices at unused cardinalities are zero. The setup-work annotation explicitly charges the finite-subset computation, and bothPricingWork includes this setup and the complete DP and OPQ enumerations. This connects the generic finite pricing routine to the published menus rather than postulating unrelated optimal prices.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix D, finite customer types and opaque reduction, p. 37; Algorithm 1, p. 38

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Supplement_PriceTree

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

noncomputable section

/-- Best value at size k+1, computed from the published subset valuation functions.
The outside zero affects no maximum on the source's nonnegative profiles. -/
def reducedOpaqueValue {N : ℕ} (v : Fin N → ℝ) (pess : Bool) (k : Fin N) : ℝ :=
  (((opqOptions N).filter (fun S => S.card = k.val + 1)).image
    (fun S => if pess then pessValue v S else rnValue v S) ∪ {0}).max' (by simp)

/-- Both customer classes, including their zero-mass class at the mixture endpoints. -/
def reducedValues {N m : ℕ} (F : FiniteTypes N m)
    (j : Bool × Fin m) : Fin N → ℝ :=
  reducedOpaqueValue (F.values j.2) j.1

def reducedWeights {N m : ℕ} (F : FiniteTypes N m) (α : ℝ)
    (j : Bool × Fin m) : ℝ :=
  (if j.1 then α else 1 - α) * F.weight j.2

def algorithmOPQ {N m : ℕ} (F : FiniteTypes N m) (α : ℝ) : Fin N → ℝ :=
  enumeratePrices (reducedValues F) (reducedWeights F α)

def treeItemPrice {N : ℕ} (p : Fin N → ℝ) : ℝ :=
  if h : 0 < N then p ⟨0, h⟩ else 0

def treeSizePrice {N : ℕ} (p : Fin N → ℝ) (s : ℕ) : ℝ :=
  if h : 0 < s ∧ s ≤ N then p ⟨s - 1, by omega⟩ else 0

/-- Brute finite subset reduction costs only a factor depending on fixed N, not on m.
This includes computing values, filtering cardinalities, and both customer classes. -/
def opaqueSetupWork (N m : ℕ) : ℕ :=
  2 * m * N * 2^N * (5 * N + 5)

def bothPricingWork {N m : ℕ} (F : FiniteTypes N m) : ℕ :=
  enumerationWork F.values + opaqueSetupWork N m + enumerationWork (reducedValues F)

end

end OpaquePricing.Dominance.Supplement


