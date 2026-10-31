-- Prove2me | Definitions.Def_MinBuying_ExchangeableConstruction
-- name    : MinBuying_ExchangeableConstruction
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T17:34:57.092231+00:00
-- url     : https://prove2.me/theorems/81f91143-f8b1-4584-ad2b-32fe080adf52
-- title:
--   Explicit finite exchangeable instance for the logarithmic pricing gap
-- statement:
--   For $n$ items indexed by $i=0,\ldots,n-1$, define ascending designated prices $r_i=4^i$, type probabilities $\lambda_i=(3/8)4^{-i}$, and type sizes $k_i=\max\{1,\lfloor n/[2(i+1)]\rfloor\}$. Conditional on type $i$, choose a $k_i$-element subset uniformly from all such subsets of the items, give its coordinates valuation $2r_i$, and give all other coordinates valuation zero. Allocate probability $(1+4^{-n})/2$ to the all-zero vector. The joint law is defined explicitly as a finite sum of scaled Dirac measures. This is the manuscript construction with the item/type indexing reversed. The generic auxiliary function uniformAtoms averages Dirac masses indexed by a finite set, counting repeated atom values with multiplicity; its value for an empty index set is the zero measure.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Theorem 3 construction, ec5–ec7 (PDF pp.32–34), with ascending rather than descending price indices.

import Definitions.Def_MinBuying_Symmetry

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace MinBuying

/-- Finite uniform mixture of Dirac masses, allowing repeated atom values. -/
def uniformAtoms {α β : Type*} [MeasurableSpace β]
    (s : Finset α) (f : α → β) : Measure β :=
  (s.card : ℝ≥0∞)⁻¹ • ∑ x ∈ s, Measure.dirac (f x)

/-- Reversed indexing of the construction on ec5: item i has price 4^i. -/
def gapPrices (n : ℕ) : Prices n := fun i => (4 : ℝ)^i.val

def gapTypeSize (n : ℕ) (i : Fin n) : ℕ := max 1 (n / (2*(i.val+1)))

def gapSubsets (n : ℕ) (i : Fin n) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard (gapTypeSize n i)

def gapValuation (n : ℕ) (i : Fin n) (S : Finset (Fin n)) : Valuations n :=
  fun j => if j ∈ S then 2*(4 : ℝ)^i.val else 0

def gapTypeLaw (n : ℕ) (i : Fin n) : JointLaw n :=
  uniformAtoms (gapSubsets n i) (gapValuation n i)

def gapTypeWeight (n : ℕ) (i : Fin n) : ℝ := (3/8 : ℝ)*(1/4 : ℝ)^i.val

def gapZeroWeight (n : ℕ) : ℝ := (1+(1/4 : ℝ)^n)/2

/-- The explicit finitely supported exchangeable witness from Theorem 3.
The remaining probability is allocated to the all-zero valuation vector. -/
def exchangeableGapLaw (n : ℕ) : JointLaw n :=
  ENNReal.ofReal (gapZeroWeight n) • Measure.dirac (fun _ : Fin n => (0 : ℝ)) +
  ∑ i : Fin n, ENNReal.ofReal (gapTypeWeight n i) • gapTypeLaw n i

end MinBuying


