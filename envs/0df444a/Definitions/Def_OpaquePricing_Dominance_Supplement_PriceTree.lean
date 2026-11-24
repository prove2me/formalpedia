-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_PriceTree
-- name    : OpaquePricing_Dominance_Supplement_PriceTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:33:56.87928+00:00
-- url     : https://prove2.me/theorems/daa7a9d3-1d8a-4202-856f-28c35ff4f3f0
-- title:
--   Algorithm 1: backwards candidate tree, full revenue scan, return and operation count
-- statement:
--   For a finite table of nonnegative valuation vectors $v_j\in\mathbb R^N$ with weights $w_j$, the backwards tree starts with a no-sale cap $B=1+\max(0,\max_{j,i}v_{j,i})$. At coordinate $i$, each assigned suffix has a no-sale child and one child for every nonnegative critical price
--   $$p_i=v_{j,i}-\max\bigl(0,\max_{t>i}(v_{j,t}-p_t)\bigr).$$
--   Earlier coordinates keep the cap until assigned. The return is the highest-revenue leaf, selected by an explicit fold with a cached incumbent score. Each score scans every type and every option, maximizing utility and then price against the outside option. The finite law is the weighted sum of Dirac measures of the given FiniteTypes data; no optimizer is supplied as input.
--
--   The real-RAM work annotation charges cap preparation, every candidate extension, every full-support leaf evaluation and each incumbent comparison/copy. A type-option scan has eight padded scalar operation slots, followed by multiplication and addition per type. Per parent, critical-price scans and child copies cost at most $m(5N+8)+N+3$ slots. Branch multiplicities are retained, as in the proof's tree; the separate distinctScanWork counts only the mandatory type visits after free deduplication. The runtimeValues family and its uniform law supply distinct positive, exchangeable two-item inputs for testing the runtime claim.
--
--   **Formalization Note** The no-sale cap implements the proof's infinity branch with finite nonnegative prices and negative utility at every supported type. Real arithmetic and comparison have unit cost, as in the source's operation count; this is not a bit-complexity claim. Negative critical prices are discarded because the published model permits only nonnegative prices. No sorted-price pruning or revenue oracle is assumed.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix D, Algorithm 1 and proof of Theorem 7, pp. 37–38

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Supplement_FiniteTypes

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

noncomputable section

/-- The actual finite valuation law, not a variable constrained by its desired properties. -/
def finiteLaw {N m : ℕ} (F : FiniteTypes N m) : Measure (Fin N → ℝ) :=
  ∑ j, ENNReal.ofReal (F.weight j) • Measure.dirac (F.values j)

/-- A finite implementation of the proof's infinity/no-purchase branch. -/
def noSalePrice {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → Fin N → ℝ) : ℝ :=
  1 + ((Finset.univ.image (fun ji : ι × Fin N => v ji.1 ji.2)) ∪ {0}).max'
    (by simp)

/-- A one-pass utility/price maximum, starting with the outside option (0,0). -/
def scanPayment {N : ℕ} (v p : Fin N → ℝ) : ℝ :=
  ((List.finRange N).foldl (fun best i =>
    let u := v i - p i
    if best.1 < u ∨ (best.1 = u ∧ best.2 < p i) then (u, p i) else best)
    (0, 0)).2

/-- Explicit full-support evaluation: no revenue oracle is assumed. -/
def scanRevenue {ι : Type*} [Fintype ι] {N : ℕ}
    (v : ι → Fin N → ℝ) (w : ι → ℝ) (p : Fin N → ℝ) : ℝ :=
  ∑ j, w j * scanPayment (v j) p

/-- Starting at the last coordinate, extend each suffix by the no-sale branch and every
nonnegative support-derived critical price. Lists retain branch multiplicity. Earlier,
unassigned coordinates still carry the no-sale cap. -/
def priceTree {ι : Type*} [Fintype ι] {N : ℕ}
    (v : ι → Fin N → ℝ) : ℕ → List (Fin N → ℝ)
  | 0 => [fun _ => noSalePrice v]
  | s + 1 =>
    if h : s < N then
      (priceTree v s).flatMap (fun p =>
        let i : Fin N := ⟨N - 1 - s, by omega⟩
        p :: (Finset.univ.toList.filterMap (fun j =>
          let r := v j i - cheaperUtility p (v j) i
          if 0 ≤ r then some (Function.update p i r) else none)))
    else priceTree v s

/-- Return the best enumerated leaf, caching the incumbent's score. -/
def enumeratePrices {ι : Type*} [Fintype ι] {N : ℕ}
    (v : ι → Fin N → ℝ) (w : ι → ℝ) : Fin N → ℝ :=
  ((priceTree v N).foldl (fun best p =>
    let score := scanRevenue v w p
    if best.2 < score then (p, score) else best)
    ((fun _ => noSalePrice v), 0)).1

/-- Costed real-RAM implementation. Each option scan is padded to eight primitive slots;
each weighted type contributes multiplication and addition. Input reads, comparisons,
list cells and copying an N-vector have unit cost per scalar. The cap is computed once.
At a parent, scan each type's later utilities and form/copy its proposed child.
The fixed charges dominate these individual operations, independently of values. -/
def treeGenerationWork {ι : Type*} [Fintype ι] {N : ℕ}
    (v : ι → Fin N → ℝ) : ℕ → ℕ
  | 0 => 2 * Fintype.card ι * N + N + 1
  | s + 1 => treeGenerationWork v s +
      if s < N then
        (priceTree v s).length * (Fintype.card ι * (5 * N + 8) + N + 3)
      else 0

/-- Total generation plus a full type scan at EVERY leaf and the argmax comparison/copy. -/
def enumerationWork {ι : Type*} [Fintype ι] {N : ℕ}
    (v : ι → Fin N → ℝ) : ℕ :=
  treeGenerationWork v N +
    (priceTree v N).length * (Fintype.card ι * (8 * N + 2) + N + 2)

def algorithmDP {N m : ℕ} (F : FiniteTypes N m) : Fin N → ℝ :=
  enumeratePrices F.values F.weight

/-- The candidates used in the distinct-leaf lower bound also satisfy descending prices.
For k≥1 the 2k vectors are (b_l,l) and (l,b_l), l=1,...,k,
where b_l=4k²+l(k+1). Every vector is a distinct positive profile. -/
def runtimeValues (k : ℕ) (j : Fin (2 * k)) (i : Fin 2) : ℝ :=
  let l : ℝ := (j.val % k + 1 : ℕ)
  let b : ℝ := 4 * (k : ℝ)^2 + l * (k + 1)
  if (j.val < k ∧ i.val = 0) ∨ (k ≤ j.val ∧ i.val = 1) then b else l

def runtimeLaw (k : ℕ) : Measure (Fin 2 → ℝ) :=
  ∑ j : Fin (2 * k), ENNReal.ofReal (1 / (2 * k : ℝ)) •
    Measure.dirac (runtimeValues k j)

/-- Even if duplicate leaves were removed for free, the source's full evaluation needs
at least one multiply/add per support type at each distinct candidate. -/
def distinctScanWork (k : ℕ) : ℕ :=
  2 * k * (priceTree (runtimeValues k) 2).toFinset.card

end

end OpaquePricing.Dominance.Supplement


