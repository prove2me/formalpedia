-- Prove2me | Definitions.Def_XinMartingaleInventory_Minimax_constructions
-- name    : XinMartingaleInventory_Minimax_constructions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:58:14.166195+00:00
-- url     : https://prove2.me/theorems/0e8e2394-8f78-484f-b735-faab760eda14
-- title:
--   Constructed policies, demand laws and backward-induction families
-- statement:
--   A stock selector induces a policy recursively: start at its value for (T,x₀,μ), then apply the remaining-horizon selector to previous post-order stock minus demand and the latest demand. Path masses are finite products of the corresponding conditional kernels. The explicit selector is max(y,β_m^n); its demand law starts from the chosen post-order stock. The independent benchmark has constant base stock 0 if μ≤U/(b+1), otherwise U, and product endpoint demand. Arbitrary simultaneous Bellman selectors must select actual feasible extrema; negative pre-order stock is passed as max(y,0). The generic p.11 law starts instead with the law selector at x₀. The backward-induction families fix the last s policy rules or conditional kernels, with constraints only at positive-mass histories for laws. As printed, the terminal law family is the singleton containing the generic optimal-policy law, independently of the competing policy. The terminal policy family is the selected policy singleton. Prefix expectations sum over positive-mass prefixes of the specified length.
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, §§2.1–3 and §7.2, p.41 (PDF p.41)

import Definitions.Def_XinMartingaleInventory_Minimax_bellman
import Definitions.Def_XinMartingaleInventory_Minimax_thresholds

noncomputable section

namespace XinMartingaleInventory.Minimax

abbrev StockSelector := ℕ → ℚ → ℚ → ℚ
abbrev LawSelector := ℕ → ℚ → ℚ → DemandLaw

/-- Recursively order using a remaining-horizon selector. Histories are most-recent first. -/
def policyRec (φ : StockSelector) (T : ℕ) (x₀ μ : ℚ) : Policy
  | [] => φ T x₀ μ
  | d :: h => φ (T-(h.length+1)) (policyRec φ T x₀ μ h-d) d

def inducedPolicy (U : ℚ) (φ : StockSelector) (T : ℕ) (x₀ μ : ℚ) : Policy :=
  canonicalPolicy U T (policyRec φ T x₀ μ)

/-- Finite product of conditional atom masses. -/
def kernelProduct (K : List ℚ → DemandLaw) : PathLaw
  | [] => 1
  | d :: h => K h d * kernelProduct K h

def inducedLaw (T : ℕ) (K : List ℚ → DemandLaw) : PathLaw :=
  fun w => if w.length = T then kernelProduct K w else 0

def explicitSelector (U b : ℚ) : StockSelector :=
  fun n y m => max y (beta U b n m)

def explicitPolicy (U b x₀ μ : ℚ) (T : ℕ) : Policy :=
  inducedPolicy U (explicitSelector U b) T x₀ μ

def optimalDemand (U b x₀ μ : ℚ) (T : ℕ) : PathLaw :=
  inducedLaw T (fun h => explicitLaw U b (T-h.length)
    (explicitPolicy U b x₀ μ T h) (previousDemand μ h))

def independentThreshold (U b μ : ℚ) : ℚ := if μ ≤ U/(b+1) then 0 else U

def independentValue (U b μ : ℚ) (T : ℕ) : ℝ :=
  if μ ≤ U/(b+1) then (T : ℝ)*b*μ else (T : ℝ)*((U : ℝ)-μ)

def independentPolicy (U b x₀ μ : ℚ) (T : ℕ) : Policy :=
  inducedPolicy U (fun _ y _ => max y (independentThreshold U b μ)) T x₀ μ

def independentDemand (U μ : ℚ) (T : ℕ) : PathLaw :=
  inducedLaw T (fun _ => endpointLaw U μ)

/-- Arbitrary simultaneous selectors of the actual Bellman extrema. -/
def validSelectors (U b : ℚ) (T : ℕ) (φ : StockSelector) (q : LawSelector) : Prop :=
  ∀ n, 1 ≤ n → n ≤ T → ∀ x ∈ Set.Icc 0 U, ∀ m ∈ Set.Icc 0 U,
    φ n x m ∈ bellmanMin U b n x m ∧ q n x m ∈ bellmanMax U b n x m

/-- At negative pre-order stock the feasible set equals that at zero. -/
def extendSelector (φ : StockSelector) : StockSelector := fun n y m => φ n (max y 0) m

def genericPolicy (U : ℚ) (φ : StockSelector) (T : ℕ) (x₀ μ : ℚ) : Policy :=
  inducedPolicy U (extendSelector φ) T x₀ μ

/-- The printed p.11 first marginal uses x₀, unlike the explicit p.13 law. -/
def genericDemand (U : ℚ) (φ : StockSelector) (q : LawSelector)
    (T : ℕ) (x₀ μ : ℚ) : PathLaw :=
  inducedLaw T (fun h => if h = [] then q T x₀ μ else
    q (T-h.length) (genericPolicy U φ T x₀ μ h) (previousDemand μ h))

/-- Printed backward-induction family, including the policy-independent terminal singleton. -/
def restrictedLaws (U μ x₀ : ℚ) (T : ℕ) (φ : StockSelector) (q : LawSelector)
    (π : Policy) (s : ℕ) : Set PathLaw :=
  if s = T then {genericDemand U φ q T x₀ μ} else
  {Q | Q ∈ martingaleLaws U μ T ∧ ∀ r, 1 ≤ r → r ≤ s → r < T →
    ∀ h, h.length = T-r → 0 < prefixMass Q h →
      conditionalMass Q h = q r (π h) (previousDemand μ h)}

def restrictedPolicies (U μ x₀ : ℚ) (T : ℕ) (φ : StockSelector) (s : ℕ) : Set Policy :=
  if s = T then {genericPolicy U φ T x₀ μ} else
  {π | π ∈ policies U x₀ T ∧ ∀ r, 1 ≤ r → r ≤ s → r < T →
    ∀ h, h.length = T-r → validHistory U h →
      π h = extendSelector φ r (preStock x₀ π h) (previousDemand μ h)}

/-- Expectation over positive-mass prefixes of exactly length k. -/
def prefixExpectation (Q : PathLaw) (k : ℕ) (f : List ℚ → ℝ) : ℝ :=
  ∑' h, if h.length = k ∧ 0 < prefixMass Q h then prefixMass Q h * f h else 0

end XinMartingaleInventory.Minimax


