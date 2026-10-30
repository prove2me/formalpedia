-- Prove2me | Definitions.Def_XinMartingaleInventory_Minimax_inventoryModel
-- name    : XinMartingaleInventory_Minimax_inventoryModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:56:45.905566+00:00
-- url     : https://prove2.me/theorems/52747a90-35fb-4ade-b194-e917e6230538
-- title:
--   History policies and the original inventory minimax problem
-- statement:
--   Let U and b be positive rationals, T≥1, and μ,x₀∈[0,U] rational. A policy chooses a rational post-order stock in [0,U] at every rational demand history of length less than T. It must be at least the previous post-order stock minus the latest demand, with initial lower bound x₀. Pre-order stocks may be negative. Functions are extended by zero outside this domain to make equality of policies exact. One-period cost is b max(d−x,0)+max(x−d,0). M(m) contains all rationally supported probability laws in [0,U] with mean m. Path laws place total probability one on length-T demand histories. MAR requires the initial conditional mean μ and, at every positive-mass nonempty history, conditional mean equal to its latest demand. IND consists of products of marginals in M(μ). The objective is the infimum over all admissible policies of the supremum over the specified law class of expected total cost. Optimal-policy and worst-law predicates require feasibility and attainment of these extrema.
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, §§2.1–3 and §7.2, p.10 (PDF p.10)

import Definitions.Def_XinMartingaleInventory_Minimax_probabilityMass

noncomputable section

namespace XinMartingaleInventory.Minimax

abbrev DemandLaw := ℚ → ℝ
abbrev PathLaw := List ℚ → ℝ
abbrev Policy := HistoryRule ℚ ℚ

def validHistory (U : ℚ) (h : List ℚ) : Prop := ∀ d ∈ h, d ∈ Set.Icc 0 U

def validDecisionHistory (U : ℚ) (T : ℕ) (h : List ℚ) : Prop :=
  h.length < T ∧ validHistory U h

/-- Canonical extension removes unused coordinates without restricting a history rule. -/
def canonicalPolicy (U : ℚ) (T : ℕ) (π : Policy) : Policy := by
  classical
  exact fun h => if validDecisionHistory U T h then π h else 0

def preStock (x₀ : ℚ) (π : Policy) : List ℚ → ℚ
  | [] => x₀
  | d :: h => π h - d

/-- The paper's Π, including the nonnegative-order restriction at every history. -/
def policies (U x₀ : ℚ) (T : ℕ) : Set Policy :=
  {π | π = canonicalPolicy U T π ∧ ∀ h, validDecisionHistory U T h →
    π h ∈ Set.Icc 0 U ∧ preStock x₀ π h ≤ π h}

def cost (b x d : ℝ) : ℝ := b * max (d - x) 0 + max (x - d) 0

def meanLaws (U m : ℚ) : Set DemandLaw :=
  {q | probabilityMass q ∧ (∀ d, d ∉ Set.Icc 0 U → q d = 0) ∧
    expectation q (fun d => (d : ℝ)) = (m : ℝ)}

def pathLaws (U : ℚ) (T : ℕ) : Set PathLaw :=
  {Q | probabilityMass Q ∧ ∀ w, ¬(w.length = T ∧ validHistory U w) → Q w = 0}

/-- The dummy preceding demand at the empty history is μ, not an extra coordinate. -/
def previousDemand (μ : ℚ) (h : List ℚ) : ℚ := h.headD μ

def martingaleLaws (U μ : ℚ) (T : ℕ) : Set PathLaw :=
  {Q | Q ∈ pathLaws U T ∧ ∀ h, h.length < T → 0 < prefixMass Q h →
    conditionalMass Q h ∈ meanLaws U (previousDemand μ h)}

/-- Product mass of potentially different one-period marginals. -/
def productMass (qs : ℕ → DemandLaw) : List ℚ → ℝ
  | [] => 1
  | d :: h => qs h.length d * productMass qs h

def independentLaws (U μ : ℚ) (T : ℕ) : Set PathLaw :=
  {Q | Q ∈ pathLaws U T ∧ ∃ qs : ℕ → DemandLaw,
    (∀ t < T, qs t ∈ meanLaws U μ) ∧
    ∀ w, w.length = T → Q w = productMass qs w}

/-- Cost of source period t+1, where t is zero based. -/
def periodCost (b : ℚ) (π : Policy) (w : List ℚ) (t : ℕ) : ℝ :=
  cost b (π (historyPrefix w t)) ((historyPrefix w (t+1)).headD 0)

def tailCost (b : ℚ) (T : ℕ) (π : Policy) (k : ℕ) (w : List ℚ) : ℝ :=
  ∑ t ∈ Finset.Ico k T, periodCost b π w t

def expectedCost (b : ℚ) (T : ℕ) (π : Policy) (Q : PathLaw) : ℝ :=
  expectation Q (tailCost b T π 0)

def worstCost (b : ℚ) (T : ℕ) (laws : Set PathLaw) (π : Policy) : ℝ :=
  sSup ((expectedCost b T π) '' laws)

/-- Original infimum of worst expected total costs, independently of any Bellman function. -/
def minimaxValue (U b x₀ : ℚ) (T : ℕ) (laws : Set PathLaw) : ℝ :=
  sInf ((worstCost b T laws) '' policies U x₀ T)

def optimalPolicy (U b x₀ : ℚ) (T : ℕ) (laws : Set PathLaw) (π : Policy) : Prop :=
  π ∈ policies U x₀ T ∧ worstCost b T laws π = minimaxValue U b x₀ T laws

def worstLaw (b : ℚ) (T : ℕ) (laws : Set PathLaw) (π : Policy) (Q : PathLaw) : Prop :=
  Q ∈ laws ∧ expectedCost b T π Q = worstCost b T laws π

end XinMartingaleInventory.Minimax


