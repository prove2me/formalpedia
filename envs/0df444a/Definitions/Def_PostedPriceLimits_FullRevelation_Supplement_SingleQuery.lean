-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_SingleQuery
-- name    : PostedPriceLimits_FullRevelation_Supplement_SingleQuery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:08:22.945816+00:00
-- url     : https://prove2.me/theorems/0e5b8658-5195-4f63-8748-ffe497f50b1a
-- title:
--   Single-query posted-price mechanisms (Definition 3.4)
-- statement:
--   A **single-query posted-price mechanism** operates on $m$ ordered items and $n$ bidders. A represented profile consists of finite nonempty sets of arbitrary nonnegative real additive clauses, with valuation $v_i(S)=\max_{u\in U_i}\sum_{x\in S}u_x$. The profile, allocation and welfare use the published XOS model without additional valuation conditions.
--
--   At each visit the deterministic mechanism chooses the next unvisited identity, a sample flag and extended nonnegative item prices from the preceding observable history. Previously allocated items have price $+\infty$, also in sample queries. The oracle returns the lexicographically smallest utility-maximizing bundle and then the lexicographically smallest supporting additive clause. A sample receives nothing; every other bidder irrevocably receives exactly the reported bundle. Every bidder is visited once. Histories contain only identities, prices, flags, oracle replies and allocated bundles. Neither full valuations nor private representations are revealed.
--
--   A randomized mechanism is an arbitrary probability space of seeds and a deterministic mechanism for each seed, independent of the fixed profile. This includes random arrival order, adaptive visiting order and arbitrary mixtures. For each fixed represented profile its welfare is measurable. Its guarantee for a positive approximation function $r$ means
--
--   $$\mathbb E_{\rm seed}\!\left[\sum_i v_i(S_i)\right]\ge\frac{\operatorname{OPT}(v)}{r(m)}$$
--
--   for every finite represented XOS profile, where OPT is the published maximum over feasible partial allocations. This interface supports the full mechanism class of Theorem 2.1.
--
--   **Formalization Note** Bidders and items use zero-based `Fin` types. The generic execution also accepts biased clause oracles for the lower-bound analysis; ordinary oracle histories carry a constant zero bias coordinate, which conveys no information. Invalid next-identity proposals are completed by the smallest unvisited identity; every valid adaptive visiting strategy is represented.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Definitions 3.3–3.4 and 3.6, p.5 (PDF 6)

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Model
import Definitions.Def_PostedPriceLimits_FullRevelation_BiasedXOS

set_option autoImplicit false
open MeasureTheory
open ComplementFreeCA.XOSGreedy
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation.Supplement

noncomputable section

/-- Definition 3.3: choose the lexicographically least supporting clause, after the
published lexicographic demand choice. The fallback is unreachable for an XOS expression. -/
def clauseResponse {m : ℕ} (E : XOSExpr m) (p : Fin m → ℝ≥0∞) :
    Finset (Fin m) × (Fin m → ℝ) :=
  let S := demandSet E.val p
  let C := E.clauses.filter (fun u => ∑ x ∈ S, u x = E.val S)
  (S, if h : C.Nonempty then Classical.choose (C.exists_min_image (fun u => toLex u) h) else 0)

/-- The complete observable record of one single-query visit. No representation,
valuation, hidden label, offset, or matrix index is disclosed. -/
structure Record (n m : ℕ) where
  bidder : Fin n
  prices : Fin m → ℝ≥0∞
  sample : Bool
  demand : Finset (Fin m)
  clause : ℝ × (Fin m → ℝ)
  bundle : Finset (Fin m)

/-- Definition 3.4: all three choices are made from the history before the reply. -/
structure DetSQ (n m : ℕ) where
  next : List (Record n m) → Option (Fin n)
  price : List (Record n m) → Fin m → ℝ≥0∞
  sample : List (Record n m) → Bool

def visited {n m : ℕ} (h : List (Record n m)) : Finset (Fin n) :=
  (h.map Record.bidder).toFinset

def allocated {n m : ℕ} (h : List (Record n m)) : Finset (Fin m) :=
  h.foldr (fun r S => r.bundle ∪ S) ∅

def nextBidder {n m : ℕ} (M : DetSQ n m) (h : List (Record n m)) : Option (Fin n) :=
  match M.next h with
  | some i => if i ∉ visited h then some i else (Finset.univ.filter (fun j => j ∉ visited h)).min
  | none => (Finset.univ.filter (fun j => j ∉ visited h)).min

def postedPrices {n m : ℕ} (M : DetSQ n m) (h : List (Record n m)) : Fin m → ℝ≥0∞ :=
  fun x => if x ∈ allocated h then ⊤ else M.price h x

/-- Generic single-query execution, shared by ordinary and biased oracles.
The oracle is not a mechanism input and its private data never enter a record. -/
def history {n m : ℕ} (M : DetSQ n m)
    (orc : Fin n → (Fin m → ℝ≥0∞) → Finset (Fin m) × (ℝ × (Fin m → ℝ))) :
    ℕ → List (Record n m)
  | 0 => []
  | t + 1 =>
    let h := history M orc t
    match nextBidder M h with
    | none => h
    | some i =>
      let p := postedPrices M h
      let sample := M.sample h
      let r := orc i p
      h ++ [⟨i, p, sample, r.1, r.2, if sample then ∅ else r.1⟩]

def outcome {n m : ℕ} (M : DetSQ n m)
    (orc : Fin n → (Fin m → ℝ≥0∞) → Finset (Fin m) × (ℝ × (Fin m → ℝ))) :
    Fin n → Finset (Fin m) :=
  fun i => ((history M orc n).filter (fun r => r.bidder = i)).foldr (fun r S => r.bundle ∪ S) ∅

def ordinaryOracle {n m : ℕ} (E : Fin n → XOSExpr m) (i : Fin n) (p : Fin m → ℝ≥0∞) :=
  let r := clauseResponse (E i) p
  (r.1, ((0 : ℝ), r.2))

/-- Arbitrary probability spaces of independent mechanism seeds, including random
arrival order. Measurability is the usual expectation convention, for every fixed profile. -/
structure RandSQ (n m : ℕ) where
  Seed : Type
  [seedMeasurableSpace : MeasurableSpace Seed]
  law : Measure Seed
  [isProbability : IsProbabilityMeasure law]
  mech : Seed → DetSQ n m
  measurable_welfare : ∀ E : Fin n → XOSExpr m,
    Measurable (fun ω => welfare E (outcome (mech ω) (ordinaryOracle E)))

attribute [instance] RandSQ.seedMeasurableSpace RandSQ.isProbability

def expectedWelfare {n m : ℕ} (M : RandSQ n m) (E : Fin n → XOSExpr m) : ℝ :=
  ∫ ω, welfare E (outcome (M.mech ω) (ordinaryOracle E)) ∂M.law

/-- Definition 3.6, for every represented XOS profile. -/
def Guarantees (r : ℕ → ℝ) (M : (n m : ℕ) → RandSQ n m) : Prop :=
  ∀ n m (E : Fin n → XOSExpr m), optWelfare E / r m ≤ expectedWelfare (M n m) E

end
end PostedPriceLimits.FullRevelation.Supplement


