-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_Model
-- name    : PostedPriceLimits_FullRevelation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:30.099882+00:00
-- url     : https://prove2.me/theorems/c57ec4d9-f749-46db-a29f-0eb58732dae8
-- title:
--   §3 model: extended-price lexicographic demand, online full-revelation mechanisms, expected and optimal welfare
-- statement:
--   This module fixes the combinatorial-auction model of Section 3 for $n$ bidders and the ordered item set $M=[m]$ (items are $\mathrm{Fin}\,m$, item $0$ first). XOS expressions, allocations and the welfare $\sum_i v_i(S_i)$ are the published `ComplementFreeCA.XOSGreedy` notions: an XOS valuation is the maximum of a finite nonempty family of additive clauses with arbitrary nonnegative real coefficients, and an allocation is a tuple of pairwise disjoint bundles (items may stay unallocated).
--
--   1. **XOS** (Definition 3.1). A set function $v:2^M\to\mathbb R$ is XOS if $v(S)=\max_{u\in U}u(S)$ for some finite nonempty $U\subseteq\mathbb R_+^m$.
--   2. **Demand oracle** (Definition 3.2). For prices $p\in[0,\infty]^m$, the utility of a bundle $S$ avoiding the $+\infty$-priced items is $v(S)-p(S)$; bundles containing a $+\infty$-priced item are never chosen. The demand set is the lexicographically smallest utility-maximizing bundle, comparing indicator vectors $(\mathbf 1[0\in S],\mathbf 1[1\in S],\dots)$ as strings (equivalently, minimizing $\sum_{x\in S}2^{m-1-x}$).
--   3. **Online full-revelation (OFR) mechanism** (Definition 3.5). A deterministic OFR mechanism maps the observed history (the visited bidders, the prices posted to them, their revealed valuations and their bundles) to the next bidder to visit and a price vector in $[0,\infty]^m$. Previously allocated items are priced $+\infty$; the visited bidder receives their demand set irrevocably, and only then the seller learns their full valuation. The next-bidder proposal is optional. An absent or already-visited proposal is replaced by the smallest unvisited bidder; when none remain the history stops. This represents every adaptive visiting order and permits the zero-bidder auction. No computational restriction is imposed.
--   4. **Randomized OFR mechanism.** A probability space of seeds $(\Omega,\mu)$ and a deterministic OFR mechanism for every seed (random arrival orders are included), required only to make the welfare a measurable function of the seed for every XOS profile.
--   5. **Expected and optimal welfare** (Definition 3.6). For an XOS profile, $\mathbb E[\sum_i v_i(S_i)]$ is the integral over seeds of the welfare of the outcome; the mechanism observes the valuations $v_i$, never their representations. $\mathrm{OPT}=\max_{(T_1,\dots,T_n)}\sum_i v_i(T_i)$ is computed as a maximum over all item assignments $M\to\{\text{unallocated}\}\cup[n]$.
--
--   A mechanism attains an $\alpha$-approximation if $\mathbb E[\sum_i v_i(S_i)]\ge\mathrm{OPT}/\alpha$ for every XOS profile. These definitions are shared by the goal theorem and by Theorem 2.2.
--
--   **Formalization Note** The `else` branch of `demandSet` is unreachable because the empty bundle is always available.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Definitions 3.1, 3.2, 3.5 and 3.6, p.5 (PDF 6); §1, p.1 (PDF 2); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model

open MeasureTheory
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation

open ComplementFreeCA.XOSGreedy

/-! ## The combinatorial-auction model of §3 (Definitions 3.1, 3.2, 3.5, 3.6)

Items are `Fin d` (the ordered item set `M = [d]`, item `0` first), bidders are `Fin n`.
XOS expressions, allocations and welfare are the published
`ComplementFreeCA.XOSGreedy` notions (finite nonempty families of nonnegative real
additive clauses; pairwise-disjoint bundles, unallocated items allowed). -/

/-- Definition 3.1: a set function `v : 2^M → ℝ` is XOS if it is the maximum of a finite
nonempty family of nonnegative additive clauses. -/
def IsXOS {d : ℕ} (v : Finset (Fin d) → ℝ) : Prop :=
  ∃ E : XOSExpr d, ∀ S, v S = E.val S

/-- Items whose price is finite; an item priced `+∞` can never be bought. -/
noncomputable def availableItems {d : ℕ} (p : Fin d → ℝ≥0∞) : Finset (Fin d) :=
  Finset.univ.filter (fun x => p x ≠ ⊤)

/-- Quasi-linear utility `v(S) - p(S)` of a bundle avoiding `+∞`-priced items. -/
noncomputable def utility {d : ℕ} (v : Finset (Fin d) → ℝ) (p : Fin d → ℝ≥0∞)
    (S : Finset (Fin d)) : ℝ :=
  v S - ∑ x ∈ S, (p x).toReal

/-- The utility-maximizing bundles at prices `p ∈ [0,∞]^d`: bundles of available items whose
utility is at least that of every bundle of available items (bundles containing a
`+∞`-priced item have utility `-∞` and are never maximizers). -/
noncomputable def utilityMaximizers {d : ℕ} (v : Finset (Fin d) → ℝ) (p : Fin d → ℝ≥0∞) :
    Finset (Finset (Fin d)) :=
  (availableItems p).powerset.filter
    (fun S => ∀ T ∈ (availableItems p).powerset, utility v p T ≤ utility v p S)

/-- The indicator string of `S` read as a binary number with item `0` as the most significant
digit; comparing these keys is the lexicographic order on indicator vectors. -/
def lexKey {d : ℕ} (S : Finset (Fin d)) : ℕ :=
  ∑ x ∈ S, 2 ^ (d - 1 - x.val)

/-- Definition 3.2 (demand oracle): the lexicographically smallest (by indicator vector)
utility-maximizing bundle at prices `p ∈ [0,∞]^d`. (The maximizer set is never empty, since
`∅` is available; the `else` branch is unreachable.) -/
noncomputable def demandSet {d : ℕ} (v : Finset (Fin d) → ℝ) (p : Fin d → ℝ≥0∞) :
    Finset (Fin d) :=
  if h : (utilityMaximizers v p).Nonempty then
    Classical.choose ((utilityMaximizers v p).exists_min_image lexKey h)
  else ∅

/-- One visit of an online full-revelation mechanism, as recorded in the seller's history:
the visited bidder, the price vector posted to them, the valuation revealed after the
visit, and the bundle they received. -/
structure OFRRecord (n m : ℕ) where
  bidder : Fin n
  prices : Fin m → ℝ≥0∞
  valuation : Finset (Fin m) → ℝ
  bundle : Finset (Fin m)

/-- Definition 3.5: a deterministic online full-revelation (OFR) mechanism. From the observed
history it chooses the next bidder to visit and the price vector `p ∈ [0,∞]^m` to post.
No computational restriction is imposed. -/
structure DetOFR (n m : ℕ) where
  next : List (OFRRecord n m) → Option (Fin n)
  price : List (OFRRecord n m) → Fin m → ℝ≥0∞

namespace DetOFR

variable {n m : ℕ}

/-- Bidders already visited in a history. -/
def visited (h : List (OFRRecord n m)) : Finset (Fin n) :=
  (h.map OFRRecord.bidder).toFinset

/-- Items already allocated in a history. -/
def allocated (h : List (OFRRecord n m)) : Finset (Fin m) :=
  h.foldr (fun r acc => r.bundle ∪ acc) ∅

/-- The bidder actually visited next: a valid proposed bidder, or the smallest unvisited
bidder. `none` is returned exactly when no bidder remains; this also permits `n = 0`. -/
noncomputable def nextBidder (M : DetOFR n m) (h : List (OFRRecord n m)) : Option (Fin n) :=
  match M.next h with
  | some i => if i ∉ visited h then some i
    else (Finset.univ.filter (fun j => j ∉ visited h)).min
  | none => (Finset.univ.filter (fun j => j ∉ visited h)).min

/-- The prices actually posted: previously allocated items are priced `+∞`. -/
noncomputable def postedPrices (M : DetOFR n m) (h : List (OFRRecord n m)) : Fin m → ℝ≥0∞ :=
  fun x => if x ∈ allocated h then ⊤ else M.price h x

/-- The history after `k` visits when the bidders' valuations are `V`: the visited bidder
receives their demand bundle irrevocably, after which the seller learns their full
valuation. -/
noncomputable def history (M : DetOFR n m) (V : Fin n → Finset (Fin m) → ℝ) :
    ℕ → List (OFRRecord n m)
  | 0 => []
  | k + 1 =>
    let h := history M V k
    match M.nextBidder h with
    | none => h
    | some i =>
      let p := M.postedPrices h
      h ++ [⟨i, p, V i, demandSet (V i) p⟩]

/-- The final allocation after all `n` visits (each bidder is visited exactly once). -/
noncomputable def outcome (M : DetOFR n m) (V : Fin n → Finset (Fin m) → ℝ) :
    Fin n → Finset (Fin m) :=
  fun i => ((M.history V n).filter (fun r => r.bidder = i)).foldr (fun r acc => r.bundle ∪ acc) ∅

end DetOFR

/-- A randomized OFR mechanism: a probability space of seeds and a deterministic OFR mechanism
for each seed (this includes random arrival orders). The only extra field is the routine
measurability making the expected welfare well defined for every XOS profile. -/
structure RandOFR (n m : ℕ) where
  Seed : Type
  [seedMeasurableSpace : MeasurableSpace Seed]
  law : Measure Seed
  [isProbability : IsProbabilityMeasure law]
  mech : Seed → DetOFR n m
  measurable_welfare : ∀ E : Fin n → XOSExpr m,
    Measurable (fun ω => welfare E ((mech ω).outcome (fun i => (E i).val)))

attribute [instance] RandOFR.seedMeasurableSpace RandOFR.isProbability

/-- Expected welfare `E[∑_i v_i(S_i)]` of a randomized OFR mechanism on the XOS profile `E`;
the mechanism observes only the valuations `v_i = (E i).val`, never the representation. -/
noncomputable def expectedWelfare {n m : ℕ} (M : RandOFR n m) (E : Fin n → XOSExpr m) : ℝ :=
  ∫ ω, welfare E ((M.mech ω).outcome (fun i => (E i).val)) ∂M.law

/-- The optimal welfare `max_{(T_1,…,T_n)} ∑_i v_i(T_i)` over all allocations, written as a
maximum over item assignments `g : M → {unallocated} ∪ [n]`. -/
noncomputable def optWelfare {n m : ℕ} (E : Fin n → XOSExpr m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun g : Fin m → Option (Fin n) => welfare E (fun i => Finset.univ.filter (fun x => g x = some i)))

end PostedPriceLimits.FullRevelation


