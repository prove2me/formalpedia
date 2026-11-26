-- Prove2me | Definitions.Def_ReusableMatching_Supplement_OCRRun
-- name    : ReusableMatching_Supplement_OCRRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:03:27.730154+00:00
-- url     : https://prove2.me/theorems/c54faa3f-6ee6-4909-b293-21623e6ec908
-- title:
--   Algorithm 2 and the online correlated rental quantities
-- statement:
--   A **proposal** is a set of at most two offline vertices. Algorithm 2 maintains a temporary state $\tau_{i,t}\in\{\text{unknown},\text{selected},\text{not-selected}\}$ and uses independent fair choices in each randomized round.
--
--   In a singleton round it selects the unique vertex and resets its future state. In a two-vertex sender round it independently draws $\ell,m\in\{1,2\}$, selects $i_\ell$, records whether $i_m$ was selected, and resets the other vertex. In a receiver round it draws $m$; a selected message chooses the other vertex, a not-selected message chooses $i_m$, and an unknown message uses a fresh fair choice. Both states are then reset. A selected vertex is matched only when it is available under the rental duration $d$.
--
--   The module also defines the exact finite probabilities $\Delta\mu_j^i$, availability probabilities $p_j^i$, previous occurrences, the expectations $\mu^i$, $\mu^i_{\mathrm{sender}}$, $\mu^i_{\mathrm{receiver}}$, and Definition 1's four-case $\gamma$-OCR bound.
--
--   **Formalization Note** Rounds are zero-based. The paper's three fresh fair choices are represented by a finite uniform coin tape, so every expectation is a finite average. The fixed linear order only labels the two elements of a set; Algorithm 2 is symmetric in those labels. The receiver interpretation follows the prose on p.17 and the analysis on p.21: not-selected selects the same vertex.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Definition 1 and Proposition 1, p.16; Algorithm 2 and explanatory prose, pp.17–18; conditional expectations, p.20

import Mathlib

namespace ReusableMatching.Supplement

set_option autoImplicit false

/-- The three values of the temporary message `τ` in Algorithm 2.

Delong, Farhadi, Niazadeh, Sivan & Udwani, *Online Bipartite Matching with
Reusable Resources*, arXiv:2110.07084v2, Algorithm 2 and §4.1.2, pp.17–18. -/
inductive OCRStatus where
  | unknown
  | selected
  | notSelected
  deriving DecidableEq, Inhabited

instance : Fintype OCRStatus where
  elems := {.unknown, .selected, .notSelected}
  complete := by intro x; cases x <;> simp

/-- The three independent fair bits used by Algorithm 2 in one round.  `sender` selects the
sender/receiver role, while `first` and `second` encode the paper's independent choices `ℓ` and
`m`.  Bits that a branch does not inspect are harmless.

arXiv:2110.07084v2, Algorithm 2, p.17. -/
structure OCRCoins where
  sender : Bool
  first : Bool
  second : Bool
  deriving DecidableEq, Fintype, Inhabited

/-- A proposal is a set of at most two offline vertices.  The empty proposal is included because
Algorithm 3 maximizes over sets of size at most two; Definition 1 and Proposition 1 separately
require every proposal to be nonempty.

arXiv:2110.07084v2, §4.1.1, p.15, and Algorithm 3, p.24. -/
structure Proposal (V : Type*) [DecidableEq V] where
  vertices : Finset V
  card_le_two : vertices.card ≤ 2

/-- The proposals to which Definition 1 applies: every round contains one or two vertices. -/
def IsOCRSequence {V : Type*} [DecidableEq V] (Q : List (Proposal V)) : Prop :=
  ∀ q ∈ Q, q.vertices.Nonempty

/-- The state after a prefix of Algorithm 2.  `matchedAt.get? t = some (some i)` means that `i`
was selected and available, hence matched, at zero-based round `t`.  The scheduled table `tau`
stores the paper's `τ_{i,t}` values, including future entries written by a sender round.

arXiv:2110.07084v2, Algorithm 2, p.17. -/
structure OCRState (V : Type*) where
  round : ℕ
  tau : V → ℕ → OCRStatus
  matchedAt : List (Option V)

/-- Initial state: before round zero all temporary messages are unknown and no vertex has been
matched. -/
def initialOCRState (V : Type*) : OCRState V where
  round := 0
  tau := fun _ _ => .unknown
  matchedAt := []

/-- A vertex is available at the current round precisely when every earlier match was at least
`d` rounds ago.  Thus a match at `j` blocks rounds `j+1, …, j+d-1` and availability returns at
`j+d`, exactly as on p.2. -/
def ocrAvailable {V : Type*} [DecidableEq V] (d : ℕ) (s : OCRState V) (i : V) : Prop :=
  ∀ t < s.round, s.matchedAt[t]? = some (some i) → t + d ≤ s.round

/-- Replace `τ_{i,t}` by `x` on the future interval `j < t < j+d`, the zero-based form of the
paper's `[j+1,j+d-1]`. -/
def setTauInterval {V : Type*} [DecidableEq V] (tau : V → ℕ → OCRStatus)
    (i : V) (j d : ℕ) (x : OCRStatus) : V → ℕ → OCRStatus :=
  fun v t => if v = i ∧ j < t ∧ t < j + d then x else tau v t

/-- A fixed labeling of a two-element proposal.  Algorithm 2 is symmetric in the labels `1,2`;
using the ambient linear order only makes that otherwise arbitrary labeling explicit. -/
def orderedProposal {V : Type*} [LinearOrder V] (q : Proposal V) : List V :=
  q.vertices.sort (· ≤ ·)

/-- The vertex labeled by a bit (`false` is label 1, `true` is label 2). -/
def bitVertex {V : Type*} (xs : List V) (b : Bool) : Option V :=
  xs[if b then 1 else 0]?

/-- Append the current match decision and advance the clock by one round. -/
noncomputable def advanceOCR {V : Type*} [DecidableEq V] (d : ℕ) (s : OCRState V)
    (tau' : V → ℕ → OCRStatus) (selectedVertex : Option V) : OCRState V := by
  classical
  let matched := match selectedVertex with
    | some i => if ocrAvailable d s i then some i else none
    | none => none
  exact
    { round := s.round + 1
      tau := tau'
      matchedAt := s.matchedAt ++ [matched] }

/-- One exact transition of Algorithm 2.

For a receiver round the three cases are the reading forced by the prose on p.17 and the analysis
on p.21: `selected` chooses the other vertex, `not-selected` chooses the same vertex, and
`unknown` uses a fresh fair bit.  The displayed pseudocode compresses the last two cases into an
`else`, but its prose explicitly says that a `not-selected` message selects `i_m`.

arXiv:2110.07084v2, Algorithm 2 and §4.1.2, pp.17–18. -/
noncomputable def ocrStep {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ) (s : OCRState V)
    (q : Proposal V) (c : OCRCoins) : OCRState V :=
  let xs := orderedProposal q
  match xs with
  | [] => advanceOCR d s s.tau none
  | [i] =>
      let tau' := setTauInterval s.tau i s.round d .unknown
      advanceOCR d s tau' (some i)
  | i1 :: i2 :: _ =>
      let il := bitVertex [i1, i2] c.first
      let im := bitVertex [i1, i2] c.second
      let ibar := bitVertex [i1, i2] (!c.second)
      if c.sender then
        let tau₁ := match ibar with
          | some i => setTauInterval s.tau i s.round d .unknown
          | none => s.tau
        let tau₂ := match im with
          | some i => setTauInterval tau₁ i s.round d
              (if c.second = c.first then .selected else .notSelected)
          | none => tau₁
        advanceOCR d s tau₂ il
      else
        let chosen := match im with
          | none => il
          | some i =>
              match s.tau i s.round with
              | .selected => ibar
              | .notSelected => im
              | .unknown => il
        let tau₁ := setTauInterval s.tau i1 s.round d .unknown
        let tau₂ := setTauInterval tau₁ i2 s.round d .unknown
        advanceOCR d s tau₂ chosen

/-- Execute Algorithm 2 on equally long lists of proposals and per-round coins. -/
noncomputable def ocrRunList {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ) :
    OCRState V → List (Proposal V) → List OCRCoins → OCRState V
  | s, q :: qs, c :: cs => ocrRunList d (ocrStep d s q c) qs cs
  | s, _, _ => s

/-- **Algorithm 2 (1/32-OCR algorithm)** as a deterministic function of its finite fair-coin
tape.  A seed is one triple of bits for every round; the probability law used below is uniform on
this finite type, so all expectations are literal finite averages.

Delong et al., arXiv:2110.07084v2, Algorithm 2, p.17 (explanatory prose pp.17–18). -/
noncomputable def OCRRun {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (ω : Fin Q.length → OCRCoins) : OCRState V :=
  ocrRunList d (initialOCRState V) Q (List.ofFn ω)

/-- Uniform expectation on a finite nonempty sample space. -/
noncomputable def finiteExpectation (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

/-- `μⁱ(Q₁,…,Q_m)`: the expected number of rounds in which Algorithm 2 actually matches `i`.

arXiv:2110.07084v2, proof of Proposition 1 and Claim 2, p.18. -/
noncomputable def mu {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) : ℝ :=
  finiteExpectation (Fin Q.length → OCRCoins) fun ω =>
    ((OCRRun d Q ω).matchedAt.count (some i) : ℝ)

/-- `Δμⁱ_j`: the exact probability that Algorithm 2 matches `i` at zero-based round `j`. -/
noncomputable def deltaMu {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ :=
  finiteExpectation (Fin Q.length → OCRCoins) fun ω =>
    if (OCRRun d Q ω).matchedAt[j]? = some (some i) then 1 else 0

/-- The proposal at round `j`, with the empty proposal outside the list. -/
def proposalAt {V : Type*} [DecidableEq V] (Q : List (Proposal V)) (j : ℕ) : Finset V :=
  (Q[j]?).map Proposal.vertices |>.getD ∅

/-- `pⁱ_j = 1 - ∑_{t=j-d+1}^{j-1} Δμⁱ_t`, written without truncated natural subtraction.
The filter `j < t+d` selects exactly the earlier rounds in the reuse window.

arXiv:2110.07084v2, §4.1.1, p.16. -/
noncomputable def availableProbability {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ :=
  1 - ∑ t ∈ (Finset.range j).filter (fun t => j < t + d), deltaMu d Q i t

/-- `prevⁱ_j`: the largest earlier round containing `i`, or `none` for the paper's `-∞`.

arXiv:2110.07084v2, §4.1.1, p.16. -/
noncomputable def previousOccurrence {V : Type*} [Fintype V] [LinearOrder V]
    (Q : List (Proposal V)) (i : V) (j : ℕ) : Option ℕ :=
  let S := (Finset.range j).filter (fun t => i ∈ proposalAt Q t)
  if h : S.Nonempty then some (S.max' h) else none

/-- Uniform coin tapes whose first round has the specified role. -/
noncomputable def roleSeeds {V : Type*} [Fintype V] [LinearOrder V] (Q : List (Proposal V))
    (sender : Bool) : Finset (Fin Q.length → OCRCoins) :=
  match Q with
  | [] => ∅
  | _ :: qs => Finset.univ.filter fun ω =>
      (ω ⟨0, Nat.zero_lt_succ qs.length⟩).sender = sender

/-- The conditional expectation `μⁱ_sender` or `μⁱ_receiver`, conditioned on the first round's
role.  The empty-list value is set to zero; Claim 3 only uses this definition when the first
proposal has two vertices, so the conditioning set then has positive cardinality.

arXiv:2110.07084v2, equation (14), p.20. -/
noncomputable def muGivenFirstRole {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) (sender : Bool) : ℝ :=
  let S := roleSeeds Q sender
  if S.card = 0 then 0 else
    (∑ ω ∈ S, ((OCRRun d Q ω).matchedAt.count (some i) : ℝ)) / S.card

/-- `μⁱ_sender`. -/
noncomputable def muSender {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) : ℝ :=
  muGivenFirstRole d Q i true

/-- `μⁱ_receiver`. -/
noncomputable def muReceiver {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) : ℝ :=
  muGivenFirstRole d Q i false

/-- The right-hand side of Definition 1 (`γ`-OCR), including `prev = -∞` in the uncorrelated
case. -/
noncomputable def gammaOCRLowerBound {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (γ : ℝ) (i : V) (j : ℕ) : ℝ :=
  let q := proposalAt Q j
  let p := availableProbability d Q i j
  if i ∉ q then 0
  else if q.card = 1 then p
  else
    match previousOccurrence Q i j with
    | none => p / 2
    | some j' =>
        if j' + d ≤ j then p / 2
        else p / 2 + γ * (availableProbability d Q i j' - deltaMu d Q i j')

/-- **Definition 1 (`γ`-OCR)** for Algorithm 2: the four-case lower bound (8), for every round
and offline vertex.

Delong et al., arXiv:2110.07084v2, Definition 1, p.16. -/
def IsGammaOCR {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (γ : ℝ) : Prop :=
  0 ≤ γ ∧ γ ≤ 1 ∧
    ∀ (i : V) (j : ℕ), j < Q.length →
      deltaMu d Q i j ≥ gammaOCRLowerBound d Q γ i j

end ReusableMatching.Supplement


