-- Prove2me | Definitions.Def_ReusableMatching_Supplement_OPDMatching
-- name    : ReusableMatching_Supplement_OPDMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:03:58.472792+00:00
-- url     : https://prove2.me/theorems/8e9dd28f-8fa8-5996-9320-590eab88ca2e
-- title:
--   Algorithm 3, OCR-based Primal-Dual matching
-- statement:
--   The **OCR-based Primal-Dual algorithm (OPD)** constructs proposals sequentially. At arrival $j$, it considers every set $Q\subseteq N(j)$ of at most two current neighbors, computes the exact dual increment $\beta_j$ that Algorithm 2 would produce after the previous proposals, and chooses a maximizer. It then gives $Q_j$ to Algorithm 2 and matches the selected resource when it is available.
--
--   For $i\in Q_j$, the module defines $q_j^i$, $u_j^i$, and the dual increments
--
--   $$
--   \Delta\beta_j^i=\beta_1r_iq_j^i/2+\beta_2r_i(\Delta\mu_j^i-q_j^i/2),
--   \qquad
--   \Delta\alpha_j^i=(1-\beta_1)r_iq_j^i/2+(1-\beta_2)r_i(\Delta\mu_j^i-q_j^i/2).
--   $$
--
--   It also defines OPD's matching, reward, finite expected reward, and its explicit online property.
--
--   **Formalization Note** Maximizing ties are represented by an arbitrary selector satisfying the maximization predicate. Its inputs are only the earlier proposals and the present neighbor set, so it cannot inspect future edges or the OCR coin tape. Empty proposals are allowed, as Algorithm 3 asks for a set of size at most two.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, §4.2.1, pp.23–24, Algorithm 3, p.24

import Mathlib
import Definitions.Def_ReusableMatching_OBMRRInstance
import Definitions.Def_ReusableMatching_IsFeasibleMatching
import Definitions.Def_ReusableMatching_OPT
import Definitions.Def_ReusableMatching_Supplement_OCRRun

namespace ReusableMatching.Supplement

set_option autoImplicit false

/-- Whether `i` is available at round `j` in a completed Algorithm-2 history.  Only the prefix
strictly before `j` is inspected. -/
def availableAt {V : Type*} [DecidableEq V] (d : ℕ) (matchedAt : List (Option V))
    (i : V) (j : ℕ) : Prop :=
  ∀ t < j, matchedAt[t]? = some (some i) → t + d ≤ j

/-- `qⁱ_j`: if the previous proposal of `i` is within the current rental window, this is the exact
probability that `i` was unavailable then and has returned by `j`; after a gap of at least `d`
(including no previous proposal), it is the paper's conventional value `pⁱ_j`.

Delong et al., arXiv:2110.07084v2, §4.2.1, pp.23–24. -/
noncomputable def qProbability {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ := by
  classical
  exact match previousOccurrence Q i j with
    | none => availableProbability d Q i j
    | some j' =>
        if j' + d ≤ j then availableProbability d Q i j
        else
          finiteExpectation (Fin Q.length → OCRCoins) fun ω =>
            let h := (OCRRun d Q ω).matchedAt
            if ¬ availableAt d h i j' ∧ availableAt d h i j then 1 else 0

/-- `uⁱ_j = pⁱ_{j'} - Δμⁱ_{j'}` when `j' = prevⁱ_j`; it is zero when there is no previous
occurrence. -/
noncomputable def uProbability {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ)
    (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ :=
  match previousOccurrence Q i j with
  | none => 0
  | some j' => availableProbability d Q i j' - deltaMu d Q i j'

/-- The increment `Δβⁱ_j` assigned when `i ∈ Q_j`.

arXiv:2110.07084v2, §4.2.1, pp.23–24. -/
noncomputable def deltaBeta {V : Type*} [Fintype V] [LinearOrder V]
    (r : V → ℝ) (d : ℕ) (β1 β2 : ℝ) (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ :=
  β1 * r i * qProbability d Q i j / 2 +
    β2 * r i * (deltaMu d Q i j - qProbability d Q i j / 2)

/-- The increment `Δαⁱ_j` assigned when `i ∈ Q_j`.

arXiv:2110.07084v2, §4.2.1, p.24. -/
noncomputable def deltaAlpha {V : Type*} [Fintype V] [LinearOrder V]
    (r : V → ℝ) (d : ℕ) (β1 β2 : ℝ) (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ :=
  (1 - β1) * r i * qProbability d Q i j / 2 +
    (1 - β2) * r i * (deltaMu d Q i j - qProbability d Q i j / 2)

/-- The dual variable `α_{i,j}`, equal to `Δαⁱ_j` on a proposed vertex and zero otherwise. -/
noncomputable def opdAlpha {V : Type*} [Fintype V] [LinearOrder V]
    (r : V → ℝ) (d : ℕ) (β1 β2 : ℝ) (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ :=
  if i ∈ proposalAt Q j then deltaAlpha r d β1 β2 Q i j else 0

/-- The paper's `φⁱ_j = min {1-pⁱ_j, (1-qⁱ_j)/2}`. -/
noncomputable def opdPhi {V : Type*} [Fintype V] [LinearOrder V]
    (d : ℕ) (Q : List (Proposal V)) (i : V) (j : ℕ) : ℝ :=
  min (1 - availableProbability d Q i j) ((1 - qProbability d Q i j) / 2)

/-- The neighbors of arrival `j`. -/
def neighborSet {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (I : OBMRRInstance V n) (j : Fin n) : Finset V :=
  Finset.univ.filter fun i => (i, j) ∈ I.E

/-- The value `β_j` that would result from appending candidate proposal `q` to the already fixed
proposal history `prefix`.  Its probabilities are exact finite averages over Algorithm 2's coins.

arXiv:2110.07084v2, §4.2.1 and Algorithm 3, pp.23–24. -/
noncomputable def candidateBeta {V : Type*} [Fintype V] [LinearOrder V]
    (r : V → ℝ) (d : ℕ) (β1 β2 : ℝ) (hist : List (Proposal V))
    (q : Proposal V) : ℝ :=
  let Q := hist ++ [q]
  ∑ i ∈ q.vertices, deltaBeta r d β1 β2 Q i hist.length

/-- A tie-selection rule for Algorithm 3.  It sees only the prior proposals and the current
arrival's neighbor set.  The instance's known weights and duration may be closed over when the
rule is chosen, but future neighbor sets are not an argument. -/
abbrev OPDSelector (V : Type*) [DecidableEq V] :=
  List (Proposal V) → Finset V → Proposal V

/-- Build Algorithm 3's proposal sequence from the arrivals' neighbor sets. -/
def opdProposalAux {V : Type*} [DecidableEq V] (select : OPDSelector V) :
    List (Proposal V) → List (Finset V) → List (Proposal V)
  | hist, [] => hist
  | hist, N :: Ns =>
      let q := select hist N
      opdProposalAux select (hist ++ [q]) Ns

theorem length_opdProposalAux {V : Type*} [DecidableEq V] (select : OPDSelector V)
    (hist : List (Proposal V)) (Ns : List (Finset V)) :
    (opdProposalAux select hist Ns).length = hist.length + Ns.length := by
  induction Ns generalizing hist with
  | nil => simp [opdProposalAux]
  | cons N Ns ih =>
      simp only [opdProposalAux]
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- The actual proposal sequence `Q₁,…,Q_n` produced by the outer algorithm. -/
def OPDProposals {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (select : OPDSelector V) : List (Proposal V) :=
  opdProposalAux select [] (List.ofFn (neighborSet I))

theorem length_OPDProposals {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (select : OPDSelector V) :
    (OPDProposals I select).length = n := by
  simp [OPDProposals, length_opdProposalAux]

/-- Algorithm 3's maximization condition along its actual history.  It permits every maximizer,
so the theorem does not impose a tie rule absent from the paper.  The empty proposal and
singletons are among the competitors.

arXiv:2110.07084v2, Algorithm 3, p.24. -/
def IsOPDSelector {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β1 β2 : ℝ) (select : OPDSelector V) : Prop :=
  ∀ j : Fin n,
    let allQ := OPDProposals I select
    let hist := allQ.take j
    let N := neighborSet I j
    let chosen := select hist N
    chosen.vertices ⊆ N ∧
      ∀ alternative : Proposal V, alternative.vertices ⊆ N →
        candidateBeta I.r I.d β1 β2 hist alternative ≤
          candidateBeta I.r I.d β1 β2 hist chosen

/-- The resource actually matched by Algorithm 3 at arrival `j`, for a fixed Algorithm-2 coin
tape. -/
noncomputable def opdDecision {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (select : OPDSelector V) (ω : Fin n → OCRCoins)
    (j : Fin n) : Option V :=
  let Q := OPDProposals I select
  let hlen : Q.length = n := length_OPDProposals I select
  (OCRRun I.d Q (fun k => ω (Fin.cast hlen k))).matchedAt[j]?
    |>.join

/-- **Algorithm 3 (OCR-based Primal-Dual, OPD)** with Algorithm 2 as its OCR subroutine: the
finite set of matched resource-arrival pairs for a given fair-coin outcome.

Delong et al., arXiv:2110.07084v2, Algorithm 3, p.24. -/
noncomputable def OPDMatching {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (select : OPDSelector V) (ω : Fin n → OCRCoins) :
    Finset (V × Fin n) :=
  Finset.univ.filter fun p => opdDecision I select ω p.2 = some p.1

/-- Reward of OPD for one coin outcome. -/
noncomputable def opdReward {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (select : OPDSelector V) (ω : Fin n → OCRCoins) : ℝ :=
  ∑ p ∈ OPDMatching I select ω, I.r p.1

/-- Expected OPD reward under the independent uniform coin tape. -/
noncomputable def expectedOPDReward {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (select : OPDSelector V) : ℝ :=
  finiteExpectation (Fin n → OCRCoins) (opdReward I select)

/-- The explicit online property of OPD.  If two instances agree through arrival `j` and their
coin tapes agree through that round, their decisions agree through `j`.  The weights and duration
are known in advance and held fixed.

arXiv:2110.07084v2, p.2 and §4.2.1, p.23 (the outer algorithm does not inspect OCR's random
decisions). -/
def IsOnlineOPD {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (select : OPDSelector V) : Prop :=
  ∀ I' : OBMRRInstance V n, I'.r = I.r → I'.d = I.d →
    ∀ (ω ω' : Fin n → OCRCoins) (j : Fin n),
      (∀ p : V × Fin n, p.2 ≤ j → (p ∈ I.E ↔ p ∈ I'.E)) →
      (∀ t : Fin n, t ≤ j → ω t = ω' t) →
      ∀ t : Fin n, t ≤ j →
        opdDecision I select ω t = opdDecision I' select ω' t

end ReusableMatching.Supplement


