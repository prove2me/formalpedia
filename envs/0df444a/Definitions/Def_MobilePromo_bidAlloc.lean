-- Prove2me | Definitions.Def_MobilePromo_bidAlloc
-- name    : MobilePromo_bidAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:51.683427+00:00
-- url     : https://prove2.me/theorems/34f6f7c6-a6c7-406d-851c-3fb2119b21c8
-- title:
--   The policy BidAlloc
-- statement:
--   **BidAlloc** works in cycles $s=1,2,\dots$, each an exploration phase followed by an exploitation phase. It keeps a counter $\Upsilon_l$ for each location, initially $0$.
--
--   1. *Exploration phase of cycle $s$.* If no campaign is active or no impression arrives, no bid is placed. Otherwise, for an arrival from $l$, the counter rises, $\Upsilon_l\leftarrow\Upsilon_l+1$, and the bid is the element in position $\Upsilon_l$ of the sequence $\bar{\boldsymbol b}_l^\infty$ that repeats $\bar{\boldsymbol b}_l$. The phase concludes whenever $\Upsilon_l\ge sk_l$ for all $l$. The estimate $\hat\gamma(s)$ is the maximum-likelihood estimate from the first $sk_l$ exploration outcomes at each $l$.
--   2. *Exploitation phase of cycle $s$.* If no campaign is active or no impression arrives, no bid is placed. Otherwise, for an arrival from $l$, the bid is $b^*_{i,t,l}(\boldsymbol c_i;\hat\gamma(s))$ of (7). The phase concludes when $Ls$ bids have been placed in it, and the exploration phase of cycle $s+1$ begins.
--
--   An impression won is allocated FEFS.
--
--   **Formalization Note** The bookkeeping is a fold of the structure `PhaseState` along the history, with the outcomes of exploration bids kept in order for each location. Only those outcomes feed the estimate, and periods with no active campaign change nothing. The counter in `PhaseState` is read before the arrival and positions are $0$-based, so position $\Upsilon_l$ of the paper is `Υ l % k l`.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, §3.1, pp.17–18

import Mathlib
import Definitions.Def_MobilePromo_MLESelector
import Definitions.Def_MobilePromo_regret

set_option autoImplicit false

namespace MobilePromo

/-- The bookkeeping of `BidAlloc` (SSRN 3523491, pp.17–18).

**Formalization Note** The exploration outcomes at `l` are kept in order in `obs l`; the exploitation
outcomes are not. -/
structure PhaseState (L : ℕ) where
  /-- The current cycle `s`. -/
  s : ℕ
  /-- `true` during an exploration phase, `false` during an exploitation phase. -/
  exploring : Bool
  /-- The exploration counters `Υ_l`. -/
  Υ : Fin L → ℕ
  /-- The number of bids placed so far in the current exploitation phase. -/
  placed : ℕ
  /-- The outcomes of the exploration bids at each location, in order. -/
  obs : Fin L → List Bool

namespace PhaseState

variable {L : ℕ} (k : Fin L → ℕ)

/-- The start of the policy: cycle `1`, exploration, `Υ_l = 0` (SSRN 3523491, p.17). -/
def init : PhaseState L := ⟨1, true, fun _ => 0, 0, fun _ => []⟩

/-- The exploration phase of cycle `s` concludes whenever `Υ_l ≥ s k_l` for all `l` (SSRN 3523491,
p.17). -/
def settle (st : PhaseState L) : PhaseState L :=
  if st.exploring = true ∧ ∀ l, st.s * k l ≤ st.Υ l then { st with exploring := false } else st

/-- The update of one period, where `active` says whether a campaign is active in it (SSRN 3523491,
pp.17–18). Nothing changes if no campaign is active or no impression arrives. In an exploration phase,
the arrival raises `Υ_l` and its outcome is recorded. In an exploitation phase the bid is counted, and
the phase concludes at `L s` bids, the exploration phase of cycle `s + 1` beginning. -/
def step (st : PhaseState L) (active : Bool) : Outcome L → PhaseState L
  | none => st
  | some (l, w) =>
    if active then
      if st.exploring then
        settle k { st with
          Υ := Function.update st.Υ l (st.Υ l + 1)
          obs := Function.update st.obs l (st.obs l ++ [w]) }
      else if st.placed + 1 < L * st.s then
        { st with placed := st.placed + 1 }
      else
        settle k { st with s := st.s + 1, exploring := true, placed := 0 }
    else st

/-- The data of the MLE of cycle `s`: `D_l(ŝ)` collects the outcomes number `(ŝ - 1) k_l + 1, …, ŝ k_l` at
`l`, the "first `s k_l` realized outcomes" (SSRN 3523491, p.17). Indices here are 0-based. -/
def data (st : PhaseState L) (s : ℕ) : (l : Fin L) → Fin s → Fin (k l) → Bool :=
  fun l ŝ g => (st.obs l).getD (ŝ * k l + g) false

end PhaseState

/-- Runs `PhaseState.step` along a list of outcomes; `acc` is the history before them. -/
def phaseAux {L : ℕ} (k : Fin L → ℕ) (active : List (Outcome L) → Bool) :
    List (Outcome L) → PhaseState L → List (Outcome L) → PhaseState L
  | _, st, [] => st
  | acc, st, o :: os => phaseAux k active (acc ++ [o]) (st.step k (active acc) o) os

/-- The phase state of `BidAlloc` after the history `h`. -/
def phaseOf {L : ℕ} (k : Fin L → ℕ) (active : List (Outcome L) → Bool)
    (h : List (Outcome L)) : PhaseState L :=
  phaseAux k active [] PhaseState.init h

/-- The policy `BidAlloc` (SSRN 3523491, §3.1, pp.17–18). With no active campaign, no bid. In an
exploration phase, the arrival from `l` gets the element in position `Υ_l + 1` of the exploration
sequence `b̄_l^∞`. In an exploitation phase of cycle `s`, it gets `b*_{i,t,l}(c; γ̂(s))` of (7). The
allocation is FEFS, which is built into `Season.state`.

**Formalization Note** `Υ_l` here is the counter before the arrival, and positions are 0-based, so the
paper's "position `Υ_l` after the increase" is `Υ_l % k_l`. The estimate is recomputed from `obs`, whose
first `s k_l` entries no longer change. -/
noncomputable def bidAlloc (M : Model) (X : Exploration M) (mle : MLESelector M X) {T : ℕ}
    (S : Schedule T) : Policy M.L := fun h l =>
  let st := phaseOf X.k (activeB S) h
  if activeB S h then
    if st.exploring then
      X.bbar l ⟨st.Υ l % X.k l, Nat.mod_lt _ (X.k_pos l)⟩
    else
      bStarAt M S (mleVec M X mle st.s (st.data X.k st.s)) h l
  else 0

end MobilePromo


