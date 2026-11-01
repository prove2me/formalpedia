-- Prove2me | Definitions.Def_TwoSidedPI_Algorithm1
-- name    : TwoSidedPI_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:19.14009+00:00
-- url     : https://prove2.me/theorems/956a5ebe-31d6-45ca-8a01-cbc6c163da78
-- title:
--   Mechanism 1 (Algorithm 1) for matroid double auctions, its run and the prices $P_i$
-- statement:
--   **Algorithm 1** runs on a report profile $b$. It keeps the served buyers $A_B$, the sellers $A_S$ who irrevocably keep their item, the number $r$ of items that may still go to buyers, the available sellers $M_{\mathrm{SELL}}$ and the buyers $M_{\mathrm{BUY}}$ not yet considered; initially $A_B=A_S=\emptyset$, $r=|S|$, $M_{\mathrm{SELL}}=S$, $M_{\mathrm{BUY}}=B$. While $M_{\mathrm{BUY}}\ne\emptyset$ and $M_{\mathrm{SELL}}\ne\emptyset$:
--
--   1. pick the seller $j\in M_{\mathrm{SELL}}$ with the smallest threshold $p_j$ and the buyer $i\in M_{\mathrm{BUY}}$ with the largest threshold $p_i(A_B,r)$;
--   2. if $A_B\cup\{i\}\notin\mathcal I_B$ or $|A_B\cup\{i\}|>r$, remove $i$ from $M_{\mathrm{BUY}}$;
--   3. otherwise let $p=p_{i,j}(A_B,r)$. If $b_j>p$, seller $j$ keeps her item: $A_S\gets A_S\cup\{j\}$, $M_{\mathrm{SELL}}\gets M_{\mathrm{SELL}}\setminus\{j\}$, $r\gets r-1$. If $b_j\le p$, buyer $i$ leaves $M_{\mathrm{BUY}}$, and if moreover $b_i>p$ the item is traded: $A_B\gets A_B\cup\{i\}$, $M_{\mathrm{SELL}}\gets M_{\mathrm{SELL}}\setminus\{j\}$, and $i$ pays $p$ to $j$.
--
--   The mechanism serves $A_B$, and the sellers in $A_S\cup M_{\mathrm{SELL}}$ keep their items. Its welfare on the truthful profile $\mathbf v$ is $\mathbf v(A(\mathbf v))=\sum_{i\in A_B(\mathbf v)}v_i+\sum_{j\in A_S(\mathbf v)\cup M_{\mathrm{SELL}}(\mathbf v)}v_j$.
--
--   For the analysis, $P_i$ is the price at which buyer $i$ was asked to buy (a seller had agreed), and $\infty$ if she never was; $P_j$ is the last price offered to seller $j$, and $0$ if she was never offered a trade. The surplus against a price $P\in\mathbb R\cup\{\infty\}$ is $(x-P)^+$, which is $0$ for $P=\infty$.
--
--   **Formalization Note** Ties are broken by injective ranks (`rkB`, larger rank first; `rkS`, smaller rank first). Thresholds are in `WithTop ℝ`, so infeasible buyers ($p_i=\infty$) are picked first and dropped without an offer. The comparisons are strict, as printed. The loop is `step` iterated $|B|+|S|$ times: each live iteration removes a buyer or a seller and a finished state is a fixed point. Each offer is logged; payments are read off the logged trades.
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Algorithm 1, p.9; §3, pp.9–10; proof of Lemma 4, pp.29–32 (A_B(v), M_SELL(v), P_i)

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices
import Definitions.Def_TwoSidedPI_Outcome

open MeasureTheory

namespace TwoSidedPI

/-- The answer to an offer in Algorithm 1 (Braun, Kesselheim, arXiv:2105.15032v1, p.9): the
seller keeps her item (`v_j > p`), or the seller agrees and the buyer buys (`v_i > p`), or the
seller agrees and the buyer declines. -/
inductive Response
  | keep
  | trade
  | decline
  deriving DecidableEq

/-- One offer made by Algorithm 1: buyer `i` and seller `j` are offered a trade at price `p`. -/
structure Offer (B S : Type*) where
  /-- The buyer `i` of the pair. -/
  buyer : B
  /-- The seller `j` of the pair. -/
  seller : S
  /-- The price `p = p_{i,j}(A_B, r)`. -/
  price : ℝ
  /-- What happened. -/
  response : Response

/-- The state `(A_B, A_S, r, M_SELL, M_BUY)` of Algorithm 1 (Braun, Kesselheim,
arXiv:2105.15032v1, p.9), with the log of the offers made so far (oldest first). -/
structure State (B S : Type*) where
  /-- Buyers irrevocably allocated an item. -/
  AB : Finset B
  /-- Sellers who irrevocably keep their item. -/
  AS : Finset S
  /-- The number of items that may still go to buyers in total. -/
  r : ℕ
  /-- Sellers still available for a trade. -/
  MSELL : Finset S
  /-- Buyers not yet considered for a trade. -/
  MBUY : Finset B
  /-- The offers made so far, oldest first. -/
  log : List (Offer B S)

/-- The initial state `A_B = ∅`, `A_S = ∅`, `r = |S|`, `M_SELL = S`, `M_BUY = B` of
Algorithm 1 (Braun, Kesselheim, arXiv:2105.15032v1, p.9). -/
def State.init (B S : Type*) [Fintype B] [Fintype S] : State B S :=
  ⟨∅, ∅, Fintype.card S, Finset.univ, Finset.univ, []⟩

/-- The seller `j ∈ arg min_{j' ∈ M_SELL} p_{j'}` picked by Algorithm 1 (Braun, Kesselheim,
arXiv:2105.15032v1, p.9), ties broken by the smaller rank `rkS` (footnote 6: "Break ties
arbitrarily, but always in the same way").

**Formalization Note** The choice minimizes `(p_j, rkS j)` lexicographically; for an injective
`rkS` the minimizer is unique, so `Classical.choose` returns it. -/
noncomputable def pickSeller {B S : Type*} (D : B ⊕ S → Measure ℝ) (rkS : S → ℕ)
    (T : Finset S) (h : T.Nonempty) : S :=
  Classical.choose (T.exists_min_image (fun j => toLex (thrS D j, rkS j)) h)

/-- The buyer `i ∈ arg max_{i' ∈ M_BUY} p_{i'}(A_B, r)` picked by Algorithm 1 (Braun, Kesselheim,
arXiv:2105.15032v1, p.9), ties broken by the larger rank `rkB`.

**Formalization Note** Thresholds live in `WithTop ℝ`, so buyers who cannot be feasibly added
(threshold `∞`) are picked first; Algorithm 1 then drops them without an offer. The choice
maximizes `(p_i(A_B, r), rkB i)` lexicographically; for an injective `rkB` the maximizer is
unique. -/
noncomputable def pickBuyer {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (rkB : B → ℕ) (AB : Finset B) (r : ℕ)
    (T : Finset B) (h : T.Nonempty) : B :=
  Classical.choose (T.exists_max_image (fun i => toLex (thrB M D AB r i, rkB i)) h)

/-- One iteration of the while loop of Algorithm 1 (Braun, Kesselheim, arXiv:2105.15032v1,
p.9) on the report profile `b`. If `M_BUY` or `M_SELL` is empty the state is unchanged.
Otherwise pick `j` and `i`; if `A_B ∪ {i} ∉ ℐ_B` or `|A_B ∪ {i}| > r`, remove `i` from `M_BUY`.
Else, with `p = p_{i,j}(A_B, r)`: if `b_j > p` the seller keeps (`A_S ← A_S ∪ {j}`,
`M_SELL ← M_SELL \ {j}`, `r ← r − 1`); if `b_j ≤ p`, `i` leaves `M_BUY`, and if moreover
`b_i > p` the trade happens (`A_B ← A_B ∪ {i}`, `M_SELL ← M_SELL \ {j}`).

**Formalization Note** The comparisons are strict, as printed. When the seller keeps,
`A_B ∪ {i}` has at most `r` elements and `i ∉ A_B`, so `r ≥ 1` and `r − 1` is exact. Every offer
is appended to the log. -/
noncomputable def step {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (rkB : B → ℕ) (rkS : S → ℕ)
    (b : B ⊕ S → ℝ) (st : State B S) : State B S := by
  classical
  exact
    if h : st.MBUY.Nonempty ∧ st.MSELL.Nonempty then
      let j := pickSeller D rkS st.MSELL h.2
      let i := pickBuyer M D rkB st.AB st.r st.MBUY h.1
      if CanAdd M st.AB st.r i then
        let p := priceReal M D st.AB st.r i j
        if p < b (Sum.inr j) then
          { st with AS := insert j st.AS, MSELL := st.MSELL.erase j, r := st.r - 1,
                    log := st.log ++ [⟨i, j, p, Response.keep⟩] }
        else if p < b (Sum.inl i) then
          { st with AB := insert i st.AB, MBUY := st.MBUY.erase i, MSELL := st.MSELL.erase j,
                    log := st.log ++ [⟨i, j, p, Response.trade⟩] }
        else
          { st with MBUY := st.MBUY.erase i, log := st.log ++ [⟨i, j, p, Response.decline⟩] }
      else { st with MBUY := st.MBUY.erase i }
    else st

/-- The final state of Algorithm 1 on the report profile `b` (Braun, Kesselheim,
arXiv:2105.15032v1, p.9).

**Formalization Note** Every iteration of the loop with `M_BUY ≠ ∅` and `M_SELL ≠ ∅` removes a
buyer from `M_BUY` or a seller from `M_SELL`, and a state with `M_BUY = ∅` or `M_SELL = ∅` is a
fixed point of `step`; so `|B| + |S|` iterations reach the state at which the while loop
stops. -/
noncomputable def run1 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (rkB : B → ℕ) (rkS : S → ℕ)
    (b : B ⊕ S → ℝ) : State B S :=
  (step M D rkB rkS b)^[Fintype.card B + Fintype.card S] (State.init B S)

/-- Mechanism 1 for matroid double auctions (Algorithm 1, Braun, Kesselheim,
arXiv:2105.15032v1, p.9) as a map from report profiles to outcomes: the buyers in the final
`A_B` are served, the sellers in the final `A_S ∪ M_SELL` keep their item (the returned set is
`A = A_B ∪ A_S ∪ M_SELL`), and in each trade between `i` and `j` at price `p_{i,j}` buyer `i`
pays `p_{i,j}` and seller `j` receives it (p.9: "i pays p_{i,j} to seller j"). Agents in no trade
pay and receive `0`. -/
noncomputable def mech1 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (rkB : B → ℕ) (rkS : S → ℕ)
    (b : B ⊕ S → ℝ) : Outcome B S :=
  let st := run1 M D rkB rkS b
  { served := st.AB
    keeps := st.AS ∪ st.MSELL
    pay := fun i => ((st.log.filter
      (fun o => decide (o.buyer = i ∧ o.response = Response.trade))).map Offer.price).sum
    recv := fun j => ((st.log.filter
      (fun o => decide (o.seller = j ∧ o.response = Response.trade))).map Offer.price).sum }

/-- The welfare `v(A(v))` of Mechanism 1 run on the truthful profile `v` (Braun, Kesselheim,
arXiv:2105.15032v1, p.29): `∑_{i ∈ A_B(v)} v_i + ∑_{j ∈ A_S(v) ∪ M_SELL(v)} v_j`. -/
noncomputable def welfare1 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (rkB : B → ℕ) (rkS : S → ℕ)
    (v : B ⊕ S → ℝ) : ℝ :=
  welfare (mech1 M D rkB rkS v) v

/-- The price `P_i` offered to buyer `i` in the run of Mechanism 1 on `v` (Braun, Kesselheim,
arXiv:2105.15032v1, proof of Lemma 4, p.32): the price of the offer in which seller `j` agreed
and buyer `i` was asked to buy, and `∞` if buyer `i` was never asked.

**Formalization Note** `∞` is `⊤ : WithTop ℝ`. The paper sets `P_i = ∞` for a buyer who was not
offered a trade because she became infeasible; here every buyer never asked (also one never
reached because `M_SELL` ran empty) gets `∞`, so her surplus `(v_i − P_i)^+` is `0`. A buyer is
asked at most once. -/
noncomputable def PB {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (rkB : B → ℕ) (rkS : S → ℕ)
    (v : B ⊕ S → ℝ) (i : B) : WithTop ℝ :=
  match (run1 M D rkB rkS v).log.find?
      (fun o => decide (o.buyer = i ∧ o.response ≠ Response.keep)) with
  | some o => (o.price : WithTop ℝ)
  | none => ⊤

/-- The last price `P_j` offered to seller `j` in the run of Mechanism 1 on `v` (Braun,
Kesselheim, arXiv:2105.15032v1, proof of Lemma 4, p.30: "The last price offered to seller j is
P_j (maybe 0 if seller j was never offered a trade)"). For a seller in `A_S(v)` it is the price
she refused when keeping her item. -/
noncomputable def PS {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (D : B ⊕ S → Measure ℝ) (rkB : B → ℕ) (rkS : S → ℕ)
    (v : B ⊕ S → ℝ) (j : S) : ℝ :=
  (((run1 M D rkB rkS v).log.filter (fun o => decide (o.seller = j))).getLast?.map
    Offer.price).getD 0

/-- The surplus `(x − P)^+` against a price `P ∈ ℝ ∪ {∞}` (Braun, Kesselheim,
arXiv:2105.15032v1, proof of Lemma 4, p.32): `max(x − P, 0)` for a finite `P`, and `0` for
`P = ∞`. -/
noncomputable def surplus (x : ℝ) (P : WithTop ℝ) : ℝ :=
  if h : P = ⊤ then 0 else max (x - P.untop h) 0

end TwoSidedPI


