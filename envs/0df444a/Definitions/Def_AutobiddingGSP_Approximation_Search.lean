-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_Search
-- name    : AutobiddingGSP_Approximation_Search
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:31.471519+00:00
-- url     : https://prove2.me/theorems/7a521655-a6bc-45cd-b57d-576d13f9baca
-- title:
--   Encoded instances, rational and real answers, real-answer search reductions, and the problems of computing approximate equilibria
-- statement:
--   **Instances.** `encAuction A` writes an auction in binary (every item listed explicitly; self-delimiting naturals and rationals). `WellFormed`: every bidder has $m_i\ge1$ items, $v_{i,1}\ge\dots\ge v_{i,m_i}>0$ (no distinct-value assumption), $1\le K\le M$, $1\ge c_1\ge\dots\ge c_K>0$. `ValidFor m r`: budget model — one budget $B_i>0$ per bidder; ROI model — no budgets; and when `r = true` also $K=M$ and every $c_k=1$ (the Remark after Theorem 1.2).
--
--   **Rational answers.** A witness is a list of rational multipliers and a finite list of weighted rankings (each the ranking list of an allocation); it represents $(\alpha,\pi)$ with $\pi(a)$ the total weight listed with $a$. `ABESearch m prec r`: answers are codes of witnesses whose $(\alpha,\pi)$ is a $\mathrm{prec}(N)$-approximate equilibrium, $N$ the instance length. `ABESearchUniform m r`: the instance is the auction followed by a rational $0<\gamma<1$ in binary.
--
--   **Real answers.** A `RealSearchProblem` has real answer vectors $y:\mathbb N\to\mathbb R$. `RealSearchReduces Q S`: polynomial-time maps $f$ (instances), `qry` (a list of comparison queries $(j,q)$, $q$ rational) and $g$ (decoder), such that for every valid $s$, $f(s)$ is valid and for **every** answer $y$ of $f(s)$, $g$ applied to $s$ and the bits $[y_j\le q],[q\le y_j]$ of all queries is an answer of $Q$ on $s$. `RealPPADHard S`: every problem of PPAD (published `QuasiStrictNE.PPAD`) reduces to $S$ this way.
--
--   `ABERealSearch m γ r`: answers are the multiplier vectors $(\alpha_0,\dots,\alpha_{n-1},0,0,\dots)$ of all γ-approximate equilibria $(\alpha,\pi)$, with real $\alpha$ and real $\pi$ (at $\gamma=0$: every exact equilibrium, rational or not).
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Theorem 1.2, p. 3 (PDF 3); §2, pp. 6–8; Lemmas 5.1–5.2, pp. 23, 25; Theorems 7.1, 8.1, pp. 35, 41

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QuasiStrictNE_PPAD
import Definitions.Def_AutobiddingGSP_Approximation_Model

namespace AutobiddingGSP.Approximation

open QAlgorithms.LocalHamiltonian

/-- A list of rationals in binary: its length (`encBin`), then each entry (`encRat`). -/
def encRatList (l : List ℚ) : List Bool := encBin l.length ++ l.flatMap encRat

/-- **The binary input code of an auction** (the instances of Theorem 1.2, p. 3): the number of
bidders, each bidder's item values as a rational list (every item listed explicitly), `K`, the
click-through rates and the budgets, all self-delimiting (`encBin`, `encRat`). -/
def encAuction (A : Auction) : List Bool :=
  encBin A.vals.length ++ A.vals.flatMap encRatList ++ encBin A.K ++ encRatList A.ctr ++
    encRatList A.budgets

namespace Auction

/-- **The standing assumptions of §2** (p. 6): every bidder has at least one item, its values are
positive and listed in nonincreasing order `v_{i,1} ≥ ⋯ ≥ v_{i,m_i} > 0` (no distinct-value
assumption), `1 ≤ K ≤ M`, and `1 ≥ c_1 ≥ ⋯ ≥ c_K > 0`. -/
def WellFormed (A : Auction) : Prop :=
  (∀ l ∈ A.vals, l ≠ [] ∧ (∀ v ∈ l, 0 < v) ∧ l.Pairwise (fun x y => y ≤ x)) ∧
    1 ≤ A.K ∧ A.K ≤ A.vals.flatten.length ∧ A.ctr.length = A.K ∧
    (∀ c ∈ A.ctr, 0 < c ∧ c ≤ 1) ∧ A.ctr.Pairwise (fun x y => y ≤ x)

/-- The instances of each constraint model. Budget model: one positive budget `B_i > 0` per
bidder (Definition 2.2, p. 7). ROI model: no budgets (Definition 2.4, p. 8). When `restricted`
holds, additionally the number of slots equals the number of items and every click-through rate
is one (the Remark after Theorem 1.2, p. 3, and Theorems 7.1 and 8.1). -/
def ValidFor (A : Auction) : Model → Bool → Prop
  | Model.budget, r => A.WellFormed ∧ A.budgets.length = A.vals.length ∧ (∀ B ∈ A.budgets, 0 < B) ∧
      (r = true → A.K = A.vals.flatten.length ∧ ∀ c ∈ A.ctr, c = 1)
  | Model.roi, r => A.WellFormed ∧ A.budgets = [] ∧
      (r = true → A.K = A.vals.flatten.length ∧ ∀ c ∈ A.ctr, c = 1)

/-- The ranking list of an allocation: the items in rank order, each as the pair
(bidder, item index), both 0-based. -/
def rankList (A : Auction) (a : A.Alloc) : List (ℕ × ℕ) :=
  (List.finRange A.numItems).map (fun k => ((a k).1.val, (a k).2.val))

/-- The randomized allocation described by a finite weighted list of rankings: `π(a)` is the sum of
the weights listed with the ranking list of `a`. -/
def mixtureOf (A : Auction) (ws : List (ℚ × List (ℕ × ℕ))) : A.Alloc → ℝ :=
  fun a => ((ws.filter (fun e => e.2 = A.rankList a)).map (fun e => (e.1 : ℝ))).sum

/-- The multiplier profile described by a list of rationals (bidder `i` reads entry `i`). -/
def alphaOf (A : Auction) (α : List ℚ) : Fin A.n → ℝ := fun i => (α.getD i.val 0 : ℝ)

/-- A rational solution representation: rational multipliers `α` (one per bidder) and a finite list
`ws` of weighted rankings, each a ranking list of some allocation, whose induced pair
`(α, π)` is a γ-approximate autobidding equilibrium of the model. Every such list is allowed (no
bound on its length or support). -/
def IsWitness (A : Auction) (m : Model) (γ : ℝ) (α : List ℚ) (ws : List (ℚ × List (ℕ × ℕ))) :
    Prop :=
  α.length = A.n ∧ (∀ e ∈ ws, ∃ a : A.Alloc, e.2 = A.rankList a) ∧
    A.IsApproxABE m γ (A.alphaOf α) (A.mixtureOf ws)

/-- The real multiplier `α_v` read through a natural-number index (`0` out of range). -/
def alphaAt (A : Auction) (α : Fin A.n → ℝ) (v : ℕ) : ℝ :=
  if h : v < A.n then α ⟨v, h⟩ else 0

end Auction

/-- The binary code of a rational solution representation: the multipliers (a rational list), the
number of weighted rankings, and each weight followed by its ranking list of pairs. -/
def encWitness (α : List ℚ) (ws : List (ℚ × List (ℕ × ℕ))) : List Bool :=
  encRatList α ++ encBin ws.length ++
    ws.flatMap (fun e => encRat e.1 ++ encBin e.2.length ++ e.2.flatMap (fun p => encBin p.1 ++ encBin p.2))

/-- **Computing a γ-approximate autobidding equilibrium**, as a finite-string search problem
(Theorem 1.2, p. 3), with the precision given as a function `prec` of the instance length `N`.

* Instances: codes `encAuction A` of auctions satisfying the standing assumptions of the model
  (and, if `r = true`, with `K = M` and all click-through rates one).
* Answers: codes of rational multipliers and a finite weighted list of rankings whose induced
  `(α, π)` is a `prec(N)`-approximate equilibrium (`Auction.IsWitness`). -/
def ABESearch (m : Model) (prec : ℕ → ℝ) (r : Bool) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ A : Auction, A.ValidFor m r ∧ s = encAuction A
  answer s t := ∃ A : Auction, A.ValidFor m r ∧ s = encAuction A ∧
    ∃ (α : List ℚ) (ws : List (ℚ × List (ℕ × ℕ))), t = encWitness α ws ∧
      A.IsWitness m (prec s.length) α ws

/-- **The uniform problem** (Theorem 1.2 and Lemmas 5.1–5.2, pp. 3, 23, 25): the precision is a
rational `0 < γ < 1` given in binary as part of the input, after the auction. Answers as in
`ABESearch`. -/
def ABESearchUniform (m : Model) (r : Bool) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (A : Auction) (γ : ℚ), A.ValidFor m r ∧ 0 < γ ∧ γ < 1 ∧ s = encAuction A ++ encRat γ
  answer s t := ∃ (A : Auction) (γ : ℚ), A.ValidFor m r ∧ 0 < γ ∧ γ < 1 ∧
    s = encAuction A ++ encRat γ ∧
    ∃ (α : List ℚ) (ws : List (ℚ × List (ℕ × ℕ))), t = encWitness α ws ∧ A.IsWitness m γ α ws

/-- **A search problem with real answers**: a validity predicate on instance strings and, for each
instance, a set of real answer vectors, written as real sequences `ℕ → ℝ`. -/
structure RealSearchProblem where
  valid : List Bool → Prop
  answer : List Bool → (ℕ → ℝ) → Prop

/-- The answers to a list of exact comparison queries `(j, q)` about a real vector `y`: for each
query, the two bits `[y_j ≤ q, q ≤ y_j]` (which determine the sign of `y_j − q`). -/
noncomputable def signBits (qs : List (ℕ × ℚ)) (y : ℕ → ℝ) : List Bool :=
  qs.flatMap (fun q => [decide (y q.1 ≤ (q.2 : ℝ)), decide ((q.2 : ℝ) ≤ y q.1)])

/-- The binary code of a list of comparison queries (index, rational threshold). -/
def encQueries (qs : List (ℕ × ℚ)) : List Bool :=
  encBin qs.length ++ qs.flatMap (fun q => encBin q.1 ++ encRat q.2)

/-- **Polynomial-time search reduction to a problem with real answers.** A polynomial-time map
`f` on instances, a polynomial-time computable list `qry s` of exact comparison queries
(coordinate index, rational threshold), and a polynomial-time decoder `g` such that for every
valid instance `s` of `Q`, `f s` is a valid instance of `S`, and for **every** real answer `y` of
`S` on `f s`, `g` applied to `s` and the query answers `signBits (qry s) y` is an answer of `Q`
on `s`.

**Formalization Note** This extends `CardinalMatching.SearchReduces` (same machine model, same
"every answer" quantifier, same pairing of the decoder's input with the separator `none`) to
answers that are arbitrary real vectors, possibly irrational: the decoder sees the answer only
through polynomially many exact sign comparisons with rationals, fixed by the instance. -/
def RealSearchReduces (Q : TetrisHard.Rows.SearchProblem) (S : RealSearchProblem) : Prop :=
  ∃ (f : List Bool → List Bool) (qry : List Bool → List (ℕ × ℚ))
    (g : List (Option (Bool ⊕ Bool)) → List Bool),
    CookPvsNP.PolyTimeComputable f ∧ CookPvsNP.PolyTimeComputable (fun s => encQueries (qry s)) ∧
    CookPvsNP.PolyTimeComputable g ∧
    ∀ s, Q.valid s → S.valid (f s) ∧
      ∀ y, S.answer (f s) y →
        Q.answer s (g (s.map (some ∘ Sum.inl) ++ none :: (signBits (qry s) y).map (some ∘ Sum.inr)))

/-- **PPAD-hardness of a problem with real answers**: every problem of PPAD (the public
`QuasiStrictNE.PPAD`: total finite-string problems reducing to End-of-Line) reduces to it by a
`RealSearchReduces` reduction. -/
def RealPPADHard (S : RealSearchProblem) : Prop :=
  ∀ Q ∈ QuasiStrictNE.PPAD, RealSearchReduces Q S

/-- **Computing a γ-approximate autobidding equilibrium, with real answers** (Theorem 1.2, p. 3;
Theorems 7.1 and 8.1, pp. 35, 41). Instances as in `ABESearch`. An answer is the multiplier vector
`(α_0, …, α_{n−1}, 0, 0, …)` of some γ-approximate equilibrium `(α, π)` with any real `α` and any
real distribution `π`; no rationality or support bound is imposed, so at `γ = 0` every exact
(possibly irrational) equilibrium is an answer. -/
def ABERealSearch (m : Model) (γ : ℝ) (r : Bool) : RealSearchProblem where
  valid s := ∃ A : Auction, A.ValidFor m r ∧ s = encAuction A
  answer s y := ∃ A : Auction, A.ValidFor m r ∧ s = encAuction A ∧
    ∃ (α : Fin A.n → ℝ) (π : A.Alloc → ℝ), A.IsApproxABE m γ α π ∧
      (∀ i : Fin A.n, y i.val = α i) ∧ ∀ j, A.n ≤ j → y j = 0

end AutobiddingGSP.Approximation


