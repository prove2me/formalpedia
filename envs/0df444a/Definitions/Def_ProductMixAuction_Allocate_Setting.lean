-- Prove2me | Definitions.Def_ProductMixAuction_Allocate_Setting
-- name    : ProductMixAuction_Allocate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:36:59.162761+00:00
-- url     : https://prove2.me/theorems/6cc7effc-057f-41a6-a4f5-91dbf294fb13
-- title:
--   §2.2, §2.5, §4.1–4.2, pp. 9–17 — product-mix bids, demand D_B(p), f_B, (local) validity, allocation problems, reductions, the edges of G_A
-- statement:
--   This module fixes the objects of §2.2, §2.5 and §4.1–4.2 of Baldwin, Goldberg, Klemperer and Lock.
--
--   **Goods and prices.** There are $n$ goods $[n]=\{1,\dots,n\}$ and a notional *reject* good $0$; write $[n]_0=\{0,1,\dots,n\}$. A price vector is $p\in\mathbb R^n$, extended by $p_0=0$.
--
--   **Bids.** A bid $b$ is a vector $(b_0,b_1,\dots,b_n)$ together with an integer weight $w(b)$; in the paper's input bids $b_0=0$, $b_1,\dots,b_n\in\mathbb Z$ and $w(b)=\pm1$ (p. 9). At prices $p$ the bid *demands* the goods
--   $$\arg\max_{i\in[n]_0}(b_i-p_i),$$
--   and it is *marginal* at $p$ if it demands more than one good. A price is non-marginal for a list $\mathcal B$ if no bid of $\mathcal B$ is marginal there; then $\mathcal B$ demands the bundle $\sum_{b\in\mathcal B}w(b)e^{i(b)}$, where $i(b)$ is the good $b$ demands.
--
--   **Demand.** The demand correspondence $D_{\mathcal B}(p)$ is the discrete convex hull $\operatorname{conv}(X)\cap\mathbb Z^{n+1}$ of the set $X$ of bundles demanded at non-marginal prices arbitrarily close to $p$ (p. 9). Bundles carry a coordinate $0$ that counts the (weighted) rejected bids; the demand on the goods $[n]$ alone is the image of $D_{\mathcal B}(p)$ under dropping that coordinate.
--
--   **Indirect utility and validity.** The indirect utility function is (3)
--   $$f_{\mathcal B}(p)=\sum_{b\in\mathcal B}w(b)\max_{i\in[n]_0}(b_i-p_i).$$
--   A list is *valid* if $f_{\mathcal B}$ is convex on $\mathbb R^n$ (p. 10), *$\varepsilon$-valid at $p$* if $f_{\mathcal B}$ is convex on the open $L^\infty$-ball $B(p;\varepsilon)$, and *locally valid at $p$* if it is $\varepsilon$-valid for some $\varepsilon>0$ (Definition 3). The aggregate list of several bidders is the concatenation of their lists.
--
--   **Allocation problems** (Definition 4). An allocation problem $\mathcal A=[p,(\mathcal B^j)_{j\in J},(m^j)_{j\in J},r]$ consists of a price $p$, a bid list $\mathcal B^j\subseteq\{0\}\times(\mathbb Z+\{0,\tfrac1{10}\})^n\times\mathbb Z$ locally valid at $p$ for every bidder $j$, partial allocations $m^j\in\mathbb Z^{n+1}_+$ and a residual supply $r\in\mathbb Z^{n+1}_+$, such that a valid allocation of $r$ exists: bundles $r^j\in D_{\mathcal B^j}(p)$ with $\sum_j r^j=r$. Each such allocation gives the *solution* $t^j=r^j+m^j$. A problem $\mathcal A'$ is a *valid reduction* of $\mathcal A$ if it is an allocation problem and every solution of $\mathcal A'$ is a solution of $\mathcal A$ (Definition 5).
--
--   **Marginal bids graph** (Definition 6). $G_{\mathcal A}$ is the multigraph on $[n]_0$ with an edge $\{i,i'\}$ ($i\neq i'$) labelled $j$ whenever bidder $j$ has a bid demanding both $i$ and $i'$ at $p$; between two goods there is at most one edge per label.
--
--   Finally, a *strong-substitutes vector* (p. 30) is a non-zero vector with at most one $+1$ entry, at most one $-1$ entry and no other non-zero entries.
--
--   **Formalization Note** Goods $[n]_0$ are `Fin (n + 1)` with index `0` the reject good; prices are `Fin n → ℝ` and `ext p` prepends $p_0=0$. Bid vectors are real (`Bid n`), because the algorithm shifts them by $\tfrac1{10}$; the paper's integral input bids are `IntBid n`, converted by `IntBid.toBid`. Bid lists are `List`s. Bundles, partial allocations and residual supplies are `ℤ`-valued; Definition 4's non-negativity is a clause of `IsAllocProblem`, not the type. `edges A` is the finite set of labelled edges $(\{i,i'\},j)$ of $G_{\mathcal A}$. The demand $D_{\mathcal B}(p)$ is one definition for every price; at a non-marginal price it is the singleton of the bundle above.
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, pp. 9–17, 30, §2.2 (3), §2.5, Definitions 3–6

import Mathlib

/-!
Baldwin, Goldberg, Klemperer, Lock, *Solving Strong-Substitutes Product-Mix Auctions*,
arXiv:1909.07313v3, §2.2 (pp. 9–10), §2.5 (p. 11), §4.1–4.2 (pp. 15–17): product-mix bids over the
goods `[n]₀ = Fin (n + 1)` (index `0` is the notional reject good), demanded goods, the demand
correspondence `D_B(p)`, the indirect utility function `f_B` (3), (local) validity (Definition 3),
allocation problems (Definition 4), solutions, valid reductions (Definition 5) and the edge set of
the marginal bids multigraph `G_A` (Definition 6).
-/

namespace ProductMixAuction.Allocate

open Finset

/-- A bid over the goods `[n]₀ = Fin (n + 1)` (p. 9): its vector `v` (with `v 0` the entry of the
reject good, `0` for every bid of the paper) and its weight `w`. -/
structure Bid (n : ℕ) where
  v : Fin (n + 1) → ℝ
  w : ℤ

/-- An integral input bid `(b₁, …, bₙ; w)` of §2.2 (p. 9). -/
structure IntBid (n : ℕ) where
  v : Fin n → ℤ
  w : ℤ

/-- The bid `(0, b₁, …, bₙ; w)` obtained by prepending the reject-good entry `0` (p. 9). -/
def IntBid.toBid {n : ℕ} (b : IntBid n) : Bid n :=
  ⟨Fin.cons 0 (fun i => (b.v i : ℝ)), b.w⟩

/-- A price vector `p ∈ ℝⁿ` extended by `p₀ = 0` for the reject good. -/
def ext {n : ℕ} (p : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons 0 p

/-- The maximal surplus `max_{i ∈ [n]₀} (bᵢ − pᵢ)` of bid `b` at prices `p`. -/
noncomputable def surplusMax {n : ℕ} (b : Bid n) (p : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => b.v i - ext p i)

/-- The set `arg max_{i ∈ [n]₀} (bᵢ − pᵢ)` of goods demanded by `b` at `p` (p. 9). -/
noncomputable def demGoods {n : ℕ} (b : Bid n) (p : Fin n → ℝ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => b.v i - ext p i = surplusMax b p)

/-- `b` is marginal at `p`: it demands more than one good (p. 9). -/
def IsMarginalBid {n : ℕ} (b : Bid n) (p : Fin n → ℝ) : Prop := 1 < (demGoods b p).card

/-- `p` is non-marginal for the list `B`: every bid of `B` demands exactly one good (p. 9). -/
def NonMarginalAt {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) : Prop :=
  ∀ b ∈ B, (demGoods b p).card = 1

/-- The bundle `Σ_{b ∈ B} w(b) e^{i(b)}` over `[n]₀` (p. 9); at a non-marginal price `i(b)` is the
unique good demanded by `b`. -/
noncomputable def nmBundle {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) : Fin (n + 1) → ℤ :=
  (B.map fun b => b.w • ∑ i ∈ demGoods b p, (Pi.single i (1 : ℤ) : Fin (n + 1) → ℤ)).sum

/-- The bundles demanded by `B` at non-marginal prices arbitrarily close to `p`. -/
def nearBundles {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) : Set (Fin (n + 1) → ℤ) :=
  {x | ∀ δ > 0, ∃ q : Fin n → ℝ, dist q p < δ ∧ NonMarginalAt B q ∧ nmBundle B q = x}

/-- The demand correspondence `D_B(p)` (p. 9), over `[n]₀` (coordinate `0` counts rejected bids):
the discrete convex hull `conv(X) ∩ ℤ^{n+1}` of the set `X` of bundles demanded at non-marginal
prices arbitrarily close to `p`. At a non-marginal `p` this is the singleton `{Σ w(b) e^{i(b)}}`. -/
def demand {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) : Set (Fin (n + 1) → ℤ) :=
  {x | (fun k => (x k : ℝ)) ∈
    convexHull ℝ ((fun (y : Fin (n + 1) → ℤ) (k : Fin (n + 1)) => (y k : ℝ)) '' nearBundles B p)}

/-- The demand correspondence on the goods `[n]` (§2.5): `D_B(p)` with the reject coordinate
dropped. -/
def demandN {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) : Set (Fin n → ℤ) :=
  Fin.tail '' demand B p

/-- The indirect utility function (3), p. 9: `f_B(p) = Σ_{b ∈ B} w(b) max_{i ∈ [n]₀} (bᵢ − pᵢ)`. -/
noncomputable def fB {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) : ℝ :=
  (B.map fun b => (b.w : ℝ) * surplusMax b p).sum

/-- A bid list is valid if `f_B` is convex on `ℝⁿ` (p. 10). -/
def Valid {n : ℕ} (B : List (Bid n)) : Prop := ConvexOn ℝ Set.univ (fB B)

/-- Definition 3 (p. 15): `B` is `ε`-valid at `p` if `f_B` restricted to the open `L∞`-ball
`B(p; ε)` is convex. (`Metric.ball` on `Fin n → ℝ` is the sup-norm ball.) -/
def EpsValid {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) (ε : ℝ) : Prop :=
  ConvexOn ℝ (Metric.ball p ε) (fB B)

/-- Definition 3 (p. 15): `B` is locally valid at `p` if it is `ε`-valid at `p` for some `ε > 0`. -/
def LocallyValid {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) : Prop :=
  ∃ ε > 0, EpsValid B p ε

/-- The aggregate bid list obtained by concatenating the lists of all bidders (p. 11). -/
noncomputable def aggregate {n : ℕ} {J : Type*} [Fintype J] (B : J → List (Bid n)) :
    List (Bid n) :=
  ((Finset.univ : Finset J).toList.map B).flatten

/-- The data `[p, (Bʲ)_{j∈J}, (mʲ)_{j∈J}, r]` of an allocation problem (Definition 4, p. 15), with
`p` stored on `[n]` (`p₀ = 0` implicitly) and the bundles `mʲ`, `r` over `[n]₀`. -/
structure AllocProblem (n : ℕ) (J : Type*) where
  p : Fin n → ℝ
  B : J → List (Bid n)
  m : J → Fin (n + 1) → ℤ
  r : Fin (n + 1) → ℤ

/-- Definition 4 (p. 15): `t` is a solution of `A` if `tʲ = rʲ + mʲ` for a valid allocation
`(rʲ)` of the residual supply, i.e. `rʲ ∈ D_{Bʲ}(p)` and `Σ_j rʲ = r`. -/
def IsSolution {n : ℕ} {J : Type*} [Fintype J] (A : AllocProblem n J)
    (t : J → Fin (n + 1) → ℤ) : Prop :=
  ∃ rr : J → Fin (n + 1) → ℤ, (∀ j, rr j ∈ demand (A.B j) A.p) ∧ ∑ j, rr j = A.r ∧
    ∀ j, t j = rr j + A.m j

/-- A bid in `{0} × (ℤ + {0, 1/10})ⁿ × ℤ` (Definition 4, item 2). -/
def BidFormat {n : ℕ} (b : Bid n) : Prop :=
  b.v 0 = 0 ∧ ∀ i : Fin n, ∃ z : ℤ, b.v i.succ = z ∨ b.v i.succ = z + 1 / 10

/-- Definition 4 (p. 15): `A` is an allocation problem. -/
def IsAllocProblem {n : ℕ} {J : Type*} [Fintype J] (A : AllocProblem n J) : Prop :=
  (∀ j, ∀ b ∈ A.B j, BidFormat b) ∧ (∀ j, LocallyValid (A.B j) A.p) ∧
    (∀ j k, 0 ≤ A.m j k) ∧ (∀ k, 0 ≤ A.r k) ∧ ∃ t, IsSolution A t

/-- Definition 5 (p. 16): `A'` is a valid reduction from `A`. -/
def IsReduction {n : ℕ} {J : Type*} [Fintype J] (A' A : AllocProblem n J) : Prop :=
  IsAllocProblem A' ∧ ∀ t, IsSolution A' t → IsSolution A t

open scoped Classical in
/-- Definition 6 (p. 16): the edges of the marginal bids multigraph `G_A`. A pair `(s(i, i'), j)`
with `i ≠ i'` is an edge labelled `j` iff bidder `j` has a bid demanding both `i` and `i'` at `p`
(a bid marginal between `i` and `i'`); parallel edges carry distinct labels. -/
noncomputable def edges {n : ℕ} {J : Type*} [Fintype J] (A : AllocProblem n J) :
    Finset (Sym2 (Fin (n + 1)) × J) :=
  Finset.univ.filter (fun e => ¬ e.1.IsDiag ∧ ∃ b ∈ A.B e.2, ∀ i ∈ e.1, i ∈ demGoods b A.p)

/-- A strong-substitutes vector (p. 30): a non-zero integral vector with at most one `+1` entry, at
most one `−1` entry and no other non-zero entries (here with real entries). -/
def IsSSVector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  x ≠ 0 ∧ (∀ k, x k = 0 ∨ x k = 1 ∨ x k = -1) ∧
    (∀ k k', x k = 1 → x k' = 1 → k = k') ∧ (∀ k k', x k = -1 → x k' = -1 → k = k')

end ProductMixAuction.Allocate


