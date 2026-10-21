-- Prove2me | Definitions.Def_PolyClinch_TwoSided_Market
-- name    : PolyClinch_TwoSided_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:26.763873+00:00
-- url     : https://prove2.me/theorems/275aa5df-48c2-43b0-ac6a-aebad18d726b
-- title:
--   pp. 4–5 — budgeted two-sided market, allocations, utilities (2)–(3), mechanisms, and the properties (ICb), (IRb), (IRs), (SBB), (PO)
-- statement:
--   The market of Hirai and Sato (§2) is a bipartite graph $(N,M,E)$ with buyers $N=\{1,\dots,n\}$, sellers $M=\{1,\dots,m\}$ and edges $E\subseteq N\times M$; $E_i$ and $E_j$ denote the edges incident to buyer $i$ and seller $j$. The goods are divisible and homogeneous. Buyer $i$ has a valuation $v_i$, a bid $v'_i$ and a budget $B_i$, all in $\mathbb R_+$; seller $j$ has a valuation (reserve price) $\rho_j\in\mathbb R_+$ and a monotone submodular function $f_j$ on $E_j$, where $f_j(F)$ is the largest amount of goods that can be transacted through $F\subseteq E_j$.
--
--   The **public information** is $\mathcal I=((N,M,E),\{v'_i\},\{B_i\},\{\rho_j\},\{f_j\})$; the true valuations are private. An **allocation** is a triple $\mathcal A=(w,p,r)$ of a transaction vector $w\in\mathbb R^E$, payments $p\in\mathbb R^N$ and revenues $r\in\mathbb R^M$ with
--   $$
--   w|_{E_j}\in P_j=P(f_j)\ (j\in M),\qquad p_i\le B_i\ (i\in N).
--   $$
--   A **mechanism** $\mathcal M$ maps public information to an allocation. The utilities are
--   $$
--   u_i(\mathcal A)=\begin{cases} v_i\,w(E_i)-p_i & p_i\le B_i,\\ -\infty & \text{otherwise,}\end{cases}\qquad u_j(\mathcal A)=r_j+\rho_j\bigl(f_j(E_j)-w(E_j)\bigr).
--   $$
--   Write $\mathcal I_i$ for $\mathcal I$ with $v'_i$ replaced by $v_i$, and $\mathcal I^*$ for $\mathcal I$ with all bids replaced by the true valuations. The properties are:
--
--   1. **(ICb)** $u_i(\mathcal M(\mathcal I))\le u_i(\mathcal M(\mathcal I_i))$ for every input and every buyer $i$;
--   2. **(IRb)** $u_i(\mathcal M(\mathcal I_i))\ge 0$;
--   3. **(IRs)** $u_j(\mathcal M(\mathcal I))\ge \rho_j f_j(E_j)$;
--   4. **(SBB)** $\sum_{i}p_i=\sum_j r_j$;
--   5. **(PO)** there is no allocation $\mathcal A$ with $\sum_i p_i\ge\sum_j r_j$ that is weakly better than $\mathcal M(\mathcal I^*)$ for every buyer and every seller and strictly better for at least one of them.
--
--   Every statement of the mission is made in this model. The properties are imposed on the inputs of Assumption 3.2 (p. 10): bids, reserve prices and true valuations are nonnegative integer multiples of the clock step $\varepsilon$.
--
--   **Formalization Note** Buyers are `Fin n` and sellers `Fin m` (0-based); transactions are functions on the subtype of edges in `E`. `Valid ε I` collects the standing assumptions: bids $v'_i$ and reserve prices $\rho_j$ are multiples $k\varepsilon$, $k\in\mathbb N$ (the reserve prices are the bids of the virtual buyers of p. 9), budgets are nonnegative reals, and each $f_j$ satisfies (1) on the subsets of $E_j$. Buyer utility takes values in `WithBot ℝ` ($-\infty=\bot$) and is only compared, never added. (IRb) is stated in the displayed form $u_i(\mathcal M(\mathcal I_i))\ge 0$, which the page gives as its meaning under (ICb). The competitor in (PO) must be an allocation (`Feasible`), and the true valuations in (ICb), (IRb) and (PO) lie on the $\varepsilon$-grid, since the mechanism is run on $\mathcal I_i$ and $\mathcal I^*$. A mechanism is a function of the public information only.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, pp. 4–5, §2, (2)–(4) and the properties (ICb), (IRb), (IRs), (SBB), (PO); p. 10, Assumption 3.2

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Polymatroid

namespace PolyClinch.TwoSided

open Finset

variable {n m : ℕ} (E : Finset (Fin n × Fin m))

/-- `E_i`: the edges of `E` incident to buyer `i` (p. 4). -/
def edgesOfBuyer (i : Fin n) : Finset ↥E := univ.filter (fun e => e.1.1 = i)

/-- `E_j`: the edges of `E` incident to seller `j` (p. 4). -/
def edgesOfSeller (j : Fin m) : Finset ↥E := univ.filter (fun e => e.1.2 = j)

/-- The public information `I` of p. 4 for the fixed bipartite graph `(N, M, E)` with buyers
`Fin n` and sellers `Fin m`: bids `v′_i`, budgets `B_i`, reserve prices `ρ_j`, and the set
functions `f_j` (only their values on subsets of `E_j` matter). -/
structure PublicInfo where
  /-- bids `v′_i` -/
  bid : Fin n → ℝ
  /-- budgets `B_i` -/
  budget : Fin n → ℝ
  /-- reserve prices (seller valuations) `ρ_j` -/
  rho : Fin m → ℝ
  /-- the monotone submodular functions `f_j` on `E_j` -/
  f : Fin m → Finset ↥E → ℝ

/-- An allocation `(w, p, r)`: transaction vector on `E`, payments of buyers, revenues of sellers
(p. 4). Feasibility is the separate predicate `Feasible`. -/
structure Allocation where
  /-- transaction vector `w = (w_ij)_{ij ∈ E}` -/
  w : ↥E → ℝ
  /-- payment vector `p = (p_i)_{i ∈ N}` -/
  p : Fin n → ℝ
  /-- revenue vector `r = (r_j)_{j ∈ M}` -/
  r : Fin m → ℝ

/-- `x` is a nonnegative integer multiple of `ε` (Assumption 3.2, p. 10). -/
def OnGrid (ε x : ℝ) : Prop := ∃ k : ℕ, x = k * ε

/-- Standing assumptions on the public information (pp. 3–4 and Assumption 3.2, p. 10): every
bid `v′_i` and every reserve price `ρ_j` is a nonnegative multiple of `ε` (the reserve prices are
the bids of the virtual buyers of p. 9), budgets are nonnegative reals, and each `f_j` satisfies
(1) on the subsets of `E_j`. -/
def Valid (ε : ℝ) (I : PublicInfo E) : Prop :=
  (∀ i, OnGrid ε (I.bid i)) ∧ (∀ i, 0 ≤ I.budget i) ∧ (∀ j, OnGrid ε (I.rho j)) ∧
    ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j)

/-- `A` is an allocation in the sense of p. 4: `w ≥ 0`, `w|_{E_j} ∈ P_j` for every seller `j`,
and `p_i ≤ B_i` for every buyer `i`. -/
def Feasible (I : PublicInfo E) (A : Allocation E) : Prop :=
  (∀ e, 0 ≤ A.w e) ∧ (∀ j, A.w ∈ polymatroidOn (edgesOfSeller E j) (I.f j)) ∧
    ∀ i, A.p i ≤ I.budget i

/-- Buyer utility (2), p. 4: `v_i w(E_i) − p_i` if `p_i ≤ B_i`, and `−∞` (`⊥`) otherwise. -/
noncomputable def buyerUtility (I : PublicInfo E) (val : Fin n → ℝ) (A : Allocation E)
    (i : Fin n) : WithBot ℝ :=
  if A.p i ≤ I.budget i then
    ((val i * ∑ e ∈ edgesOfBuyer E i, A.w e - A.p i : ℝ) : WithBot ℝ)
  else ⊥

/-- Seller utility (3), p. 5: `r_j + ρ_j (f_j(E_j) − w(E_j))`. -/
noncomputable def sellerUtility (I : PublicInfo E) (A : Allocation E) (j : Fin m) : ℝ :=
  A.r j + I.rho j * (I.f j (edgesOfSeller E j) - ∑ e ∈ edgesOfSeller E j, A.w e)

/-- A mechanism maps the public information (only) to an allocation (p. 4). -/
def Mechanism := PublicInfo E → Allocation E

/-- `I_i`: `I` with the bid of buyer `i` replaced by `b` (p. 5). -/
def withBid (I : PublicInfo E) (i : Fin n) (b : ℝ) : PublicInfo E :=
  { I with bid := Function.update I.bid i b }

/-- `I*`: `I` with all bids replaced by `val` (p. 5). -/
def withBids (I : PublicInfo E) (val : Fin n → ℝ) : PublicInfo E :=
  { I with bid := val }

/-- The allocation `A` is Pareto-dominated in the sense of (PO), p. 5: there is an allocation `A'`
with `∑ p'_i ≥ ∑ r'_j` that is weakly better for every buyer (utility (2) with true valuations
`val`) and every seller (utility (3)), strictly for at least one of them. -/
def ParetoImprovable (I : PublicInfo E) (val : Fin n → ℝ) (A : Allocation E) : Prop :=
  ∃ A' : Allocation E, Feasible E I A' ∧ ∑ j, A'.r j ≤ ∑ i, A'.p i ∧
    (∀ i, buyerUtility E I val A i ≤ buyerUtility E I val A' i) ∧
    (∀ j, sellerUtility E I A j ≤ sellerUtility E I A' j) ∧
    ((∃ i, buyerUtility E I val A i < buyerUtility E I val A' i) ∨
      (∃ j, sellerUtility E I A j < sellerUtility E I A' j))

/-- The mechanism outputs an allocation (p. 4) on every valid input. -/
def OutputsAllocations (ε : ℝ) (M : Mechanism E) : Prop :=
  ∀ I, Valid E ε I → Feasible E I (M I)

/-- (ICb), p. 5: for every valid input `I` and true valuations `val` (on the `ε`-grid), each
buyer is weakly better off bidding `val i`. -/
def ICb (ε : ℝ) (M : Mechanism E) : Prop :=
  ∀ (I : PublicInfo E) (val : Fin n → ℝ), Valid E ε I → (∀ i, OnGrid ε (val i)) → ∀ i,
    buyerUtility E I val (M I) i ≤ buyerUtility E I val (M (withBid E I i (val i))) i

/-- (IRb), p. 5, in the displayed form `u_i(M(I_i)) ≥ 0`. -/
def IRb (ε : ℝ) (M : Mechanism E) : Prop :=
  ∀ (I : PublicInfo E) (val : Fin n → ℝ), Valid E ε I → (∀ i, OnGrid ε (val i)) → ∀ i,
    0 ≤ buyerUtility E I val (M (withBid E I i (val i))) i

/-- (IRs), p. 5: `u_j(M(I)) ≥ ρ_j f_j(E_j)`. -/
def IRs (ε : ℝ) (M : Mechanism E) : Prop :=
  ∀ I, Valid E ε I → ∀ j, I.rho j * I.f j (edgesOfSeller E j) ≤ sellerUtility E I (M I) j

/-- (SBB), p. 5: `∑_i p_i = ∑_j r_j`. -/
def SBB (ε : ℝ) (M : Mechanism E) : Prop :=
  ∀ I, Valid E ε I → ∑ i, (M I).p i = ∑ j, (M I).r j

/-- (PO), p. 5: when all buyers bid truthfully (input `I*`), the mechanism's allocation is not
Pareto-dominated by any allocation. -/
def PO (ε : ℝ) (M : Mechanism E) : Prop :=
  ∀ (I : PublicInfo E) (val : Fin n → ℝ), Valid E ε I → (∀ i, OnGrid ε (val i)) →
    ¬ ParetoImprovable E I val (M (withBids E I val))

end PolyClinch.TwoSided


