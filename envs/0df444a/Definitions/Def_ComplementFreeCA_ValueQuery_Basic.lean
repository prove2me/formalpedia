-- Prove2me | Definitions.Def_ComplementFreeCA_ValueQuery_Basic
-- name    : ComplementFreeCA_ValueQuery_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:54:34.426834+00:00
-- url     : https://prove2.me/theorems/e7841f79-ef8e-4534-ac47-06c4ca91495f
-- title:
--   Combinatorial auctions with complement-free bidders: the value-query algorithm, maximal-in-range rules and VCG incentive compatibility
-- statement:
--   This bundle fixes the model of §1 and §5 of Dobzinski, Nisan and Schapira (2010). A set $M=\{1,\dots,m\}$ of items is sold to $n$ bidders. Bidder $i$ has a **valuation** $v_i$ assigning a real value $v_i(S)$ to every bundle $S\subseteq M$; a **profile** is the tuple $v=(v_1,\dots,v_n)$.
--
--   1. **Normalized**, **monotone**, **complement free** (p. 1–2): $v(\emptyset)=0$; $S\subseteq T\Rightarrow v(S)\le v(T)$; $v(S\cup T)\le v(S)+v(T)$ for all $S,T$. A **CF valuation** has all three properties.
--   2. **Allocation and welfare** (p. 1): an allocation $A=(A_1,\dots,A_n)$ gives pairwise disjoint bundles (items may stay unallocated); its social welfare under $v$ is $\sum_i v_i(A_i)$.
--   3. **Matchings** (§5.2, step (ii)): a matching in the complete bipartite graph between items $a_j$ and bidders $b_i$ is a partial map from items to bidders under which no bidder receives two items. Its weight under reports $b$ is the sum of the edge costs $b_i(\{j\})$ over its edges; the allocation it induces gives every matched item to its bidder.
--   4. **Tie-breaking rules.** A maximum-weight matching rule chooses, for every report profile $b$, a matching of maximum weight under $b$. A top-bidder rule chooses, for every $b$, a bidder maximizing $b_i(M)$.
--   5. **The algorithm** (§5.2, step (iii)): on reports $b$, if the top bidder's value $b_{\mathrm{top}}(M)$ is strictly higher than the weight $|P|$ of the chosen maximum-weight matching $P$, all items go to the top bidder; otherwise every edge $(a_j,b_i)\in P$ gives item $j$ to bidder $i$.
--   6. **Range and maximal in range** (§5.1): the range of the algorithm consists of the allocations giving all of $M$ to one bidder and the allocations in which every bidder receives at most one item. An allocation rule is maximal in range with range $R$ on a domain $D$ of valuations if, at every report profile from $D$, it outputs an allocation of $R$ maximizing reported welfare over $R$.
--   7. **VCG payments and incentive compatibility** (§5.1): bidder $i$ receives $\sum_{k\ne i} b_k(f(b)_k)$, so its total utility with true valuation $v_i$ is $v_i(f(b)_i)+\sum_{k\ne i}b_k(f(b)_k)$. The mechanism is incentive compatible on $D$ if, for every profile $v$ from $D$, every bidder $i$ and every misreport $v_i'\in D$, reporting $v_i$ gives $i$ at least the utility of reporting $v_i'$ while the others report $v_{-i}$.
--
--   These objects are shared by the statements of Theorem 5.1 and its proof.
--
--   **Formalization Note** Bidders are `Fin n`, items `Fin m`, bundles `Finset (Fin m)`. A matching is `μ : Fin m → Option (Fin n)`; `μ j = some i` means item $j$ is matched to bidder $i$. The maximum-weight matching and the top bidder are not unique, so they enter as function parameters `mat`, `top` of the report profile with specification predicates, and every statement is quantified over all such rules; the algorithm reads only the reports. The payment follows the paper's convention that the mechanism pays the bidders (footnote 2, p. 11). `IncentiveCompatibleOn` mirrors `AGT.MechIncentiveCompatible` (platform definition `agt_mechanism`) on the outcomes $a\mapsto v_i(a_i)$ with Groves payments $h_i=0$.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 1 (§1, model), p. 2 (complement free), p. 11 (§5.1 VCG and maximal in range; §5.2 steps (i)–(iii))

import Mathlib

namespace ComplementFreeCA.ValueQuery

open Finset

/-! Model of Dobzinski–Nisan–Schapira, *Approximation Algorithms for Combinatorial Auctions with
Complement-Free Bidders*, Math. Oper. Res. 35(1), 2010: §1 (pp. 1–2), §5.1 and §5.2 (p. 11).
Bidders are `Fin n`, items `Fin m`, bundles `Finset (Fin m)`, a valuation is
`Finset (Fin m) → ℝ`, and a (report) profile is `Fin n → Finset (Fin m) → ℝ`. -/

/-- A valuation is **normalized** if `v ∅ = 0` (p. 1). -/
def IsNormalized {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  v ∅ = 0

/-- A valuation is **monotone** if `S ⊆ T → v S ≤ v T` (p. 1). -/
def IsMonotone {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T : Finset (Fin m), S ⊆ T → v S ≤ v T

/-- A valuation is **complement free** (subadditive): `v (S ∪ T) ≤ v S + v T` for all `S, T`
(p. 2). -/
def IsCF {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T : Finset (Fin m), v (S ∪ T) ≤ v S + v T

/-- The valuations of the paper's CF setting: normalized and monotone (the standing assumptions
of p. 1) and complement free (p. 2). -/
def IsCFValuation {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  IsNormalized v ∧ IsMonotone v ∧ IsCF v

/-- An **allocation** gives the bidders pairwise disjoint bundles (`S_i ∩ S_j = ∅` for `i ≠ j`,
p. 1). Items may stay unallocated. -/
def IsAllocation {n m : ℕ} (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i k : Fin n, i ≠ k → Disjoint (A i) (A k)

/-- The **social welfare** `∑ i, v_i(A_i)` of an allocation `A` under the profile `v` (p. 1). -/
def welfare {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (A : Fin n → Finset (Fin m)) : ℝ :=
  ∑ i, v i (A i)

/-- A **matching** in the complete bipartite graph between items and bidders (§5.2, step (ii)),
encoded as a partial map `μ` from items to bidders: `μ j = some i` means the edge `(a_j, b_i)`
is in the matching. It is a matching when no bidder is matched to two items. -/
def IsMatching {n m : ℕ} (μ : Fin m → Option (Fin n)) : Prop :=
  ∀ (j j' : Fin m) (i : Fin n), μ j = some i → μ j' = some i → j = j'

/-- The **weight** of a matching `μ` under the reports `b`: the sum of the edge costs
`b_i({j})` over the edges `(a_j, b_i)` of `μ` (§5.2, step (ii)). -/
def matchingWeight {n m : ℕ} (b : Fin n → Finset (Fin m) → ℝ) (μ : Fin m → Option (Fin n)) : ℝ :=
  ∑ j, (μ j).elim 0 (fun i => b i {j})

/-- The allocation read off a matching: bidder `i` receives the items matched to it
(§5.2, step (iii), second alternative). -/
def matchingAlloc {n m : ℕ} (μ : Fin m → Option (Fin n)) : Fin n → Finset (Fin m) :=
  fun i => univ.filter (fun j => μ j = some i)

/-- `mat` is a **maximum-weight matching rule**: for every report profile `b`, `mat b` is a
matching whose weight under `b` is at least that of every matching. Ties are left to `mat`. -/
def IsMaxWeightMatchingRule {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n)) : Prop :=
  ∀ b : Fin n → Finset (Fin m) → ℝ,
    IsMatching (mat b) ∧ ∀ μ : Fin m → Option (Fin n), IsMatching μ →
      matchingWeight b μ ≤ matchingWeight b (mat b)

/-- `top` picks, for every report profile `b`, a bidder maximizing the reported value `b_i(M)`
of the grand bundle (§5.2, step (iii)). Ties are left to `top`. -/
def IsTopBidderRule {n m : ℕ} (top : (Fin n → Finset (Fin m) → ℝ) → Fin n) : Prop :=
  ∀ (b : Fin n → Finset (Fin m) → ℝ) (i : Fin n), b i univ ≤ b (top b) univ

/-- The allocation giving all items `M` to bidder `i` and nothing to the others. -/
def allToOne {n m : ℕ} (i : Fin n) : Fin n → Finset (Fin m) :=
  fun k => if k = i then univ else ∅

/-- **The algorithm of §5.2** on the report profile `b`, given a maximum-weight matching rule
`mat` and a top-bidder rule `top`: if the reported value `b_top(M)` of the bidder maximizing
`b_i(M)` is higher than the weight of the matching `P = mat b`, all items go to that bidder;
otherwise every matched item goes to its matched bidder. It reads only the reports. -/
noncomputable def alg {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n))
    (top : (Fin n → Finset (Fin m) → ℝ) → Fin n)
    (b : Fin n → Finset (Fin m) → ℝ) : Fin n → Finset (Fin m) :=
  if matchingWeight b (mat b) < b (top b) univ then allToOne (top b) else matchingAlloc (mat b)

/-- The **range** of the algorithm of §5.2: the allocations giving all items to one bidder, and
the allocations in which every bidder receives at most one item. -/
def ValueQueryRange {n m : ℕ} : Set (Fin n → Finset (Fin m)) :=
  {a | (∃ i, a = allToOne i) ∨ (IsAllocation a ∧ ∀ i, (a i).card ≤ 1)}

/-- An allocation rule `f` is **maximal in range** with range `R` on the valuation domain `D`
(§5.1, p. 11): at every report profile drawn from `D`, `f` outputs an allocation of `R` that
maximizes the reported welfare over `R`. -/
def IsMaximalInRange {n m : ℕ} (D : (Finset (Fin m) → ℝ) → Prop)
    (R : Set (Fin n → Finset (Fin m)))
    (f : (Fin n → Finset (Fin m) → ℝ) → Fin n → Finset (Fin m)) : Prop :=
  ∀ b : Fin n → Finset (Fin m) → ℝ, (∀ k, D (b k)) →
    f b ∈ R ∧ ∀ a ∈ R, welfare b a ≤ welfare b (f b)

/-- The **VCG payment** of §5.1 received by bidder `i` when the allocation rule `f` runs on the
reports `b`: the sum `∑_{k ≠ i} b_k(f(b)_k)` of the other bidders' reported values. -/
def vcgPayment {n m : ℕ} (f : (Fin n → Finset (Fin m) → ℝ) → Fin n → Finset (Fin m))
    (i : Fin n) (b : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  ∑ k ∈ univ.erase i, b k (f b k)

/-- The **total utility** of bidder `i` with true valuation `vi` when `f` with VCG payments runs
on the reports `b`: the value of its bundle plus the payment it receives (§5.1). -/
def vcgUtility {n m : ℕ} (f : (Fin n → Finset (Fin m) → ℝ) → Fin n → Finset (Fin m))
    (i : Fin n) (vi : Finset (Fin m) → ℝ) (b : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  vi (f b i) + vcgPayment f i b

/-- The mechanism given by the allocation rule `f` and the VCG payments of §5.1 is
**incentive compatible** (truthful in dominant strategies) on the valuation domain `D`: for every
profile `v` of valuations in `D`, every bidder `i` and every misreport `v'` in `D`, reporting
`v i` truthfully gives bidder `i` at least the utility of reporting `v'`, whatever the others
report. -/
def IncentiveCompatibleOn {n m : ℕ} (D : (Finset (Fin m) → ℝ) → Prop)
    (f : (Fin n → Finset (Fin m) → ℝ) → Fin n → Finset (Fin m)) : Prop :=
  ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ k, D (v k)) → ∀ (i : Fin n) (v' : Finset (Fin m) → ℝ),
    D v' → vcgUtility f i (v i) (Function.update v i v') ≤ vcgUtility f i (v i) v

end ComplementFreeCA.ValueQuery


