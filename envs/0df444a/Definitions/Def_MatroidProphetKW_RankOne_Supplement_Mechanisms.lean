-- Prove2me | Definitions.Def_MatroidProphetKW_RankOne_Supplement_Mechanisms
-- name    : MatroidProphetKW_RankOne_Supplement_Mechanisms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:05:09.679839+00:00
-- url     : https://prove2.me/theorems/0457b4fd-7e83-405c-8624-c7127f78c86d
-- title:
--   §6, pp. 11–14 — BMUMD mechanisms, IR + truthful class, mechanism M (Alg. 1), table V (17), adversary (Alg. 2), M^copies (Alg. 3)
-- statement:
--   The setting is Bayesian multi-parameter unit-demand mechanism design (BMUMD). There is a finite set $\mathcal U$ of services, partitioned into groups $J_1,\dots,J_n$, one per bidder, and a family $\mathcal I$ of feasible sets. **Unit demand** means that every feasible set meets every $J_i$ in at most one service. Values are independent, $v_x\sim F_x$. Prices are $p_x=\varphi_x^{-1}(T(A,x))$ if $A\cup\{x\}\in\mathcal I$ and $p_x=\infty$ otherwise, where $A$ is the set allocated so far and $T(A,x)$ is the threshold that the prophet-inequality algorithm uses for $x$ after accepting $A$.
--
--   1. **Deterministic mechanisms.** A mechanism maps reported values $b$ to an allocation $\mathcal A(b)\subseteq\mathcal U$ and payments $\pi_i(b)$. It is **individually rational and truthful** when, on the type space:
--      - its allocations are feasible;
--      - it is dominant-strategy incentive compatible: no bidder gains by misreporting its values for $J_i$, whatever the others report;
--      - a served bidder pays at most its value for its service, and an unserved bidder pays $0$;
--      - its allocation events and payments are measurable and its payments integrable.
--
--      Its revenue $R(\mathcal A)$ is the expected total payment.
--   2. **Mechanism $M$ (Algorithm 1).** Bidders $1,\dots,n$ are processed in order. Bidder $i$ sees the prices $(p_x)_{x\in J_i}$. Among the services with $b_x\ge p_x$ it buys one of maximal utility $b_x-p_x$ and pays $p_x$, and $x$ is added to $A$. If no service of $J_i$ has $b_x\ge p_x$, it buys nothing and pays $0$.
--   3. **Table (17).** $V(A,n)=0$. For $i<n$, sort $J_{i+1}$ as $x_1,\dots,x_k$ by increasing $p_x+V(A\cup\{x\},i+1)$, with prices computed at $A$, and set
--   $$V(A,i)=\Big(\prod_{j=1}^kF_{x_j}(p_{x_j})\Big)V(A,i+1)+\sum_{\ell=1}^k\Big(\prod_{j=1}^{\ell-1}F_{x_j}(p_{x_j})\Big)\big(1-F_{x_\ell}(p_{x_\ell})\big)\big(p_{x_\ell}+V(A\cup\{x_\ell\},i+1)\big),$$
--   with $F(\infty)=1$, so a term with an infinite price vanishes.
--   4. **Adversary (Algorithm 2) and $M^{\mathrm{copies}}$ (Algorithm 3).** With $A$ allocated after $J_1,\dots,J_{i-1}$, the adversary presents $J_i$ in increasing order of $p_x+V(A\cup\{x\},i)$. $M^{\mathrm{copies}}$ sells to the first $x$ in this order with $b_x\ge p_x$, charges it $p_x$ and adds it to $A$; if there is none it sells nothing in $J_i$. Its revenue $R(M^{\mathrm{copies}})$ and virtual surplus $\Phi(M^{\mathrm{copies}})=\mathbb E[\sum_{x\in A}\varphi_x(v_x)]$ are expectations under truthful bids.
--
--   $M$ is the posted-price mechanism of Theorem 1. $M^{\mathrm{copies}}$ is the single-parameter mechanism through which its revenue is compared with the prophet inequality, in (18) and (19).
--
--   **Formalization Note** The carrier `BMech` is an abbreviation of the published `CHMSPricing.UnitDemand.MultiMechanism`, whose allocation and payment fields have no distribution assumptions. Its bounded-support truthfulness predicate is not used: `IsTruthfulIR` is defined locally on the present, possibly unbounded type space. Bidders are `Fin n` (0-based), and group `i` in the code is the paper's $J_{i+1}$. Feasibility and the thresholds are parameters `feas` and `T`; the theorems instantiate them. Sorting ties and the bidder's ties between equally good services are broken by the fixed enumeration `Fintype.equivFin`. $F(p)=\Pr[v\le p]$ is used for the probability $\Pr[v<p]$ of not buying, which is the same because the laws have densities. The adversary's key uses $V(A\cup\{x\},i)$ for the paper's 1-based group $J_i$. The paper's line 17 prints $V(A\cup\{x\},i-1)$; preprocessing line 7 and the proof of (18) both use the table entry that follows the group. $M^{\mathrm{copies}}$ computes thresholds at its own allocated set. This preserves the source price test on the original virtual values. A run on clipped weights can accept a negative virtual value at threshold zero; the copies mechanism rejects that value. Thus the paper's claim of identical selected sets is used only with the original virtual-value acceptance test, up to null price-boundary events, rather than literally with the clipped run.
--
--   The table is extended to stage 0 by (17), as used in the proof of (18); the printed preprocessing loop lists only stages n through 1. Values on infeasible A or after stage n are unused defaults.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 11, §6 (BMUMD, Lemma 4's mechanism class); p. 12, Algorithm 1; p. 13, Algorithm 2 and (17); p. 14, Algorithm 3

import Mathlib
import Definitions.Def_MatroidProphetKW_RankOne_Supplement_ValueDist
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace MatroidProphetKW.RankOne.Supplement

open MeasureTheory

/-!
Kleinberg & Weinberg, *Matroid Prophet Inequalities*, arXiv:1201.4764v1, §6 (pp. 11–15).

The services `𝒰` form a finite type `α`; the bidders are `Fin n`, in the order `0, 1, …, n − 1`
(the paper's `1, …, n`); `owner x` is the bidder whose group `J_i = {x | owner x = i}` contains
`x`. The feasibility constraint is a predicate `feas` on finite sets of services, and `T A x` is the
threshold `T(A, x)` of the prophet-inequality algorithm (instantiated in the theorems with the
§3.3 thresholds (9) for a matroid and the §4.2 thresholds for an intersection of `p` matroids).
-/

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- BMUMD's unit-demand assumption (§6, p. 11): every feasible set meets every group `J_i` in at
most one service. -/
def IsUnitDemand (feas : Finset α → Prop) (owner : α → Fin n) : Prop :=
  ∀ S, feas S → ∀ i, (S.filter (fun x => owner x = i)).card ≤ 1

/-! ### Deterministic BMUMD mechanisms and the benchmark class -/

/-- A deterministic direct mechanism for a BMUMD instance: it maps the reported value profile
`b = (b_x)_{x ∈ 𝒰}` to an allocation `alloc b ⊆ 𝒰` and a payment `pay b i` of every bidder `i`.
This reuses the published carrier, which has no assumptions on value distributions;
the local truthfulness predicate below uses the present support intervals. -/
abbrev BMech (α : Type*) (n : ℕ) := CHMSPricing.UnitDemand.MultiMechanism α n

namespace BMech

/-- The value, at true values `v`, of the services of `J_i` that `A` allocates at reports `b`
(`0` when none; under unit demand there is at most one). -/
noncomputable def valueOf (A : BMech α n) (owner : α → Fin n) (i : Fin n) (v b : α → ℝ) : ℝ :=
  ∑ x ∈ (A.alloc b).filter (fun x => owner x = i), v x

/-- Quasilinear utility of bidder `i` with true values `v` when the report profile is `b`. -/
noncomputable def utility (A : BMech α n) (owner : α → Fin n) (i : Fin n) (v b : α → ℝ) : ℝ :=
  A.valueOf owner i v b - A.pay b i

/-- Expected revenue `R(A) = E_v[∑_i π_i(v)]` under the prior, bids truthful. -/
noncomputable def revenue (D : α → ValueDist) (A : BMech α n) : ℝ :=
  ∫ v, ∑ i, A.pay v i ∂(prior D)

end BMech

/-- An individually rational and truthful deterministic BMUMD mechanism (the class of Lemma 4,
p. 11, from Chawla–Hartline–Malec–Sivan [5]): on the type space,
* its allocation is feasible;
* it is dominant-strategy incentive compatible: no bidder `i` gains by misreporting its values for
  the services of `J_i` (all of them at once), whatever the reports of the others;
* it is individually rational: a served bidder pays at most its value for the service it gets, and
  an unserved bidder pays `0`;
* its allocation events are measurable and its payments measurable and integrable. -/
structure IsTruthfulIR (D : α → ValueDist) (feas : Finset α → Prop) (owner : α → Fin n)
    (A : BMech α n) : Prop where
  feasible : ∀ v ∈ typeSpace D, feas (A.alloc v)
  dsic : ∀ v ∈ typeSpace D, ∀ i, ∀ b ∈ typeSpace D, (∀ x, owner x ≠ i → b x = v x) →
    A.utility owner i v b ≤ A.utility owner i v v
  ir_served : ∀ v ∈ typeSpace D, ∀ i, ∀ x ∈ A.alloc v, owner x = i → A.pay v i ≤ v x
  ir_unserved : ∀ v ∈ typeSpace D, ∀ i,
    (A.alloc v).filter (fun x => owner x = i) = ∅ → A.pay v i = 0
  alloc_measurable : ∀ x, MeasurableSet {v | x ∈ A.alloc v}
  pay_measurable : ∀ i, Measurable (fun v => A.pay v i)
  pay_integrable : ∀ i, Integrable (fun v => A.pay v i) (prior D)

/-! ### Prices -/

open Classical in
/-- The posted price of service `x` when the set `A` has been allocated (Algorithm 1, line 4,
p. 12; Algorithm 2, lines 6 and 16; Algorithm 3, line 7): `p_x = φ_x^{-1}(T(A, x))` if
`A ∪ {x}` is feasible, and `∞` otherwise. -/
noncomputable def price (D : α → ValueDist) (feas : Finset α → Prop) (T : Finset α → α → ℝ)
    (A : Finset α) (x : α) : WithTop ℝ :=
  if feas (insert x A) then (D x).phiInv (T A x) else ⊤

/-- The real amount charged at price `p` (only used where `p` is finite). -/
noncomputable def charge (p : WithTop ℝ) : ℝ := p.untopD 0

/-- `F_x(p)` at a price `p ∈ ℝ ∪ {∞}`, with `F_x(∞) = 1`. -/
noncomputable def cdfTop (D : ValueDist) : WithTop ℝ → ℝ
  | ⊤ => 1
  | (r : ℝ) => D.cdf r

/-- The first element of a finite set of services in the fixed enumeration `Fintype.equivFin`
(the fixed tie-breaking rule), or `none` if the set is empty. -/
noncomputable def pickFirst (S : Finset α) : Option α :=
  if h : S.Nonempty then
    some ((Fintype.equivFin α).symm ((S.image (Fintype.equivFin α)).min' (h.image _)))
  else none

/-! ### Mechanism `M` (Algorithm 1) -/

open Classical in
/-- Line 7 of Algorithm 1: bidder `i`, facing the posted prices `p_x = price … A x` of its
services `x ∈ J_i`, with (reported) values `b`, buys a service `x` with `b_x ≥ p_x` maximizing its
utility `b_x − p_x` (ties broken by the fixed enumeration), and buys nothing if there is no service
with `b_x ≥ p_x`. -/
noncomputable def bidderChoice (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) (A : Finset α) (i : Fin n) (b : α → ℝ) :
    Option α :=
  let K := Finset.univ.filter (fun x => owner x = i ∧ price D feas T A x ≤ ((b x : ℝ) : WithTop ℝ))
  pickFirst (K.filter (fun x => ∀ y ∈ K,
    b y - charge (price D feas T A y) ≤ b x - charge (price D feas T A x)))

/-- The set `A` allocated by mechanism `M` after bidders `0, …, k − 1` have been processed. -/
noncomputable def mStage (D : α → ValueDist) (feas : Finset α → Prop) (T : Finset α → α → ℝ)
    (owner : α → Fin n) (b : α → ℝ) : ℕ → Finset α
  | 0 => ∅
  | k + 1 =>
    if h : k < n then
      match bidderChoice D feas T owner (mStage D feas T owner b k) ⟨k, h⟩ b with
      | some x => insert x (mStage D feas T owner b k)
      | none => mStage D feas T owner b k
    else mStage D feas T owner b k

/-- Mechanism `M` (Algorithm 1, p. 12) as a direct mechanism: bidders `0, 1, …, n − 1` are offered,
in this order, the posted prices `p_x = φ_x^{-1}(T(A, x))` (`∞` if `A ∪ {x}` is infeasible) of their
services; bidder `i` chooses as in `bidderChoice`, receives the chosen service and pays its price,
or receives nothing and pays `0`. -/
noncomputable def mechM (D : α → ValueDist) (feas : Finset α → Prop) (T : Finset α → α → ℝ)
    (owner : α → Fin n) : BMech α n where
  alloc b := mStage D feas T owner b n
  pay b i :=
    match bidderChoice D feas T owner (mStage D feas T owner b i) i b with
    | some x => charge (price D feas T (mStage D feas T owner b i) x)
    | none => 0

/-! ### The dynamic program (17) of Algorithm 2 -/

open Classical in
/-- The services of group `J_i` sorted in increasing order of `key`, ties broken by the fixed
enumeration `Fintype.equivFin` (Algorithm 2, lines 7 and 17). -/
noncomputable def sortGroup (owner : α → Fin n) (i : Fin n) (key : α → WithTop ℝ) : List α :=
  ((Finset.univ.filter (fun x => owner x = i)).toList).insertionSort
    (fun x y => key x < key y ∨ (key x = key y ∧ Fintype.equivFin α x ≤ Fintype.equivFin α y))

/-- One backward step of (17) (p. 13): with `cont = V(·, i + 1)` (0-based group `i` is the paper's
`J_{i+1}`) and prices `p_x = price … A x`, sort `J_{i+1}` as `x_1, …, x_k` by increasing
`p_x + V(A ∪ {x}, i + 1)` and return
`(∏_{j=1}^k F_{x_j}(p_{x_j})) · V(A, i+1) + ∑_{ℓ=1}^k (∏_{j=1}^{ℓ−1} F_{x_j}(p_{x_j})) ·
(1 − F_{x_ℓ}(p_{x_ℓ})) · (p_{x_ℓ} + V(A ∪ {x_ℓ}, i+1))`, with `F(∞) = 1` (so a term with an
infinite price vanishes). -/
noncomputable def Vstep (D : α → ValueDist) (feas : Finset α → Prop) (T : Finset α → α → ℝ)
    (owner : α → Fin n) (i : Fin n) (cont : Finset α → ℝ) (A : Finset α) : ℝ :=
  let xs := sortGroup owner i (fun x => price D feas T A x + ((cont (insert x A) : ℝ) : WithTop ℝ))
  let Fp : Fin xs.length → ℝ := fun j => cdfTop (D xs[j]) (price D feas T A xs[j])
  (∏ j, Fp j) * cont A +
    ∑ l : Fin xs.length, (∏ j ∈ Finset.univ.filter (fun j => j < l), Fp j) * (1 - Fp l) *
      (charge (price D feas T A xs[l]) + cont (insert xs[l] A))

/-- Auxiliary recursion: `Vaux m k = V(·, k)` when `m = n − k` groups remain. -/
noncomputable def Vaux (D : α → ValueDist) (feas : Finset α → Prop) (T : Finset α → α → ℝ)
    (owner : α → Fin n) : ℕ → ℕ → Finset α → ℝ
  | 0, _, _ => 0
  | m + 1, k, A => if h : k < n then Vstep D feas T owner ⟨k, h⟩ (Vaux D feas T owner m (k + 1)) A
      else 0

/-- The table `V(A, k)` of Algorithm 2 (p. 13), `k = 0, …, n` bidders processed: `V(A, n) = 0` and,
for `k < n`, `V(A, k)` is given by (17) from `V(·, k + 1)`. -/
noncomputable def V (D : α → ValueDist) (feas : Finset α → Prop) (T : Finset α → α → ℝ)
    (owner : α → Fin n) (k : ℕ) (A : Finset α) : ℝ :=
  Vaux D feas T owner (n - k) k A

/-! ### The adversary (Algorithm 2, main loop) and mechanism `M^copies` (Algorithm 3) -/

/-- The order in which the adversary presents group `J_i` (0-based) once `A` has been allocated
(Algorithm 2, lines 16–17, p. 13): increasing `p_x + V(A ∪ {x}, i + 1)`, where `i + 1` is the number
of groups processed after `J_i`. -/
noncomputable def advGroupOrder (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) (A : Finset α) (i : Fin n) : List α :=
  sortGroup owner i (fun x => price D feas T A x + ((V D feas T owner ((i : ℕ) + 1) (insert x A) : ℝ) : WithTop ℝ))

open Classical in
/-- In group `J_i`, `M^copies` sells to the first service `x` in the adversary's order with
`b_x ≥ p_x` (Algorithm 3, line 12, p. 14; Algorithm 2, lines 19–20), or to nobody. -/
noncomputable def copiesChoice (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) (A : Finset α) (i : Fin n) (b : α → ℝ) :
    Option α :=
  (advGroupOrder D feas T owner A i).find? (fun x => decide (price D feas T A x ≤ ((b x : ℝ) : WithTop ℝ)))

/-- The set `A` allocated by `M^copies` after groups `0, …, k − 1` have been processed. -/
noncomputable def copiesStage (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) (b : α → ℝ) : ℕ → Finset α
  | 0 => ∅
  | k + 1 =>
    if h : k < n then
      match copiesChoice D feas T owner (copiesStage D feas T owner b k) ⟨k, h⟩ b with
      | some x => insert x (copiesStage D feas T owner b k)
      | none => copiesStage D feas T owner b k
    else copiesStage D feas T owner b k

/-- The allocation of `M^copies` at bids `b` (Algorithm 3, p. 14). -/
noncomputable def copiesAlloc (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) (b : α → ℝ) : Finset α :=
  copiesStage D feas T owner b n

/-- The total payment collected by `M^copies` at bids `b`: in each group the selected service pays
its posted price (Algorithm 3, line 14). -/
noncomputable def copiesPayment (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) (b : α → ℝ) : ℝ :=
  ∑ i : Fin n,
    match copiesChoice D feas T owner (copiesStage D feas T owner b i) i b with
    | some x => charge (price D feas T (copiesStage D feas T owner b i) x)
    | none => 0

/-- `R(M^copies)`: the expected revenue of `M^copies` under the prior, bids truthful (`b = v`). -/
noncomputable def copiesRevenue (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) : ℝ :=
  ∫ v, copiesPayment D feas T owner v ∂(prior D)

/-- `Φ(M^copies)`: the expected virtual surplus `E_v[∑_{x ∈ A(v)} φ_x(v_x)]` of the allocation of
`M^copies` (§6, pp. 11–12), bids truthful. -/
noncomputable def copiesVirtualSurplus (D : α → ValueDist) (feas : Finset α → Prop)
    (T : Finset α → α → ℝ) (owner : α → Fin n) : ℝ :=
  ∫ v, ∑ x ∈ copiesAlloc D feas T owner v, (D x).phi (v x) ∂(prior D)

end MatroidProphetKW.RankOne.Supplement


