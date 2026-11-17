-- Prove2me | Definitions.Def_SupplyRevenue_Supplement_Sampled
-- name    : SupplyRevenue_Supplement_Sampled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:32:34.468476+00:00
-- url     : https://prove2.me/theorems/be780cde-d4cf-4b3c-a566-222e7c39cf58
-- title:
--   The sampled interface: oracle programs, their law and costs, and the deployed matrix law
-- statement:
--   This file models the **sampled interface** of the paper (p.3): an algorithm accesses the instance $D$ and the source $\sigma$ only by sampling.
--
--   A **program** is a controller that, from its rational input and the transcript of all answers received so far, chooses the next query:
--
--   1. **halt** with a list of rationals (the stored data);
--   2. **coin**: one fair bit, the program's only own randomness;
--   3. **draw a type** of buyer $i$: a fresh independent type from $D_i$, answered by a handle that may be queried any number of times;
--   4. **draw a source atom** of buyer $i$: a fresh atom of $\sigma_i$, drawn with its weight, answered by its assortment and rational prices;
--   5. **demand query** on a handle at a chosen assortment and nonnegative rational prices: answered by the tie-ruled full-stock demand of that drawn type.
--
--   There is no other access: no values, clauses, supports, masses, expectations, orders or partitions. The law of a run is obtained by unfolding the program step by step (types by their masses, atoms by their weights, coins with probability $1/2$); expectations over halted runs are suprema over the unfolding depth in $[0,\infty]$, and a run that never halts contributes $0$.
--
--   Each run records the numbers of type draws, source draws, demand queries and fair coins, the largest bit size of a query, and the total bit size of the source offers observed. The bit size of a rational is the binary length of its numerator and denominator.
--
--   **Deployment** runs a second program on the stored data that may only toss coins and draw source atoms; its output is decoded into a personalized price matrix $P$. The deployed revenue in order $\pi$ is $\mathbb E_{\text{deploy}}[\mathrm{Rev}(P,D,\pi)]$, and the **inclusive revenue** is $\mathbb E_{\text{training}}\bigl[\mathbb E_{\text{deploy}}[\mathrm{Rev}]\bigr]$, training failure counted as $0$. `CostBounds` collects the cost clauses of Theorem 1.2: termination with probability one, polynomial counts on every run, polynomial query, stored and deployed bit sizes, and polynomially many fair coins in expectation.
--
--   **Formalization Note** Programs are functions from (input, transcript) to the next query; Theorem 1.2 requires them to be `Computable`. An invalid buyer index, or a type or demand query during deployment, ends the run without output. A demand query on an invalid handle answers $\emptyset$, and query prices are clamped at $0$. Polynomials are $c(1+x)^k$.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), p.3 (Sampled interface) and Theorem 1.2, pp.3–4

import Mathlib
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Supplement_Classes

open scoped ENNReal

namespace SupplyRevenue
namespace Supplement

/-!
# The sampled interface: oracle programs, their law, costs and the deployed matrix law

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
p.3, "Sampled interface": "Independent type draws are reusable for repeated exact-demand queries at chosen rational
prices and assortments, not merely one observed purchase. Source draws are independent of type; a rational source and
calibration R ≤ R̂ ≤ 2R, R > 0, are supplied. There is no value, clause, support, expectation, stock-law, worst-order or
source-optimization oracle, nor a valuation-denominator or minimum-marginal input. Store rational response rules and
weights, not training types or stocks. Deployment uses fresh source/row coins sampled before arrivals; a common branch
may correlate rows." Theorem 1.2, pp.3–4: counts, bit lengths, "rejection-based sampling work … polynomial in
expectation", "including training failure".

**Formalization Note**
* A program is a **controller** `List ℚ × List (List ℚ) → Query`: from its rational input and the transcript of all
  oracle answers so far it chooses the next query. Theorems require the controller to be `Computable` (Mathlib's
  computability on `Primcodable` types), so it is an algorithm; no running-time bound is part of the model, since
  Theorem 1.2 claims none beyond the listed counts, bits and expected coins.
* Queries: `halt out` stops with the stored rational list `out`; `coin` is one fair bit (the program's only own
  randomness: no Bernoulli or uniform primitive); `drawType i` draws a fresh independent type of buyer `i` from `D i`
  and answers its handle (the number of earlier type draws), which may be queried any number of times;
  `drawSource i` draws a fresh atom of `σ i` with its weight and answers the offer as rationals (price on assortment
  items, `-1` off the assortment); `demand h A p` answers, as `m` indicator bits, the tie-ruled full-stock demand of
  drawn type `h` at the offer with assortment `A` and prices `max 0 (p_j)` (an invalid handle answers `∅`). There is no
  other access: the controller never sees `D`, `σ`'s weights, values, the order, `tie` or `δ`.
* An invalid buyer index, or (in deployment) a type or demand query, ends the run without output (probability mass
  lost), so the termination clauses of the theorems exclude them.
* The law of a run is built by unfolding `k` steps (`runE`), and the expectation of a nonnegative `f` over halted runs is
  `⨆ k` in `ℝ≥0∞` (`expectRun`); a run that never halts contributes `0`. Zero-mass types and atoms contribute `0`, so
  "every run" means every run of positive probability.
* The cost record counts type draws, source draws, demand queries and fair coins, the largest query size, and the total
  size of the source offers observed. `sizeQ q` is the binary length of numerator and denominator.
* Deployment runs a second controller on input `[n, m] ++ stored` with no type or demand query; its output is decoded
  into a price matrix by `decodeMatrix` (entry `2(im+j)` nonzero: `j` on buyer `i`'s assortment; entry `2(im+j)+1`:
  the price, clamped at `0`). Its revenue in order `π` is `E_deploy[Rev(P, D, π)]`, and the inclusive revenue is
  `E_training[E_deploy[Rev]]`, training failure included as `0`.
-/

/-- The bit size of a rational: binary lengths of the numerator's absolute value and of the denominator. -/
def sizeQ (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den

/-- The size of a list of rationals: its length plus the sizes of its entries. -/
def sizeL (l : List ℚ) : ℕ := l.length + (l.map sizeQ).sum

/-- A query of a sampled-interface program. -/
inductive Query where
  | halt (out : List ℚ)
  | coin
  | drawType (i : ℕ)
  | drawSource (i : ℕ)
  | demand (h : ℕ) (A : List ℕ) (p : List ℚ)

/-- Queries as a sum type, for computability. -/
def Query.equiv : Query ≃ (List ℚ ⊕ (Unit ⊕ (ℕ ⊕ (ℕ ⊕ (ℕ × List ℕ × List ℚ))))) where
  toFun
    | .halt o => .inl o
    | .coin => .inr (.inl ())
    | .drawType i => .inr (.inr (.inl i))
    | .drawSource i => .inr (.inr (.inr (.inl i)))
    | .demand h A p => .inr (.inr (.inr (.inr (h, A, p))))
  invFun
    | .inl o => .halt o
    | .inr (.inl _) => .coin
    | .inr (.inr (.inl i)) => .drawType i
    | .inr (.inr (.inr (.inl i))) => .drawSource i
    | .inr (.inr (.inr (.inr (h, A, p)))) => .demand h A p
  left_inv := by intro q; cases q <;> rfl
  right_inv := by intro x; rcases x with o | _ | i | i | ⟨h, A, p⟩ <;> rfl

instance : Primcodable Query := Primcodable.ofEquiv _ Query.equiv

/-- The size of a query (its numbers and rationals, in binary). -/
def Query.size : Query → ℕ
  | .halt out => sizeL out
  | .coin => 0
  | .drawType i => Nat.size i
  | .drawSource i => Nat.size i
  | .demand h A p => Nat.size h + A.length + (A.map Nat.size).sum + sizeL p

/-- A program of the sampled interface: the next query as a function of the input and the answers so far. -/
abbrev Controller := List ℚ × List (List ℚ) → Query

/-- The cost record of a run. -/
structure Cost where
  types : ℕ
  sources : ℕ
  demands : ℕ
  coins : ℕ
  maxQuery : ℕ
  observed : ℕ

/-- The empty cost record. -/
def Cost.zero : Cost := ⟨0, 0, 0, 0, 0, 0⟩

/-- A halted run: the stored rational output and the cost record. -/
structure Outcome where
  out : List ℚ
  cost : Cost

/-- The answer to a source draw: per item, the price if on the assortment, `-1` otherwise. -/
noncomputable def observeOffer {m : ℕ} (o : Offer m) : List ℚ :=
  List.ofFn fun j : Fin m => if j ∈ o.assort then toRat (o.price j) else -1

/-- The offer posed by a demand query: assortment `{j : j ∈ A}`, prices `max 0 (p_j)` (missing entries `0`). -/
noncomputable def queryOffer (m : ℕ) (A : List ℕ) (p : List ℚ) : Offer m where
  assort := Finset.univ.filter fun j : Fin m => j.val ∈ A
  price := fun j => max 0 ((p.getD j.val 0 : ℚ) : ℝ)
  price_nonneg := fun _ => le_max_left _ _

/-- The answer to a demand query on handle `h`: the tie-ruled full-stock demand of the `h`-th drawn type, as `m`
indicator values; an invalid handle answers `∅`. -/
noncomputable def demandAnswer {n m : ℕ} (tie : Tie m) (D : Instance n m)
    (ty : List (Σ i : Fin n, Fin (D i).numTypes)) (h : ℕ) (A : List ℕ) (p : List ℚ) : List ℚ :=
  let Q : Finset (Fin m) :=
    match ty[h]? with
    | some x => demand tie ((D x.1).val x.2) (queryOffer m A p) Finset.univ
    | none => ∅
  List.ofFn fun j : Fin m => if j ∈ Q then 1 else 0

/-- The expectation of `f` over runs halted within `k` steps, from transcript `tr`, drawn types `ty`, cost `c`.
`typesAllowed = false` (deployment) makes type and demand queries end the run without output. -/
noncomputable def runE {n m : ℕ} (ctrl : Controller) (tie : Tie m) (D : Instance n m) (σ : Source n m)
    (typesAllowed : Bool) (inp : List ℚ) (f : Outcome → ℝ≥0∞) :
    ℕ → List (List ℚ) → List (Σ i : Fin n, Fin (D i).numTypes) → Cost → ℝ≥0∞
  | 0, _, _, _ => 0
  | k + 1, tr, ty, c =>
    let q := ctrl (inp, tr)
    let c := { c with maxQuery := max c.maxQuery q.size }
    match q with
    | .halt out => f ⟨out, c⟩
    | .coin =>
        2⁻¹ * runE ctrl tie D σ typesAllowed inp f k (tr ++ [[1]]) ty { c with coins := c.coins + 1 } +
        2⁻¹ * runE ctrl tie D σ typesAllowed inp f k (tr ++ [[0]]) ty { c with coins := c.coins + 1 }
    | .drawType i =>
        if h : i < n ∧ typesAllowed = true then
          ∑ θ : Fin (D ⟨i, h.1⟩).numTypes, ENNReal.ofReal ((D ⟨i, h.1⟩).mass θ) *
            runE ctrl tie D σ typesAllowed inp f k (tr ++ [[(ty.length : ℚ)]]) (ty ++ [⟨⟨i, h.1⟩, θ⟩])
              { c with types := c.types + 1 }
        else 0
    | .drawSource i =>
        if h : i < n then
          ∑ a : Fin (σ ⟨i, h⟩).N, ENNReal.ofReal ((σ ⟨i, h⟩).weight a) *
            runE ctrl tie D σ typesAllowed inp f k (tr ++ [observeOffer ((σ ⟨i, h⟩).atom a)]) ty
              { c with sources := c.sources + 1,
                       observed := c.observed + sizeL (observeOffer ((σ ⟨i, h⟩).atom a)) }
        else 0
    | .demand hd A p =>
        if typesAllowed = true then
          runE ctrl tie D σ typesAllowed inp f k (tr ++ [demandAnswer tie D ty hd A p]) ty
            { c with demands := c.demands + 1 }
        else 0

/-- `E[f(outcome)]` over halted runs (nonhalting runs contribute `0`), in `ℝ≥0∞`. -/
noncomputable def expectRun {n m : ℕ} (ctrl : Controller) (tie : Tie m) (D : Instance n m) (σ : Source n m)
    (typesAllowed : Bool) (inp : List ℚ) (f : Outcome → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ k, runE ctrl tie D σ typesAllowed inp f k [] [] Cost.zero

/-- Expectation over a training run on input `inp` (full sampled interface). -/
noncomputable def trainE {n m : ℕ} (ctrl : Controller) (tie : Tie m) (D : Instance n m) (σ : Source n m)
    (inp : List ℚ) (f : Outcome → ℝ≥0∞) : ℝ≥0∞ :=
  expectRun ctrl tie D σ true inp f

/-- Expectation over a deployment run on stored data `stored` (input `[n, m] ++ stored`; coins and source draws only). -/
noncomputable def deployE {n m : ℕ} (ctrl : Controller) (tie : Tie m) (D : Instance n m) (σ : Source n m)
    (stored : List ℚ) (f : Outcome → ℝ≥0∞) : ℝ≥0∞ :=
  expectRun ctrl tie D σ false ((n : ℚ) :: (m : ℚ) :: stored) f

/-- The price matrix encoded by a deployment output. -/
noncomputable def decodeMatrix (n m : ℕ) (l : List ℚ) : Matrix' n m := fun i =>
  { assort := Finset.univ.filter fun j : Fin m => l.getD (2 * (i.val * m + j.val)) 0 ≠ 0
    price := fun j => max 0 ((l.getD (2 * (i.val * m + j.val) + 1) 0 : ℚ) : ℝ)
    price_nonneg := fun _ => le_max_left _ _ }

/-- The expected actual revenue, in order `π`, of the matrix law deployed from stored data. -/
noncomputable def deployRev {n m : ℕ} (ctrlD : Controller) (tie : Tie m) (D : Instance n m) (σ : Source n m)
    (stored : List ℚ) (π : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  deployE ctrlD tie D σ stored fun o => ENNReal.ofReal (rev tie D (decodeMatrix n m o.out) π)

/-- The inclusive revenue in order `π`: `E_training[E_deploy[Rev]]`, training failure counted as `0`. -/
noncomputable def inclusiveRev {n m : ℕ} (ctrlT ctrlD : Controller) (tie : Tie m) (D : Instance n m)
    (σ : Source n m) (inp : List ℚ) (π : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  trainE ctrlT tie D σ inp fun o => deployRev ctrlD tie D σ o.out π

/-- A polynomial bound `c (1 + x)^k`. -/
def poly (c k x : ℕ) : ℕ := c * (1 + x) ^ k

/-- `⌈log₂(1/ρ)⌉`. -/
def logInv (ρ : ℚ) : ℕ := Nat.clog 2 ⌈ρ⁻¹⌉₊

open Classical in
/-- The cost clauses of Theorem 1.2 for one training/deployment pair on input `inp`, with the polynomial `c(1+x)^k`.
`lρ = ⌈log₂(1/ρ)⌉` (`0` without `ρ`) and `sIn` the size of the rational inputs.
1. Training halts with probability one, and so does deployment from every stored output.
2. On every training run and every deployment run, type draws + source draws + demand queries `≤ poly(n + m + lρ)`.
3. The size of every query (so every queried price and assortment) and of the stored data `≤ poly(n + m + lρ + sIn +
   observed)`, with `observed` the total size of the source offers seen in that run (in deployment: in both runs).
4. The expected numbers of fair coins of training and of deployment are `≤ poly(n + m + lρ + sIn)`. -/
def CostBounds {n m : ℕ} (ctrlT ctrlD : Controller) (c k : ℕ) (tie : Tie m) (D : Instance n m)
    (σ : Source n m) (inp : List ℚ) (lρ sIn : ℕ) : Prop :=
  trainE ctrlT tie D σ inp (fun _ => 1) = 1 ∧
  trainE ctrlT tie D σ inp
      (fun o => if deployE ctrlD tie D σ o.out (fun _ => 1) = 1 then 0 else 1) = 0 ∧
  trainE ctrlT tie D σ inp
      (fun o => if o.cost.types + o.cost.sources + o.cost.demands ≤ poly c k (n + m + lρ) ∧
          o.cost.maxQuery ≤ poly c k (n + m + lρ + sIn + o.cost.observed) ∧
          sizeL o.out ≤ poly c k (n + m + lρ + sIn + o.cost.observed) then 0 else 1) = 0 ∧
  trainE ctrlT tie D σ inp
      (fun o => deployE ctrlD tie D σ o.out
        (fun o' => if o'.cost.types + o'.cost.sources + o'.cost.demands ≤ poly c k (n + m + lρ) ∧
            o'.cost.maxQuery ≤ poly c k (n + m + lρ + sIn + o.cost.observed + o'.cost.observed) ∧
            sizeL o'.out ≤ poly c k (n + m + lρ + sIn + o.cost.observed + o'.cost.observed)
          then 0 else 1)) = 0 ∧
  trainE ctrlT tie D σ inp (fun o => (o.cost.coins : ℝ≥0∞)) ≤ (poly c k (n + m + lρ + sIn) : ℝ≥0∞) ∧
  trainE ctrlT tie D σ inp (fun o => deployE ctrlD tie D σ o.out (fun o' => (o'.cost.coins : ℝ≥0∞))) ≤
    (poly c k (n + m + lρ + sIn) : ℝ≥0∞)

end Supplement
end SupplyRevenue


