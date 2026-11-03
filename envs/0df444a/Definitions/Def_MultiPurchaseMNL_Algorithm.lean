-- Prove2me | Definitions.Def_MultiPurchaseMNL_Algorithm
-- name    : MultiPurchaseMNL_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:11.881023+00:00
-- url     : https://prove2.me/theorems/a84dd159-a8f4-4b2f-ab00-4cdba444eecd
-- title:
--   §2.2, §4.1–§4.3, pp.11, 17–19 — the approximation scheme as an instrumented program `ptas`
-- statement:
--   The algorithm of Theorem 1, written as one deterministic program that counts its unit-cost operations ($+,-,\times,/$, comparisons, $\lfloor\cdot\rfloor$, $\lceil\cdot\rceil$, array access, list cons) in the published cost monad `CapacitatedAssort.General.Work`.
--
--   On input $\varepsilon$:
--
--   1. If $\varepsilon\ge1$ or $n=0$, return $\emptyset$. Otherwise set $q=\lceil 2/\varepsilon\rceil$, $\varepsilon'=1/q$, $\delta=\varepsilon'/(6m_{\max})$ and $N=6m_{\max}^2q=6m_{\max}^2/\varepsilon'$.
--   2. Every assortment with at most $N$ products is a candidate (the case $|S^*|\le N$ of §4.1).
--   3. If $N<n$: for every heavy set $H$ with $|H|=N$, compute $L$; for every $\bar w\in\{w_i:i\in L\}$ and every $k=0,1,\dots,K$, where $K$ is the least $k$ with $\bar w(1+\delta)^k\ge n\bar w$, put $W=\bar w(1+\delta)^k$, compute the proxies $\tilde\pi_i$ by the recursion (4), solve the knapsack problem (5) on $L$ with values $r_i\tilde\pi_i$ after rounding weights down to multiples of $u=\delta W/((1+\delta)^2n)$ and accepting rounded totals in $[\lceil W/((1+\delta)u)\rceil-n,\lfloor W/u\rfloor]$, and make $H\cup T$ a candidate when the knapsack returns $T$.
--   4. Return the candidate of largest expected revenue, computed exactly by the recursion of Lemma 1 (`evalR`); ties go to the earlier candidate.
--
--   `output I ε` is the returned assortment and `ops I ε` the number of operations.
--
--   **Formalization Note** Subsets are produced by explicit charged generators (`combos`, `subsetsUpTo`), never by `Finset.powerset` or a choice function. The program never evaluates the Gumbel probabilities: it evaluates revenues only through `evalR`, which Lemma 1 links to the model. The grid and window of the knapsack, $\varepsilon'$, and selection by exact revenue are readings of points the paper leaves informal (§4.1 "1/ϵ takes an integer value", (6) p.19, and the returned "set of products $\tilde S$").
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §2.2, p.11; §4.1, p.17; §4.2, pp.17–19, (4)–(6); §4.3, p.19

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MultiPurchaseMNL_Model

namespace MultiPurchaseMNL

open CapacitatedAssort.General

variable {n mmax : ℕ}

/-! # The approximation scheme of §4 as one instrumented program

Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), §2.2, p.11; §4.1–§4.3, pp.17–19.

**Formalization Note (cost model).** Programs run in `CapacitatedAssort.General.Work`, a state monad
counting operations. Unit-cost operations are `+, −, ×, /, ≤, <` on reals, `⌊·⌋₊`, `⌈·⌉₊`, array
reads and writes, and a cons onto a persistent list. Each `charge k` groups a fixed number of these
operations at the place they execute; loops charge per iteration. Assortments and heavy sets are
lists of products without repetition, and subsets are produced by an explicit charged generator. -/

/-- `w(l) = Σ_{j∈l} wⱼ` by a charged loop. -/
noncomputable def wsumW (I : Instance n mmax) (l : List (Fin n)) : Work ℝ := do
  charge 1 -- initialization
  let mut acc : ℝ := 0
  for j in l do
    charge 3 -- dispatch, read, addition
    acc := acc + I.w j
  return acc

/-- `l − j` (removal of the first occurrence of `j`) by a charged linear scan. -/
def eraseW (l : List (Fin n)) (j : Fin n) : Work (List (Fin n)) := do
  charge (2 * l.length + 1) -- one comparison and one cons per scanned cell
  return l.erase j

/-- Membership `j ∈ l` by a charged linear scan. -/
def memW (l : List (Fin n)) (j : Fin n) : Work Bool := do
  charge (l.length + 1) -- one comparison per scanned cell
  return decide (j ∈ l)

/-- `min_{j∈l} wⱼ` by a charged loop; `0` on the empty list, which the program never passes. -/
noncomputable def minW (I : Instance n mmax) (l : List (Fin n)) : Work ℝ :=
  match l with
  | [] => do charge 1; return 0
  | j :: t => do
      charge 2 -- read, initialization
      let mut acc : ℝ := I.w j
      for k in t do
        charge 3 -- dispatch, read, comparison
        acc := min acc (I.w k)
      return acc

/-- **The recursion of Lemma 1**, §2.2, p.11, executed: `πₘ(i, l)` for a product `i` of the
assortment `l`, by `π₀ = 0` and
`πₘ₊₁(i, l) = (wᵢ + Σ_{j∈l−i} wⱼ · πₘ(i, l−j)) / (1 + w(l))`. -/
noncomputable def piW (I : Instance n mmax) (i : Fin n) : ℕ → List (Fin n) → Work ℝ
  | 0, _ => do charge 1; return 0
  | m + 1, l => do
      let tot ← wsumW I l
      let li ← eraseW l i
      charge 2 -- read, initialization
      let mut acc : ℝ := I.w i
      for j in li do
        charge 1 -- dispatch
        let lj ← eraseW l j
        let v ← piW I i m lj
        charge 3 -- read, multiplication, addition
        acc := acc + I.w j * v
      charge 2 -- addition, division
      return acc / (1 + tot)

/-- **The revenue evaluator of §2.2**, p.11: `R(l) = Σ_{i∈l} rᵢ · Σ_{m=0}^{m_max} Pr[M = m] · πₘ(i, l)`,
with `πₘ` computed by the recursion of Lemma 1 (`piW`). -/
noncomputable def evalR (I : Instance n mmax) (l : List (Fin n)) : Work ℝ := do
  charge 1 -- initialization
  let mut tot : ℝ := 0
  for i in l do
    charge 2 -- dispatch, initialization
    let mut ci : ℝ := 0
    for m in List.finRange (mmax + 1) do
      charge 1 -- dispatch
      let v ← piW I i m.val l
      charge 3 -- read, multiplication, addition
      ci := ci + I.p m * v
    charge 3 -- read, multiplication, addition
    tot := tot + I.r i * ci
  return tot

/-- **The value function (4)**, §4.2, p.18, executed: `V(i, 0, H) = 0` and
`V(i, m+1, H) = (wᵢ + [W/(1+δ)² − δ·w(H₋ᵢ)]⁺ · V(i, m, H) + Σ_{j∈H₋ᵢ} wⱼ · V(i, m, H₋ⱼ))
  / (1 + (1+δ)·W + w(H))`.
It mirrors `MultiPurchaseMNL.V` operation by operation. -/
noncomputable def VW (I : Instance n mmax) (δ W : ℝ) (i : Fin n) : ℕ → List (Fin n) → Work ℝ
  | 0, _ => do charge 1; return 0
  | m + 1, H => do
      let wH ← wsumW I H
      let Hi ← eraseW H i
      let wHi ← wsumW I Hi
      charge 7 -- (1+δ), its square, division, multiplication, subtraction, max, initialization
      let coef := max 0 (W / (1 + δ) ^ 2 - δ * wHi)
      let v0 ← VW I δ W i m H
      charge 3 -- read, multiplication, addition
      let mut acc : ℝ := I.w i + coef * v0
      for j in Hi do
        charge 1 -- dispatch
        let Hj ← eraseW H j
        let v ← VW I δ W i m Hj
        charge 3 -- read, multiplication, addition
        acc := acc + I.w j * v
      charge 5 -- (1+δ), two multiplications/additions, one more addition, division
      return acc / (1 + (1 + δ) * W + wH)

/-- The proxy `π̃ᵢ = Σₘ Pr[M = m] · V(i, m, H)`, §4.2, p.18, executed. -/
noncomputable def proxyW (I : Instance n mmax) (δ W : ℝ) (H : List (Fin n)) (i : Fin n) :
    Work ℝ := do
  charge 1 -- initialization
  let mut acc : ℝ := 0
  for m in List.finRange (mmax + 1) do
    charge 1 -- dispatch
    let v ← VW I δ W i m.val H
    charge 3 -- read, multiplication, addition
    acc := acc + I.p m * v
  return acc

/-- **Subset generator**: every sublist of `l` with exactly `k` elements, by the recursion
`C(x :: xs, k+1) = {x :: s : s ∈ C(xs, k)} ∪ C(xs, k+1)`. One charge per call, per set and per cons. -/
def combos {α : Type} : List α → ℕ → Work (List (List α))
  | _, 0 => do charge 1; return [[]]
  | [], _ + 1 => do charge 1; return []
  | x :: xs, k + 1 => do
      charge 1 -- dispatch
      let withX ← combos xs k
      let withoutX ← combos xs (k + 1)
      let mut out : List (List α) := withoutX
      for s in withX do
        charge 2 -- dispatch, two conses
        out := (x :: s) :: out
      return out

/-- **Subset generator**: every sublist of `l` with at most `k` elements, by the recursion
`U(x :: xs, k+1) = {x :: s : s ∈ U(xs, k)} ∪ U(xs, k+1)`. One charge per call, per set and per cons. -/
def subsetsUpTo {α : Type} : List α → ℕ → Work (List (List α))
  | _, 0 => do charge 1; return [[]]
  | [], _ + 1 => do charge 1; return [[]]
  | x :: xs, k + 1 => do
      charge 1 -- dispatch
      let withX ← subsetsUpTo xs k
      let withoutX ← subsetsUpTo xs (k + 1)
      let mut out : List (List α) := withoutX
      for s in withX do
        charge 2 -- dispatch, two conses
        out := (x :: s) :: out
      return out

/-- A cell of the knapsack table: the best value of a rounded total (`⊥` if unreachable) and a
witness list of products attaining it. -/
structure KCell (n : ℕ) where
  val : WithBot ℝ
  wit : List (Fin n)

instance : Inhabited (KCell n) := ⟨⟨⊥, []⟩⟩

/-- **The knapsack subroutine of (5)–(6)**, §4.2, pp.18–19: maximize `Σ_{i∈T} cᵢ` over `T ⊆ L`
whose total weight lies in `[W/(1+δ), W]`, after rounding weights down to a grid.

The grid is `u = δW/((1+δ)²n)`; product `i` gets the rounded weight `ŵᵢ = ⌊wᵢ/u⌋₊`, and a set is
accepted when its rounded total lies in `[⌈W/((1+δ)u)⌉₊ − n, ⌊W/u⌋₊]`. The table, indexed by the
rounded total, is filled item by item (`s ↦ max(old[s], old[s − ŵᵢ] + cᵢ)`, a new value replacing
the old one only when strictly larger), and the accepted cell of largest value (first one on ties)
is returned with its witness; `none` if no accepted cell is reachable.

**Formalization Note.** The paper rounds to multiples of `δW/n` and does not place the window; this
grid and window make every set of true weight in `[W/(1+δ), W]` accepted and every accepted set of
true weight in `[W/(1+δ)², (1+δ)W]` (reading 4 of the mission). -/
noncomputable def knapsack (I : Instance n mmax) (L : List (Fin n)) (c : Fin n → ℝ) (W δ : ℝ) :
    Work (Option (List (Fin n))) := do
  charge 14 -- u, hi, lo: additions, a square, multiplications, divisions, floor, ceiling, subtraction
  let u : ℝ := δ * W / ((1 + δ) ^ 2 * n)
  let hi : ℕ := ⌊W / u⌋₊
  let lo : ℕ := ⌈W / ((1 + δ) * u)⌉₊ - n
  let mut tab ← tabulate (hi + 1) fun s => do
    charge 2 -- test, write
    return (if s.val = 0 then ⟨((0 : ℝ) : WithBot ℝ), []⟩ else ⟨⊥, []⟩ : KCell n)
  for i in L do
    charge 4 -- dispatch, read, division, floor
    let a : ℕ := ⌊I.w i / u⌋₊
    let old := tab
    tab ← tabulate (hi + 1) fun s => do
      charge 8 -- read, comparison, subtraction, read, read of c, addition, comparison, cons
      let keep := old[s.val]!
      if a ≤ s.val then
        let prev := old[s.val - a]!
        let cand : WithBot ℝ := prev.val + ((c i : ℝ) : WithBot ℝ)
        if keep.val < cand then
          return (⟨cand, i :: prev.wit⟩ : KCell n)
        else
          return keep
      else
        return keep
  let mut best : Option (List (Fin n)) := none
  let mut bestVal : WithBot ℝ := ⊥
  for s in List.range (hi + 1) do
    charge 4 -- dispatch, comparison, read, comparison
    if lo ≤ s then
      let cell := tab[s]!
      if bestVal < cell.val then
        best := some cell.wit
        bestVal := cell.val
  return best

/-- Keep the better of the current best candidate `b = (S, R(S))` and `S'`, evaluating `R(S')`
exactly by `evalR`; ties keep `b`. -/
noncomputable def consider (I : Instance n mmax) (b : List (Fin n) × ℝ) (S' : List (Fin n)) :
    Work (List (Fin n) × ℝ) := do
  let v ← evalR I S'
  charge 1 -- comparison
  if b.2 < v then return (S', v) else return b

/-- **One guess of the heavy set** `H` (§4.1–§4.2, pp.17–19), run against the current best
candidate `b`:
1. the light set `L = {i ∉ H : wᵢ ≤ min_{j∈H} wⱼ}`;
2. for each `w̄ ∈ {wᵢ : i ∈ L}`, the loop bound `K = min{k : w̄(1+δ)^k ≥ n·w̄}` (searched up to
   `fuel`), and for each `k ∈ {0, …, K}` the guess `W = w̄(1+δ)^k`;
3. for each `W`, the proxies `π̃ᵢ = Σₘ Pr[M = m]·V(i, m, H)` of (4), the knapsack of (5)–(6) on
   `L` with values `rᵢ·π̃ᵢ`, and, when it returns `T`, the candidate `H ∪ T`. -/
noncomputable def heavyRound (I : Instance n mmax) (δ : ℝ) (fuel : ℕ) (H : List (Fin n))
    (b : List (Fin n) × ℝ) : Work (List (Fin n) × ℝ) := do
  let mn ← minW I H
  charge 1 -- initialization
  let mut L : List (Fin n) := []
  for i in (List.finRange n).reverse do
    charge 1 -- dispatch
    let inH ← memW H i
    charge 3 -- read, comparison, cons
    if !inH && decide (I.w i ≤ mn) then
      L := i :: L
  let mut best := b
  for wb in L do
    charge 2 -- dispatch, read
    let wbar := I.w wb
    let mut K : ℕ := fuel
    let mut x : ℝ := wbar
    for k in List.range fuel do
      charge 5 -- dispatch, multiplication, comparison, addition, multiplication
      if (n : ℝ) * wbar ≤ x then
        K := k
        break
      x := x * (1 + δ)
    let mut Wk : ℝ := wbar
    for _k in List.range (K + 1) do
      charge 1 -- dispatch
      let prox ← tabulate n fun i => proxyW I δ Wk H i
      let T? ← knapsack I L (fun i => I.r i * prox[i.val]!) Wk δ
      match T? with
      | none => pure ()
      | some T =>
          charge (H.length + 1) -- concatenation
          best ← consider I best (H ++ T)
      charge 2 -- addition, multiplication
      Wk := Wk * (1 + δ)
  return best

/-- **The approximation scheme of Theorem 1**, §4.1–§4.3, pp.17–19, as one deterministic program.

On input `ε`:
1. if `1 ≤ ε` or `n = 0`, return `∅`. Otherwise `q = ⌈2/ε⌉₊`, `ε' = 1/q` (so `1/ε'` is an integer,
   §4.1, p.17, "we assume without loss of generality that 1/ϵ takes an integer value"),
   `δ = ε'/(6·m_max)` and `N = 6·m_max²·q = 6m²_max/ε'`;
2. (the case `|S*| ≤ N` of §4.1) every assortment with at most `N` products is a candidate;
3. (the case `|S*| > N`, run only when `N < n`) for every heavy set `H` with `|H| = N`, the guesses of
   `heavyRound`;
4. the candidate of largest expected revenue, computed exactly by `evalR` (first one on ties; `∅` if
   no candidate has positive revenue), is returned.

**Formalization Note.** The loop bound `K` of `heavyRound` is searched for at most
`fuel = n·6·m_max·q + 1` steps, enough because `(1+δ)^k ≥ 1 + kδ` and `1/δ = 6·m_max·q`. -/
noncomputable def ptas (I : Instance n mmax) (ε : ℝ) : Work (Finset (Fin n)) := do
  charge 2 -- two comparisons
  if 1 ≤ ε ∨ n = 0 then
    return ∅
  charge 10 -- division, ceiling, conversion, division, multiplications for δ, N and fuel
  let q : ℕ := ⌈2 / ε⌉₊
  let εi : ℝ := 1 / (q : ℝ)
  let δ : ℝ := εi / (6 * (mmax : ℝ))
  let N : ℕ := 6 * mmax ^ 2 * q
  let fuel : ℕ := n * (6 * mmax * q) + 1
  charge (n + 1) -- the list of products
  let prods := List.finRange n
  let mut best : List (Fin n) × ℝ := ([], 0)
  let small ← subsetsUpTo prods N
  for S in small do
    charge 1 -- dispatch
    best ← consider I best S
  charge 1 -- comparison
  if N < n then
    let heavy ← combos prods N
    for H in heavy do
      charge 1 -- dispatch
      best ← heavyRound I δ fuel H best
  charge (best.1.length + 1) -- the output bit vector
  return best.1.toFinset

/-- The internal accuracy `ε' = 1/⌈2/ε⌉₊` of `ptas`. -/
noncomputable def epsInt (ε : ℝ) : ℝ := 1 / (⌈2 / ε⌉₊ : ℝ)

/-- The assortment returned by `ptas I ε`. -/
noncomputable def output (I : Instance n mmax) (ε : ℝ) : Finset (Fin n) := ((ptas I ε).run 0).1

/-- The number of operations charged by `ptas I ε`. -/
noncomputable def ops (I : Instance n mmax) (ε : ℝ) : ℕ := ((ptas I ε).run 0).2

end MultiPurchaseMNL


