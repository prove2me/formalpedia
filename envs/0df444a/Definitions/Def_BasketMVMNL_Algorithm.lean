-- Prove2me | Definitions.Def_BasketMVMNL_Algorithm
-- name    : BasketMVMNL_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:47.166987+00:00
-- url     : https://prove2.me/theorems/9620f564-d374-4746-8f10-1c1b1784670e
-- title:
--   Algorithm U1, p.13 — the FPTAS as an instrumented program in the unit-cost model
-- statement:
--   Algorithm U1 takes $\epsilon'>0$ and works as follows.
--
--   1. For each group $j$ and each threshold $t\in\{0,\dots,I\}$ it forms the prefix sums $\sum_{i<t}r_{i,j}v_{i,j}$ and $g=1+\sum_{i<t}v_{i,j}$, and finds the rounding exponent $m$ of $g$ (the least $m\ge1$ with $g\le(1+\epsilon')^m$) by repeated multiplication. It sets $M=\max_j m(1+\sum_i v_{i,j})$.
--   2. For each $K=J,J+1,\dots,JM$ it solves the dynamic program
--   $$
--   \bar V_j(s_{j-1})=\max_{x_j\text{ is RO}}\Big[\frac{\sum_i r_{i,j}v_{i,j}x_{i,j}}{\big[\frac{v_0-1}{(1+\epsilon')^K}+1\big]\bar\gamma_j(x_j)}+\bar V_{j+1}\big(\bar\gamma_j(x_j)\,s_{j-1}\big)\Big]
--   $$
--   with $s_0=1$, $\bar V_{J+1}((1+\epsilon')^K)=0$ and $\bar V_{J+1}((1+\epsilon')^k)=-\infty$ for $k\neq K$, and traces back the maximizing revenue-ordered assortment $x^K$.
--   3. It outputs $\bar x^*=\arg\max_{x\in\{x^K:J\le K\le JM\}}\bar R(x)$, i.e. the candidate with the largest DP value $\bar V_1(1)$.
--
--   The program also counts its operations; `output P ε'` is the returned assortment and `ops P ε'` the count. These are the objects of Theorem 1.
--
--   **Formalization Note** The cost model is the reused `CapacitatedAssort.General.Work` (a state monad counting unit operations): $+,-,\times,/$, comparisons, $\lceil\cdot\rceil_+$, array reads and writes and loop dispatch are charged where they execute. No logarithm or exponential is evaluated, and the program never evaluates $R$ or $\bar R$. The DP state $k$ stands for $s=(1+\epsilon')^k$, so states are integers. The rounding loop runs at most $\lceil(g-1)/\epsilon'\rceil_++1$ steps, which by Bernoulli's inequality suffices, and stops at the first $m$ with $g\le(1+\epsilon')^m$. A $K$ whose DP value is $-\infty$ gives no candidate; ties go to the smallest threshold in a cell and the smallest $K$ overall. Writing the output costs $JI+1$.
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, §4.2, p.13 (Algorithm U1 and the paragraph before it); EC.3, pp.ec5–ec6 (running-time count)

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_BasketMVMNL_Model

namespace BasketMVMNL

open CapacitatedAssort.General

variable {J I : ℕ}

/-- The precomputed data of one group `j`, indexed by the threshold `t ∈ {0, …, I}` of the
revenue-ordered local assortment `{i : i < t}`: `lam[t] = Σ_{i<t} rᵢ,ⱼ vᵢ,ⱼ` (the numerator of the
summand of (7)), `m[t]` the rounding exponent of `γ = 1 + Σ_{i<t} vᵢ,ⱼ`, and
`gbar[t] = (1 + ϵ′)^{m[t]}`, the rounded `γ̄ⱼ`. -/
structure GroupTab where
  lam : Array ℝ
  m : Array ℕ
  gbar : Array ℝ
  deriving Inhabited

/-- The prefix sums `Σ_{i<t} rᵢ,ⱼ vᵢ,ⱼ` and `1 + Σ_{i<t} vᵢ,ⱼ`, `t = 0, …, I`, by one charged pass
over the products of group `j`. -/
noncomputable def prefixSums (P : Instance J I) (j : Fin J) : Work (Array ℝ × Array ℝ) := do
  charge 4 -- two allocations, two initializations
  let mut lam : Array ℝ := #[0]
  let mut g : Array ℝ := #[1]
  let mut accL : ℝ := 0
  let mut accG : ℝ := 1
  for i in List.finRange I do
    charge 9 -- dispatch, three reads, one multiplication, two additions, two pushes
    accL := accL + P.r j i * P.v j i
    accG := accG + P.v j i
    lam := lam.push accL
    g := g.push accG
  return (lam, g)

/-- **The rounding of §4.2, p.13**, for one value `g ≥ 1`: starting from `m = 1` and
`pw = 1 + ϵ′`, multiply `pw` by `1 + ϵ′` while `pw < g`. It returns the least `m ≥ 1` with
`g ≤ (1 + ϵ′)^m` and `pw = (1 + ϵ′)^m`.

**Formalization Note.** The `while` loop is a `for` loop over `fuel = ⌈(g − 1)/ϵ′⌉₊ + 1` steps with
early exit; for `ϵ′ > 0`, Bernoulli's inequality `(1 + ϵ′)^m ≥ 1 + mϵ′` shows the fuel never runs
out. Only executed iterations are charged. No logarithm or exponential is evaluated. -/
noncomputable def roundUp (ε' g : ℝ) : Work (ℕ × ℝ) := do
  charge 6 -- fuel: subtraction, division, integer rounding, addition; two initializations
  let fuel := ⌈(g - 1) / ε'⌉₊ + 1
  let mut m : ℕ := 1
  let mut pw : ℝ := 1 + ε'
  for _ in List.range fuel do
    charge 2 -- dispatch, comparison
    if pw < g then
      charge 3 -- addition 1 + ϵ′, multiplication, increment
      pw := pw * (1 + ε')
      m := m + 1
    else
      break
  return (m, pw)

/-- The table of group `j`: prefix sums, then the rounding of every `γⱼ` of the `I + 1`
revenue-ordered local assortments. -/
noncomputable def groupTable (P : Instance J I) (ε' : ℝ) (j : Fin J) : Work GroupTab := do
  let (lam, g) ← prefixSums P j
  charge 2 -- two allocations
  let mut ms : Array ℕ := #[]
  let mut gb : Array ℝ := #[]
  for t in List.range (I + 1) do
    charge 4 -- dispatch, read, two pushes
    let (m, pw) ← roundUp ε' g[t]!
    ms := ms.push m
    gb := gb.push pw
  return ⟨lam, ms, gb⟩

/-- The tables of all groups, group `j` at index `j`. -/
noncomputable def groupTables (P : Instance J I) (ε' : ℝ) : Work (Array GroupTab) :=
  tabulate J (groupTable P ε')

/-- The terminal row of the DP for a given `K`, Algorithm U1 step 1, p.13:
`V̄_{J+1}((1 + ϵ′)^K) = 0` and `V̄_{J+1}((1 + ϵ′)^k) = −∞` for `k ≠ K`, `k ∈ {0, …, K}`. A cell holds the
value (`⊥` is `−∞`) and the maximizing threshold. -/
def terminalRow (K : ℕ) : Work (Array (WithBot ℝ × ℕ)) :=
  tabulate (K + 1) fun k => do
    charge 2 -- test, write
    return if k.val = K then ((0 : ℝ), 0) else (⊥, 0)

/-- **One cell of the DP of Algorithm U1**, step 1, p.13, at stage `j` (table `tab`) and state
`k`, which stands for `s_{j−1} = (1 + ϵ′)^k`:
`V̄ⱼ(s) = max_{xⱼ RO} [ Σᵢ rᵢ,ⱼ vᵢ,ⱼ xᵢ,ⱼ / ([(v₀ − 1)/(1 + ϵ′)^K + 1] γ̄ⱼ(xⱼ)) + V̄_{j+1}(γ̄ⱼ(xⱼ)·s) ]`.
`c` is `(v₀ − 1)/(1 + ϵ′)^K + 1`, and `next` the row of stage `j + 1`. The maximum runs over the
`I + 1` thresholds `t`; a successor state `k + m[t] > K` is `−∞` by the boundary condition and is
skipped. The first maximizing `t` is kept. -/
noncomputable def dpCell (tab : GroupTab) (c : ℝ) (K k : ℕ) (next : Array (WithBot ℝ × ℕ)) :
    Work (WithBot ℝ × ℕ) := do
  charge 2 -- two initializations
  let mut best : WithBot ℝ := ⊥
  let mut arg : ℕ := 0
  for t in List.range (tab.m.size) do
    charge 4 -- dispatch, read, addition, comparison
    let k' := k + tab.m[t]!
    if k' ≤ K then
      charge 8 -- three reads, multiplication, division, addition, comparison
      let cand : WithBot ℝ := (next[k']!).1 + ((tab.lam[t]! / (c * tab.gbar[t]!) : ℝ) : WithBot ℝ)
      if best < cand then
        charge 2 -- two writes
        best := cand
        arg := t
  return (best, arg)

/-- The row of stage `j`: one cell for every state `k ∈ {0, …, K}`. -/
noncomputable def dpRow (tab : GroupTab) (c : ℝ) (K : ℕ) (next : Array (WithBot ℝ × ℕ)) :
    Work (Array (WithBot ℝ × ℕ)) :=
  tabulate (K + 1) fun k => dpCell tab c K k.val next

/-- **The DP of Algorithm U1 for one `K`**, steps 1–2, p.13: the rows of stages `J, J − 1, …, 1`
computed backwards from the terminal row, then the traceback from stage 1 at `s₀ = 1` (state
`k = 0`). It returns `V̄₁(1)` (`⊥` when no path reaches `(1 + ϵ′)^K`) and the thresholds
`t₀, …, t_{J−1}` of `x^K`. `c` is `(v₀ − 1)/(1 + ϵ′)^K + 1`. -/
noncomputable def dpForK (J : ℕ) (tabs : Array GroupTab) (c : ℝ) (K : ℕ) :
    Work (WithBot ℝ × Array ℕ) := do
  let last ← terminalRow K
  charge (J + 1) -- allocation of the table of rows
  let mut rows : Array (Array (WithBot ℝ × ℕ)) := Array.replicate J #[]
  let mut next := last
  for j in (List.range J).reverse do
    charge 3 -- dispatch, read, write
    let row ← dpRow tabs[j]! c K next
    rows := rows.set! j row
    next := row
  charge 2 -- two initializations
  let mut k : ℕ := 0
  let mut ts : Array ℕ := #[]
  for j in List.range J do
    charge 7 -- dispatch, three reads, addition, push, write
    let t := ((rows[j]!)[k]!).2
    ts := ts.push t
    k := k + (tabs[j]!).m[t]!
  return ((next[0]!).1, ts)

/-- **Algorithm U1**, §4.2, p.13, as an instrumented program in the unit-cost model
`CapacitatedAssort.General.Work` (the state counts operations).

1. For every group, the prefix sums and the rounding exponents `mⱼ` and powers `γ̄ⱼ` of the `I + 1`
   revenue-ordered local assortments; `M = maxⱼ mⱼ(all of group j)`.
2. For each `K = J, …, JM`: `b = (1 + ϵ′)^K` (kept by one multiplication per `K`),
   `c = (v₀ − 1)/b + 1`, and the DP `dpForK`; a `K` whose DP has value `−∞` gives no candidate.
3. Output `x̄* = argmax R̄(x^K)`: the candidate with the largest DP value, the first `K` on ties
   (Algorithm U1 step 2: "By definition, we have R̄(x^K) = V̄₁(1)").

**Formalization Note.** Unit-cost real RAM: `+, −, ×, /`, comparisons, `⌈·⌉₊`, array reads and
writes and loop dispatch are charged where they execute. No logarithm or exponential is used; the
program never evaluates `R` or `R̄`. The DP state `k` stands for `s = (1 + ϵ′)^k`. The returned
assortment is `x j i = (i < tⱼ)`; writing it costs `J·I + 1`. -/
noncomputable def algU1 (P : Instance J I) (ε' : ℝ) : Work (Assortment J I) := do
  let tabs ← groupTables P ε'
  charge 1 -- initialization of M
  let mut M : ℕ := 0
  for j in List.range J do
    charge 4 -- dispatch, two reads, maximum
    M := max M ((tabs[j]!).m[I]!)
  charge 2 -- initialization of b
  let mut b : ℝ := 1
  for _ in List.range J do
    charge 3 -- dispatch, addition, multiplication
    b := b * (1 + ε')
  charge (J + 3) -- initialization of the incumbent
  let mut best : WithBot ℝ := ⊥
  let mut bestTs : Array ℕ := Array.replicate J 0
  for K in List.range' J (J * M + 1 - J) do
    charge 4 -- dispatch, subtraction, division, addition
    let c := (P.v0 - 1) / b + 1
    let (val, ts) ← dpForK J tabs c K
    charge 1 -- comparison
    if best < val then
      charge 2 -- two writes
      best := val
      bestTs := ts
    charge 2 -- addition, multiplication
    b := b * (1 + ε')
  charge (J * I + 1) -- writing the output assortment
  return fun j i => decide (i.val < bestTs[j.val]!)

/-- The assortment `x̄*` returned by Algorithm U1 with input `ϵ′`. -/
noncomputable def output (P : Instance J I) (ε' : ℝ) : Assortment J I :=
  ((algU1 P ε').run 0).1

/-- The number of unit operations Algorithm U1 executes with input `ϵ′`. -/
noncomputable def ops (P : Instance J I) (ε' : ℝ) : ℕ :=
  ((algU1 P ε').run 0).2

end BasketMVMNL


