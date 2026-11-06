-- Prove2me | Definitions.Def_BilateralProfit_OneRound
-- name    : BilateralProfit_OneRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:57.748812+00:00
-- url     : https://prove2.me/theorems/9732df4d-c34e-4003-ab7f-dd81eae6159f
-- title:
--   Algorithm 2 (OneRound) with eqs. (5), (6), (8), as a cost-counted program
-- statement:
--   Fix $K$, $\beta=K^2\log^6K$, and the parameters of eq. (8),
--   $$H=1+\beta\log\big(|\mathcal A|(1+\beta K)\big),\qquad \eta=\frac1{2KH^2},\qquad J=\big\lceil 4K^2H^2\log(|\mathcal A||G_K|)\big\rceil .$$
--   For a table $\rho$ on $G_K\times\mathcal A$, a candidate price $a$ and a bit $z$, eq. (5) defines the update
--   $$Q^\rho_z(a')=\frac{\beta K\,\mathbb P_\rho(A=a'\mid z_a(V)=z)+1/|\mathcal A|}{1+\beta K},$$
--   and for a proposal $(a,Q_0,Q_1)$ and weights $w$, eq. (6) defines the **score**
--   $$h_a(v,a')=\mathrm{Profit}(v,a')-\mathrm{Profit}(v,a)-\beta\log\frac{Q_{z_a(v)}(a')}{w(a')}.$$
--
--   **OneRound**$(w)$ (Algorithm 2): draw $j^\star$ uniformly from $\{1,\dots,J\}$; set $\rho$ uniform on $G_K\times\mathcal A$; for $j=1,\dots,j^\star$: for each $a\in\mathcal A$ form $Q^\rho_0,Q^\rho_1$ by (5) and compute $\mathbb E_\rho[h_a(V,A)]$ by (6); choose a minimizing price $a$ (ties by a fixed order) with its updates $Q_0,Q_1$; update every entry $\rho(v,a')\leftarrow\rho(v,a')(1+\eta h_a(v,a'))/(1+\eta\,\mathbb E_\rho[h_a(V,A)])$. Return the last selected proposal $(a,Q_0,Q_1)$.
--
--   The program is written in a counting monad: every arithmetic operation, logarithm, comparison, table read or write and loop step adds one to a counter, so the same definition yields the proposal and the number of operations used.
--
--   **Formalization Note** The draw $j^\star$ is an input $j\in\{0,\dots,J-1\}$ with $j^\star=j+1$. The fixed order of $\mathcal A$ is lexicographic in the index pair; the first strict minimum is kept. The conditional probability in (5) is the ratio of the joint and the marginal probability, with value $0$ for a zero denominator; along the algorithm the tables stay positive, so this case does not arise. Tables are materialized once per entry; a read costs one unit. The counter is the published `Work` monad (`StateM ℕ`). Bit complexity is not modelled.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §4.1, pp.17–18 (PDF 19–20): eq. (5), eq. (6), Algorithm 2, eq. (8)

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_BilateralProfit_Analysis

namespace BilateralProfit

open CapacitatedAssort.General (Work charge)

/-! # Algorithm 2 (`OneRound`), with equations (5), (6) and (8), as a cost-counted program

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), §4.1, pp.17–18
(PDF 19–20): eq. (5) `Q^ρ_z`, eq. (6) the score `h_a`, Algorithm 2, eq. (8) `H, η, J`.

**Cost model.** Programs run in the published `Work` monad (`StateM ℕ`): the state counts
unit-cost operations. One unit pays for a real `+ − × ÷`, `log`, comparison or Boolean test, a
table cell read or write, a list cons, one loop dispatch. Every line pays through `charge`, with
a comment listing what a grouped charge stands for; nothing computes a value without being
charged where it is computed. The value of a program is its first component; the cost is the
final counter from `0`. There is no separate cost formula.

**Formalization Note.** Tables (`w`, `Q_z`, `ρ`) are materialized by `tab`, which runs the
entry computation once per domain element and stores the result in an association list; a
later read of a table is a cell read (charged inside the grouped charge of the reading line).
`j⋆ ∈ {1, …, J}` is the index `j : Fin J` with `j⋆ = j + 1`, so OneRound performs `j + 1`
iterations. Ties in line 5 are broken by the fixed order `actList` (lexicographic in the index
pair): the first strict minimum is kept. In (5), the conditional probability
`P_ρ(A = a′ | z_a(V) = z)` is `P_ρ(A = a′, z_a(V) = z) / P_ρ(z_a(V) = z)`, with Lean's `x / 0 = 0`
if the denominator vanishes; this never happens along the algorithm, whose tables stay positive,
and `v = (0,1)` always trades and `v = (1,0)` never trades at any `a ∈ 𝒜`. -/

/-- The grid indices in the fixed order (lexicographic). -/
def gridList (K : ℕ) : List (Grid K) :=
  (List.finRange (K + 1)).flatMap fun i => (List.finRange (K + 1)).map fun j => (i, j)

/-- The actions `𝒜` in the fixed order used for tie-breaking (lexicographic). -/
def actList (K : ℕ) : List (Act K) :=
  (gridList K).filterMap fun x => if h : x.1 ≤ x.2 then some ⟨x, h⟩ else none

/-- The decisions `G_K × 𝒜` of the inner MWU, in a fixed order. -/
def tableList (K : ℕ) : List (Grid K × Act K) :=
  (gridList K).flatMap fun v => (actList K).map fun a => (v, a)

/-- `|𝒜|`. -/
noncomputable def nA (K : ℕ) : ℝ := Fintype.card (Act K)

/-- `|G_K| = (K+1)²`. -/
noncomputable def nG (K : ℕ) : ℝ := Fintype.card (Grid K)

/-- `H = 1 + β log(|𝒜|(1 + βK))` (8). -/
noncomputable def Hpar (K : ℕ) : ℝ := 1 + beta K * Real.log (nA K * (1 + beta K * K))

/-- `η = 1/(2KH²)` (8). -/
noncomputable def eta (K : ℕ) : ℝ := 1 / (2 * K * Hpar K ^ 2)

/-- `J = ⌈4K²H² log(|𝒜||G_K|)⌉` (8). -/
noncomputable def Jpar (K : ℕ) : ℕ := ⌈4 * (K : ℝ) ^ 2 * Hpar K ^ 2 * Real.log (nA K * nG K)⌉₊

/-- The weight floor `1/(|𝒜|(1 + βK))` required by Algorithm 2. -/
noncomputable def wFloor (K : ℕ) : ℝ := 1 / (nA K * (1 + beta K * K))

/-- A proposal `(a, Q_0, Q_1)`: a price and its two potential weight updates. -/
abbrev Proposal (K : ℕ) : Type := Act K × (Act K → ℝ) × (Act K → ℝ)

/-- The update `Q_{z_a(v)}` a proposal assigns upon the trade outcome at valuation `v`. -/
noncomputable def Qsel {K : ℕ} (P : Proposal K) (v : Grid K) : Act K → ℝ :=
  if Trades (pt K v) (pt K P.1.1) then P.2.2 else P.2.1

/-- The score (6): `h_a(v, a′) = Profit(v, a′) − Profit(v, a) − β log(Q_{z_a(v)}(a′)/w(a′))`. -/
noncomputable def hScore {K : ℕ} (w : Act K → ℝ) (P : Proposal K) (v : Grid K) (a' : Act K) :
    ℝ :=
  profit (pt K v) (pt K a'.1) - profit (pt K v) (pt K P.1.1) -
    beta K * Real.log (Qsel P v a' / w a')

/-- A charged sum `Σ_{x ∈ l} f x`. -/
def sumW {α : Type} (l : List α) (f : α → Work ℝ) : Work ℝ := do
  charge 1 -- initialise the accumulator
  let mut s : ℝ := 0
  for x in l do
    charge 2 -- loop dispatch, addition
    let y ← f x
    s := s + y
  return s

/-- Materialize a table over the domain list `l`: each entry is computed once, by `f`, and
stored; the table is read back by lookup. -/
def tab {α : Type} [DecidableEq α] (l : List α) (f : α → Work ℝ) : Work (α → ℝ) := do
  charge 1 -- allocate
  let mut acc : List (α × ℝ) := []
  for x in l do
    charge 2 -- loop dispatch, cell write (cons)
    let y ← f x
    acc := (x, y) :: acc
  return fun x => (acc.lookup x).getD 0

/-- For one candidate price `a`: the updates `Q^ρ_0, Q^ρ_1` of (5) and `E_ρ[h_a(V, A)]` by (6)
(Algorithm 2, line 4). -/
noncomputable def candidate (K : ℕ) (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) (a : Act K) :
    Work ((Act K → ℝ) × (Act K → ℝ) × ℝ) := do
  -- `P_ρ(A = a′, z_a(V) = 1)` and `P_ρ(A = a′, z_a(V) = 0)` for every `a′`
  let j1 ← tab (actList K) fun a' => sumW (gridList K) fun v => do
    charge 6 -- read ρ(v,a′), two coordinate reads, two comparisons, multiplication
    pure (ρ (v, a') * tradeBit (pt K v) (pt K a.1))
  let j0 ← tab (actList K) fun a' => sumW (gridList K) fun v => do
    charge 7 -- as above, plus one subtraction
    pure (ρ (v, a') * (1 - tradeBit (pt K v) (pt K a.1)))
  -- `P_ρ(z_a(V) = 1)` and `P_ρ(z_a(V) = 0)`
  let p1 ← sumW (actList K) fun a' => do
    charge 1 -- table read
    pure (j1 a')
  let p0 ← sumW (actList K) fun a' => do
    charge 1 -- table read
    pure (j0 a')
  -- equation (5)
  let Q1 ← tab (actList K) fun a' => do
    charge 9 -- table read, β, K, two products, division, 1/|𝒜|, addition, division
    pure ((beta K * K * (j1 a' / p1) + 1 / nA K) / (1 + beta K * K))
  let Q0 ← tab (actList K) fun a' => do
    charge 9 -- as above
    pure ((beta K * K * (j0 a' / p0) + 1 / nA K) / (1 + beta K * K))
  -- `E_ρ[h_a(V, A)]` by (6)
  let sc ← sumW (tableList K) fun x => do
    charge 20 -- reads of ρ, w, Q; two profits (2 comparisons, subtraction, product each);
              -- trade test; division; log; product by β; two subtractions; product by ρ
    pure (ρ x * hScore w (a, Q0, Q1) x.1 x.2)
  return (Q0, Q1, sc)

/-- One iteration of Algorithm 2 (lines 4–6): select the proposal minimizing `E_ρ[h_a(V, A)]`
(first minimum in `actList` order) and update the table
`ρ(v, a′) ← ρ(v, a′)(1 + ηh_a(v, a′))/(1 + ηE_ρ[h_a(V, A)])`. Returns the selected proposal and
the updated table. -/
noncomputable def oneStep (K : ℕ) (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    Work (Proposal K × (Grid K × Act K → ℝ)) := do
  let mut best : Option (Proposal K × ℝ) := none
  for a in actList K do
    charge 1 -- loop dispatch
    let (Q0, Q1, sc) ← candidate K w ρ a
    match best with
    | none => best := some ((a, Q0, Q1), sc)
    | some (_, bsc) =>
      charge 1 -- comparison
      if sc < bsc then best := some ((a, Q0, Q1), sc)
  charge 1 -- read the selection
  let (P, E) := best.getD (default, 0)
  let ρ' ← tab (tableList K) fun x => do
    charge 22 -- read ρ, the score h (as in `candidate`), η, two products, two additions,
              -- division
    pure (ρ x * (1 + eta K * hScore w P x.1 x.2) / (1 + eta K * E))
  return (P, ρ')

/-- Iterate `oneStep` `n + 1` times from the table `ρ`; return the last selected proposal. -/
noncomputable def oneRoundLoop (K : ℕ) (w : Act K → ℝ) :
    ℕ → (Grid K × Act K → ℝ) → Work (Proposal K)
  | 0, ρ => do
    let (P, _) ← oneStep K w ρ
    return P
  | n + 1, ρ => do
    let (_, ρ') ← oneStep K w ρ
    oneRoundLoop K w n ρ'

/-- Algorithm 2, `OneRound(w)`, with the draw `j⋆ = j + 1 ∈ {1, …, J}` given as input:
initialise `ρ` uniform on `G_K × 𝒜`, run `j⋆` iterations, return the last selected proposal
`(a, Q_0, Q_1)`. -/
noncomputable def oneRound (K : ℕ) (w : Act K → ℝ) (j : Fin (Jpar K)) : Work (Proposal K) := do
  charge 40 -- the parameters β, H, η, J of (8) and the draw of `j⋆`
  let ρ₀ ← tab (tableList K) fun _ => do
    charge 3 -- two cardinalities, division
    pure (1 / (nA K * nG K))
  oneRoundLoop K w j.val ρ₀

/-- The value and the final counter of a `Work` program run from counter `0`. -/
def runW {α : Type} (m : Work α) : α × ℕ := m.run 0

/-- The proposal returned by `OneRound(w)` for the draw `j⋆ = j + 1`. -/
noncomputable def oneRoundVal (K : ℕ) (w : Act K → ℝ) (j : Fin (Jpar K)) : Proposal K :=
  (runW (oneRound K w j)).1

end BilateralProfit


