-- Prove2me | Definitions.Def_MenuCostPricing_Algorithm
-- name    : MenuCostPricing_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:14.444508+00:00
-- url     : https://prove2.me/theorems/c0ed2aef-f94f-459d-8054-831183ae3832
-- title:
--   §3.3–§3.7 and App. B.1, B.6 — the FPTAS as an instrumented program: weight guesses, the evaluator (19), the table of $\hat{\mathcal V}$, the traceback and the final selection
-- statement:
--   The algorithm of Theorem 3.1 written as a program in a unit-cost RAM model whose state counts operations (the reused `CapacitatedAssort.General.Work` monad). With $\epsilon_h=\min(\epsilon,1)$ and $\delta=\epsilon_h/(8\varrho_{\max})$:
--
--   1. enumerate the $L^T$ single-product price vectors and their price-change counts;
--   2. **weight guesses** (Lemma 3.2, App. B.1): $K=\lceil\log_{1+\delta}n\rceil$ by a multiply-until loop, candidates $w^t_{i\ell}(1+\delta)^k$, $k\le K$, for each period, and all vectors of one candidate per period;
--   3. for every guess $\hat w$: the rewards $\hat{\mathcal R}^i_{2\delta,\delta}(x_i)$ of every product and price vector by the **evaluator** (19), which fills $\hat{\mathcal R}(t,u)$ for $u=0,\dots,u^1_i$ backwards from $\hat{\mathcal R}(T+1,\cdot)=0$ using binomial masses computed by square and multiply;
--   4. for every $\Gamma\subseteq[2,T]$ and every $\rho_{\mathrm{single}}$ among those rewards: the table of $\hat{\mathcal V}$ over the grid states, bottom-up, each cell storing its value and first minimizer; $\hat\rho$ by (11); the strategy $\hat x$ obtained by following the minimizers from $(1,\vec0,\hat\rho)$, with its proxy reward;
--   5. return the candidate with the largest proxy reward (first on ties), or nothing.
--
--   `output I ε` is the strategy returned and `ops I ε` the number of unit operations executed; `guessCandidate` and `tableEntry` expose step 4 for one guess.
--
--   **Formalization Note** Unit cost: $+,-,\times,/$ and comparisons on reals and naturals, $\lfloor\cdot\rfloor$, $\lceil\cdot\rceil$, input reads, array reads and writes, list cons, loop dispatch; each is charged where it executes. Powers are computed by charged repeated multiplication and square-and-multiply, never in one step; no logarithm is evaluated; the binomial loop never runs up to a support point $\nu$ (given in binary). The program never evaluates $R$ or any measure. The selection of step 5 is the reading of "after accounting for the guessing procedure" (§3.7): every candidate is feasible, so selecting by proxy reward is sound.
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.3, p.15; §3.6–§3.7, pp.19–22; App. B.1, p.46; App. B.6, pp.51–52

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP

namespace MenuCostPricing

open CapacitatedAssort.General

variable {n L T : ℕ}

namespace Instance

variable (I : Instance n L T)

/-- Input read: the price `p_{iℓ}` at natural indices (`0` out of range). -/
def pAt (i ℓ : ℕ) : ℝ := if h : i < n ∧ ℓ < L then I.p ⟨i, h.1⟩ ⟨ℓ, h.2⟩ else 0

/-- Input read: the weight `wᵗ_{iℓ}` at natural indices (`0` out of range). -/
def wAt (t i ℓ : ℕ) : ℝ :=
  if h : t < T ∧ i < n ∧ ℓ < L then I.w ⟨t, h.1⟩ ⟨i, h.2.1⟩ ⟨ℓ, h.2.2⟩ else 0

/-- Input read: the starting inventory `u¹ᵢ` at a natural index (`0` out of range). -/
def uAt (i : ℕ) : ℕ := if h : i < n then I.u ⟨i, h⟩ else 0

/-- Input read: the support list of `Nₜ` at a natural index (empty out of range). -/
def suppAt (t : ℕ) : List ℕ := if h : t < T then I.supp ⟨t, h⟩ else []

/-- Input read: the mass `Pr[Nₜ = ν]` at a natural index (`0` out of range). -/
def massAt (t ν : ℕ) : ℝ := if h : t < T then I.mass ⟨t, h⟩ ν else 0

end Instance

/-- `a ^ k` by square and multiply: one loop iteration per bit of `k` (plus the final test), each
charged. The loop is a `while e ≠ 0` loop; `k + 1` is only fuel, and only executed iterations are
charged. -/
noncomputable def powW (a : ℝ) (k : ℕ) : Work ℝ := do
  charge 3 -- three initializations
  let mut acc : ℝ := 1
  let mut b : ℝ := a
  let mut e : ℕ := k
  for _ in List.range (k + 1) do
    charge 2 -- dispatch, test e = 0
    if e = 0 then break
    charge 5 -- parity test, multiplication, squaring, halving, write
    if e % 2 = 1 then
      acc := acc * b
    b := b * b
    e := e / 2
  return acc

namespace Instance

variable (I : Instance n L T)

/-- **The evaluator of `R̂ⁱ_{α,β}(xᵢ)`, equation (19), App. B.6, pp.51–52.** For product `i` with
price-level digits `xi` (`xi[t]` is the level in period `t`), guesses `ŵ` and accuracy `β`, it fills
the table `R̂(t, u)`, `u = 0, …, u¹ᵢ`, for `t = T, …, 1` from the base case `R̂(T + 1, ·) = 0`:
`R̂(t, u) = Σ_{ν∈Sₜ} Pr[Nₜ = ν] Σ_{d≤ν} Pr[D̂ᵗᵢ = d | Nₜ = ν]·(min{d, u}·p + R̂(t + 1, [u − d]⁺))`,
with `[D̂ᵗᵢ | Nₜ = ν] ∼ Binomial(ν, q̂)`, and returns `R̂(1, u¹ᵢ)`.

**Formalization Note.** For each listed `ν` the masses `C(ν, d)·q̂^d·(1 − q̂)^{ν−d}` are computed only
for `d < m = min{u¹ᵢ, ν + 1}`: one charged square-and-multiply power `(1 − q̂)^{ν+1−m}`, then
incremental products. All `d ≥ u` share `min{d, u} = u` and `[u − d]⁺ = 0`, so their total mass
`1 − Σ_{d<min{u,m}} Pr[d]` is one tail term. The loop never runs `d` up to `ν`, which is given in
binary. `q̂` is clamped to `[0, 1]` exactly as in `Instance.proxyLaw`. -/
noncomputable def evalReward (ŵ : Array ℝ) (β : ℝ) (i : ℕ) (xi : Array ℕ) : Work ℝ := do
  charge 1 -- read u¹ᵢ
  let u := I.uAt i
  charge (u + 2) -- allocation of the row R̂(T + 1, ·) = 0
  let mut next : Array ℝ := Array.replicate (u + 1) 0
  for s in List.range T do
    -- dispatch, index T − 1 − s (2), reads of xᵢ, w, p, ŵₜ, q̂ (addition, multiplication,
    -- addition, division), clamp (two comparisons), allocation
    charge 15
    let t := T - 1 - s
    let ℓ := xi[t]!
    let pr := I.pAt i ℓ
    let q := clampUnit (I.wAt t i ℓ / (1 + (1 + β) * ŵ[t]!))
    charge (u + 1)
    let mut cur : Array ℝ := Array.replicate (u + 1) 0
    for ν in I.suppAt t do
      charge 7 -- dispatch, mass read, addition, minimum, subtraction 1 − q̂, exponent (2)
      let pν := I.massAt t ν
      let m := min u (ν + 1)
      let r := 1 - q
      let base ← powW r (ν + 1 - m)
      charge 2 -- two initializations
      let mut pw : Array ℝ := #[]
      let mut acc : ℝ := 1
      for _ in List.range m do
        charge 3 -- dispatch, push, multiplication
        pw := pw.push acc
        acc := acc * r
      charge 3 -- three initializations
      let mut P : Array ℝ := #[]
      let mut c : ℝ := 1
      let mut qd : ℝ := 1
      for d in List.range m do
        -- dispatch, index m − 1 − d (2), read, three multiplications, push, binomial update
        -- (subtraction, two casts, multiplication, addition, division), power update
        charge 14
        P := P.push (c * qd * base * pw[m - 1 - d]!)
        c := c * ((ν - d : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)
        qd := qd * q
      for u' in List.range (u + 1) do
        charge 4 -- dispatch, minimum, two initializations
        let kmax := min u' m
        let mut acc2 : ℝ := 0
        let mut tot : ℝ := 0
        for d in List.range kmax do
          -- dispatch, two reads, subtraction, cast, multiplication, two additions,
          -- multiplication, addition
          charge 10
          acc2 := acc2 + P[d]! * ((d : ℝ) * pr + next[u' - d]!)
          tot := tot + P[d]!
        -- tail: subtraction, cast, multiplication, read, addition, multiplication, addition;
        -- update: read, multiplication, addition, write
        charge 11
        acc2 := acc2 + (1 - tot) * ((u' : ℝ) * pr + next[0]!)
        cur := cur.set! u' (cur[u']! + pν * acc2)
    next := cur
  charge 1 -- read R̂(1, u¹ᵢ)
  return next[u]!

end Instance

/-- All `L^T` single-product price vectors, as digit arrays (`m ↦` its mixed-radix digits, period
`0` least significant), with the number `∆ⁱ(xᵢ)` of price changes of each. -/
noncomputable def optionTable (L T : ℕ) : Work (Array (Array ℕ) × Array ℕ) := do
  let bases := Array.replicate T L
  charge (T + 1) -- building the bases
  let nOpt ← boxSize bases
  charge 2 -- two initializations
  let mut opts : Array (Array ℕ) := #[]
  let mut dls : Array ℕ := #[]
  for m in List.range nOpt do
    charge 1 -- dispatch
    let dig ← decode bases m
    charge (T + 2) -- conversion of the digits, initialization
    let xi := dig.map Int.toNat
    let mut cnt : ℕ := 0
    for s in List.range T do
      charge 5 -- dispatch, test, two reads, comparison
      if 1 ≤ s then
        if xi[s - 1]! ≠ xi[s]! then
          charge 1 -- increment
          cnt := cnt + 1
    charge 2 -- two pushes
    opts := opts.push xi
    dls := dls.push cnt
  return (opts, dls)

namespace Instance

variable (I : Instance n L T)

/-- The table `R̂ⁱ_{α,β}(xᵢ)` for every product `i` and every option `m` of `optionTable`, by
`evalReward`. -/
noncomputable def rhatTable (ŵ : Array ℝ) (β : ℝ) (opts : Array (Array ℕ)) :
    Work (Array (Array ℝ)) :=
  tabulate n fun i => tabulate opts.size fun m => do
    charge 1 -- read of the option
    I.evalReward ŵ β i.val opts[m.val]!

/-- **The weight guesses of Lemma 3.2 / App. B.1, p.46.** First `K = ⌈log_{1+δ} n⌉`, the least `k`
with `(1 + δ)^k ≥ n`, by a charged multiply-until loop (no logarithm is evaluated; the fuel
`⌈n/δ⌉ + 1` suffices since `(1 + δ)^k ≥ 1 + kδ`, and only executed iterations are charged). For each
period `t` the candidates are `wᵗ_{iℓ}·(1 + δ)^k` for every product `i`, level `ℓ` and
`k = 0, …, K` (the guess `wᵗmax` of B.1 is one of the `wᵗ_{iℓ}`); the output is every vector with
one candidate per period, enumerated in mixed radix (period `0` least significant). -/
noncomputable def weightGuesses (δ : ℝ) : Work (Array (Array ℝ)) := do
  charge 6 -- fuel: division, ceiling, addition; three initializations
  let fuel := ⌈(n : ℝ) / δ⌉₊ + 1
  let mut K : ℕ := 0
  let mut pw : ℝ := 1
  for _ in List.range fuel do
    charge 3 -- dispatch, cast, comparison
    if (n : ℝ) ≤ pw then break
    charge 3 -- addition, multiplication, increment
    pw := pw * (1 + δ)
    K := K + 1
  charge 1 -- initialization
  let mut cands : Array (Array ℝ) := #[]
  for t in List.range T do
    charge 2 -- dispatch, initialization
    let mut row : Array ℝ := #[]
    for i in List.range n do
      charge 1 -- dispatch
      for ℓ in List.range L do
        charge 2 -- dispatch, read
        let mut c := I.wAt t i ℓ
        for _ in List.range (K + 1) do
          charge 4 -- dispatch, push, addition, multiplication
          row := row.push c
          c := c * (1 + δ)
    charge 1 -- push
    cands := cands.push row
  charge (T + 4) -- two multiplications, an addition, building the bases
  let C := n * L * (K + 1)
  let bases := Array.replicate T C
  let total ← boxSize bases
  charge 1 -- initialization
  let mut out : Array (Array ℝ) := #[]
  for j in List.range total do
    charge 2 -- dispatch, initialization
    let dig ← decode bases j
    let mut g : Array ℝ := #[]
    for s in List.range T do
      charge 5 -- dispatch, two reads, conversion, push
      g := g.push ((cands[s]!)[(dig[s]!).toNat]!)
    charge 1 -- push
    out := out.push g
  return out

/-- **The table of the approximate dynamic program `V̂`, (9)–(10), p.20**, for the guess
`(Γ, ŵ, ρ_single)` (`gam[t]` is `t ∈ Γ`) and accuracy `δ`, given the options `opts`, their price-change
counts `dls` and the rewards `rh[i][m] = R̂ⁱ_{2δ,δ}(option m)`. Row `i` (`i = 0, …, n`; row `n` is the
base case (10)) has one cell per grid state `(ω, ρ) ∈ Dω × Dρ`, at index `j·(⌈n²/δ⌉ + 1) + kρ` with `j`
the mixed-radix index of the weight indices `kω` (radix `⌈n/δ⌉ + 1`, period `0` least significant).
A cell holds the value (`⊤` is `∞`) and the first option attaining the minimum.

**Formalization Note.** Rows are computed bottom-up, each cell once (a recursion without the table
would be exponential). The reward index is updated by truncated subtraction (clamp at `0`), the
weight indices by `roundIdx`; both are computed with charged arithmetic (`⌊·⌋₊` is unit cost). -/
noncomputable def dpTable (δ : ℝ) (gam : Array Bool) (ŵ : Array ℝ) (ρs : ℝ)
    (opts : Array (Array ℕ)) (dls : Array ℕ) (rh : Array (Array ℝ)) :
    Work (Array (Array (WithTop ℝ × ℕ))) := do
  charge 10 -- ⌈n/δ⌉ (division, ceiling), ⌈n²/δ⌉ (square, division, ceiling), step of Dρ (3)
  let kw := ⌈(n : ℝ) / δ⌉₊
  let kr := ⌈(n : ℝ) ^ 2 / δ⌉₊
  let sR := δ * ρs / n
  let sW ← tabulate T fun t => do
    charge 4 -- read, multiplication, division, write
    return δ * ŵ[t.val]! / n
  let bases := Array.replicate T (kw + 1)
  charge (T + 2) -- building the bases
  let nW ← boxSize bases
  charge 2 -- addition, multiplication
  let nS := nW * (kr + 1)
  let kRt ← tabulate n fun i => tabulate opts.size fun m => do
    charge 6 -- read, comparison, division, floor, minimum, write
    return roundIdx sR kr (rh[i.val]!)[m.val]!
  let okG ← tabulate opts.size fun m => do
    charge 1 -- initialization
    let mut ok := true
    for s in List.range T do
      charge 6 -- dispatch, test, three reads, comparison
      if 1 ≤ s then
        if gam[s]! = false ∧ (opts[m.val]!)[s - 1]! ≠ (opts[m.val]!)[s]! then
          ok := false
    return ok
  let base ← tabulate nS fun st => do
    charge 5 -- division, remainder, cast, multiplication, comparison
    let j := st.val / (kr + 1)
    let kρ := st.val % (kr + 1)
    let kωz ← decode bases j
    let mut ok := decide ((kρ : ℝ) * sR ≤ 0)
    for s in List.range T do
      charge 8 -- dispatch, three reads, subtraction, two multiplications, comparison
      if ¬ ((1 - 2 * δ) * ŵ[s]! ≤ (((kωz[s]!).toNat : ℕ) : ℝ) * sW[s]!) then
        ok := false
    charge 1 -- write
    return (if ok then ((0 : ℝ) : WithTop ℝ) else ⊤, 0)
  charge (n + 3) -- allocation of the rows
  let mut rows : Array (Array (WithTop ℝ × ℕ)) := Array.replicate (n + 1) #[]
  rows := rows.set! n base
  let mut next := base
  for i' in List.range n do
    charge 3 -- dispatch, index n − 1 − i' (2)
    let i := n - 1 - i'
    let row ← tabulate nS fun st => do
      charge 4 -- division, remainder, two initializations
      let j := st.val / (kr + 1)
      let kρ := st.val % (kr + 1)
      let kωz ← decode bases j
      charge T -- conversion of the digits
      let kω := kωz.map Int.toNat
      let mut best : WithTop ℝ := ⊤
      let mut arg : ℕ := 0
      for m in List.range opts.size do
        charge 3 -- dispatch, read, test
        if okG[m]! then
          let xi := opts[m]!
          charge 1 -- initialization
          let mut fits := true
          for s in List.range T do
            charge 8 -- dispatch, four reads, multiplication, addition, comparison
            if ¬ ((kω[s]! : ℝ) * sW[s]! + I.wAt s i xi[s]! ≤ ŵ[s]!) then
              fits := false
          if fits then
            charge 1 -- initialization
            let mut nk : Array ℤ := #[]
            for s in List.range T do
              -- dispatch, four reads, multiplication, addition, comparison, division, floor,
              -- minimum, cast, push
              charge 13
              nk := nk.push (roundIdx sW[s]! kw ((kω[s]! : ℝ) * sW[s]! + I.wAt s i xi[s]!) : ℤ)
            let j' ← encode bases nk
            -- read, subtraction, multiplication, addition, read, read, cast, multiplication,
            -- addition, comparison
            charge 10
            let kρ' := kρ - (kRt[i]!)[m]!
            let cand : WithTop ℝ :=
              ((I.v * (dls[m]! : ℝ) : ℝ) : WithTop ℝ) + (next[j' * (kr + 1) + kρ']!).1
            if cand < best then
              charge 2 -- two writes
              best := cand
              arg := m
      return (best, arg)
    charge 1 -- write
    rows := rows.set! i row
    next := row
  return rows

/-- **One guess `(Γ, ŵ, ρ_single)` of the FPTAS, §3.6–§3.7, pp.20–21.** Build the table `V̂`, take
`ρ̂ = max{ρ ∈ Dρ : V̂(1, 0⃗, ρ) ≤ B − |Γ|·f}` (11) by a downward scan of the reward indices, and follow
the stored minimizers from `(1, 0⃗, ρ̂)` to obtain `x̂ = (x̂₁, …, x̂ₙ)` (as digit arrays, one per
product) together with its proxy reward `R̂_{2δ,δ}(x̂) = Σᵢ R̂ⁱ_{2δ,δ}(x̂ᵢ)`, read from `rh`. It returns
`none` when the set in (11) is empty. -/
noncomputable def dpGuess (δ : ℝ) (gam : Array Bool) (ŵ : Array ℝ) (ρs : ℝ)
    (opts : Array (Array ℕ)) (dls : Array ℕ) (rh : Array (Array ℝ)) :
    Work (Option (Array (Array ℕ) × ℝ)) := do
  let rows ← I.dpTable δ gam ŵ ρs opts dls rh
  charge 6 -- ⌈n/δ⌉ (2), ⌈n²/δ⌉ (3), initialization
  let kw := ⌈(n : ℝ) / δ⌉₊
  let kr := ⌈(n : ℝ) ^ 2 / δ⌉₊
  let mut card : ℕ := 0
  for s in List.range T do
    charge 3 -- dispatch, read, test
    if gam[s]! then
      charge 1 -- increment
      card := card + 1
  charge 5 -- cast, multiplication, subtraction, cast, initialization
  let budget : WithTop ℝ := ((I.B - (card : ℝ) * I.f : ℝ) : WithTop ℝ)
  let mut found : Option ℕ := none
  for s in List.range (kr + 1) do
    charge 4 -- dispatch, subtraction, two reads, comparison
    let k := kr - s
    if ((rows[0]!)[k]!).1 ≤ budget then
      charge 1 -- write
      found := some k
      break
  let some k0 := found | return none
  let bases := Array.replicate T (kw + 1)
  charge (2 * T + 5) -- bases, initial state, four initializations
  let mut kω : Array ℤ := Array.replicate T 0
  let mut kρ := k0
  let mut xs : Array (Array ℕ) := #[]
  let mut r : ℝ := 0
  for i in List.range n do
    charge 1 -- dispatch
    let j ← encode bases kω
    charge 9 -- multiplication, addition, two reads, read, push, read, addition, initialization
    let m := ((rows[i]!)[j * (kr + 1) + kρ]!).2
    let xi := opts[m]!
    xs := xs.push xi
    r := r + (rh[i]!)[m]!
    let mut nk : Array ℤ := #[]
    for s in List.range T do
      -- dispatch, reads, step δŵₜ/n (2), multiplication, addition, comparison, division,
      -- floor, minimum, cast, push
      charge 15
      let st := δ * ŵ[s]! / n
      nk := nk.push (roundIdx st kw ((((kω[s]!).toNat : ℕ) : ℝ) * st + I.wAt s i xi[s]!) : ℤ)
    kω := nk
    charge 10 -- step δρ_single/n (2), read, comparison, division, floor, minimum, subtraction,
              -- two writes
    kρ := kρ - roundIdx (δ * ρs / n) kr (rh[i]!)[m]!
  return some (xs, r)

/-- `ϱmax = maxᵢ pⁱmax/pⁱmin`, computed by one charged pass over the prices. -/
noncomputable def rhoMaxW : Work ℝ := do
  charge 1 -- initialization
  let mut ρ : ℝ := 1
  for i in List.range n do
    charge 3 -- dispatch, two reads
    let mut hi := I.pAt i 0
    let mut lo := I.pAt i 0
    for ℓ in List.range L do
      charge 6 -- dispatch, two reads, two comparisons, write
      hi := max hi (I.pAt i ℓ)
      lo := min lo (I.pAt i ℓ)
    charge 4 -- division, test, comparison, write
    if i = 0 then ρ := hi / lo else ρ := max ρ (hi / lo)
  return ρ

/-- **The FPTAS of Theorem 3.1**, §3.3–§3.7, pp.15–22, as an instrumented program in the unit-cost
model `CapacitatedAssort.General.Work` (the state counts operations). With `εh = min ε 1` and
`δ = εh/(8ϱmax)` (p.15; `α = 2δ`, `β = δ`, p.19):

1. the options (all `L^T` single-product price vectors) and their price-change counts;
2. the weight guesses `ŵ` of Lemma 3.2 (B.1);
3. for every `ŵ`: the rewards `R̂ⁱ_{2δ,δ}(xᵢ)` of every product and option by the evaluator (19);
   for every `Γ ⊆ [2, T]` (bitmask, `2^{T−1}` of them) and every `ρ_single` among those rewards
   (p.20, "enumerating over all O(nL^T) single-product pricing strategies"): the program `dpGuess`;
4. among all guesses that produce a candidate `x̂`, return the one with the largest proxy reward
   `R̂_{2δ,δ}(x̂)` (the first on ties); `none` if no guess produces one.

**Formalization Note.** "Our algorithm" is this explicit program; the paper's §3.7 says only "after
accounting for the guessing procedure", and the selection by proxy reward is the reading recorded in
the mission notes (every candidate is feasible, so it is sound). Unit cost: `+, −, ×, /`,
comparisons on `ℝ` and `ℕ`, `⌊·⌋₊`, `⌈·⌉₊`, input reads, array reads and writes, list cons, loop
dispatch. Powers are computed by charged repeated multiplication; no logarithm is evaluated. The
program never evaluates `R` or any measure. The output is returned as digit arrays (product `i`'s
levels by period) and written at cost `n·T + 1`. -/
noncomputable def fptas (ε : ℝ) : Work (Option (Array (Array ℕ))) := do
  charge 2 -- two comparisons
  if ¬ (0 < n ∧ 0 < L) then return none
  let ρ ← I.rhoMaxW
  charge 3 -- minimum, multiplication, division
  let δ := min ε 1 / (8 * ρ)
  let (opts, dls) ← optionTable L T
  let guesses ← I.weightGuesses δ
  let gbases := Array.replicate (T - 1) 2
  charge (T + 1) -- building the bases
  let nG ← boxSize gbases
  charge 2 -- two initializations
  let mut best : Option (Array (Array ℕ)) := none
  let mut bestR : ℝ := 0
  for ŵ in guesses do
    charge 1 -- dispatch
    let rh ← I.rhatTable ŵ δ opts
    for b in List.range nG do
      charge 1 -- dispatch
      let bits ← decode gbases b
      let gam ← tabulate T fun t => do
        charge 3 -- test, subtraction, read
        return (if t.val = 0 then false else decide (bits[t.val - 1]! = 1))
      for i in List.range n do
        charge 1 -- dispatch
        for m in List.range opts.size do
          charge 3 -- dispatch, two reads
          let ρs := (rh[i]!)[m]!
          let c ← I.dpGuess δ gam ŵ ρs opts dls rh
          charge 3 -- test, comparison, writes
          match c with
          | some (xs, r) =>
            if best.isNone ∨ bestR < r then
              best := some xs
              bestR := r
          | none => pure ()
  charge (n * T + 1) -- writing the output
  return best

end Instance

/-- The strategy whose level for product `i` in period `t` is digit `t` of `xs[i]`. -/
def toStrategy (h : 0 < L) (xs : Array (Array ℕ)) : Strategy n L T :=
  fun t i => ⟨(xs[i.val]!)[t.val]! % L, Nat.mod_lt _ h⟩

/-- The membership array of a set `Γ` of periods: entry `t` is `t ∈ Γ`. -/
def gamArr (Γ : Finset (Fin T)) : Array Bool := Array.ofFn fun t : Fin T => decide (t ∈ Γ)

/-- The mixed-radix index `Σₜ kω t · (K + 1)^t` of the weight indices `kω` (period `0` least
significant), as computed by `encode`. -/
def wIndex (K : ℕ) (kω : Fin T → ℕ) : ℕ := ∑ t, kω t * (K + 1) ^ t.val

/-- The cell index `wIndex(kω)·(⌈n²/δ⌉ + 1) + kρ` of the grid state `(kω, kρ)` in a row of `dpTable`. -/
noncomputable def stateIdx (n : ℕ) (δ : ℝ) (kω : Fin T → ℕ) (kρ : ℕ) : ℕ :=
  wIndex (KW n δ) kω * (KR n δ + 1) + kρ

namespace Instance

variable (I : Instance n L T)

/-- The table `V̂` the program builds for the guess `(Γ, ŵ, ρ_single)` and accuracy `δ`. -/
noncomputable def guessTable (δ : ℝ) (Γ : Finset (Fin T)) (ŵ : Fin T → ℝ) (ρs : ℝ) :
    Array (Array (WithTop ℝ × ℕ)) :=
  ((do
    let (opts, dls) ← optionTable L T
    let rh ← I.rhatTable (Array.ofFn ŵ) δ opts
    I.dpTable δ (gamArr Γ) (Array.ofFn ŵ) ρs opts dls rh) : Work _).run 0 |>.1

/-- The value the program stores for the state `(i + 1, ω, ρ)` (weight indices `kω`, reward index
`kρ`) of the guess `(Γ, ŵ, ρ_single)`. -/
noncomputable def tableEntry (δ : ℝ) (Γ : Finset (Fin T)) (ŵ : Fin T → ℝ) (ρs : ℝ) (i : ℕ)
    (kω : Fin T → ℕ) (kρ : ℕ) : WithTop ℝ :=
  ((I.guessTable δ Γ ŵ ρs)[i]!)[stateIdx n δ kω kρ]!.1

/-- **The candidate of the guess `(Γ, ŵ, ρ_single)`**: the strategy `x̂` the program derives for this
guess (§3.7, p.21) with the proxy reward the program records for it, or `none` when `ρ̂` does not
exist. -/
noncomputable def guessCandidate (δ : ℝ) (Γ : Finset (Fin T)) (ŵ : Fin T → ℝ) (ρs : ℝ) :
    Option (Strategy n L T × ℝ) :=
  match ((do
    let (opts, dls) ← optionTable L T
    let rh ← I.rhatTable (Array.ofFn ŵ) δ opts
    I.dpGuess δ (gamArr Γ) (Array.ofFn ŵ) ρs opts dls rh) : Work _).run 0 |>.1 with
  | some (xs, r) => if h : 0 < L then some (toStrategy h xs, r) else none
  | none => none

/-- **The output of the FPTAS** on accuracy `ε`: a pricing strategy, or `none`. -/
noncomputable def output (ε : ℝ) : Option (Strategy n L T) :=
  match ((I.fptas ε).run 0).1 with
  | some xs => if h : 0 < L then some (toStrategy h xs) else none
  | none => none

/-- **The number of unit operations** the FPTAS executes on accuracy `ε`. -/
noncomputable def ops (ε : ℝ) : ℕ := ((I.fptas ε).run 0).2

end Instance

end MenuCostPricing


