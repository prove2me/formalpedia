-- Prove2me | Definitions.Def_NestedLogitFPTAS_Program
-- name    : NestedLogitFPTAS_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:41.699958+00:00
-- url     : https://prove2.me/theorems/1b38f1c6-a70c-4932-9ebe-bb6033923b2f
-- title:
--   §3.3–§3.4, pp.12–14 — the FPTAS as one instrumented program
-- statement:
--   The program `fptas` is the algorithm of Theorem 1.1. It computes $\gamma^\pm$, $W^\uparrow$, $W^\downarrow$, $r_{\max}$, $r_{\min}$, $\pi_{\min}$, the accuracy levels and the grids. It then computes bottom-up, for $k=M+1,\dots,1$, the approximate value function
--   $$
--   \tilde F(k,\omega,\rho)=\min\big\{\mathcal A(k,\omega_k,\rho_k)+\tilde F(k+1,\omega_{>k},\rho_{>k}):\ \omega_k+\omega_{>k}\le\omega,\ \rho_k+\rho_{>k}\ge\rho\big\},\tag{4}
--   $$
--   over $\omega_k,\omega_{>k}\in\mathcal D_\omega$ and $\rho_k,\rho_{>k}\in\mathcal D_\rho$, with $\tilde F(M+1,0,0)=0$ and $\tilde F(M+1,\omega,\rho)=\infty$ otherwise. Over the pairs with $\tilde F(1,\omega,\rho)\le\mathcal C$ it finally picks one maximizing $\rho/(w_0+\omega)$ and returns the assortment recorded at that state, or `none` if no pair qualifies.
--
--   `output I ε` and `ops I ε` are the returned value and the operation count of a run. `Ftilde` reads the table, and `selected` is the pair picked.
--
--   **Formalization Note** A state stores its value and a persistent witness, so the table is filled once per state; a recursion without a table would be exponential. Every loop iteration and arithmetic step is charged at its site, and no subset of products is enumerated. As in the "straightforward implementation" of §3.4, $\mathcal A$ is run anew for each admissible choice. Ties in the final selection go to the first pair in lexicographic order of the grid indices. At $w_0+\omega=0$ the ratio is Lean's $0$.
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §3.3, p.12; §3.4, pp.13–14

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_SingleNest

namespace NestedLogitFPTAS

open CapacitatedAssort.General

/-- What `prepare` computes once: the accuracy levels of the single-nest algorithm, the grids as
ascending arrays, and the list of products of each nest. -/
structure Params (n : ℕ) where
  δω : ℝ
  δρ : ℝ
  Dω : Array ℝ
  Dρ : Array ℝ
  nests : Array (List (Fin n))

/-- A state of the approximate DP: `F̃(k, ω, ρ)` and the witness, one list of products per nest,
nest `k` first. -/
structure Entry (n : ℕ) where
  val : WithTop ℝ
  wit : List (List (Fin n))

instance {n : ℕ} : Inhabited (Entry n) := ⟨⟨⊤, []⟩⟩

/-- A row of the approximate DP: the states of one `k`, indexed by `[p][q]`. -/
abbrev Row (n : ℕ) := Array (Array (Entry n))

/-- A charged left fold of a binary operation over a list, from `init`. Every `f` passed below is at
most two array reads and one addition or division. -/
noncomputable def foldLoop {ι : Type} (op : ℝ → ℝ → ℝ) (l : List ι) (f : ι → ℝ) (init : ℝ) :
    Work ℝ := do
  let mut acc := init
  for i in l do
    charge 6 -- dispatch, evaluation of f (up to three operations), read of acc, operation
    acc := op acc (f i)
  return acc

/-- The minimum of `f` over a list; `0` on the empty list, which `Standing` excludes. -/
noncomputable def minLoop {ι : Type} (l : List ι) (f : ι → ℝ) : Work ℝ :=
  match l with
  | [] => pure 0
  | i :: t => foldLoop min t f (f i)

/-- The maximum of `f` over a list; `0` on the empty list, which `Standing` excludes. -/
noncomputable def maxLoop {ι : Type} (l : List ι) (f : ι → ℝ) : Work ℝ :=
  match l with
  | [] => pure 0
  | i :: t => foldLoop max t f (f i)

/-- The array `0, start, start·b, …, start·b^last`, by repeated multiplication. -/
noncomputable def geomGrid (b start : ℝ) (last : ℕ) : Work (Array ℝ) := do
  let mut out : Array ℝ := #[0]
  let mut x := start
  for _ in List.range (last + 1) do
    charge 3 -- dispatch, push, multiplication
    out := out.push x
    x := x * b
  return out

/-- The products of each nest in increasing order, by one pass over the products from the last. -/
def bucket {n M : ℕ} (I : Instance n M) : Work (Array (List (Fin n))) := do
  charge (M + 1) -- allocation
  let mut out : Array (List (Fin n)) := Array.replicate M []
  for i in (List.finRange n).reverse do
    charge 4 -- dispatch, read of the nest, array read, cons and write
    out := out.modify (I.nest i).val (fun l => i :: l)
  return out

/-- The preprocessing: `γ⁺`, `γ⁻`, `W↑`, `W↓`, `r_max`, `r_min`, `π_min` by charged loops, then the
accuracy levels of §3.4, p.13, and the corrected grids of §3.3, p.12. -/
noncomputable def prepare {n M : ℕ} (I : Instance n M) (ε : ℝ) : Work (Params n) := do
  charge 2 -- comparison and read for ϵ̂ = min ϵ 1
  let εh := min ε 1
  let nests ← bucket I
  let nestsM := List.finRange M
  let gp ← foldLoop max nestsM I.γ 1
  let gm ← foldLoop min nestsM I.γ 1
  let totals ← tabulate M fun m => do
    charge 1 -- read
    let s ← foldLoop (· + ·) nests[m.val]! I.w 0
    charge 2 -- read and addition
    return I.w0n m + s
  let smallest ← tabulate M fun m => do
    charge 1 -- read
    minLoop nests[m.val]! I.w
  let wu ← foldLoop max nestsM (fun m => totals[m.val]!) 1
  let wd ← foldLoop min nestsM (fun m => I.w0n m + smallest[m.val]!) 1
  let rmax ← maxLoop (List.finRange n) I.r
  let rmin ← minLoop (List.finRange n) I.r
  let pm ← minLoop nestsM (fun m => smallest[m.val]! / totals[m.val]!)
  charge (M + 40) -- the arithmetic of the parameters below; M multiplications for (1 - ξρ)^M
  let xω := εh * gm / (2560 * (M : ℝ) * gp)
  let xρ := εh / (640 * (M : ℝ))
  let Pω := ⌈(gp * Real.log (wu / wd) + Real.log (M : ℝ)) / Real.log (1 + xω)⌉₊ + M + 1
  let Lρ := (1 - xρ) ^ M * pm * rmin * wd ^ gp
  let Qρ := ⌈Real.log ((M : ℝ) * rmax * wu ^ gp / Lρ) / Real.log (1 + xρ)⌉₊
  let Dω ← geomGrid (1 + xω) (wd ^ gp) Pω
  let Dρ ← geomGrid (1 + xρ) Lρ Qρ
  return ⟨εh / (640 * gp), εh / 80, Dω, Dρ, nests⟩

/-- The terminal row `k = M + 1`: `F̃(M+1, 0, 0) = 0`, and `F̃(M+1, ω, ρ) = ∞` for
`(0,0) ≠ (ω,ρ) ∈ Dω × Dρ`, §3.4, p.13. Index `0` of each grid is the point `0`. -/
def terminalRow {n : ℕ} (P : Params n) : Work (Row n) :=
  tabulate P.Dω.size fun p => tabulate P.Dρ.size fun q => do
    charge 3 -- two tests, one write
    return if p.val = 0 ∧ q.val = 0 then ⟨0, []⟩ else ⟨⊤, []⟩

/-- One evaluation of the recursion (4), §3.4, p.13, at the state `(k, ω, ρ)`: the minimum of
`A(k, ωk, ρk) + F̃(k+1, ω>k, ρ>k)` over the grid points with `ωk + ω>k ≤ ω` and `ρk + ρ>k ≥ ρ`. `next`
is the row of `k + 1`. As in the "straightforward implementation" of §3.4, p.14, `A` is executed anew
for each admissible choice. -/
noncomputable def dpState {n M : ℕ} (I : Instance n M) (P : Params n) (k : Fin M) (ω ρ : ℝ)
    (next : Row n) : Work (Entry n) := do
  let mut best : Entry n := ⟨⊤, []⟩
  for p₁ in List.range P.Dω.size do
    charge 1 -- dispatch
    for p₂ in List.range P.Dω.size do
      charge 1 -- dispatch
      for q₁ in List.range P.Dρ.size do
        charge 1 -- dispatch
        for q₂ in List.range P.Dρ.size do
          charge 7 -- dispatch, four reads, two additions with their comparisons
          if P.Dω[p₁]! + P.Dω[p₂]! ≤ ω ∧ ρ ≤ P.Dρ[q₁]! + P.Dρ[q₂]! then
            charge 2 -- two reads for the arguments of A
            let a ← singleNest I P.δω P.δρ P.nests[k.val]! k P.Dω[p₁]! P.Dρ[q₁]!
            charge 4 -- one read, one addition, one comparison, one cons
            let e := (next[p₂]!)[q₂]!
            let v := a.val + e.val
            if v < best.val then
              best := ⟨v, a.wit :: e.wit⟩
  return best

/-- The row of nest `k` from the row `next` of `k + 1`: (4) at every `(ω, ρ) ∈ Dω × Dρ`. -/
noncomputable def dpRow {n M : ℕ} (I : Instance n M) (P : Params n) (k : Fin M) (next : Row n) :
    Work (Row n) :=
  tabulate P.Dω.size fun p => tabulate P.Dρ.size fun q => do
    charge 2 -- two reads
    dpState I P k P.Dω[p.val]! P.Dρ[q.val]! next

/-- The table of `F̃`, computed bottom-up from `k = M + 1` to `k = 1`, each row exactly once. The
result is a list of rows: entry `k` is the row of nest `k : Fin M` (the paper's `k + 1`), and entry
`M` is the terminal row. -/
noncomputable def dpTable {n M : ℕ} (I : Instance n M) (P : Params n) : Work (List (Row n)) := do
  let last ← terminalRow P
  let mut rows : List (Row n) := [last]
  for k in (List.finRange M).reverse do
    charge 2 -- dispatch, cons
    let row ← dpRow I P k (rows.headD #[])
    rows := row :: rows
  return rows

/-- "Final algorithm", §3.4, p.14: over the `C`-feasible pairs `(ω, ρ)`, those with
`F̃(1, ω, ρ) ≤ C`, the indices of the pair maximizing `ρ/(w₀ + ω)`; `none` if there is no such pair.
Ties go to the first pair in lexicographic order of the indices. `row` is the row of `k = 1`.

**Formalization Note.** At `w₀ + ω = 0` the ratio is Lean's `ρ/0 = 0`; that happens only for `w₀ = 0`,
`ω = 0`, and the only feasible such pair has `ρ = 0`. -/
noncomputable def selectPair {n M : ℕ} (I : Instance n M) (P : Params n) (row : Row n) :
    Work (Option (ℕ × ℕ)) := do
  let mut best : Option (ℕ × ℕ) := none
  let mut bestRatio : ℝ := 0
  for p in List.range P.Dω.size do
    charge 1 -- dispatch
    for q in List.range P.Dρ.size do
      charge 9 -- dispatch, one read and one comparison, three reads, one addition, one division,
               -- one comparison
      if ((row[p]!)[q]!).val ≤ ((I.C : ℝ) : WithTop ℝ) then
        let ratio := P.Dρ[q]! / (I.w0 + P.Dω[p]!)
        if best.isNone ∨ bestRatio < ratio then
          best := some (p, q)
          bestRatio := ratio
  return best

/-- The assortment `S̃ = (S̃₁, …, S̃_M)` from the witness of a state.

**Formalization Note.** The output is a bit vector over the products, so an insertion is one array
write, charged `2` with its dispatch. -/
def assemble {n : ℕ} (wit : List (List (Fin n))) : Work (Finset (Fin n)) := do
  let mut out : Finset (Fin n) := ∅
  for l in wit do
    charge 1 -- dispatch
    for i in l do
      charge 2 -- dispatch, write
      out := insert i out
  return out

/-- **The FPTAS of Theorem 1.1**: the preprocessing, the bottom-up table of `F̃`, the final selection
and the traced assortment. The program uses unit-cost `+, -, ×, /, ≤, ⌊·⌋, ⌈·⌉`, `Real.rpow`,
`Real.log` and array accesses, each charged at its execution site, as the paper's count does (§3.4,
§4.2). It enumerates no subset of products. -/
noncomputable def fptas {n M : ℕ} (I : Instance n M) (ε : ℝ) :
    Work (Option (Finset (Fin n))) := do
  let P ← prepare I ε
  let rows ← dpTable I P
  let row := rows.headD #[]
  let sel ← selectPair I P row
  match sel with
  | none => return none
  | some (p, q) =>
    charge 2 -- two reads
    let S ← assemble ((row[p]!)[q]!).wit
    return some S

namespace Instance

variable {n M : ℕ} (I : Instance n M)

/-- The value computed by `prepare`. -/
noncomputable def prepared (ε : ℝ) : Params n := ((prepare I ε).run 0).1

/-- The rows computed by `dpTable`. -/
noncomputable def rows (ε : ℝ) : List (Row n) := ((dpTable I (I.prepared ε)).run 0).1

/-- The table entry of `F̃` at nest index `k` (the paper's `k + 1`; `k = M` is the terminal row) and
grid indices `(p, q)`, that is, at the state `(ω, ρ) = (omegaAt p, rhoAt q)`. -/
noncomputable def Ftilde (ε : ℝ) (k p q : ℕ) : WithTop ℝ :=
  ((((I.rows ε).getD k #[])[p]!)[q]!).val

/-- The grid indices selected by the final step. -/
noncomputable def selected (ε : ℝ) : Option (ℕ × ℕ) :=
  ((selectPair I (I.prepared ε) ((I.rows ε).headD #[])).run 0).1

/-- The output of the program: an assortment, or `none`. -/
noncomputable def output (ε : ℝ) : Option (Finset (Fin n)) := ((fptas I ε).run 0).1

/-- The number of operations charged by the program. -/
noncomputable def ops (ε : ℝ) : ℕ := ((fptas I ε).run 0).2

end Instance

end NestedLogitFPTAS


