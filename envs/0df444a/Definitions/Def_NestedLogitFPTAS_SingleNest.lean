-- Prove2me | Definitions.Def_NestedLogitFPTAS_SingleNest
-- name    : NestedLogitFPTAS_SingleNest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:53.287735+00:00
-- url     : https://prove2.me/theorems/561f17e6-496a-48b4-a9ce-b8c569898945
-- title:
--   §4, pp.18–19 — the single-nest algorithm $\mathcal A$ as an instrumented program
-- statement:
--   Given $k$, $\omega_k,\rho_k$ and accuracy levels, the algorithm $\mathcal A(k,\omega_k,\rho_k)$ works as follows. If $\omega_k=\rho_k=0$ it returns $\emptyset$, and if exactly one of them is $0$ it reports an empty neighbourhood. Otherwise it sets
--   $$
--   w_{\rm base}=\frac{\delta_\omega}{|N_k|}\omega_k^{1/\gamma_k},\qquad \lambda_{\rm base}=\frac{\delta_\rho}{|N_k|}\cdot\frac{\rho_k}{\omega_k^{1-1/\gamma_k}},
--   $$
--   rounds $w_i$ and $\lambda_i=r_iw_i$ down to integer multiples of these units, and computes by a knapsack recursion the minimum cost $G(t,\eta,\zeta)$ of a subset of the first $t$ products with rounded weight $\eta$ and rounded $\lambda$-quantity $\zeta$, for $0\le\eta\le\lceil2|N_k|/\delta_\omega\rceil$ and $0\le\zeta\le\lceil4|N_k|/\delta_\rho\rceil$. It then minimizes $G(|N_k|,\eta,\zeta)$ over the intervals of p.19 and returns the corresponding set, or reports an empty neighbourhood if the minimum is $\infty$.
--
--   The cost of the computed set is the number $\mathcal A(k,\omega_k,\rho_k)$ of the recursion (4); it is $\infty$ when none is computed.
--
--   **Formalization Note** The program runs in the cost monad `Work` of `CapacitatedAssort.General`, with every operation charged. $G$ is kept twice, over all subsets and over **nonempty** subsets, and the final search reads the second: the printed search can return $\emptyset$ when $\delta_\rho\ge1/3$ (see `GCell`). The recursion starts at $t=0$ because the printed terminal conditions assign $G(1,0,0)$ twice when $\bar w_1=\bar\lambda_1=0$. Witnesses are persistent lists, so a cons costs one operation. The products of the nest are passed as a list computed once by `prepare`.
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §4.1–§4.2, pp.18–19; §3.4, p.13

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_NestedLogitFPTAS_Model

namespace NestedLogitFPTAS

open CapacitatedAssort.General

/-- A value of the single-nest DP with its witness, a persistent list of products. -/
structure Cell (n : ℕ) where
  val : WithTop ℝ
  wit : List (Fin n)

instance {n : ℕ} : Inhabited (Cell n) := ⟨⟨⊤, []⟩⟩

/-- One state `(t, η, ζ)` of the single-nest DP.

**Formalization Note (correction).** `all` is the value `G` of §4.2, p.18, over all subsets;
`nonempty` is the same minimum over **nonempty** subsets, which is what the final search reads. The
printed algorithm can return `∅` when `δρ ≥ 1/3`: one product with `w = 0.05`, `r = 12`, `c = 1`,
`w₀ₖ = 1`, `γₖ = 1`, `ωₖ = ρₖ = 1`, `δρ = 1/2`, `δω = 1/16` has a nonempty neighbourhood, but
`(η, ζ) = (0, 0)` lies in both search intervals with `G = 0`, and `w₊(∅) = 0` is outside
`(1 ± 2δω)·1`. -/
structure GCell (n : ℕ) where
  all : Cell n
  nonempty : Cell n

instance {n : ℕ} : Inhabited (GCell n) := ⟨⟨default, default⟩⟩

/-- The table of `G` at one `t`, indexed by `[η][ζ]`. -/
abbrev GTable (n : ℕ) := Array (Array (GCell n))

/-- The initial condition: `G(0,0,0) = 0` for all subsets, every other state `∞`, and no nonempty
subset of the empty prefix.

**Formalization Note.** §4.2 starts at `t = 1` with `G(1,0,0) = 0` and `G(1, w̄₁, λ̄₁) = c₁`, which
assigns `G(1,0,0)` twice when `w̄₁ = λ̄₁ = 0`. The recursion here starts at `t = 0` instead. -/
def gInit {n : ℕ} (ηMax ζMax : ℕ) : Work (GTable n) :=
  tabulate (ηMax + 1) fun η => tabulate (ζMax + 1) fun ζ => do
    charge 4 -- two tests, two writes
    return if η.val = 0 ∧ ζ.val = 0 then ⟨⟨0, []⟩, ⟨⊤, []⟩⟩ else ⟨⟨⊤, []⟩, ⟨⊤, []⟩⟩

/-- One layer of the recursion of §4.2, p.18, for the product `i` of cost `ci` with rounded weight
`wb = w̄ᵢ/w_base` and rounded `lb = λ̄ᵢ/λ_base`:
`G(t,η,ζ) = min{cₜ + G(t-1, η - wb, ζ - lb), G(t-1,η,ζ)}`. Offering `i` makes the set nonempty, so
both new values take the offer from the `all` table. -/
noncomputable def gStep {n : ℕ} (ci : ℝ) (i : Fin n) (wb lb ηMax ζMax : ℕ) (G : GTable n) :
    Work (GTable n) :=
  tabulate (ηMax + 1) fun η => tabulate (ζMax + 1) fun ζ => do
    charge 13 -- two subtractions with their tests, three reads, one addition, one cons, two
              -- comparisons, three writes
    let offer : Cell n :=
      if wb ≤ η.val ∧ lb ≤ ζ.val then
        let prev := ((G[η.val - wb]!)[ζ.val - lb]!).all
        ⟨(ci : WithTop ℝ) + prev.val, i :: prev.wit⟩
      else ⟨⊤, []⟩
    let stay := (G[η.val]!)[ζ.val]!
    return ⟨if offer.val < stay.all.val then offer else stay.all,
      if offer.val < stay.nonempty.val then offer else stay.nonempty⟩

/-- The whole table of `G` over the products `items` of the nest, §4.2, p.18. `w̄ᵢ` and `λ̄ᵢ` are held
as the integers `⌊wᵢ/w_base⌋` and `⌊λᵢ/λ_base⌋`, the multiples of the base units of p.18. -/
noncomputable def gTable {n M : ℕ} (I : Instance n M) (wbase lbase : ℝ) (ηMax ζMax : ℕ)
    (items : List (Fin n)) : Work (GTable n) := do
  let mut G ← gInit ηMax ζMax
  for i in items do
    charge 8 -- dispatch, three reads, one multiplication, two divisions with floors
    let wb := ⌊I.w i / wbase⌋₊
    let lb := ⌊I.r i * I.w i / lbase⌋₊
    G ← gStep (I.c i) i wb lb ηMax ζMax G
  return G

/-- The final search of §4.2, pp.18–19: the minimum of the nonempty `G(|Nₖ|, η, ζ)` over the states
`(η, ζ)` of the state space in the box `[ηlo, ηhi] × [ζlo, ζhi]`. -/
noncomputable def gSearch {n : ℕ} (ηlo ηhi ζlo ζhi : ℝ) (ηMax ζMax : ℕ) (G : GTable n) :
    Work (Cell n) := do
  let mut best : Cell n := ⟨⊤, []⟩
  for η in List.range (ηMax + 1) do
    charge 1 -- dispatch
    for ζ in List.range (ζMax + 1) do
      charge 9 -- dispatch, two conversions, four comparisons, one read, one comparison
      if ηlo ≤ (η : ℝ) ∧ (η : ℝ) ≤ ηhi ∧ ζlo ≤ (ζ : ℝ) ∧ (ζ : ℝ) ≤ ζhi then
        let e := ((G[η]!)[ζ]!).nonempty
        if e.val < best.val then
          best := e
  return best

/-- The single-nest algorithm `A(k, ωk, ρk)` of Theorem 3.1, §4, pp.18–19, on the list `items` of the
products of nest `k`. The result has value `⊤` for "report that the neighbourhood is empty";
otherwise its value is the cost of its witness.

* `ωk = ρk = 0`: the empty assortment. If exactly one of them is `0`, the neighbourhood is empty,
  since `rᵢ, wᵢ > 0`. These are the "trivial" cases of §4.1, p.18.
* Otherwise `w_base = (δω/|Nₖ|)·ωk^{1/γk}`, `λ_base = (δρ/|Nₖ|)·ρk/ωk^{1-1/γk}`, the state space is
  `0..⌈2|Nₖ|/δω⌉ × 0..⌈4|Nₖ|/δρ⌉`, and the search intervals are those of p.19.

**Formalization Note.** `items` is an argument so that a call costs `O(|Nₖ|³/(δωδρ))` and not `Ω(n)`.
The list is computed once by `prepare`. `§4.1, p.18` prints `λ_base` with `ω` for `ωₖ`, a slip. -/
noncomputable def singleNest {n M : ℕ} (I : Instance n M) (δω δρ : ℝ) (items : List (Fin n))
    (k : Fin M) (ωk ρk : ℝ) : Work (Cell n) := do
  charge 4 -- two tests against 0, two conjunction/disjunction steps
  if ωk = 0 ∧ ρk = 0 then
    return ⟨0, []⟩
  if ωk = 0 ∨ ρk = 0 then
    return ⟨⊤, []⟩
  charge 34 -- list length, three reads, two rpows, two subtractions and divisions for the exponents,
            -- nine more multiplications and divisions, two ceilings, and the eight subtractions,
            -- multiplications and divisions of the four interval ends
  let m : ℝ := (items.length : ℝ)
  let root := ωk ^ (1 / I.γ k)
  let scale := ωk ^ (1 - 1 / I.γ k)
  let wbase := δω / m * root
  let lbase := δρ / m * (ρk / scale)
  let ηMax := ⌈2 * m / δω⌉₊
  let ζMax := ⌈4 * m / δρ⌉₊
  let ηlo := ((1 - 2 * δω) * root - I.w0n k) / wbase
  let ηhi := ((1 + δω) * root - I.w0n k) / wbase
  let ζlo := (1 - 3 * δρ) * ρk / (lbase * scale)
  let ζhi := (1 + 3 * δρ) * ρk / (lbase * scale)
  let G ← gTable I wbase lbase ηMax ζMax items
  gSearch ηlo ηhi ζlo ζhi ηMax ζMax G

namespace Instance

variable {n M : ℕ} (I : Instance n M)

/-- The products of nest `k` in increasing order, as `prepare` lists them. -/
def nestList (k : Fin M) : List (Fin n) := (List.finRange n).filter (fun i => I.nest i = k)

/-- The result of `A(k, ωk, ρk)` with the accuracy levels `δω`, `δρ`. -/
noncomputable def Acell (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) : Cell n :=
  ((singleNest I δω δρ (I.nestList k) k ωk ρk).run 0).1

/-- The operation count of `A(k, ωk, ρk)`. -/
noncomputable def Aops (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) : ℕ :=
  ((singleNest I δω δρ (I.nestList k) k ωk ρk).run 0).2

open Classical in
/-- The assortment computed by `A(k, ωk, ρk)`, and `none` when it reports an empty neighbourhood. -/
noncomputable def Aset (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) : Option (Finset (Fin n)) :=
  if (I.Acell δω δρ k ωk ρk).val = ⊤ then none else some (I.Acell δω δρ k ωk ρk).wit.toFinset

/-- `A(k, ωk, ρk)` as a number: the total cost of the computed assortment, `⊤` (`∞`) when none is
computed, §3.4, p.13. -/
noncomputable def Acost (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) : WithTop ℝ :=
  match I.Aset δω δρ k ωk ρk with
  | some T => ((I.cost T : ℝ) : WithTop ℝ)
  | none => ⊤

/-- `w_base = (δω/|Nₖ|)·ωk^{1/γk}`, §4.1, p.18. -/
noncomputable def wBase (δω : ℝ) (k : Fin M) (ωk : ℝ) : ℝ :=
  δω / ((I.nestSet k).card : ℝ) * ωk ^ (1 / I.γ k)

/-- `λ_base = (δρ/|Nₖ|)·ρk/ωk^{1-1/γk}`, §4.1, p.18. -/
noncomputable def lamBase (δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) : ℝ :=
  δρ / ((I.nestSet k).card : ℝ) * (ρk / ωk ^ (1 - 1 / I.γ k))

/-- The value `G(|Nₖ|, η, ζ)` over nonempty subsets that `A(k, ωk, ρk)` reads, Lemma 4.3, p.19: the
table of `G` after all the products of nest `k`, at the base units `w_base`, `λ_base` and over the
state space of §4.2. The definition is meant for `ωk, ρk > 0`. -/
noncomputable def GN (δω δρ : ℝ) (k : Fin M) (ωk ρk : ℝ) (η ζ : ℕ) : WithTop ℝ :=
  let N : ℝ := ((I.nestSet k).card : ℝ)
  ((((gTable I (I.wBase δω k ωk) (I.lamBase δρ k ωk ρk) ⌈2 * N / δω⌉₊ ⌈4 * N / δρ⌉₊
    (I.nestList k)).run 0).1[η]!)[ζ]!).nonempty.val

end Instance

end NestedLogitFPTAS


