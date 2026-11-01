-- Prove2me | Definitions.Def_StrategicNRM_Game
-- name    : StrategicNRM_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:45.965304+00:00
-- url     : https://prove2.me/theorems/705a7a52-e9af-478f-bba5-5dfe564c6303
-- title:
--   Policies, rules and plays with rationing
-- statement:
--   A **price path** gives each product a price in $\mathbb R\cup\{\infty\}$ at each time; there is no sign constraint. A **rule** maps a price path to a decision $(\tau,a)$. A rule of a customer arriving at $t$ is **feasible** if on every path $\tau\in[t,T]$, a purchase is at a finite price, and the rule is non-anticipating: if two paths agree up to $s$ and the rule stops by $s$ on one of them, it does the same on the other.
--
--   A **policy** $\theta$ gives the prices at $t$ as a function of $t$ and of the sales $(\tau,j)$ strictly before $t$, which is causality with respect to $\mathcal F_t=\sigma(\mathcal S_{t-})$. The policy is **admissible** if it posts $\infty$ on every product using a resource $i$ with $X^i_{t-}=0$, for $t\in[0,T]$.
--
--   A **play** of a crowd assigns each customer an outcome, such that, with $p$ the price path that the sales of the outcomes produce, each customer attempts what his rule does on $p$, and the attempt is served if and only if every resource of the product is still there when his turn comes in the order (purchase time, arrival time, index). A customer not served exits at the same time with nothing, and pays nothing.
--
--   **Formalization Note** The rationing is a reading of ties. §2 does not say what happens when several customers buy at one instant, and prices depend on $\mathcal S_{t-}$ only, so a price jump may draw more buyers than the units left; read literally the seller would oversell, and Theorem 1 would be false. Plays without excess demand at a tie are unchanged. Assuming "no overselling" instead would exclude every policy with a price jump, as Poisson counts are unbounded. The play is a predicate that refers to itself through the path; for feasible rules and a finite crowd it has exactly one solution, by induction on sale events.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §2, pp.6–8

import Mathlib
import Definitions.Def_StrategicNRM_Instance

open MeasureTheory

namespace StrategicNRM

variable {n m : ℕ}

/-- A customer's decision `(τ, a)`: the exit time and the product he tries to buy then, if any.
Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), §2, p.7. -/
abbrev Decision (n : ℕ) := ℝ × Option (Fin n)

/-- A path of posted prices. `⊤` is the infinite price of p.7. Prices have no sign constraint:
p.6 has `π_t ∈ ℝⁿ` and Π imposes none. -/
abbrev PricePath (n : ℕ) := ℝ → Fin n → WithTop ℝ

/-- A stopping and purchasing rule: the decision taken on each price path. The non-anticipation is
in `FeasibleRule`. -/
abbrev Rule (n : ℕ) := PricePath n → Decision n

/-- A rule of a customer arriving at `t`: the exit time lies in `[t,T]` on every path (p.8), a
purchase is at a finite price, and the rule is non-anticipating (`𝒞ₜ`-progressive, p.8): if two
paths agree up to `s` and the rule stops by `s` on one of them, then it does the same on the
other.

**Formalization Note.** Rules read the path from time `0`, as `𝒫ₜ = {πₛ : s ≤ t}` of p.7 does.
The paper's rule buys only at utility `≥ 0`, so it never buys at `∞`; `FeasibleRule` says so for
every path because `paid` reads a price as a real number. -/
structure FeasibleRule (I : Instance n m) (t : ℝ) (r : Rule n) : Prop where
  time_mem : ∀ p, (r p).1 ∈ Set.Icc t I.T
  finite_price : ∀ p j, (r p).2 = some j → p (r p).1 j ≠ ⊤
  nonanticipating : ∀ p p' s, (∀ u ≤ s, p u = p' u) → (r p).1 ≤ s → r p' = r p

/-- A pricing policy: the prices as a function of the record of sales and of the time. Read
through `priceAt`.

Chen & Trichakis, SSRN 2959489, §2, p.7: `𝒮ₜ = {(τ_φ, a_φ) : τ_φ ≤ t, 1ᵀa_φ = 1}`.

**Formalization Note.** A policy is a deterministic function of the sales, which is what being
`ℱₜ`-progressive means here: `ℱₜ = σ(𝒮ₜ₋)` holds no exogenous randomization. No measurability is
required of the policy itself; what the argument uses is the measurability in `IsEquilibrium`. -/
abbrev Policy (n : ℕ) := Multiset (ℝ × Fin n) → ℝ → Fin n → WithTop ℝ

/-- The prices at `t` given all sales `S`: they see only the sales strictly before `t`, which is
Causality (p.7) with `ℱₜ = σ(𝒮ₜ₋)`. -/
noncomputable def priceAt (θ : Policy n) (S : Multiset (ℝ × Fin n)) : PricePath n :=
  fun t => θ (S.filter fun e => e.1 < t) t

/-- The inventory `Xⁱ_{t−}` of resource `r` after the sales `S` strictly before `t`, in `ℤ`. -/
noncomputable def stock (I : Instance n m) (S : Multiset (ℝ × Fin n)) (t : ℝ) (r : Fin m) : ℤ :=
  I.x0 r - ((S.filter fun e => e.1 < t).map fun e => (I.A r e.2 : ℤ)).sum

/-- The set `Π` of admissible policies, p.7: property 1 (Causality) is built into `priceAt`, and
this is property 2 (Non-negative inventory): `πʲₜ = ∞` if `Xⁱ_{t−} = 0` and `A_{ij} = 1`. -/
def Admissible (I : Instance n m) (θ : Policy n) : Prop :=
  ∀ S t j r, t ∈ Set.Icc 0 I.T → stock I S t r = 0 → I.A r j = 1 → priceAt θ S t j = ⊤

/-- The record of sales of the customers' outcomes `o`: `(τ, j)` for each purchase. -/
noncomputable def salesOf {k : ℕ} (o : Fin k → Decision n) : Multiset (ℝ × Fin n) :=
  (Finset.univ : Finset (Fin k)).val.filterMap fun i => (o i).2.map fun j => ((o i).1, j)

/-- The price paid by a customer whose outcome is `d`, on the path `p`: `pᵩ = πᵀ_τ a` (p.7).

**Formalization Note.** `WithTop.untopD 0` is never applied to `⊤` on a feasible rule, by
`FeasibleRule.finite_price`. -/
noncomputable def paid (p : PricePath n) (d : Decision n) : ℝ :=
  match d.2 with
  | some j => (p d.1 j).untopD 0
  | none => 0

/-- `d` can be served given that `used r` units of each resource `r` are already gone. -/
def Fits (I : Instance n m) (used : Fin m → ℕ) (d : Decision n) : Prop :=
  ∀ j, d.2 = some j → ∀ r, I.A r j = 1 → used r + 1 ≤ I.x0 r

open Classical in
/-- The outcome of the attempt `d`: `d` itself if it can be served, else the customer exits at the
same time with nothing. -/
noncomputable def ration (fits : Prop) (d : Decision n) : Decision n :=
  if fits then d else (d.1, none)

open Classical in
/-- The units of resource `r` used by the customers served strictly before customer `i` in the
order `(τ, t, index)`, lexicographically. -/
noncomputable def consumedBefore (I : Instance n m) {k : ℕ} (c : Fin k → CType n)
    (o : Fin k → Decision n) (i : Fin k) (r : Fin m) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l => (o l).1 < (o i).1 ∨ ((o l).1 = (o i).1 ∧
      ((c l).1 < (c i).1 ∨ ((c l).1 = (c i).1 ∧ l < i)))), I.usage r (o l).2

/-- `o` is a play of the crowd `c` under the policy `θ` and the rules `σ`: writing `p` for the path
of prices that the sales of `o` produce, each customer attempts `σ (c i) p`, and the attempt is
served if and only if every resource of the product is still there when his turn comes in the
order `(τ, t, index)`.

Chen & Trichakis, SSRN 2959489, §2, p.7, with the **reading of ties**. The paper does not say what
happens when customers buy at the same instant, and prices depend only on `𝒮ₜ₋`, so one instant
may draw more buyers than the units left. Attempts at one instant are served in order of arrival
while stock lasts, and a rationed customer leaves with nothing. Plays without excess demand at a
tie are unchanged, so this covers every play the printed model defines.

**Formalization Note.** The predicate refers to itself through `p`. For feasible rules and finite
`k` it has exactly one solution, by induction on sale events. -/
def IsPlay (I : Instance n m) (θ : Policy n) (σ : CType n → Rule n) {k : ℕ}
    (c : Fin k → CType n) (o : Fin k → Decision n) : Prop :=
  ∀ i, o i = ration (Fits I (consumedBefore I c o i) (σ (c i) (priceAt θ (salesOf o))))
    (σ (c i) (priceAt θ (salesOf o)))

end StrategicNRM


