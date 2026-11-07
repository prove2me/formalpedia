-- Prove2me | Definitions.Def_SupplyRevenue_BuyMany
-- name    : SupplyRevenue_BuyMany
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:23.3162+00:00
-- url     : https://prove2.me/theorems/8d1aeeae-d37d-4208-bed6-0f2e3a3e003e
-- title:
--   Buy-many menus and the benchmark $B$
-- statement:
--   A **menu** is a set of options (a lottery over whole subsets, a nonnegative price), containing the empty option $(\delta_\emptyset,0)$. A **strategy** either stops, or buys an option and continues as a function of the realized subset. A menu is **buy-many** when, for each strategy over it, some option of the menu has price at most the strategy's expected payment, and its lottery can be coupled with the law of the strategy's union so that the union is contained in the lottery's draw almost surely.
--
--   A **certificate** for a buyer is a buy-many menu and a selection of an option for each type, maximizing $v(L)-\text{price}$ over the menu at each supported type, where $v(L)=E_{T\sim L}v(T)$. Then $R_{BM}(D_i,x_i)$ is the supremum of expected price over finite mixtures of certificates with expected inclusion marginals at most $x_i$, and
--
--   $$B(D)=\sup_{x\ge 0,\ \sum_i x_{ij}\le 1\ \forall j}\ \sum_i R_{BM}(D_i,x_i).$$
--
--   Also, $\mathrm{BM\ Profit}_c(D_i)$ is the supremum over certificates of $E[\text{price}-c\cdot x(L)]$. Inclusion vectors enter only supply and linear cost, never value.
--
--   **Formalization Note** Strategies have finite depth. The selection has no tie rule, so $B$ does not depend on the residual order.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, p.2, (1); §2, p.6

import Mathlib
import Definitions.Def_SupplyRevenue_Buyer

open scoped ENNReal

namespace SupplyRevenue

/-!
# Buy-many menus and the benchmark `B`

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§1.1, p.2: "Buy-many menus dominate adaptive repeated purchases: an option of no larger expected payment can be coupled
to contain their union"; "Lotteries over whole subsets have v(L) = E_{T∼L} v(T); inclusion vectors describe only supply
and linear cost c · x(L)"; display (1), `B(D) = sup_{Σ_i x_ij ≤ 1 ∀j} Σ_i R_BM(D_i, x_i)`.

**Formalization Note** A menu is any set of options containing `(δ_∅, 0)`, finite or not (reading R5). A strategy is a
finite-depth adaptive plan: `next T` is chosen after seeing the realized subset `T`, and draws are independent. A
certificate selects, for each supported type, *any* utility-maximizing option, with no payment tie (R6): this makes `B`
seller-favourable, so the upper bound is the stronger one. A selection is required only at supported types, and at the
others it must merely lie in the menu. Values of lotteries are expected values on whole subsets, never computed from
marginals. `R_BM` mixes certificates, with expected marginals `≤ x_i` (R7), and `B` ranges over `x ≥ 0`. Suprema are in
`ℝ≥0∞` (R9). `B` does not depend on the residual order `tie`.
-/

/-- A menu option: a lottery over whole subsets and a nonnegative price. -/
structure MenuOption (m : ℕ) where
  lot : Lottery m
  price : ℝ
  price_nonneg : 0 ≤ price

/-- The empty option `(δ_∅, 0)`. -/
def MenuOption.empty (m : ℕ) : MenuOption m where
  lot := Lottery.dirac ∅
  price := 0
  price_nonneg := le_rfl

/-- The whole-lottery value `v(L) = E_{T∼L} v(T)` (p.2). -/
noncomputable def MenuOption.value {m : ℕ} (o : MenuOption m) (v : Finset (Fin m) → ℝ) : ℝ :=
  o.lot.E v

/-- A finite-depth adaptive purchase strategy: stop, or buy an option and continue as a function of its realized
subset. -/
inductive Strategy (m : ℕ) where
  | stop : Strategy m
  | buy (o : MenuOption m) (next : Finset (Fin m) → Strategy m) : Strategy m

/-- Every option the strategy may buy lies in the menu. -/
def Strategy.Over {m : ℕ} (menu : Set (MenuOption m)) : Strategy m → Prop
  | .stop => True
  | .buy o next => o ∈ menu ∧ ∀ T, (next T).Over menu

/-- The expected payment of a strategy. -/
noncomputable def Strategy.pay {m : ℕ} : Strategy m → ℝ
  | .stop => 0
  | .buy o next => o.price + ∑ T, o.lot.mass T * (next T).pay

/-- The law of the union of all realized subsets of a strategy, as a mass function. -/
noncomputable def Strategy.unionMass {m : ℕ} : Strategy m → Finset (Fin m) → ℝ
  | .stop => fun W => if W = ∅ then 1 else 0
  | .buy o next => fun W =>
      ∑ T, ∑ U, if T ∪ U = W then o.lot.mass T * (next T).unionMass U else 0

/-- A coupling of the mass function `w` with the lottery `L` in which the `w`-draw is contained in the `L`-draw almost
surely. -/
def CouplesInside {m : ℕ} (w : Finset (Fin m) → ℝ) (L : Lottery m) : Prop :=
  ∃ γ : Finset (Fin m) → Finset (Fin m) → ℝ,
    (∀ U T, 0 ≤ γ U T) ∧ (∀ U, ∑ T, γ U T = w U) ∧ (∀ T, ∑ U, γ U T = L.mass T) ∧
    ∀ U T, γ U T ≠ 0 → U ⊆ T

/-- The buy-many property (p.2): the menu contains `(δ_∅, 0)`, and for every adaptive strategy over the menu some menu
option has price at most the strategy's expected payment and couples to contain the realized union. -/
def IsBuyMany {m : ℕ} (menu : Set (MenuOption m)) : Prop :=
  MenuOption.empty m ∈ menu ∧
    ∀ s : Strategy m, s.Over menu →
      ∃ o ∈ menu, o.price ≤ s.pay ∧ CouplesInside s.unionMass o.lot

/-- A buy-many certificate for a buyer: a buy-many menu and a selection of an option for each type, maximizing
`v(L) − price` over the menu at each supported type (reading R6). -/
structure Certificate {m : ℕ} (b : Buyer m) where
  menu : Set (MenuOption m)
  buyMany : IsBuyMany menu
  sel : Fin b.numTypes → MenuOption m
  sel_mem : ∀ θ, sel θ ∈ menu
  sel_opt : ∀ θ, 0 < b.mass θ → ∀ o ∈ menu,
    o.value (b.val θ) - o.price ≤ (sel θ).value (b.val θ) - (sel θ).price

/-- The expected price of a certificate. -/
noncomputable def Certificate.rev {m : ℕ} {b : Buyer m} (C : Certificate b) : ℝ :=
  b.E fun θ => (C.sel θ).price

/-- The expected inclusion marginal of a certificate. -/
noncomputable def Certificate.marginal {m : ℕ} {b : Buyer m} (C : Certificate b) (j : Fin m) : ℝ :=
  b.E fun θ => (C.sel θ).lot.incl j

/-- `R_BM(D_i, x_i)`: the supremum over finite mixtures of certificates with expected marginals `≤ x_i` of the expected
price (reading R7). -/
noncomputable def capBM {m : ℕ} (b : Buyer m) (x : Fin m → ℝ) : ℝ≥0∞ :=
  ⨆ (μ : Mix (Certificate b)) (_ : ∀ j, μ.E (fun C => C.marginal j) ≤ x j),
    ENNReal.ofReal (μ.E fun C => C.rev)

/-- `B(D)`, display (1), p.2. -/
noncomputable def buyManyRev {n m : ℕ} (D : Instance n m) : ℝ≥0∞ :=
  ⨆ (x : Fin n → Fin m → ℝ) (_ : (∀ i j, 0 ≤ x i j) ∧ ∀ j, ∑ i, x i j ≤ 1),
    ∑ i, capBM (D i) (x i)

/-- `BM Profit_c(D_i)` (p.6): the supremum over certificates of `E[price − c · x(L)]`. The single-option empty menu makes
the supremum at least zero. -/
noncomputable def bmProfit {m : ℕ} (b : Buyer m) (c : Fin m → ℝ) : ℝ≥0∞ :=
  ⨆ C : Certificate b, ENNReal.ofReal
    (b.E fun θ => (C.sel θ).price - ∑ j, c j * (C.sel θ).lot.incl j)

end SupplyRevenue


