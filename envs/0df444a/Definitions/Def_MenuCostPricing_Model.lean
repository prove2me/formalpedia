-- Prove2me | Definitions.Def_MenuCostPricing_Model
-- name    : MenuCostPricing_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:39.590106+00:00
-- url     : https://prove2.me/theorems/5af2464e-3b8c-4053-976d-0a957140ee38
-- title:
--   §1.1, pp.2–4 — dynamic pricing with menu costs: instances, pricing strategies, menu costs, budget feasibility (2), the MNL demand law, inventories (1) and the expected revenue $R(x)$
-- statement:
--   A retailer prices $n$ products over $T$ periods, choosing in every period one of $L$ price levels for each product; $p_{i\ell}>0$ is the price of product $i$ at level $\ell$. A **pricing strategy** $x$ fixes the level $x^t_i$ of every product in every period, so $\sum_\ell p_{i\ell}x^t_{i\ell}=p_{i,x^t_i}$.
--
--   In period $t$ a random number $N_t$ of customers arrives; $N_1,\dots,N_T$ are independent, and $N_t$ has a known finite support $S_t$ with masses $\Pr[N_t=\nu]$. Each customer independently chooses by a time-dependent multinomial logit model with weights $w^t_{i\ell}\ge0$: under $x$ the customer is interested in product $i$ with probability
--   $$
--   \pi^t_i(x)=\frac{w^t_{i,x^t_i}}{1+w_t(x)},\qquad w_t(x)=\sum_{j\in[n]}w^t_{j,x^t_j},
--   $$
--   and buys nothing with probability $1/(1+w_t(x))$. The demand $D^t_i(x)=\sum_{\nu=1}^{N_t}Y^t_i(x,\nu)$ counts the interested customers; a customer whose product is sold out leaves. With starting inventories $u^1_i$, the inventory at the start of period $t$ is
--   $$
--   U^t_i(x)=\Big[u^1_i-\sum_{\tau<t}D^\tau_i(x)\Big]^+ ,
--   $$
--   equation (1), and the **expected revenue** is
--   $$
--   R(x)=\sum_{t\in[T]}\sum_{i\in[n]}\mathbb E\big[\min\{U^t_i(x),D^t_i(x)\}\big]\cdot p_{i,x^t_i}.
--   $$
--   $R_i(x)$ is the $i$-th inner sum (the revenue from product $i$).
--
--   Menu costs: $\Delta_{t-1,t}(x)$ counts the products whose price changes between periods $t-1$ and $t$; $C_{\mathrm{var}}(x)=v\sum_{t=2}^T\Delta_{t-1,t}(x)$ and $C_{\mathrm{fixed}}(x)=f\sum_{t=2}^T\mathbb 1[\Delta_{t-1,t}(x)>0]$. A strategy is **budget-feasible** when $C_{\mathrm{var}}(x)+C_{\mathrm{fixed}}(x)\le B$, (2). Finally $p^i_{\max},p^i_{\min}$ are the extreme prices of product $i$, $\varrho_{\max}=\max_i p^i_{\max}/p^i_{\min}$, $\|U^1\|_\infty=\max_i u^1_i$, $\sigma_{\max}$ is the largest support size and $L_\nu$ the largest bit length of a support point.
--
--   This is the model of the whole mission: every statement is about these objects.
--
--   **Formalization Note** Products, levels and periods are `Fin n`, `Fin L`, `Fin T` (0-based; Lean period $t$ is the paper's $t+1$, and $\Delta$ is defined for Lean periods $t\ge1$). The support of $N_t$ is a list with masses. `Standing` collects the assumptions: $n,L\ge1$, prices $>0$, weights $\ge0$, $f,v\ge0$, a duplicate-free support in $\mathbb N$ with masses $\ge0$ summing to $1$. The demand law is built from PMFs: per period, $N_t$, then $N_t$ i.i.d. categorical choices on $\{\text{none}\}\cup[n]$, counted per product; periods are independent (`Measure.pi`). The PMF constructions fall back to a point mass only when the masses do not sum to one, which `Standing` excludes.
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §1.1, pp.2–4 (model, (1), (2), DPMC); §3.1, p.14 (ϱmax); App. B.2, p.48 (Rᵢ(x)); App. B.6, p.51 (σmax)

import Mathlib

namespace MenuCostPricing

open MeasureTheory

/-- **An instance of dynamic pricing with menu costs (DPMC).** Feldman & Segev, *Dynamic Pricing
with Menu Costs: Approximation Schemes and Applications to Grocery Retail*, author manuscript
(Mar 2025), §1.1, pp.2–4.

There are `n` products, `L` price levels and `T` periods. `p i ℓ` is the price `p_{iℓ}` of product
`i` at level `ℓ`; `w t i ℓ` is the MNL preference weight `wᵗ_{iℓ}` of product `i` priced at level `ℓ`
in period `t`; `u i` is the starting inventory `u¹ᵢ`; `supp t` lists the support of the number `Nₜ`
of customers arriving in period `t` and `mass t ν` is `Pr[Nₜ = ν]`; `f` is the fixed menu cost,
`v` the variable menu cost and `B` the budget.

**Formalization Note.** Products, levels and periods are `Fin n`, `Fin L`, `Fin T`, 0-based: Lean
period `t` is the paper's period `t + 1`. Assumption (a) of p.2 ("the support of each Nₜ is known and
finite") is the list `supp t`; assumption (b) ("oracle access to its probability mass function") is
`mass t`. Masses of values not in the list are never read. -/
structure Instance (n L T : ℕ) where
  p : Fin n → Fin L → ℝ
  w : Fin T → Fin n → Fin L → ℝ
  u : Fin n → ℕ
  supp : Fin T → List ℕ
  mass : Fin T → ℕ → ℝ
  f : ℝ
  v : ℝ
  B : ℝ

/-- A **pricing strategy** (§1.1, p.2): "any vector x that chooses exactly one price for each product
in each time period". `x t i` is the level `ℓ` with `xᵗ_{iℓ} = 1`.

**Formalization Note.** The binary vector `(xᵗ_{iℓ})` with exactly one `1` per `(t, i)` is the
function `t ↦ i ↦ ℓ`; `Σ_ℓ p_{iℓ} xᵗ_{iℓ}` is `p i (x t i)`. -/
abbrev Strategy (n L T : ℕ) := Fin T → Fin n → Fin L

namespace Instance

variable {n L T : ℕ} (I : Instance n L T)

/-- **The standing assumptions of §1.1, pp.2–3.** At least one product and one price level; "all
prices are strictly positive" (p.2); MNL preference weights are nonnegative; the arrival law is a
probability mass function on a finite set of nonnegative integers, given as a duplicate-free list
with nonnegative masses summing to `1` (assumptions (a)–(b), p.2); the menu costs `f`, `v` are
nonnegative. The budget `B` is any real.

**Formalization Note.** `0 < n`, `0 < L`, `w ≥ 0`, `f, v ≥ 0` and `ν ∈ ℕ` are what the paper's
words mean ("products", "a discrete menu of L potential price levels", "preference weight", "menu
costs", "number of customers"); they are not printed as formulas. -/
structure Standing : Prop where
  n_pos : 0 < n
  L_pos : 0 < L
  p_pos : ∀ i ℓ, 0 < I.p i ℓ
  w_nonneg : ∀ t i ℓ, 0 ≤ I.w t i ℓ
  supp_nodup : ∀ t, (I.supp t).Nodup
  mass_nonneg : ∀ t ν, 0 ≤ I.mass t ν
  mass_sum : ∀ t, ((I.supp t).map (I.mass t)).sum = 1
  f_nonneg : 0 ≤ I.f
  v_nonneg : 0 ≤ I.v

/-- The price `Σ_ℓ p_{iℓ} xᵗ_{iℓ}` of product `i` in period `t` under `x`. -/
def price (x : Strategy n L T) (t : Fin T) (i : Fin n) : ℝ := I.p i (x t i)

/-- The total weight `wₜ(x) = Σ_{j∈[n]} Σ_{ℓ∈[L]} wᵗ_{jℓ} xᵗ_{jℓ}` of period `t` (p.2). -/
def wt (x : Strategy n L T) (t : Fin T) : ℝ := ∑ j, I.w t j (x t j)

/-- The MNL choice probability `πᵗᵢ(x) = (1/(1 + wₜ(x)))·Σ_ℓ wᵗ_{iℓ} xᵗ_{iℓ}` (p.2). -/
noncomputable def piChoice (x : Strategy n L T) (t : Fin T) (i : Fin n) : ℝ :=
  I.w t i (x t i) / (1 + I.wt x t)

end Instance

variable {n L T : ℕ}

/-- The period before `t` (Lean index `t - 1`), used only when `1 ≤ t.val`. -/
def prevPeriod (t : Fin T) (h : 1 ≤ t.val) : Fin T := ⟨t.val - 1, by omega⟩

/-- `∆_{t−1,t}(x) = Σ_{i∈[n]} 1[x^{t−1}_{i·} ≠ xᵗ_{i·}]` (p.3), the number of products whose price
changes from the period before `t` to `t`.

**Formalization Note.** Defined for Lean periods `t` with `1 ≤ t.val` (paper periods `2, …, T`);
it is `0` at `t = 0`, where the paper does not define it. -/
def Delta (x : Strategy n L T) (t : Fin T) : ℕ :=
  if h : 1 ≤ t.val then (Finset.univ.filter (fun i => x (prevPeriod t h) i ≠ x t i)).card else 0

/-- The Lean periods `t` with `1 ≤ t.val`, i.e. the paper's periods `2, …, T`. -/
def laterPeriods (T : ℕ) : Finset (Fin T) := Finset.univ.filter (fun t => 1 ≤ t.val)

namespace Instance

variable (I : Instance n L T)

/-- The variable menu cost `Cvar(x) = v · Σ_{t=2}^T ∆_{t−1,t}(x)` (p.3). -/
def Cvar (x : Strategy n L T) : ℝ := I.v * ∑ t ∈ laterPeriods T, (Delta x t : ℝ)

/-- The fixed menu cost `Cfixed(x) = f · Σ_{t=2}^T 1[∆_{t−1,t}(x) > 0]` (p.3). -/
def Cfixed (x : Strategy n L T) : ℝ :=
  I.f * ((laterPeriods T).filter (fun t => 0 < Delta x t)).card

/-- Budget feasibility (2), p.4: `Cvar(x) + Cfixed(x) ≤ B`. -/
def Feasible (x : Strategy n L T) : Prop := I.Cvar x + I.Cfixed x ≤ I.B

/-- `pⁱmax`, the largest price `max_ℓ p_{iℓ}` of product `i` (`0` if `L = 0`). -/
noncomputable def pmax (i : Fin n) : ℝ :=
  if h : 0 < L then Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (I.p i) else 0

/-- `pⁱmin`, the smallest price `min_ℓ p_{iℓ}` of product `i` (`0` if `L = 0`). -/
noncomputable def pmin (i : Fin n) : ℝ :=
  if h : 0 < L then Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (I.p i) else 0

/-- `ϱmax = max_{i∈[n]} pⁱmax / pⁱmin` (p.14), "the maximal ratio between extremal prices over all
products" (`1` if `n = 0`, a case excluded by `Standing`). -/
noncomputable def rhoMax : ℝ :=
  if h : 0 < n then Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (fun i => I.pmax i / I.pmin i)
  else 1

/-- `‖U¹‖∞ = maxᵢ u¹ᵢ`, the largest starting inventory. -/
def uMax : ℕ := Finset.univ.sup I.u

/-- `σmax`, the largest support size of `N₁, …, N_T` (App. B.6, p.51), as the longest list. -/
def sigmaMax : ℕ := Finset.univ.sup (fun t => (I.supp t).length)

/-- The largest bit length `Nat.size ν + 1` of a listed support point `ν` (`0` if none). -/
def bitMax : ℕ := Finset.univ.sup (fun t => ((I.supp t).map (fun ν => Nat.size ν + 1)).foldr max 0)

/-- **The law of `Nₜ`** (§1.1, p.2), mass `Pr[Nₜ = ν]` at each listed `ν`.

**Formalization Note.** Under `Standing` (duplicate-free list, nonnegative masses summing to `1`)
the defining sum is `1` and this is the PMF with mass `mass t ν` at each listed `ν`; the fallback
`PMF.pure 0` is only reached outside `Standing`. -/
noncomputable def arrLaw (t : Fin T) : PMF ℕ := by
  classical
  exact
    if h : ∑ ν ∈ (I.supp t).toFinset, ENNReal.ofReal (I.mass t ν) = 1 then
      PMF.ofFinset (fun ν => if ν ∈ (I.supp t).toFinset then ENNReal.ofReal (I.mass t ν) else 0)
        (I.supp t).toFinset
        (by rw [← h]; exact Finset.sum_congr rfl (fun ν hν => by simp only [hν, if_true]))
        (by intro ν hν; simp only [hν, if_false])
    else PMF.pure 0

/-- **The MNL choice of one customer in period `t`** (p.2): product `i` (`some i`) with probability
`πᵗᵢ(x) = wᵗ_{i,x}/(1 + wₜ(x))`, no purchase (`none`) with probability `1/(1 + wₜ(x))`.

**Formalization Note.** Under `Standing` (weights `≥ 0`) the masses sum to `1` and this is the
stated law; the fallback `PMF.pure none` is only reached outside `Standing`. -/
noncomputable def choiceLaw (x : Strategy n L T) (t : Fin T) : PMF (Option (Fin n)) := by
  classical
  let g : Option (Fin n) → ENNReal := fun o =>
    match o with
    | none => ENNReal.ofReal (1 / (1 + I.wt x t))
    | some i => ENNReal.ofReal (I.piChoice x t i)
  exact if h : ∑ o, g o = 1 then PMF.ofFintype g h else PMF.pure none

/-- The vector of counts `(Σ_{ν≤k} Yᵗᵢ(x, ν))ᵢ` after `k` i.i.d. customers of period `t`, each
choosing by `choiceLaw`; a customer choosing product `i` adds `1` to coordinate `i`. -/
noncomputable def countsAfter (x : Strategy n L T) (t : Fin T) : ℕ → PMF (Fin n → ℕ)
  | 0 => PMF.pure 0
  | k + 1 => (countsAfter x t k).bind fun c =>
      (I.choiceLaw x t).map fun o =>
        match o with
        | none => c
        | some i => c + Pi.single i 1

/-- **The law of the demand vector `(Dᵗᵢ(x))ᵢ` of period `t`** (p.3):
`Dᵗᵢ(x) = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν)`, where `Nₜ` is drawn from `arrLaw` and the `Nₜ` customers choose
independently by the MNL rule. -/
noncomputable def countsLaw (x : Strategy n L T) (t : Fin T) : PMF (Fin n → ℕ) :=
  (I.arrLaw t).bind (I.countsAfter x t)

/-- **The joint law of the demand path** `d = (Dᵗᵢ(x))_{t,i}`: periods are independent (p.2,
"N₁, …, N_T are independent"), each with law `countsLaw`. -/
noncomputable def demandLaw (x : Strategy n L T) : Measure (Fin T → Fin n → ℕ) :=
  Measure.pi fun t => (I.countsLaw x t).toMeasure

end Instance

/-- The inventory level (1), p.3, at the beginning of period `t` along a demand path `d` of one
product: `[u − Σ_{τ<t} d τ]⁺`. -/
def invLevel (u : ℕ) (d : Fin T → ℕ) (t : Fin T) : ℝ :=
  max 0 ((u : ℝ) - ∑ τ ∈ Finset.univ.filter (fun τ => τ < t), (d τ : ℝ))

namespace Instance

variable (I : Instance n L T)

/-- `Uᵗᵢ(x) = [u¹ᵢ − Σ_{τ∈[t−1]} D^τᵢ(x)]⁺`, equation (1), p.3, along the demand path `d`. -/
def U (d : Fin T → Fin n → ℕ) (t : Fin T) (i : Fin n) : ℝ := invLevel (I.u i) (fun τ => d τ i) t

/-- **The expected revenue** of §1.1, p.4:
`R(x) = Σ_{t∈[T]} Σ_{i∈[n]} E[min{Uᵗᵢ(x), Dᵗᵢ(x)}] · Σ_ℓ p_{iℓ} xᵗ_{iℓ}`. -/
noncomputable def R (x : Strategy n L T) : ℝ :=
  ∑ t, ∑ i, (∫ d, min (I.U d t i) (d t i : ℝ) ∂(I.demandLaw x)) * I.price x t i

/-- The expected revenue from product `i` (App. B.2, p.48):
`Rᵢ(x) = Σ_{t∈[T]} E[min{Uᵗᵢ(x), Dᵗᵢ(x)}] · Σ_ℓ p_{iℓ} xᵗ_{iℓ}`. -/
noncomputable def Ri (x : Strategy n L T) (i : Fin n) : ℝ :=
  ∑ t, (∫ d, min (I.U d t i) (d t i : ℝ) ∂(I.demandLaw x)) * I.price x t i

end Instance

end MenuCostPricing


