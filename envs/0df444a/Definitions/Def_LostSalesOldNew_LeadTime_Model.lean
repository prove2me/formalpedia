-- Prove2me | Definitions.Def_LostSalesOldNew_LeadTime_Model
-- name    : LostSalesOldNew_LeadTime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:07.654984+00:00
-- url     : https://prove2.me/theorems/fae34ff9-7a63-45b9-8636-365699ea87cb
-- title:
--   Zipkin's lost-sales system: pipeline transition, demand law, cost data, the one-period costs q^l, the DP operator of (2)–(3), finite-horizon costs and the optimal cost f*^L
-- statement:
--   This file sets up the discrete-time, single-item inventory system with **lost sales** and a constant order **lead time** $L \ge 1$, in the transformed cost accounting of Zipkin (2008), §2.
--
--   **State and dynamics.** The state of the system with lead time $L$ is the vector $x = (x_0, x_1, \dots, x_{L-1}) \in \mathbb R^L$: $x_0$ is the stock on hand after this period's arrival, and $x_l$ ($1 \le l \le L-1$) is the outstanding order that arrives $l$ periods later. Given the state $x$, an order $z \ge 0$ and a demand $d$, the next state is
--   $$x_+ = \bigl([x_0 - d]^+ + x_1,\; x_2,\; \dots,\; x_{L-1},\; z\bigr),$$
--   where $[a]^+ = \max(a,0)$; demand that cannot be met is lost. For a vector $x^l = (x_0,\dots,x_l)$ of length $l+1$ and a demand $d$, the **shift** $x_+^{l-1} = ([x_0-d]^+ + x_1, x_2, \dots, x_l)$ is the vector of the first $l$ components of the next state; it does not involve a new order. The transition is the shift applied to $x^L = (x, z)$.
--
--   **Demand.** Demands are independent and identically distributed with law $D$, a probability measure on $\mathbb R$ carried by $[0,\infty)$; the demands of $l$ consecutive periods have the product law $D^{\otimes l}$.
--
--   **Costs.** The data are the unit procurement cost $c \ge 0$, the unit holding cost $\hat h \ge 0$, the unit lost-sales penalty $p \ge 0$ and the discount factor $\gamma \in [0,1)$. The transformed holding cost is $h = \hat h - \gamma c$ (which may be negative). With $[a]^- = \max(-a,0)$,
--   $$q^0(y) = c\,y + h\,E\bigl[[y-d]^+\bigr] + p\,E\bigl[[y-d]^-\bigr],$$
--   and for $l \ge 0$
--   $$q^l(x^l) = \gamma^l\, E\bigl[q^0(y_{+l})\bigr],$$
--   where $y_{+l}$ is the stock on hand $l$ periods later, obtained from $x^l$ by $l$ successive shifts with the demands of the intervening periods. The one-period cost of the system with lead time $L$ is $q(x,z) = q^L(x^L)$ with $x^L = (x,z)$.
--
--   **Optimal costs.** The dynamic-programming operator of (2)–(3) acts on functions $f$ of the state with values in $[0,\infty]$:
--   $$(Tf)(x) = \inf_{z \ge 0}\Bigl\{ q(x,z) + \gamma\, E\bigl[f(x_+)\bigr] \Bigr\}.$$
--   The finite-horizon optimal costs are $f^{(0)} = 0$ and $f^{(n+1)} = T f^{(n)}$, which is recursion (2) read with $n$ periods to go. The infinite-horizon optimal cost of the system with lead time $L$ is
--   $$f^{*L}(x) = \sup_{n} f^{(n)}(x) = \lim_{n\to\infty} f^{(n)}(x).$$
--
--   These objects are shared by every statement of the mission: the recursion for $q^l$, the optimality equation (3), and the lead-time comparison of §5.
--
--   **Formalization Note.** States are `Fin L → ℝ`; $x^L = (x,z)$ is `Fin.snoc x z`, and $x^{L-2}$ (dropping the most recent order) is `Fin.init`. `shift` is the paper's $x_+^{l-1}$ and `next` the full transition. The paper calls $f^*$ "the solution" of (3); here the optimal cost is defined as the limit of the finite-horizon costs (2), and that it solves (3) is a separate theorem. Values of the operator are in `ℝ≥0∞`, with `ENNReal.ofReal` applied to $q$ and the expectation of $f$ taken as a lower Lebesgue integral; this loses nothing because $q \ge 0$ on nonnegative states under the sign conditions on $c,\hat h,p,\gamma$ (since $E[(y-d)^+] \le y$ for $y\ge 0$). The expectations in $q^0$ and $q^l$ are Bochner integrals, meaningful when demand has finite mean; the theorems assume it. The cost signs and $\gamma < 1$ are fields of the cost structure.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), §2 Formulation, pp. 1256–1257 (dynamics, costs, (2), (3), q^0 and q^l)

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

namespace LostSalesOldNew.LeadTime

open MeasureTheory

/-- The cost data of §2 (p. 1257): unit procurement cost `c`, unit holding cost `ĥ` (`hhat`), unit
lost-sales penalty `p`, discount factor `γ < 1`. The signs are implicit in the paper (they are
costs); `γ < 1` is the paper's condition for (3). -/
structure Costs where
  c : ℝ
  hhat : ℝ
  p : ℝ
  γ : ℝ
  c_nonneg : 0 ≤ c
  hhat_nonneg : 0 ≤ hhat
  p_nonneg : 0 ≤ p
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

/-- The transformed holding cost `h = ĥ − γc` (p. 1257). It may be negative. -/
def Costs.h (K : Costs) : ℝ := K.hhat - K.γ * K.c

/-- `q^0(y) = c y + h E[[y − d]^+] + p E[[y − d]^−]` (p. 1257), with `[a]^− = max(−a, 0)`, the
demand `d` distributed according to `D`. -/
noncomputable def q0 (K : Costs) (D : Measure ℝ) (y : ℝ) : ℝ :=
  K.c * y + K.h * ∫ d, max (y - d) 0 ∂D + K.p * ∫ d, max (d - y) 0 ∂D

/-- `y_{+l}`: the stock on hand `l` periods later, after that period's arrival, computed from the
subvector `x^l = (x_0, …, x_l)` and the demands `ds 0, …, ds (l−1)` of the `l` periods in between
(`ds 0` is the current period's demand). -/
noncomputable def yAfter : (l : ℕ) → (Fin (l + 1) → ℝ) → (Fin l → ℝ) → ℝ
  | 0, x, _ => x 0
  | l + 1, x, ds => yAfter l (LostSalesOldNew.StateReduction.shift x (ds 0)) (Fin.tail ds)

/-- `q^l(x^l) = γ^l E[q^0(y_{+l})]` (p. 1257), the demands of the `l` intervening periods i.i.d.
with law `D` (the product measure `D^{⊗l}`). -/
noncomputable def qL (K : Costs) (D : Measure ℝ) (l : ℕ) (x : Fin (l + 1) → ℝ) : ℝ :=
  K.γ ^ l * ∫ ds, q0 K D (yAfter l x ds) ∂(Measure.pi fun _ : Fin l => D)

/-- The dynamic-programming operator of (2)–(3) for the system with lead time `L`:
`(T f)(x) = inf_{z ≥ 0} { q(x, z) + γ E[f(x_+)] }`, with `q(x, z) = q^L(x^L)`, `x^L = (x, z)`.
Values in `[0, ∞]`. -/
noncomputable def bellman (K : Costs) (D : Measure ℝ) (L : ℕ) (f : (Fin L → ℝ) → ENNReal)
    (x : Fin L → ℝ) : ENNReal :=
  ⨅ (z : ℝ) (_ : 0 ≤ z),
    (ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) x z))
      + ENNReal.ofReal K.γ * ∫⁻ d, f (LostSalesOldNew.StateReduction.next x z d) ∂D)

/-- (2): the optimal cost with `n` periods to go, `f_{T+1−n}`, obtained from `f_{T+1} = 0` by `n`
applications of the operator. -/
noncomputable def fH (K : Costs) (D : Measure ℝ) (L : ℕ) : ℕ → (Fin L → ℝ) → ENNReal
  | 0 => fun _ => 0
  | n + 1 => bellman K D L (fH K D L n)

/-- `f*^L`: the infinite-horizon optimal discounted cost of the system with lead time `L`, the
limit (supremum) of the finite-horizon optimal costs (2) as the horizon grows. -/
noncomputable def fStar (K : Costs) (D : Measure ℝ) (L : ℕ) (x : Fin L → ℝ) : ENNReal :=
  ⨆ n, fH K D L n x

end LostSalesOldNew.LeadTime


