-- Prove2me | Definitions.Def_ClarkScarf_Serial_Model
-- name    : ClarkScarf_Serial_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:15:05.48035+00:00
-- url     : https://prove2.me/theorems/da2b047e-0c4f-4687-aadd-b490dae37d21
-- title:
--   The two-installation serial inventory model of Clark–Scarf §§2–3: costs (1), (5), recursions (14), (15), (7), and Λ, g of (25)–(26)
-- statement:
--   This file sets up the two-installation serial inventory system of Clark and Scarf (1960). Installation 2 supplies installation 1; customer demand arrives only at installation 1 (Assumption 1); excess demand is backlogged (Assumption 4). Periods are counted backwards: $n$ is the number of periods remaining.
--
--   **Data.** Real numbers $h,p\ge 0$ (marginal holding and shortage costs at installation 1), a discount factor $\alpha\ge0$, a unit shipping cost $c_1\ge0$ from installation 2 to installation 1, a setup cost $K\ge0$ and a unit cost $c\ge0$ for system orders, a demand density $\varphi\ge0$ with $\int_0^\infty\varphi(t)\,dt=1$ and finite mean $\int_0^\infty t\varphi(t)\,dt<\infty$, and the natural one-period cost $\tilde L$ at echelon 2, assumed non-negative, continuous and of at most linear growth ($\tilde L(x)\le a+b|x|$).
--
--   **State.** $x_1$ is the stock on hand at installation 1, $w_1$ the stock that will arrive at installation 1 one period from now, and $x_2$ the echelon-2 stock (on hand at 1, plus in transit, plus on hand at 2); the states of interest satisfy $x_1+w_1\le x_2$. Shipments from 2 to 1 take two periods, system orders one period.
--
--   **Costs.** The expected one-period holding and shortage cost (1) is
--   $$L(x)=\begin{cases} hx+p\int_x^\infty (t-x)\varphi(t)\,dt, & x>0,\\ p\int_0^\infty (t-x)\varphi(t)\,dt, & x\le 0,\end{cases}$$
--   and the order cost (5) is $c(z)=K+cz$ for $z>0$, $c(0)=0$.
--
--   **The isolated installation-1 problem (15).** $\hat C_0\equiv0$ and
--   $$\hat C_{n}(x_1,w_1)=\inf_{y\ge x_1+w_1}\Big\{c_1(y-x_1-w_1)+L(x_1)+\alpha\int_0^\infty \hat C_{n-1}(x_1+w_1-t,\,y-x_1-w_1)\varphi(t)\,dt\Big\}.$$
--   The expression in braces is $\hat J_{n-1}(x_1,w_1;y)$ (`isoObj`). A number $\bar x$ is a *critical number* for $n$ periods if ordering up to $\bar x$ (i.e. choosing $y=\max(x_1+w_1,\bar x)$) attains the infimum at every state.
--
--   **The system problem (14).** $C_0\equiv0$ and
--   $$C_{n}(x_1,w_1,x_2)=\inf_{\substack{x_1+w_1\le y\le x_2\\ 0\le z}}\Big\{c(z)+c_1(y-x_1-w_1)+\tilde L(x_2)+L(x_1)+\alpha\int_0^\infty C_{n-1}(x_1+w_1-t,\,y-x_1-w_1,\,x_2+z-t)\varphi(t)\,dt\Big\};$$
--   the expression in braces is $J_{n-1}(x_1,w_1,x_2;y,z)$ (`sysObj`).
--
--   **The functions $f_n$ of (7).** $f_n\equiv0$ for $n\le2$ (no shipment placed now arrives before the horizon ends), and for $n\ge3$
--   $$f_n(u)=\inf_{y\ge u}\Big\{c_1(y-u)+\alpha^2\int_0^\infty\!\!\int_0^\infty L(y-t_1-t_2)\varphi(t_1)\varphi(t_2)\,dt_2\,dt_1+\alpha\int_0^\infty f_{n-1}(y-t)\varphi(t)\,dt\Big\}.$$
--
--   **The augmentation $\Lambda$ of (25) and the functions $g_n$ of (26).** For $n$ periods remaining with critical number $\bar x_n$, $\Lambda_n(x_2)=0$ if $n\le 2$ or $x_2\ge\bar x_n$, and otherwise
--   $$\Lambda_n(x_2)=c_1(x_2-\bar x_n)+\alpha^2\int_0^\infty\!\!\int_0^\infty[L(x_2-t-y)-L(\bar x_n-t-y)]\varphi(t)\varphi(y)\,dy\,dt+\alpha\int_0^\infty[f_{n-1}(x_2-t)-f_{n-1}(\bar x_n-t)]\varphi(t)\,dt.$$
--   Given a sequence $(\bar x_n)$, $g_0\equiv0$ and $g_n(x_2)=\inf_{z\ge0}\{c(z)+\tilde L(x_2)+\Lambda_n(x_2)+\alpha\int_0^\infty g_{n-1}(x_2+z-t)\varphi(t)\,dt\}$.
--
--   These are the objects of Theorems 1 and 2 of the paper: Theorem 1 says $C_n=\hat C_n+g_n(x_2)$.
--
--   **Formalization Note** Every expectation $\int_0^\infty F(t)\varphi(t)\,dt$ is the set integral over $(0,\infty)$, so values of $\varphi$ off $(0,\infty)$ are irrelevant. Every infimum is a real `⨅` over a subtype; the objectives are non-negative, so the infima are genuine, and the feasible sets are nonempty on the state domain $x_1+w_1\le x_2$ (off it the system infimum is over an empty set and returns the junk value $0$; every statement about $C_n$ restricts to the domain). The Lean index of `isoObj`, `sysObj` and `IsCriticalNumber` is $n$ for the problem with $n+1$ periods remaining; `Lambda n` is $\Lambda_{n+1}$ and uses $f_n$. Finite mean of the demand and the conditions on $\tilde L$ are not on the page; they are the conditions under which every expectation in (14) is finite (Assumption 3 leaves $\tilde L$ unspecified). The paper's notation uses $C_n$ for both value functions; here the isolated one is $\hat C_n$ (`isoCost`) and the system one $C_n$ (`sysCost`).
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, pp. 476-484: eq. (1) p. 476, eq. (5) p. 478, Assumptions 1-4 pp. 478-479, two-installation example p. 479, eq. (7) p. 480, eqs. (14)-(15) p. 482, eqs. (25)-(26) p. 484

import Mathlib

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- The data of the two-installation serial inventory model of Clark and Scarf (1960), §§2–3,
with its standing hypotheses. Installation 1 faces the demand; installation 2 supplies it with a
lead time of two periods; system (echelon 2) orders arrive after one period.

* `h`, `p`: marginal holding and shortage cost at installation 1, eq. (1);
* `α`: the discount factor;
* `c1`: unit shipping cost from installation 2 to installation 1;
* `K`, `c`: setup and unit cost of the echelon-2 order cost (5);
* `φ`: the demand density on `(0, ∞)`;
* `Lt`: `L̃`, the natural one-period cost at echelon 2 (Assumption 3). -/
structure Model where
  h : ℝ
  p : ℝ
  α : ℝ
  c1 : ℝ
  K : ℝ
  c : ℝ
  φ : ℝ → ℝ
  Lt : ℝ → ℝ
  h_nonneg : 0 ≤ h
  p_nonneg : 0 ≤ p
  α_nonneg : 0 ≤ α
  c1_nonneg : 0 ≤ c1
  K_nonneg : 0 ≤ K
  c_nonneg : 0 ≤ c
  φ_nonneg : ∀ t, 0 ≤ φ t
  φ_total : ∫ t in Ioi (0 : ℝ), φ t = 1
  φ_mean : IntegrableOn (fun t => t * φ t) (Ioi (0 : ℝ))
  Lt_nonneg : ∀ x, 0 ≤ Lt x
  Lt_cont : Continuous Lt
  Lt_growth : ∃ a b : ℝ, ∀ x, Lt x ≤ a + b * |x|

namespace Model

/-- The expected one-period holding and shortage cost (1) at installation 1, as a function of the
stock on hand `x` at the beginning of the period. -/
noncomputable def L (M : Model) (x : ℝ) : ℝ :=
  if 0 < x then M.h * x + M.p * ∫ t in Ioi x, (t - x) * M.φ t
  else M.p * ∫ t in Ioi (0 : ℝ), (t - x) * M.φ t

/-- The echelon-2 order cost (5): `c(z) = K + c z` for `z > 0` and `c(0) = 0`. -/
noncomputable def orderCost (M : Model) (z : ℝ) : ℝ :=
  if 0 < z then M.K + M.c * z else 0

/-- `Ĉ_n(x₁, w₁)`, the optimal `n`-period cost of installation 1 in isolation, eq. (15):
`Ĉ_0 ≡ 0` and `Ĉ_{n+1}(x₁, w₁) = inf_{y ≥ x₁ + w₁} {c₁(y - x₁ - w₁) + L(x₁)
+ α ∫₀^∞ Ĉ_n(x₁ + w₁ - t, y - x₁ - w₁) φ(t) dt}`. -/
noncomputable def isoCost (M : Model) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun x₁ w₁ => ⨅ y : {y : ℝ // x₁ + w₁ ≤ y},
      (M.c1 * ((y : ℝ) - x₁ - w₁) + M.L x₁ +
        M.α * ∫ t in Ioi (0 : ℝ), isoCost M n (x₁ + w₁ - t) ((y : ℝ) - x₁ - w₁) * M.φ t)

/-- The expression in braces of (15) for `n + 1` periods remaining, as a function of the target
`y` of stock on hand plus in transit at installation 1. -/
noncomputable def isoObj (M : Model) (n : ℕ) (x₁ w₁ y : ℝ) : ℝ :=
  M.c1 * (y - x₁ - w₁) + M.L x₁ +
    M.α * ∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (y - x₁ - w₁) * M.φ t

theorem isoCost_succ (M : Model) (n : ℕ) (x₁ w₁ : ℝ) :
    M.isoCost (n + 1) x₁ w₁ = ⨅ y : {y : ℝ // x₁ + w₁ ≤ y}, M.isoObj n x₁ w₁ y := rfl

/-- `C_n(x₁, w₁, x₂)`, the optimal `n`-period system cost, eq. (14): `C_0 ≡ 0` and
`C_{n+1}(x₁, w₁, x₂) = inf_{x₁ + w₁ ≤ y ≤ x₂, 0 ≤ z} {c(z) + c₁(y - x₁ - w₁) + L̃(x₂) + L(x₁)
+ α ∫₀^∞ C_n(x₁ + w₁ - t, y - x₁ - w₁, x₂ + z - t) φ(t) dt}`. The pair `q` is `(y, z)`. -/
noncomputable def sysCost (M : Model) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0 => fun _ _ _ => 0
  | n + 1 => fun x₁ w₁ x₂ =>
      ⨅ q : {q : ℝ × ℝ // x₁ + w₁ ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2},
        (M.orderCost (q : ℝ × ℝ).2 + M.c1 * ((q : ℝ × ℝ).1 - x₁ - w₁) + M.Lt x₂ + M.L x₁ +
          M.α * ∫ t in Ioi (0 : ℝ),
            sysCost M n (x₁ + w₁ - t) ((q : ℝ × ℝ).1 - x₁ - w₁) (x₂ + (q : ℝ × ℝ).2 - t) *
              M.φ t)

/-- The expression in braces of (14) for `n + 1` periods remaining, as a function of the
installation-1 target `y` and the system order quantity `z`. -/
noncomputable def sysObj (M : Model) (n : ℕ) (x₁ w₁ x₂ y z : ℝ) : ℝ :=
  M.orderCost z + M.c1 * (y - x₁ - w₁) + M.Lt x₂ + M.L x₁ +
    M.α * ∫ t in Ioi (0 : ℝ), M.sysCost n (x₁ + w₁ - t) (y - x₁ - w₁) (x₂ + z - t) * M.φ t

theorem sysCost_succ (M : Model) (n : ℕ) (x₁ w₁ x₂ : ℝ) :
    M.sysCost (n + 1) x₁ w₁ x₂ =
      ⨅ q : {q : ℝ × ℝ // x₁ + w₁ ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2},
        M.sysObj n x₁ w₁ x₂ (q : ℝ × ℝ).1 (q : ℝ × ℝ).2 := rfl

/-- `f_n(u)` of (7), the part of the isolated cost of installation 1 that a shipment can
modify: `f_n ≡ 0` for `n ≤ 2` (no shipment arrives within the horizon), and for `n + 3` periods
`f_{n+3}(u) = inf_{y ≥ u} {c₁(y - u) + α² ∫₀^∞∫₀^∞ L(y - t₁ - t₂) φ(t₁) φ(t₂) dt₂ dt₁
+ α ∫₀^∞ f_{n+2}(y - t) φ(t) dt}`. -/
noncomputable def fLag (M : Model) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun _ => 0
  | 2 => fun _ => 0
  | n + 3 => fun u => ⨅ y : {y : ℝ // u ≤ y},
      (M.c1 * ((y : ℝ) - u) +
        M.α ^ 2 * (∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
          M.L ((y : ℝ) - t₁ - t₂) * M.φ t₁ * M.φ t₂) +
        M.α * ∫ t in Ioi (0 : ℝ), fLag M (n + 2) ((y : ℝ) - t) * M.φ t)

/-- `x̄` is a single critical number of the isolated installation-1 problem (15) with `n + 1`
periods remaining: ordering up to `x̄` when `x₁ + w₁ < x̄`, and not ordering otherwise, attains the
infimum in (15) at every state. -/
def IsCriticalNumber (M : Model) (n : ℕ) (xbar : ℝ) : Prop :=
  ∀ x₁ w₁ y : ℝ, x₁ + w₁ ≤ y → M.isoObj n x₁ w₁ (max (x₁ + w₁) xbar) ≤ M.isoObj n x₁ w₁ y

/-- `Λ(x₂)` of (25), the augmentation of the echelon-2 natural cost, for `n + 1` periods remaining
with critical number `x̄`: for `n ≥ 2` and `x₂ < x̄`,
`Λ(x₂) = c₁(x₂ - x̄) + α² ∫₀^∞∫₀^∞ [L(x₂ - t - y) - L(x̄ - t - y)] φ(t) φ(y) dy dt
+ α ∫₀^∞ [f_n(x₂ - t) - f_n(x̄ - t)] φ(t) dt`, and `Λ(x₂) = 0` otherwise. -/
noncomputable def Lambda (M : Model) (n : ℕ) (xbar x₂ : ℝ) : ℝ :=
  if 2 ≤ n ∧ x₂ < xbar then
    M.c1 * (x₂ - xbar) +
      M.α ^ 2 * (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
        (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) +
      M.α * ∫ t in Ioi (0 : ℝ), (M.fLag n (x₂ - t) - M.fLag n (xbar - t)) * M.φ t
  else 0

/-- The functions `g_n(x₂)` of (26), given critical numbers `xbar (n + 1)` for `n + 1` periods
remaining: `g_0 ≡ 0` and `g_{n+1}(x₂) = inf_{z ≥ 0} {c(z) + L̃(x₂) + Λ(x₂)
+ α ∫₀^∞ g_n(x₂ + z - t) φ(t) dt}` with `Λ` taken for `n + 1` periods and `x̄ = xbar (n + 1)`. -/
noncomputable def gClark (M : Model) (xbar : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x₂ => ⨅ z : {z : ℝ // 0 ≤ z},
      (M.orderCost (z : ℝ) + M.Lt x₂ + M.Lambda n (xbar (n + 1)) x₂ +
        M.α * ∫ t in Ioi (0 : ℝ), gClark M xbar n (x₂ + (z : ℝ) - t) * M.φ t)

end Model

end ClarkScarf.Serial


