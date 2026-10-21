-- Prove2me | Definitions.Def_RegretPricing_Structure_Model
-- name    : RegretPricing_Structure_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:45.402362+00:00
-- url     : https://prove2.me/theorems/468b01c2-7bbf-41be-a3b4-f57055292195
-- title:
--   §2–§3, pp. 4–10 — regretful seller: WTP law with IFR, revenue π, regrets r_o and r_u, regret objective π̂ (4), the regret DP (10)
-- statement:
--   This file fixes the single-period and multi-period model of Li and Liu's regretful seller.
--
--   **Willingness-to-pay.** A customer's willingness-to-pay $v$ has density $f$ and distribution function $F(x)=\int_{-\infty}^x f(t)\,dt$, with survival function $\bar F = 1-F$ and failure rate $h(x)=f(x)/\bar F(x)$. The standing assumptions are: the support is $[a,b]$ with $0\le a<b<\infty$, i.e. $f\ge 0$, $f=0$ outside $[a,b]$, $f$ is integrable with $\int f=1$; and $f$ is continuous on $[a,b]$. The law has an **increasing failure rate (IFR)** if $h$ is non-decreasing on $\{x<b\}$.
--
--   **Single period.** With salvage value (opportunity cost) $z$, the revenue beyond the salvage value of price $p$ is
--   $$\pi(p,z)=(p-z)\bar F(p).$$
--   The overpricing and underpricing regrets are
--   $$r_o(p,z)=\sup_{y<p}\,(y-z)\big[\bar F(y)-\bar F(p)\big],\qquad r_u(p,z)=\sup_{y\ge p}\pi(y,z)-\pi(p,z),$$
--   and for regret parameters $\alpha,\beta$ the regretful seller's objective is (second line of (4))
--   $$\hat\pi(p,z)=\pi(p,z)-\alpha\,r_o(p,z)-\beta\,r_u(p,z).$$
--   We write $\pi^*(z)=\sup_p\pi(p,z)$ and $\max_p\hat\pi(p,z)=\sup_p\hat\pi(p,z)$. A price $p$ is an *unbiased optimal price* $p^*$ at $z$ if it maximizes $\pi(\cdot,z)$, and a *regretful optimal price* $\hat p$ at $z$ if it maximizes $\hat\pi(\cdot,z)$.
--
--   **Dynamic problem.** With arrival probability $\lambda$ per period, time-to-go $t$ and remaining inventory $x$, the regretful seller's mental value-to-go satisfies (10):
--   $$U_0(x)=0,\quad U_t(0)=0,\quad U_{t}(x)=U_{t-1}(x)+\lambda\max_p\hat\pi\big(p,\Delta U_{t-1}(x)\big)\ (t,x\ge1),$$
--   where $\Delta U_t(x)=U_t(x)-U_t(x-1)$ is the marginal value of inventory.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note.** All quantities are real. The paper's maxima are real suprema over the indicated subtypes; every family involved is bounded above because $0\le\bar F\le1$ and $\bar F=0$ beyond $b$. The term $\pi(y,z)-(y-z)\bar F(p)$ is written in the equivalent form $(y-z)[\bar F(y)-\bar F(p)]$. Continuity of $f$ on $[a,b]$ is added (Proposition 1 evaluates $f(a)$, $h(a)$, and the proofs use $F'=f$). IFR is posed on $x<b$ because $h=f/0$ takes Lean's junk value $0$ for $x\ge b$. The inventory cap $x\le c$ of (10) is dropped: the recursion never increases $x$, so this only extends the domain. $\Delta U_t(x)$ is used only for $x\ge 1$ (natural-number subtraction).
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), pp. 4–10 (PDF 4–10), §2, §3, (1), (4), (10)

import Mathlib

namespace RegretPricing.Structure

open MeasureTheory

/-- The customer's willingness-to-pay law (§2, p. 4): support endpoints `a < b` and a
density `f` on `ℝ`. -/
structure WTP where
  a : ℝ
  b : ℝ
  f : ℝ → ℝ

/-- The cumulative distribution function `F(x) = ∫_{(-∞, x]} f`. -/
noncomputable def WTP.F (D : WTP) (x : ℝ) : ℝ := ∫ t in Set.Iic x, D.f t

/-- The survival function `F̄(x) = 1 - F(x)`. -/
noncomputable def WTP.Fbar (D : WTP) (x : ℝ) : ℝ := 1 - D.F x

/-- The failure rate `h(x) = f(x) / F̄(x)` (Lean's junk value `0` where `F̄(x) = 0`). -/
noncomputable def WTP.h (D : WTP) (x : ℝ) : ℝ := D.f x / D.Fbar x

/-- Standing assumptions of §2, p. 4: `0 ≤ a < b < ∞`, `f` a probability density vanishing
outside `[a, b]`, and (added) `f` continuous on `[a, b]`. -/
def WTP.Standing (D : WTP) : Prop :=
  0 ≤ D.a ∧ D.a < D.b ∧ (∀ x, 0 ≤ D.f x) ∧ (∀ x, x ∉ Set.Icc D.a D.b → D.f x = 0) ∧
    Integrable D.f ∧ ∫ x, D.f x = 1 ∧ ContinuousOn D.f (Set.Icc D.a D.b)

/-- Increasing failure rate (§2, p. 4), posed on `x < b`, where `F̄(x) > 0` can hold. -/
def WTP.IFR (D : WTP) : Prop := MonotoneOn D.h (Set.Iio D.b)

/-- The additional revenue beyond the salvage value, `π(p, z) = (p - z) F̄(p)`, (1). -/
noncomputable def revenue (D : WTP) (p z : ℝ) : ℝ := (p - z) * D.Fbar p

/-- The overpricing regret `r_o(p, z) = max_{y < p} [π(y, z) - (y - z) F̄(p)]` (Lemma 1, p. 5),
written as `sup_{y < p} (y - z) (F̄(y) - F̄(p))`. -/
noncomputable def ro (D : WTP) (p z : ℝ) : ℝ :=
  ⨆ y : {y : ℝ // y < p}, (y.1 - z) * (D.Fbar y.1 - D.Fbar p)

/-- The underpricing regret `r_u(p, z) = max_{y ≥ p} π(y, z) - π(p, z)` (Lemma 1, p. 5). -/
noncomputable def ru (D : WTP) (p z : ℝ) : ℝ :=
  (⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z) - revenue D p z

/-- The regretful seller's objective, second line of (4), p. 5:
`π̂(p, z) = π(p, z) - α r_o(p, z) - β r_u(p, z)`. -/
noncomputable def πhat (D : WTP) (α β p z : ℝ) : ℝ :=
  revenue D p z - α * ro D p z - β * ru D p z

/-- The unbiased optimal revenue `π*(z) = max_p (p - z) F̄(p)` (proof of Proposition 4, p. 20). -/
noncomputable def πstar (D : WTP) (z : ℝ) : ℝ := ⨆ p : ℝ, revenue D p z

/-- The regretful seller's optimal value `max_p π̂(p, z)`. -/
noncomputable def regretValue (D : WTP) (α β z : ℝ) : ℝ := ⨆ p : ℝ, πhat D α β p z

/-- `p` is an unbiased optimal price `p*` at salvage value `z`. -/
def IsUnbiasedPrice (D : WTP) (z p : ℝ) : Prop := ∀ p', revenue D p' z ≤ revenue D p z

/-- `p` is a regretful optimal price `p̂` at salvage value `z`, i.e. a maximizer of (4). -/
def IsRegretPrice (D : WTP) (α β z p : ℝ) : Prop := ∀ p', πhat D α β p' z ≤ πhat D α β p z

/-- The regretful seller's mental value-to-go `U_t(x)` of (10), p. 10, with time-to-go `t`
and remaining inventory `x`: `U_0(x) = 0`, `U_t(0) = 0`, and
`U_{t+1}(x) = U_t(x) + λ max_p π̂(p, U_t(x) - U_t(x - 1))` for `x ≥ 1`. -/
noncomputable def U (D : WTP) (α β lam : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | t + 1, x + 1 =>
      U D α β lam t (x + 1) + lam * regretValue D α β (U D α β lam t (x + 1) - U D α β lam t x)

/-- The marginal value of inventory `ΔU_t(x) = U_t(x) - U_t(x - 1)`, used for `x ≥ 1`. -/
noncomputable def dU (D : WTP) (α β lam : ℝ) (t x : ℕ) : ℝ :=
  U D α β lam t x - U D α β lam t (x - 1)

end RegretPricing.Structure


