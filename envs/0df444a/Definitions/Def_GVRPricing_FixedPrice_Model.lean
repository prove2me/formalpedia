-- Prove2me | Definitions.Def_GVRPricing_FixedPrice_Model
-- name    : GVRPricing_FixedPrice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:18:34.303849+00:00
-- url     : https://prove2.me/theorems/e667537d-8da2-444d-aa90-e157f24a4621
-- title:
--   §2.1 — regular demand function: allowable rates Λ, inverse demand p(λ), revenue rate r(λ) = λp(λ), least maximizer λ*
-- statement:
--   This file fixes the demand model of Gallego and van Ryzin (1994), §2.1, in **rate space**, as the paper itself prefers.
--
--   A firm chooses a demand intensity $\lambda$ from the set of **allowable rates** $\Lambda=\{\lambda(p): p\in\mathcal P\}$, where $\mathcal P=\mathbb R^+\cup\{p_\infty\}$ and $p_\infty$ is the **null price** (possibly $+\infty$), at which demand vanishes. The market then charges the price $p(\lambda)$, the inverse of the demand function $\lambda(p)$. A **regular demand function** is described by the data $(\Lambda, p, \lambda^*)$ subject to:
--
--   1. $0\in\Lambda$ (the null price), every $\lambda\in\Lambda$ is nonnegative, and $\Lambda$ is an interval;
--   2. on the nonzero rates, $p$ is strictly decreasing (prices and rates are in one-to-one correspondence and $\lambda(p)$ is non-increasing) and nonnegative;
--   3. the **revenue rate**
--   $$r(\lambda)=\lambda\,p(\lambda)$$
--   (eq. (1)) satisfies $r(0)=0$, is continuous on $\Lambda$ (so $\lim_{\lambda\to0}r(\lambda)=0$), concave on $\Lambda$ and bounded;
--   4. $\lambda^*=\min\{\lambda\in\Lambda: r(\lambda)=\max_{\mu\in\Lambda}r(\mu)\}$, the least maximizer of $r$, exists.
--
--   The file also names $r^*=r(\lambda^*)=p^*\lambda^*$, the maximal revenue rate, and $p^*=p(\lambda^*)$ (§3.2, p. 1006), and the price collected at a sale made at intensity $\lambda$: $p(\lambda)$ if $\lambda\neq0$ and $0$ at the null rate.
--
--   Every object of the mission (the stochastic pricing problem, the deterministic problem, the fixed-price heuristics) is built on these data. Exponential demand $\lambda(p)=ae^{-p}$ ($\Lambda=[0,a]$, $p(\lambda)=\log(a/\lambda)$, $\lambda^*=a/e$) and linear demand are instances.
--
--   **Formalization Note** The model is stated in rate space: `Λ`, `p` and `lstar` are the data, and the price-space demand function $\lambda(p)$ is the inverse of `p` on $\Lambda\setminus\{0\}$. The value `p 0` is never used, because the null price may be $+\infty$; the sale price at rate $0$ is set to $0$, which affects only a probability-zero event. That $\Lambda$ is an interval is the reading that makes concavity of $r$ on $\Lambda$ meaningful. Surjectivity of $\lambda(\cdot)$ onto $\Lambda$ from all prices $p\ge0$ is not required (the paper's linear-demand example does not have it either). Differentiability and strict concavity are not assumed.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), pp. 1003–1004 (PDF 5–6), §2.1, eq. (1), definition of a regular demand function; p. 1006 (PDF 8), §3.2, p* and r*

import Mathlib

open Set

namespace GVRPricing.FixedPrice

/-- A **regular demand function** in rate space (Gallego–van Ryzin 1994, §2.1, pp. 1003–1004,
eq. (1)).

* `Λ` is the set of allowable demand rates `Λ = {λ(p) : p ∈ 𝒫}` with `𝒫 = ℝ⁺ ∪ {p_∞}`; it
  contains `0` (the rate of the null price `p_∞`), consists of nonnegative rates and is an
  interval (`OrdConnected`), so that concavity of `r` on `Λ` is meaningful.
* `p : ℝ → ℝ` is the inverse demand `p(λ)`; on the nonzero rates it is strictly decreasing
  (one-to-one correspondence between prices and rates, `λ(p)` non-increasing) and nonnegative
  (prices lie in `ℝ⁺`). Its value at the rate `0` is never used: the null price `p_∞` may be `+∞`.
* The revenue rate `r(λ) = λ p(λ)` (eq. (1)) equals `0` at `λ = 0`; it is continuous on `Λ`
  (with `r 0 = 0` this is `lim_{λ→0} r(λ) = 0`), concave on `Λ` and bounded above.
* `lstar` is the least maximizer `λ* = min {λ : r(λ) = max_{λ ≥ 0} r(λ)}` of `r` on `Λ`; the
  field `isLeast_lstar` asserts that it exists and is the least one, so it is determined by the
  other data. -/
structure Model where
  /-- The set of allowable demand rates. -/
  Λ : Set ℝ
  /-- The inverse demand function `p(λ)`. -/
  p : ℝ → ℝ
  zero_mem : (0 : ℝ) ∈ Λ
  nonneg : ∀ l ∈ Λ, 0 ≤ l
  ordConnected : Λ.OrdConnected
  strictAntiOn : StrictAntiOn p (Λ \ {0})
  price_nonneg : ∀ l ∈ Λ, l ≠ 0 → 0 ≤ p l
  continuousOn : ContinuousOn (fun l => l * p l) Λ
  concaveOn : ConcaveOn ℝ Λ (fun l => l * p l)
  bddAbove : BddAbove ((fun l => l * p l) '' Λ)
  /-- The least maximizer `λ*` of the revenue rate. -/
  lstar : ℝ
  isLeast_lstar : IsLeast {l ∈ Λ | ∀ m ∈ Λ, m * p m ≤ l * p l} lstar

namespace Model

variable (M : Model)

/-- The revenue rate `r(λ) = λ p(λ)` (eq. (1)); `r 0 = 0`. -/
def r (l : ℝ) : ℝ := l * M.p l

/-- `r* = p* λ* = r(λ*)`, the maximal revenue rate (§3.2, p. 1006). -/
def rstar : ℝ := M.r M.lstar

/-- `p* = p(λ*)`, the revenue-maximizing price (§3.2, p. 1006). -/
def pstar : ℝ := M.p M.lstar

open Classical in
/-- The price collected at a sale made while the intensity is `l`: `p(l)` for `l ≠ 0`, and `0`
for the null rate `l = 0` (a sale at the null price is a probability-zero event; this convention
only keeps the junk value `p 0` out of every revenue). -/
noncomputable def price (l : ℝ) : ℝ := if l = 0 then 0 else M.p l

end Model

end GVRPricing.FixedPrice


