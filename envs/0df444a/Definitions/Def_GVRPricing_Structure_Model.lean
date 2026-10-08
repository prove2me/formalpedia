-- Prove2me | Definitions.Def_GVRPricing_Structure_Model
-- name    : GVRPricing_Structure_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:04:16.913632+00:00
-- url     : https://prove2.me/theorems/5ac80834-8450-4e66-91b3-60db8ac43b9b
-- title:
--   §2.1 — regular demand function: inverse demand $p(\lambda)$, allowable rates $\Lambda$, revenue rate $r(\lambda)=\lambda p(\lambda)$, least maximizer $\lambda^*$
-- statement:
--   A single product is sold by a monopolist who sets its price; the market answers with a Poisson stream of demand whose rate depends on the price. Following Gallego and van Ryzin, the model is written in **rate space**: the decision is a target demand rate $\lambda$, and the market sets the price $p(\lambda)$.
--
--   A **regular demand function** consists of:
--
--   1. a set $\Lambda \subseteq [0,\infty)$ of **allowable rates**, an interval containing $0$ (the rate $0$ corresponds to the *null price* $p_\infty$, possibly $+\infty$, at which nothing sells);
--   2. an **inverse demand function** $p(\lambda)$, strictly decreasing and nonnegative on the positive allowable rates $\Lambda\setminus\{0\}$ (a one-to-one correspondence between prices and rates, with demand non-increasing in price);
--   3. the **revenue rate**
--   $$r(\lambda) = \lambda\,p(\lambda), \qquad r(0) = 0,$$
--   which is continuous on $\Lambda$ (in particular $\lim_{\lambda\to 0} r(\lambda) = 0$), concave on $\Lambda$, and bounded;
--   4. the **least maximizer** $\lambda^* = \min\{\lambda\in\Lambda : r(\lambda) = \max_{\mu\in\Lambda} r(\mu)\}$, which is assumed to exist.
--
--   The file also names $r^* = r(\lambda^*)$, $p^* = p(\lambda^*)$, and the deterministic optimal rate $\lambda^D(n,t) = \min\{\lambda^*, n/t\}$ for a stock $n$ and a horizon $t>0$ (the run-out rate of the deterministic problem, Proposition 2 of the paper), which is used in Proposition 3.
--
--   Every statement of the mission is made over an arbitrary regular demand function; the exponential demand $\lambda(p) = a e^{-p}$ (with $\Lambda = [0,a]$, $p(\lambda) = \log(a/\lambda)$) and linear demand are examples.
--
--   **Formalization Note** The revenue rate is `fun x => x * p x`, so $r(0)=0$ whatever value the Lean function `p` takes at `0`; that value plays no role. Since $p \ge 0$ on $\Lambda\setminus\{0\}$ and $\Lambda \subseteq [0,\infty)$, $r \ge 0$ on $\Lambda$, so "bounded" is encoded as bounded above. The least maximizer is a field together with `IsLeast` of the maximizer set, i.e. existence of a least maximizer is part of the definition as in the paper. No differentiability or strict concavity is assumed here; theorems that need them state them as hypotheses. This definition duplicates the regular demand model of the first mission of this series (`GVRPricing.FixedPrice`), because unpublished drafts cannot import each other.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), pp. 1003–1004 (PDF 5–6), §2.1, eq. (1) and the definition of a regular demand function; §2.2, p. 1004 (allowable rates Λ); Proposition 2, p. 1006 (λ^D)

import Mathlib

namespace GVRPricing.Structure

/-- The revenue rate `r(λ) = λ p(λ)` of eq. (1) (Gallego–van Ryzin 1994, p. 1003) built from an
inverse demand function `p`. At the null rate `λ = 0` it is `0 * p 0 = 0` whatever value `p 0`
carries, so `r 0 = 0` holds by construction (the null price `p_∞` may be `+∞`). -/
def revRate (p : ℝ → ℝ) (x : ℝ) : ℝ := x * p x

/-- A **regular demand function** (Gallego–van Ryzin 1994, §2.1, pp. 1003–1004; §2.2, p. 1004),
written in rate space as the paper prefers.

* `Λ` is the set of allowable demand rates `Λ = {λ(p) : p ∈ 𝒫}`; it contains the null rate `0`
  (the null price `p_∞ ∈ 𝒫`), lies in `[0, ∞)` and is an interval.
* `p` is the inverse demand function: it is strictly decreasing on the positive rates (one-to-one
  correspondence between prices and rates, `λ(p)` non-increasing) and nonnegative there
  (prices lie in `ℜ⁺ ∪ {p_∞}`). Its value at the rate `0` is irrelevant.
* The revenue rate `r(λ) = λ p(λ)` is continuous on `Λ` (with `r 0 = 0` this is
  `lim_{λ→0} r(λ) = 0`), concave, and bounded (it is `≥ 0` on `Λ`, so bounded above suffices).
* `lamStar` is the least maximizer `λ* = min {λ : r(λ) = max r}` of `r` over `Λ`. -/
structure Model where
  /-- The set of allowable demand rates `Λ`. -/
  Λ : Set ℝ
  /-- The inverse demand function `p(λ)`. -/
  p : ℝ → ℝ
  /-- The least maximizer `λ*` of the revenue rate. -/
  lamStar : ℝ
  zero_mem : (0 : ℝ) ∈ Λ
  subset_nonneg : Λ ⊆ Set.Ici 0
  ordConnected : Λ.OrdConnected
  p_strictAntiOn : StrictAntiOn p (Λ \ {0})
  p_nonneg : ∀ x ∈ Λ \ {0}, 0 ≤ p x
  r_continuousOn : ContinuousOn (revRate p) Λ
  r_concaveOn : ConcaveOn ℝ Λ (revRate p)
  r_bddAbove : BddAbove (revRate p '' Λ)
  lamStar_isLeast : IsLeast {x | x ∈ Λ ∧ ∀ y ∈ Λ, revRate p y ≤ revRate p x} lamStar

namespace Model

variable (M : Model)

/-- The revenue rate `r(λ) = λ p(λ)` of the model, eq. (1). -/
def r : ℝ → ℝ := revRate M.p

/-- The maximal revenue rate `r* = r(λ*)`. -/
def rStar : ℝ := M.r M.lamStar

/-- The revenue-maximizing price `p* = p(λ*)`. -/
def pStar : ℝ := M.p M.lamStar

/-- The deterministic optimal rate `λ^D(n, t) = min {λ*, n / t}` (the run-out rate of the
deterministic problem, Gallego–van Ryzin 1994, Proposition 2, p. 1006, used in Proposition 3,
p. 1009). Meaningful for `t > 0`. -/
noncomputable def detRate (n : ℕ) (t : ℝ) : ℝ := min M.lamStar ((n : ℝ) / t)

end Model

end GVRPricing.Structure


