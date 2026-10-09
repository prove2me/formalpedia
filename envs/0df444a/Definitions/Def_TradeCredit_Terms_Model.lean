-- Prove2me | Definitions.Def_TradeCredit_Terms_Model
-- name    : TradeCredit_Terms_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:48.881417+00:00
-- url     : https://prove2.me/theorems/f109d114-523c-40cf-a37b-ee5effdb3a3a
-- title:
--   §3–§5, pp. 7–13 — IFR demand, bank-loan kernel F̂_b, C(θ), Q(θ_b, θ_t), the threshold domain Θ, supplier profit (8), optimal contracts
-- statement:
--   This file fixes the model of Yang and Birge's trade credit paper in the reduced form the paper itself uses from §5 on, where the supplier chooses the bank-loan default threshold $\theta_b$ and the trade-credit default threshold $\theta_t$.
--
--   **Demand (§3, p. 7).** Demand has a density $f$ with support $[0,+\infty)$. Its CDF, complementary CDF, failure rate and generalized failure rate are
--   $$F(x)=\int_0^x f(t)\,dt,\qquad \bar F(x)=1-F(x),\qquad h(x)=\frac{f(x)}{\bar F(x)},\qquad g(x)=x\,h(x).$$
--   The standing assumptions (`DemandModel`) are: $f$ is continuous on $[0,\infty)$, $f(x)>0$ for $x\ge 0$, $f(x)=0$ for $x<0$, $f$ is integrable on $[0,\infty)$ with $\int_0^\infty f=1$, and the failure rate $h$ is (weakly) increasing on $[0,\infty)$ (IFR). The retail price is normalized to $p=1$ and the salvage value is $s=0$.
--
--   **Bank loan (§4, pp. 10–11).** For the bank's deadweight cost proportion $\alpha_b\in[0,1]$ and retailer cash $K>0$,
--   $$\hat F_b(x)=\bar F(x)\,[1-\alpha_b g(x)],\qquad C(\theta)=\frac{K+\int_0^\theta \hat F_b(x)\,dx}{\hat F_b(\theta)}-\theta .$$
--
--   **Order quantity and prices (Corollary 3, p. 12; (11), p. 14).** With $M^*=g^{-1}(1)\,\bar F(g^{-1}(1))$, the maximum of $q\bar F(q)$,
--   $$Q(\theta_b,\theta_t)=\min\{q\ge 0:\ q\bar F(q)=[\theta_t+C(\theta_b)]\,\bar F(\theta_t)\},$$
--   $$w_t=\frac{\bar F(Q)}{\bar F(\theta_t)},\qquad w_c=\hat F_b(\theta_b)\,w_t,\qquad d_t=1-\frac{w_c}{w_t}=1-\hat F_b(\theta_b).$$
--
--   **Domain.** $\Theta$ is the set of $(\theta_b,\theta_t)$ with
--   1. $0\le\theta_b\le\theta_t$;
--   2. $[\theta_t+C(\theta_b)]\,\bar F(\theta_t)\le M^*$;
--   3. $\theta_t\le Q(\theta_b,\theta_t)$, which is $w_t\le 1$ by (11);
--   4. $c\le w_c$.
--
--   **Supplier profit (8), p. 13.** For unit cost $c$ and the supplier's deadweight cost proportion $\alpha_t\in[0,1]$,
--   $$\Pi_s(\theta_b,\theta_t)=K+\int_0^{\theta_t}\bar F(x)\,dx-c\,Q(\theta_b,\theta_t)-\Big[\alpha_b\int_0^{\theta_b}x\,dF(x)+\alpha_t\int_{\theta_b}^{\theta_t}(x-\theta_b)\,dF(x)\Big].$$
--   The optimal profit is $\Pi_s^*=\sup_\Theta \Pi_s$, and an **optimal trade credit contract** is any $(\theta_b,\theta_t)\in\Theta$ that maximizes $\Pi_s$ over $\Theta$.
--
--   Every statement of the mission (Proposition 3, Corollary 3, Proposition 6 and the Appendix C lemmas) is about these objects.
--
--   **Formalization Note** "Support $[0,+\infty)$" and "PDF $f$" are read as a continuous density that is positive on $[0,\infty)$. The paper never states continuity, but its implicit-function arguments need it. Constraints 3 and 4 of $\Theta$ are not in the printed $\Theta$ of Corollary 3. They are the image under (11) of the contract restriction $c\le w_c\le w_t\le 1$ of §3.1 (p. 8), which Corollary 3's mapping claims. Without them, (8) would let the supplier collect more than the retailer's revenue, and $C$ could pass its pole where $\hat F_b$ vanishes. $g^{-1}(1)$ is written as $\sup\{q\ge 0: g(q)\le 1\}$, and $Q$ as the infimum of the nonnegative roots: the root set is closed, so this is the paper's minimum whenever a root exists. The integral $\int x\,dF(x)$ is written $\int x f(x)\,dx$. Lean's division and `sSup`/`sInf` return $0$ on bad input. Every statement of the mission stays inside $\Theta$, where $\bar F>0$ and $\hat F_b>0$ and the root set of $Q$ is nonempty, and a statement about $Q$ off $\Theta$ carries the nonemptiness explicitly.
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), pp. 7–14, §3 (demand, §3.1 c ≤ w_c ≤ w_t ≤ 1), §4 (2) and F̂_b, Proposition 1 (C(θ)), Corollary 3 (Θ, Q), (8), (11)

import Mathlib

namespace TradeCredit.Terms

open MeasureTheory

/-- The demand CDF `F(x) = ∫₀ˣ f(t) dt` of a demand density `f` (§3, p. 7). -/
noncomputable def F (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0)..x, f t

/-- The complementary CDF `F̄(x) = 1 - F(x)` (§3, p. 7). -/
noncomputable def Fbar (f : ℝ → ℝ) (x : ℝ) : ℝ := 1 - F f x

/-- The failure rate `h(x) = f(x) / F̄(x)` (§3, p. 7). Lean's division returns `0` where
`F̄(x) = 0`; under `DemandModel` this never happens. -/
noncomputable def failureRate (f : ℝ → ℝ) (x : ℝ) : ℝ := f x / Fbar f x

/-- The generalized failure rate `g(x) = x h(x)` (§3, p. 7). -/
noncomputable def genFailureRate (f : ℝ → ℝ) (x : ℝ) : ℝ := x * failureRate f x

/-- The standing demand assumptions of §3 (p. 7): the demand has a continuous density `f`
with support `[0, +∞)` (read as: `f > 0` on `[0, ∞)` and `f = 0` on `(-∞, 0)`), total mass `1`,
and an increasing failure rate (IFR). -/
structure DemandModel (f : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn f (Set.Ici 0)
  pos : ∀ x : ℝ, 0 ≤ x → 0 < f x
  zero_of_neg : ∀ x : ℝ, x < 0 → f x = 0
  integrableOn : IntegrableOn f (Set.Ici 0)
  total : ∫ x in Set.Ici 0, f x = 1
  ifr : MonotoneOn (failureRate f) (Set.Ici 0)

/-- The bank's repayment kernel `F̂_b(x) = F̄(x)[1 - α_b g(x)]` (§4, p. 10, after (2)). -/
noncomputable def Fhatb (f : ℝ → ℝ) (αb x : ℝ) : ℝ :=
  Fbar f x * (1 - αb * genFailureRate f x)

/-- `C(θ) = (K + ∫₀^θ F̂_b(x) dx) / F̂_b(θ) - θ` (Proposition 1, p. 11). -/
noncomputable def Cfun (f : ℝ → ℝ) (αb K θ : ℝ) : ℝ :=
  (K + ∫ x in (0)..θ, Fhatb f αb x) / Fhatb f αb θ - θ

/-- `g⁻¹(1)`: the point `q ≥ 0` with `g(q) = 1`, written as the largest `q ≥ 0` with
`g(q) ≤ 1` (under `DemandModel`, `g` is continuous, strictly increasing and unbounded on
`[0, ∞)`, so this set is `[0, g⁻¹(1)]`). -/
noncomputable def gInv1 (f : ℝ → ℝ) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ genFailureRate f q ≤ 1}

/-- `M* = g⁻¹(1) F̄(g⁻¹(1))`, the maximum of `q F̄(q)` (Corollary 3, p. 12). -/
noncomputable def Mstar (f : ℝ → ℝ) : ℝ := gInv1 f * Fbar f (gInv1 f)

/-- The order quantity `Q(θ_b, θ_t) = min{q : q F̄(q) = [θ_t + C(θ_b)] F̄(θ_t)}`
(Corollary 3, p. 12), the smallest nonnegative root. -/
noncomputable def Qfun (f : ℝ → ℝ) (αb K θb θt : ℝ) : ℝ :=
  sInf {q : ℝ | 0 ≤ q ∧ q * Fbar f q = (θt + Cfun f αb K θb) * Fbar f θt}

/-- The credit price `w_t = F̄(q) / F̄(θ_t)` with `q = Q(θ_b, θ_t)` ((11), p. 14). -/
noncomputable def wt (f : ℝ → ℝ) (αb K θb θt : ℝ) : ℝ :=
  Fbar f (Qfun f αb K θb θt) / Fbar f θt

/-- The cash price `w_c = F̂_b(θ_b) F̄(q) / F̄(θ_t)` ((11), p. 14). -/
noncomputable def wc (f : ℝ → ℝ) (αb K θb θt : ℝ) : ℝ :=
  Fhatb f αb θb * wt f αb K θb θt

/-- The early-payment discount `d_t = 1 - w_c / w_t = 1 - F̂_b(θ_b)` (§3.1, p. 8, with (11)). -/
noncomputable def dt (f : ℝ → ℝ) (αb θb : ℝ) : ℝ := 1 - Fhatb f αb θb

/-- The supplier's domain of thresholds `Θ`: the printed set of Corollary 3 (p. 12),
`θ_t ≥ θ_b ≥ 0` and `[θ_t + C(θ_b)] F̄(θ_t) ≤ g⁻¹(1) F̄(g⁻¹(1))`, together with the image under
(11) of §3.1's `w_c ≤ w_t ≤ 1` and `c ≤ w_c` (p. 8): `θ_t ≤ Q(θ_b, θ_t)` (⇔ `w_t ≤ 1`) and
`c ≤ w_c`. -/
def Theta (f : ℝ → ℝ) (c αb K : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧
    (p.2 + Cfun f αb K p.1) * Fbar f p.2 ≤ Mstar f ∧
    p.2 ≤ Qfun f αb K p.1 p.2 ∧
    c ≤ wc f αb K p.1 p.2}

/-- The supplier's expected profit (8) (p. 13) as a function of the thresholds:
`Π_s = K + ∫₀^{θ_t} F̄ - c Q(θ_b, θ_t) - [α_b ∫₀^{θ_b} x dF(x) + α_t ∫_{θ_b}^{θ_t} (x - θ_b) dF(x)]`. -/
noncomputable def PiS (f : ℝ → ℝ) (c αb αt K θb θt : ℝ) : ℝ :=
  K + (∫ x in (0)..θt, Fbar f x) - c * Qfun f αb K θb θt -
    (αb * (∫ x in (0)..θb, x * f x) + αt * (∫ x in θb..θt, (x - θb) * f x))

/-- The supplier's optimal profit `Π*_s = sup_{(θ_b, θ_t) ∈ Θ} Π_s(θ_b, θ_t)`. -/
noncomputable def PiSstar (f : ℝ → ℝ) (c αb αt K : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => PiS f c αb αt K p.1 p.2) '' Theta f c αb K)

/-- `(θ_b, θ_t)` is an optimal trade credit contract: it lies in `Θ` and maximizes `Π_s` over `Θ`. -/
def IsOptimalContract (f : ℝ → ℝ) (c αb αt K θb θt : ℝ) : Prop :=
  (θb, θt) ∈ Theta f c αb K ∧
    IsMaxOn (fun p : ℝ × ℝ => PiS f c αb αt K p.1 p.2) (Theta f c αb K) (θb, θt)

end TradeCredit.Terms


