-- Prove2me | Definitions.Def_OrgDiversity_Optimal_Model
-- name    : OrgDiversity_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:22.845373+00:00
-- url     : https://prove2.me/theorems/607fdd98-8e66-43b7-838b-ab2517bb6797
-- title:
--   §2–§3, pp. 10–24 — decision maker / implementer organization: implementation, project choice, information effort, success probability
-- statement:
--   This file sets up the two-agent organization of Itoh and Morita (§2, pp. 10–12) and the backward-induction objects of §3.
--
--   **Primitives.** The state is $\theta\in\{1,2\}$, each with probability $1/2$; project $d\in\{1,2\}$ succeeds only if $\theta=d$ and the implementer (IM) exerts effort. IM's effort cost $\tilde c$ has CDF $F$ and density $f$. On success the decision maker (DM) receives $B_H$ from project 1 and $B_L<B_H$ from project 2. IM receives $b_H$ from his favourite project and $b_L<b_H$ from the other. The organization is **homogeneous** ($hom$) if IM's favourite is project 1 and **heterogeneous** ($het$) if it is project 2. The parameter record also carries the standing assumptions (`Standing`), Assumption 1 ($\Gamma\ge F(b_H/2)/F(b_L/2)$), Assumption 2 ($\Gamma\ge\gamma$) and Assumption 3 ($xf(x)$ weakly increasing on $x>0$), with $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   **Signal.** IM chooses information effort $\pi\in[0,1]$ at cost $\eta(\pi;k)=\pi^2/(2k)$. With probability $\pi$ a signal $\sigma\in\{1,2\}$ arrives (each with probability $1/2$), otherwise $\sigma=\phi$. The posterior that project $d$ is efficient is
--   $$\Pr[\theta=d\mid\sigma]=\begin{cases}1/2,&\sigma=\phi,\\ \alpha,&\sigma=d,\\ 1-\alpha,&\sigma\ne d,\end{cases}\qquad \alpha\in(1/2,1].$$
--
--   **Backward induction.**
--   1. IM implements project $d$ iff $\tilde c\le \Pr[\theta=d\mid\sigma]\,b$, so the success probability is $p(b,d,\sigma)=\Pr[\theta=d\mid\sigma]\,F(\Pr[\theta=d\mid\sigma]\,b)$.
--   2. DM chooses $d^*(\sigma)=2$ iff $p(b,2,\sigma)B_L>p(b,1,\sigma)B_H$, and project 1 when indifferent.
--   3. IM's net benefit is $K(b,d,\sigma)=p(b,d,\sigma)\,b-\int_0^{\Pr[\theta=d\mid\sigma]b}c\,f(c)\,dc$. His ex ante payoff is
--   $$\pi\Big(\tfrac12K(b,d^*(1),1)+\tfrac12K(b,d^*(2),2)\Big)+(1-\pi)K(b,d^*(\phi),\phi)-\frac{\pi^2}{2k}.$$
--   An optimal effort is any maximizer of this payoff over $[0,1]$.
--   4. The principal's profit $V$ is the success probability $\pi\big(\tfrac12p(\cdot,d^*(1),1)+\tfrac12p(\cdot,d^*(2),2)\big)+(1-\pi)p(\cdot,d^*(\phi),\phi)$.
--
--   The file also defines $K(x)=\int_0^xF(c)\,dc$ and the four marginal benefits of information of pp. 18 and 20: $\tfrac12K(\alpha b_H)+\tfrac12K((1-\alpha)b_H)-K(b_H/2)$ (homogeneous, non-reactive DM), $\tfrac12K(\alpha b_H)+\tfrac12K(\alpha b_L)-K(b_H/2)$ (homogeneous, reactive), and the same with $b_L$ and $b_H$ exchanged for the heterogeneous organization. It also defines the threshold predicates for $\alpha_{hom}\in(1/2,1)$, $\alpha_{het}\in[1/2,1)$ and $\hat\alpha\in(1/2,1)$, which solve $\alpha F(\alpha b_L)=(1-\alpha)F((1-\alpha)b_H)\Gamma$, $\alpha F(\alpha b_H)=(1-\alpha)F((1-\alpha)b_L)\Gamma$ and $\alpha F(\alpha b_L)=(1-\alpha)F((1-\alpha)b_H)$ respectively.
--
--   These are the objects every result of the paper's §3 is stated about.
--
--   **Formalization Note** All quantities are real. $F$ is a function on $\mathbb R$, but the standing assumptions constrain it only on $[0,\infty)$ (the paper's "$F$ strictly increasing" together with $F(0)=0$ can only mean this). The paper calls $f$ the density of $F$; this is made explicit by local integrability of $f$ and $F(x)=\int_0^x f(c)\,dc$ for $x\ge0$. Continuity of $F$ on $[0,\infty)$ and $F'=f$ on $(0,\infty)$ are also assumed. The signal is encoded by its posteriors, which the paper states (p. 11), not derived from a joint law. Assumption 1 is written as the ratio of the page; $F(b_L/2)>0$ under the standing assumptions, so the division is safe.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), pp. 10–24, §2, §3.1–3.4, Assumptions 1–3, the definitions of α_hom (p. 15), α_het (p. 16), α̂ (p. 23)

import Mathlib

namespace OrgDiversity.Optimal

noncomputable section

/-- The two organizations (p. 11): in `hom` IM's favourite project is project 1 (DM's
favourite); in `het` IM's favourite project is project 2. -/
inductive Org
  | hom
  | het
  deriving DecidableEq, Repr

/-- The two relevant projects `d ∈ {1, 2}` (p. 10). -/
inductive Proj
  | one
  | two
  deriving DecidableEq, Repr

/-- The signal `σ ∈ {ϕ, 1, 2}` (p. 11); `phi` is "no additional information". -/
inductive Sig
  | phi
  | one
  | two
  deriving DecidableEq, Repr

/-- Primitives of the model (§2, pp. 10–11): IM's private benefits `b_L < b_H`, DM's private
benefits `B_L < B_H`, the CDF `F` of IM's implementation cost `c̃` and its density `f`. -/
structure Params where
  bL : ℝ
  bH : ℝ
  BL : ℝ
  BH : ℝ
  F : ℝ → ℝ
  f : ℝ → ℝ

/-- Standing assumptions of §2–§3.1 (pp. 10–13): `0 < b_L < b_H`, `0 < B_L < B_H`, `F(0) = 0`,
`F` strictly increasing and continuous on `[0, ∞)`, `f` is its density there, and
`F(b_H) ≤ 1`. The integral clause makes the paper's word "density" explicit. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.bL ∧ P.bL < P.bH ∧ 0 < P.BL ∧ P.BL < P.BH ∧ P.F 0 = 0 ∧
  StrictMonoOn P.F (Set.Ici 0) ∧ ContinuousOn P.F (Set.Ici 0) ∧
  (∀ x : ℝ, 0 < x → HasDerivAt P.F (P.f x) x) ∧
  (∀ x : ℝ, 0 ≤ x → IntervalIntegrable P.f MeasureTheory.volume 0 x ∧
    P.F x = ∫ c in (0 : ℝ)..x, P.f c) ∧
  P.F P.bH ≤ 1

/-- Assumption 1 (p. 14): `Γ = B_H / B_L ≥ F(b_H/2) / F(b_L/2)`. -/
def Params.Assumption1 (P : Params) : Prop :=
  P.F (P.bH / 2) / P.F (P.bL / 2) ≤ P.BH / P.BL

/-- Assumption 2 (p. 14): `Γ = B_H / B_L ≥ γ = b_H / b_L`. -/
def Params.Assumption2 (P : Params) : Prop :=
  P.bH / P.bL ≤ P.BH / P.BL

/-- Assumption 3 (p. 20): `x f(x)` is (weakly) increasing in `x > 0`. -/
def Params.Assumption3 (P : Params) : Prop :=
  MonotoneOn (fun x => x * P.f x) (Set.Ioi 0)

/-- `α_hom` (p. 15): a solution in `(1/2, 1)` of `α F(α b_L) = (1 - α) F((1 - α) b_H) Γ`. -/
def Params.IsAlphaHom (P : Params) (a : ℝ) : Prop :=
  a ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
    a * P.F (a * P.bL) = (1 - a) * P.F ((1 - a) * P.bH) * (P.BH / P.BL)

/-- `α_het` (p. 16): a solution in `[1/2, 1)` of `α F(α b_H) = (1 - α) F((1 - α) b_L) Γ`. -/
def Params.IsAlphaHet (P : Params) (a : ℝ) : Prop :=
  a ∈ Set.Ico (1 / 2 : ℝ) 1 ∧
    a * P.F (a * P.bH) = (1 - a) * P.F ((1 - a) * P.bL) * (P.BH / P.BL)

/-- `α̂` (p. 23): a solution in `(1/2, 1)` of `α F(α b_L) = (1 - α) F((1 - α) b_H)`. -/
def Params.IsAlphaHat (P : Params) (a : ℝ) : Prop :=
  a ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ a * P.F (a * P.bL) = (1 - a) * P.F ((1 - a) * P.bH)

/-- Posterior `Pr[θ = d | σ]` (p. 11): `1/2` if `σ = ϕ`, `α` if `σ = d`, `1 - α` otherwise. -/
def post (α : ℝ) : Proj → Sig → ℝ
  | _, .phi => 1 / 2
  | .one, .one => α
  | .two, .two => α
  | .one, .two => 1 - α
  | .two, .one => 1 - α

/-- IM's private benefit `b` from project `d` on success (p. 11). -/
def imBen (P : Params) : Org → Proj → ℝ
  | .hom, .one => P.bH
  | .hom, .two => P.bL
  | .het, .one => P.bL
  | .het, .two => P.bH

/-- DM's private benefit `B` from project `d` on success (p. 10). -/
def dmBen (P : Params) : Proj → ℝ
  | .one => P.BH
  | .two => P.BL

/-- Success probability `p(b, d, σ) = Pr[θ = d | σ] · F(Pr[θ = d | σ] · b)` (§3.1–3.2,
pp. 13–15): IM implements iff `c̃ ≤ Pr[θ = d | σ] · b`. -/
def succ (P : Params) (o : Org) (α : ℝ) (d : Proj) (σ : Sig) : ℝ :=
  post α d σ * P.F (post α d σ * imBen P o d)

/-- DM's project choice `d*(σ)` (§3.2, timing step 4, p. 12): project 2 iff its expected benefit
`p(b, 2, σ) B_L` strictly exceeds that of project 1; project 1 if indifferent. -/
def dStar (P : Params) (o : Org) (α : ℝ) (σ : Sig) : Proj :=
  if succ P o α .one σ * dmBen P .one < succ P o α .two σ * dmBen P .two then .two else .one

/-- IM's expected net benefit `K(b, d, σ) = p(b, d, σ) b - ∫₀^{Pr[θ=d|σ] b} c f(c) dc`
(§3.3, p. 17). -/
def netBen (P : Params) (o : Org) (α : ℝ) (d : Proj) (σ : Sig) : ℝ :=
  succ P o α d σ * imBen P o d - ∫ c in (0 : ℝ)..(post α d σ * imBen P o d), c * P.f c

/-- IM's ex ante payoff from information effort `π` (§3.3, p. 18): with probability `π` the
signal is `1` or `2` (each `1/2`), with probability `1 - π` it is `ϕ`; DM then chooses `d*(σ)`;
the information cost is `η(π; k) = π² / (2k)`. -/
def imPayoff (P : Params) (o : Org) (α k π : ℝ) : ℝ :=
  π * ((1 / 2) * netBen P o α (dStar P o α .one) .one +
      (1 / 2) * netBen P o α (dStar P o α .two) .two) +
    (1 - π) * netBen P o α (dStar P o α .phi) .phi - π ^ 2 / (2 * k)

/-- `π` is an optimal information-gathering effort of IM: it maximizes `imPayoff` over `[0, 1]`. -/
def IsOptimalEffort (P : Params) (o : Org) (α k π : ℝ) : Prop :=
  π ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ π' ∈ Set.Icc (0 : ℝ) 1, imPayoff P o α k π' ≤ imPayoff P o α k π

/-- Success probability of the organization given IM's effort `π` (§3.4, p. 23 and
Appendix A3, p. 45): the principal's expected profit `V`. -/
def successProb (P : Params) (o : Org) (α π : ℝ) : ℝ :=
  π * ((1 / 2) * succ P o α (dStar P o α .one) .one +
      (1 / 2) * succ P o α (dStar P o α .two) .two) +
    (1 - π) * succ P o α (dStar P o α .phi) .phi

/-- `K(x) = ∫₀ˣ F(c) dc` (§3.3, p. 17). -/
def Kint (P : Params) (x : ℝ) : ℝ :=
  ∫ c in (0 : ℝ)..x, P.F c

/-- Marginal benefit of information, homogeneous organization, non-reactive DM (p. 18):
`½ K(α b_H) + ½ K((1 - α) b_H) - K(b_H / 2)`. -/
def mbNhom (P : Params) (α : ℝ) : ℝ :=
  (1 / 2) * Kint P (α * P.bH) + (1 / 2) * Kint P ((1 - α) * P.bH) - Kint P (P.bH / 2)

/-- Marginal benefit of information, homogeneous organization, reactive DM (p. 18):
`½ K(α b_H) + ½ K(α b_L) - K(b_H / 2)`. -/
def mbRhom (P : Params) (α : ℝ) : ℝ :=
  (1 / 2) * Kint P (α * P.bH) + (1 / 2) * Kint P (α * P.bL) - Kint P (P.bH / 2)

/-- Marginal benefit of information, heterogeneous organization, non-reactive DM (p. 20):
`½ K(α b_L) + ½ K((1 - α) b_L) - K(b_L / 2)`. -/
def mbNhet (P : Params) (α : ℝ) : ℝ :=
  (1 / 2) * Kint P (α * P.bL) + (1 / 2) * Kint P ((1 - α) * P.bL) - Kint P (P.bL / 2)

/-- Marginal benefit of information, heterogeneous organization, reactive DM (p. 20):
`½ K(α b_L) + ½ K(α b_H) - K(b_L / 2)`. -/
def mbRhet (P : Params) (α : ℝ) : ℝ :=
  (1 / 2) * Kint P (α * P.bL) + (1 / 2) * Kint P (α * P.bH) - Kint P (P.bL / 2)

end

end OrgDiversity.Optimal


