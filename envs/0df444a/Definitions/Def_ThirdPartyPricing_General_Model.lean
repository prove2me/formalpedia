-- Prove2me | Definitions.Def_ThirdPartyPricing_General_Model
-- name    : ThirdPartyPricing_General_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:22.591425+00:00
-- url     : https://prove2.me/theorems/b4d05751-ffb2-416a-86d7-8f168d2a8e1a
-- title:
--   §3–§4, pp. 7–10 — symmetric differentiated duopoly with demand shifter a, standing assumptions (2)–(5), third-party algorithm design problem and equilibrium (11)
-- statement:
--   The model of §3–§4 of Harrington's working paper: a symmetric differentiated-products duopoly whose demand depends on a high-frequency demand state $a$, and a third party that sells a pricing algorithm conditioning on $a$.
--
--   **Primitives.** A reusable symmetric differentiated duopoly specifies a common constant marginal cost $c\ge 0$, a price cap $p^{\max}>c$, firm 1's demand $D_1(p_1,p_2,a)$, an ambient interval $[a_0,a_1]$ of demand states, and the joint-profit-maximizing price $p^M(a)$. Firm 2's demand is given by symmetry (1), $D_2(p_1,p_2,a)=D_1(p_2,p_1,a)$. Profits are
--   $$\pi_1(p_1,p_2,a)=(p_1-c)D_1(p_1,p_2,a),\qquad \pi_2(p_1,p_2,a)=(p_2-c)D_1(p_2,p_1,a).$$
--
--   **Standing assumptions** (pp. 7–8), for prices $p_1,p_2\in[c,p^{\max}]$ and states $a\in[a_0,a_1]$:
--   1. $D_1$ is twice continuously differentiable in $(p_1,p_2,a)$;
--   2. (2): $\partial D_1/\partial p_2>0$, $\partial D_1/\partial a>0$, $\partial D_1/\partial p_1<0$;
--   3. (3): $\partial^2 D_1/\partial p_1\partial p_2\ge 0$ and $\partial^2 D_1/\partial p_1\partial a\ge 0$;
--   4. (5): $\pi_1(p_1,p_2,a)$ is strictly concave in $p_1$ on $[c,p^{\max}]$, with $\partial^2\pi_1/\partial p_1^2<0$ at every price in the box;
--   5. $(p-c)D_1(p,p,a)$ is strictly concave in $p$ on $[c,p^{\max}]$ and maximized there at $p^M(a)\in(c,p^{\max})$;
--   6. $p^M$ is non-decreasing in $a$, and $D_1(p^M(a),c,a)>0$;
--   7. $\partial\pi_1(p^{\max},p_2,a)/\partial p_1<0$ (no corner solution at the price cap).
--
--   **Beliefs.** The demand state is distributed on a support $A=[\underline a,\bar a]\subseteq[a_0,a_1]$, $\underline a<\bar a$, with a continuous density $F'=f\ge 0$ integrating to $1$.
--
--   **The design problem and equilibrium** (11). With $\beta$ the probability that both firms adopt the algorithm (conditional on one adopting), the third party's pointwise objective when the non-adopting rival charges $\tilde p$ is
--   $$(1-\beta)\pi_1(p,\tilde p,a)+\beta\pi_1(p,p,a),$$
--   and the non-adopter's expected profit from price $p$ against an algorithm $\phi$ is $\int_{\underline a}^{\bar a}\pi_2(\phi(a),p,a)F'(a)\,da$. A pair $(\hat\phi,\hat p)$ is an equilibrium when $\hat p\in[c,p^{\max}]$, for every $a\in A$ the price $\hat\phi(a)\in[c,p^{\max}]$ maximizes the third party's objective against $\hat p$ over $[c,p^{\max}]$, and $\hat p$ maximizes the non-adopter's expected profit against $\hat\phi$ over $[c,p^{\max}]$. A **minimal** (resp. **maximal**) equilibrium is one whose $\hat p$ is the least (resp. greatest) among all equilibria.
--
--   This file is the shared model on which every statement of the mission (Theorems 1–2, footnote 13, Lemmas 3–4 and the steps of the proof of Theorem 1) is posed.
--
--   **Formalization Note** Partial derivatives are derivatives of one-variable sections, and $D_1$ is assumed $C^2$ on all of $\mathbb R^3$. The paper states (2)–(3) "when $D_1>0$" and assumes (8) ($D_1(p,p,a)=0$ for $p>p^{\max}$), which together would make $D_1$ vanish on part of the price box; here (2)–(3) are imposed on the whole box and (8) is replaced by its role (prices restricted to $[c,p^{\max}]$ without loss), stated as interiority: $c<p^M(a)<p^{\max}$ and $\partial\pi_1/\partial p_1<0$ at $p^{\max}$. The paper's $p^M(a)$ is the unrestricted joint-profit maximizer; here it is a primitive constrained to maximize joint profit on $[c,p^{\max}]$. The ambient range $[a_0,a_1]$ lets the support shrink while the assumptions stay fixed. The equilibrium uses the pointwise form (11), which the paper states is equivalent to (10); $\mu$, $\sigma^2$, $\psi$ and $p^N$ are not needed and not defined.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), pp. 7–10, §3.1, §3.2, §4, (1)–(11)

import Mathlib

namespace ThirdPartyPricing.General

/-- A symmetric differentiated-products duopoly: common marginal cost, price cap, and firm 1's
demand. Firm 2's demand is obtained by interchanging the two prices. -/
structure SymmetricDuopoly where
  c : ℝ
  pmax : ℝ
  D : ℝ → ℝ → ℝ → ℝ

/-- The paper's state-dependent primitives extend the general symmetric duopoly with an ambient
demand-state range and the joint-profit-maximizing price `pM a` = pᴹ(a). -/
structure Primitives extends SymmetricDuopoly where
  a₀ : ℝ
  a₁ : ℝ
  pM : ℝ → ℝ

namespace Primitives

variable (P : Primitives)

/-- The price interval `[c, pmax]`. -/
def prices : Set ℝ := Set.Icc P.c P.pmax

/-- The ambient range of demand states `[a₀, a₁]`. -/
def states : Set ℝ := Set.Icc P.a₀ P.a₁

/-- Firm 1's profit (4): π1(p1, p2, a) = (p1 − c) D1(p1, p2, a). -/
def π₁ (p1 p2 a : ℝ) : ℝ := (p1 - P.c) * P.D p1 p2 a

/-- Firm 2's profit, with firm 2's demand D2(p1, p2, a) = D1(p2, p1, a) given by symmetry (1). -/
def π₂ (p1 p2 a : ℝ) : ℝ := (p2 - P.c) * P.D p2 p1 a

/-- The third party's pointwise objective in (11) and (18): with adoption probability `β` and the
non-adopter's price `pt`, the value of charging `p` in demand state `a`. -/
def tpObj (β pt a p : ℝ) : ℝ := (1 - β) * P.π₁ p pt a + β * P.π₁ p p a

/-- The non-adopter's expected profit (11), (19) from charging `p` against the algorithm `φ`,
when the demand state has density `f` on `[alo, ahi]`. -/
noncomputable def naProfit (alo ahi : ℝ) (f φ : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ a in alo..ahi, P.π₂ (φ a) p a * f a

/-- The standing assumptions of §3.1 (pp. 7–8). Partial derivatives are `deriv` of sections.
The sign conditions (2)–(3) are imposed on the whole box `[c, pmax]² × [a₀, a₁]`, and (8) is
replaced by its role (prices restricted to `[c, pmax]` without loss): the own-price derivative of
π1 is negative at `pmax`, and `pM a` is interior. -/
structure Standing : Prop where
  c_nonneg : 0 ≤ P.c
  c_lt_pmax : P.c < P.pmax
  a₀_lt_a₁ : P.a₀ < P.a₁
  smooth : ContDiff ℝ 2 (fun x : ℝ × ℝ × ℝ => P.D x.1 x.2.1 x.2.2)
  dD_p2 : ∀ p1 ∈ P.prices, ∀ p2 ∈ P.prices, ∀ a ∈ P.states,
    0 < deriv (fun y => P.D p1 y a) p2
  dD_a : ∀ p1 ∈ P.prices, ∀ p2 ∈ P.prices, ∀ a ∈ P.states,
    0 < deriv (fun z => P.D p1 p2 z) a
  dD_p1 : ∀ p1 ∈ P.prices, ∀ p2 ∈ P.prices, ∀ a ∈ P.states,
    deriv (fun x => P.D x p2 a) p1 < 0
  d2D_p1p2 : ∀ p1 ∈ P.prices, ∀ p2 ∈ P.prices, ∀ a ∈ P.states,
    0 ≤ deriv (fun y => deriv (fun x => P.D x y a) p1) p2
  d2D_p1a : ∀ p1 ∈ P.prices, ∀ p2 ∈ P.prices, ∀ a ∈ P.states,
    0 ≤ deriv (fun z => deriv (fun x => P.D x p2 z) p1) a
  concave_own : ∀ p2 ∈ P.prices, ∀ a ∈ P.states,
    StrictConcaveOn ℝ P.prices (fun p => P.π₁ p p2 a)
  own_second_neg : ∀ p1 ∈ P.prices, ∀ p2 ∈ P.prices, ∀ a ∈ P.states,
    deriv (fun x => deriv (fun y => P.π₁ y p2 a) x) p1 < 0
  concave_joint : ∀ a ∈ P.states,
    StrictConcaveOn ℝ P.prices (fun p => (p - P.c) * P.D p p a)
  pM_max : ∀ a ∈ P.states, IsMaxOn (fun p => (p - P.c) * P.D p p a) P.prices (P.pM a)
  pM_interior : ∀ a ∈ P.states, P.pM a ∈ Set.Ioo P.c P.pmax
  pM_mono : MonotoneOn P.pM P.states
  demand_pos : ∀ a ∈ P.states, 0 < P.D (P.pM a) P.c a
  interior_pmax : ∀ p2 ∈ P.prices, ∀ a ∈ P.states, deriv (fun p => P.π₁ p p2 a) P.pmax < 0

/-- `f` = F′ is a continuous probability density on `[alo, ahi]`. -/
def IsDensity (alo ahi : ℝ) (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Icc alo ahi) ∧ (∀ a ∈ Set.Icc alo ahi, 0 ≤ f a) ∧
    ∫ a in alo..ahi, f a = 1

/-- The support `A = [alo, ahi]` is a non-degenerate sub-interval of the ambient range. -/
def IsSupport (alo ahi : ℝ) : Prop := P.a₀ ≤ alo ∧ alo < ahi ∧ ahi ≤ P.a₁

/-- Equilibrium (11), p. 10: `φ a` maximizes the third party's objective against `p` in every
demand state `a ∈ [alo, ahi]`, and `p` maximizes the non-adopter's expected profit against `φ`. -/
def IsEquilibrium (alo ahi : ℝ) (f : ℝ → ℝ) (β : ℝ) (φ : ℝ → ℝ) (p : ℝ) : Prop :=
  p ∈ P.prices ∧
    (∀ a ∈ Set.Icc alo ahi, φ a ∈ P.prices ∧ IsMaxOn (P.tpObj β p a) P.prices (φ a)) ∧
    IsMaxOn (P.naProfit alo ahi f φ) P.prices p

/-- The minimal equilibrium: an equilibrium whose non-adopter price is least among all
equilibria. -/
def IsMinimalEquilibrium (alo ahi : ℝ) (f : ℝ → ℝ) (β : ℝ) (φ : ℝ → ℝ) (p : ℝ) : Prop :=
  P.IsEquilibrium alo ahi f β φ p ∧
    ∀ φ' p', P.IsEquilibrium alo ahi f β φ' p' → p ≤ p'

/-- The maximal equilibrium: an equilibrium whose non-adopter price is greatest among all
equilibria. -/
def IsMaximalEquilibrium (alo ahi : ℝ) (f : ℝ → ℝ) (β : ℝ) (φ : ℝ → ℝ) (p : ℝ) : Prop :=
  P.IsEquilibrium alo ahi f β φ p ∧
    ∀ φ' p', P.IsEquilibrium alo ahi f β φ' p' → p' ≤ p

end Primitives

end ThirdPartyPricing.General


