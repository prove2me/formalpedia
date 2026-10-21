-- Prove2me | Definitions.Def_EVSubsidy_Marginal_Model
-- name    : EVSubsidy_Marginal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:52.286287+00:00
-- url     : https://prove2.me/theorems/0a16bb05-31c0-419d-9eb1-1232f919a273
-- title:
--   §3, pp. 7–13 — two-location EV and charging market
-- statement:
--   The base model has two locations A and B. A fraction $\eta$ of potential drivers lives at A, while $1-\eta$ lives at B. Driver benefit $z$ has the exponential distribution with parameter $a$. The common regulated charging fee is $f$, and $s_i/(1-\rho_i)+c_i\tau$ is the search and waiting cost at location $i$ when expected utilization is $\rho_i$.
--
--   For a subsidy policy $\omega=(\alpha_A,\alpha_B,\beta,\gamma)$, the model defines logit charging choice probabilities, the vehicle purchase thresholds, charging arrival rates, provider profit, and the rational expectations equilibrium. Gross social surplus is the external benefit plus a driver surplus integral plus provider surplus:
--
--   $$
--   GSS(\omega,\xi,m)=\theta T(\lambda_A+\lambda_B)+
--   \sum_{i=A,B}\eta_i\int_{z_i^*}^{\infty}(z-z_i^*)\,dH(z)+
--   \left[\sum_i\alpha_i nm_i+\beta\sum_i\lambda_i+f\sum_i\lambda_i-\sum_i k_i nm_i\right].
--   $$
--
--   The definitions supply the common mathematical setting for the equilibrium theorem and both marginal subsidy comparisons.
--
--   **Formalization Note** The arrival equation is multiplied by $nm_i$ to exclude a false zero pile equilibrium from total real division. The exponential CDF equals zero below zero. The subsidy value is $S=\sum_i\alpha_i nm_i+(\beta+T\gamma/\mu)\sum_i\lambda_i$, as read from the proof's subsidy derivatives. The standing assumptions include $\theta\geq0$ and the positive pile regime is explicit.
--
--   A pile subsidy pair is balanced when, among feasible nonnegative pairs with the same equilibrium subsidy value, no pair yields higher gross social surplus.
-- source:
--   Zhang & Dou, Coping with Spatial Mismatch: Subsidy Design for Electric Vehicle and Charging Markets, SSRN 3336398 (authors' version), pp. 7–15 (PDF 7–15), §3, Definition 1, equations (1)–(13)

import Mathlib

namespace EVSubsidy.Marginal
noncomputable section

inductive Loc | A | B
  deriving DecidableEq

structure Params where
  η : ℝ
  a : ℝ
  T : ℝ
  τ : ℝ
  f : ℝ
  p : ℝ
  θ : ℝ
  μ : ℝ
  δ : ℝ
  n : ℝ
  s : Loc → ℝ
  c : Loc → ℝ
  k : Loc → ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.η ∧ P.η < 1 ∧ 0 < P.a ∧ 0 < P.T ∧ 0 < P.τ ∧ 0 < P.f ∧
  0 ≤ P.θ ∧ 0 < P.μ ∧ P.μ ≤ 1 ∧ 0 ≤ P.δ ∧ 0 < P.n ∧
  0 < P.s .A ∧ P.s .A ≤ P.s .B ∧ 0 ≤ P.c .A ∧ P.c .A ≤ P.c .B ∧
  0 < P.k .B ∧ P.k .B < P.k .A

structure Policy where
  α : Loc → ℝ
  β : ℝ
  γ : ℝ

def F (P : Params) (ρ : Loc → ℝ) (i : Loc) : ℝ :=
  P.f + P.c i * P.τ + P.s i / (1 - ρ i)

def ue (P : Params) (ρ : Loc → ℝ) : Loc → ℝ
  | .A => F P ρ .A
  | .B => -Real.log (Real.exp (-F P ρ .A) + Real.exp (-F P ρ .B))

def phi (P : Params) (ρ : Loc → ℝ) (i : Loc) : ℝ :=
  Real.exp (-F P ρ i) / (Real.exp (-F P ρ .A) + Real.exp (-F P ρ .B))

def zStar (P : Params) (ω : Policy) (ρ : Loc → ℝ) (i : Loc) : ℝ :=
  P.p - ω.γ + ue P ρ i / P.T

def H (P : Params) (z : ℝ) : ℝ :=
  if z ≤ 0 then 0 else 1 - Real.exp (-(P.a * z))

def lam (P : Params) (ω : Policy) (ρ : Loc → ℝ) : Loc → ℝ
  | .A => (1 - P.η) / P.T * phi P ρ .A * (1 - H P (zStar P ω ρ .B)) +
      P.η / P.T * (1 - H P (zStar P ω ρ .A))
  | .B => (1 - P.η) / P.T * phi P ρ .B * (1 - H P (zStar P ω ρ .B))

def spProfit (P : Params) (ω : Policy) (ρ m : Loc → ℝ) : ℝ :=
  ((ω.β + P.f) * ρ .A * m .A / P.τ - (P.k .A - ω.α .A) * m .A) +
  ((ω.β + P.f) * ρ .B * m .B / P.τ - (P.k .B - ω.α .B) * m .B)

def IsRE (P : Params) (ω : Policy) (ξ m : Loc → ℝ) : Prop :=
  (∀ i, 0 ≤ ξ i ∧ ξ i < 1) ∧ (∀ i, 0 ≤ m i) ∧
  (∀ m' : Loc → ℝ, (∀ i, 0 ≤ m' i) → spProfit P ω ξ m' ≤ spProfit P ω ξ m) ∧
  (∀ i, ξ i * (P.n * m i) = P.τ * lam P ω ξ i)

def popShare (P : Params) : Loc → ℝ
  | .A => P.η
  | .B => 1 - P.η

def hDens (P : Params) (z : ℝ) : ℝ :=
  if 0 ≤ z then P.a * Real.exp (-(P.a * z)) else 0

def driverSurplus (P : Params) (ω : Policy) (ξ : Loc → ℝ) : ℝ :=
  popShare P .A * ∫ z in Set.Ioi (zStar P ω ξ .A),
      (z - zStar P ω ξ .A) * hDens P z +
  popShare P .B * ∫ z in Set.Ioi (zStar P ω ξ .B),
      (z - zStar P ω ξ .B) * hDens P z

def spSurplus (P : Params) (ω : Policy) (ξ m : Loc → ℝ) : ℝ :=
  (ω.α .A * m .A * P.n + ω.α .B * m .B * P.n) +
  ω.β * (lam P ω ξ .A + lam P ω ξ .B) +
  (P.f * lam P ω ξ .A + P.f * lam P ω ξ .B) -
  (P.k .A * m .A * P.n + P.k .B * m .B * P.n)

def GSS (P : Params) (ω : Policy) (ξ m : Loc → ℝ) : ℝ :=
  P.θ * P.T * (lam P ω ξ .A + lam P ω ξ .B) +
  driverSurplus P ω ξ + spSurplus P ω ξ m

def subsidy (P : Params) (ω : Policy) (ξ m : Loc → ℝ) : ℝ :=
  (ω.α .A * P.n * m .A + ω.α .B * P.n * m .B) +
  (ω.β + P.T * ω.γ / P.μ) * (lam P ω ξ .A + lam P ω ξ .B)

def UG (P : Params) (ω : Policy) (ξ m : Loc → ℝ) : ℝ :=
  GSS P ω ξ m - (1 + P.δ) * subsidy P ω ξ m

def Delta (P : Params) (ξ : Loc → ℝ) : ℝ :=
  (P.c .B - P.c .A) * P.τ +
  (P.s .B / (1 - ξ .B) - P.s .A / (1 - ξ .A))

def Regime (P : Params) (ω : Policy) : Prop :=
  ∀ i, ω.α i < P.k i ∧ (P.k i - ω.α i) * P.τ < ω.β + P.f

def xiStar (P : Params) (ω : Policy) (i : Loc) : ℝ :=
  (P.k i - ω.α i) * P.τ / (ω.β + P.f)

def IsEqSelection (P : Params) (E : Policy → (Loc → ℝ) × (Loc → ℝ)) : Prop :=
  ∀ ω, Regime P ω → IsRE P ω (E ω).1 (E ω).2

def GSSat (P : Params) (E : Policy → (Loc → ℝ) × (Loc → ℝ)) (ω : Policy) : ℝ :=
  GSS P ω (E ω).1 (E ω).2

def mixBG (β γ : ℝ) : Policy := ⟨fun _ => 0, β, γ⟩

def mixAG (αA αB γ : ℝ) : Policy :=
  ⟨fun i => match i with | .A => αA | .B => αB, 0, γ⟩

/-- At a fixed subsidy value, no other feasible pile-subsidy pair improves GSS. -/
def Balanced (P : Params) (E : Policy → (Loc → ℝ) × (Loc → ℝ))
    (αA αB γ : ℝ) : Prop :=
  ∀ αA' αB' : ℝ,
    0 ≤ αA' → 0 ≤ αB' → Regime P (mixAG αA' αB' γ) →
    subsidy P (mixAG αA' αB' γ)
      (E (mixAG αA' αB' γ)).1 (E (mixAG αA' αB' γ)).2 =
      subsidy P (mixAG αA αB γ)
        (E (mixAG αA αB γ)).1 (E (mixAG αA αB γ)).2 →
    GSSat P E (mixAG αA' αB' γ) ≤ GSSat P E (mixAG αA αB γ)

def BetaMarginallyBeatsGamma (P : Params)
    (E : Policy → (Loc → ℝ) × (Loc → ℝ)) (β γ : ℝ) : Prop :=
  ∃ dβ dγ : ℝ,
    HasDerivAt (fun b => GSSat P E (mixBG b γ)) dβ β ∧
    HasDerivAt (fun g => GSSat P E (mixBG β g)) dγ γ ∧
    P.μ / P.T * dγ ≤ dβ

def alphaDir (P : Params) (αA αB : ℝ) (i : Loc) : ℝ :=
  match i with
  | .A => (P.k .A - αA) ^ 2 / (P.f * P.k .A)
  | .B => (P.k .B - αB) ^ 2 / (P.f * P.k .B)

def GammaMarginallyBeatsAlphaFlex (P : Params)
    (E : Policy → (Loc → ℝ) × (Loc → ℝ)) (αA αB γ : ℝ) : Prop :=
  ∃ dα dγ : ℝ,
    HasDerivAt
      (fun t => GSSat P E
        (mixAG (αA + t * alphaDir P αA αB .A)
          (αB + t * alphaDir P αA αB .B) γ)) dα 0 ∧
    HasDerivAt (fun g => GSSat P E (mixAG αA αB g)) dγ γ ∧
    dα ≤ P.μ / P.T * dγ

def GSSClosed (P : Params) (ω : Policy) : ℝ :=
  (P.θ * P.T + P.T / P.a) *
    (lam P ω (xiStar P ω) .A + lam P ω (xiStar P ω) .B)

end
end EVSubsidy.Marginal


