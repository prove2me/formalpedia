-- Prove2me | Definitions.Def_YieldPostpone_Payment_Setting
-- name    : YieldPostpone_Payment_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:45.727682+00:00
-- url     : https://prove2.me/theorems/b0df80d5-0029-4da5-8b41-7c25bb433029
-- title:
--   Two-point yield and four supply-chain games
-- statement:
--   A supplier produces a planned quantity $Q$ at unit cost $c$, and a retailer orders $q$. The realized yield factor $Y$ is $1$ with probability $\theta$ and $\alpha$ with probability $1-\theta$, where $0<\alpha,\theta<1$. Demand at retail price $p$ is $a-bp$, with $a,b>0$. The quantity delivered is $\widehat q=\min\{YQ,q\}$.
--
--   $$\mu=\mathbb E Y=\alpha(1-\theta)+\theta,\qquad 0<c<a\mu/b.$$
--
--   Under pay-by-order the transfer is $wq$ and the supplier produces $Q=q$; under pay-by-delivery the transfer is $w\widehat q$ and the supplier chooses nonnegative $Q$ to maximize expected transfer less $cQ$. The retailer chooses nonnegative $q$ and either an advance price or a price after observing delivery. These choices give scenarios OA, OR, DA, and DR. A profile specifies choices after every observed history; subgame-perfect equilibrium requires optimal decisions in every subgame. Its outcome is the retailer profit, supplier profit, and expected consumer surplus, in that order. Consumer surplus integrates inverse demand less market price over the quantity sold.
--
--   The file also defines the paper's cost thresholds $c^{OA}_1,c^{OA}_2,c^{OR},c^{DA},c^{DR}_1,c^{DR}_2,\widetilde C,\overline C$ and yield-region thresholds. These shared definitions give the mission's statements a single model.
--
--   **Formalization Note** Wholesale and retail prices obey the strict bounds in Appendix B (3). For a pay-by-delivery production tie, $Q=q$ is selected whenever it maximizes profit. The responsive price is used to calculate consumer surplus in OR and DR, correcting the swapped scenario labels in (2). The larger quadratic root represents $c^{OA}_2$; the largest real cubic root represents $\theta_2$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), §3, pp. 7–10, (1)–(2), Table 1; App. B, PDF pp. 33–37 (appendix pp. 1–5), (3)–(6); App. C, PDF p. 38 (appendix p. 6), (8)

import Mathlib

noncomputable section

namespace YieldPostpone.Payment

structure Params where
  a : ℝ
  b : ℝ
  α : ℝ
  θ : ℝ

def Params.μ (P : Params) : ℝ := P.α * (1 - P.θ) + P.θ

def Params.Valid (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.b ∧ 0 < P.α ∧ P.α < 1 ∧ 0 < P.θ ∧ P.θ < 1

def costAdm (P : Params) (c : ℝ) : Prop := 0 < c ∧ c < P.a * P.μ / P.b

def E (P : Params) (f : ℝ → ℝ) : ℝ :=
  P.θ * f 1 + (1 - P.θ) * f P.α

def demand (P : Params) (p : ℝ) : ℝ := P.a - P.b * p

inductive Scenario | OA | OR | DA | DR
  deriving DecidableEq

def Scenario.byDelivery : Scenario → Bool
  | .OA | .OR => false
  | .DA | .DR => true

def Scenario.responsive : Scenario → Bool
  | .OA | .DA => false
  | .OR | .DR => true

def delivered (y Q q : ℝ) : ℝ := min (y * Q) q

def transfer (P : Params) (k : Scenario) (w Q q y : ℝ) : ℝ :=
  if k.byDelivery then w * delivered y Q q else w * q

def supplierProfit (P : Params) (c : ℝ) (k : Scenario) (w Q q : ℝ) : ℝ :=
  E P (fun y => transfer P k w Q q y) - c * Q

def wAdm (P : Params) (c : ℝ) (k : Scenario) (w : ℝ) : Prop :=
  (if k.byDelivery then c / P.μ < w else c < w) ∧ w < P.a / P.b

def pAdm (P : Params) (p : ℝ) : Prop := 0 < p ∧ p < P.a / P.b

def salesRev (P : Params) (p x : ℝ) : ℝ := p * min (demand P p) x

structure Profile where
  w : ℝ
  Q : ℝ → ℝ → ℝ
  q : ℝ → ℝ
  p : ℝ → ℝ
  pr : ℝ → ℝ → ℝ → ℝ

def retailerProfit (P : Params) (k : Scenario) (σ : Profile)
    (w q' p' : ℝ) : ℝ :=
  E P (fun y =>
    let x := delivered y (σ.Q w q') q'
    (if k.responsive then salesRev P (σ.pr w q' x) x else salesRev P p' x) -
      transfer P k w (σ.Q w q') q' y)

def supplierValue (P : Params) (c : ℝ) (k : Scenario)
    (σ : Profile) (w : ℝ) : ℝ :=
  supplierProfit P c k w (σ.Q w (σ.q w)) (σ.q w)

def IsSPE (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : Prop :=
  (if k.byDelivery then
      ∀ w q, wAdm P c k w → 0 ≤ q →
        0 ≤ σ.Q w q ∧
        (∀ Q', 0 ≤ Q' → supplierProfit P c k w Q' q ≤
          supplierProfit P c k w (σ.Q w q) q) ∧
        ((∀ Q', 0 ≤ Q' → supplierProfit P c k w Q' q ≤
          supplierProfit P c k w q q) → σ.Q w q = q)
    else ∀ w q, σ.Q w q = q) ∧
  (if k.responsive then
      ∀ w q x, 0 ≤ x →
        pAdm P (σ.pr w q x) ∧
        ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x
    else True) ∧
  (∀ w, wAdm P c k w →
    0 ≤ σ.q w ∧
    (if k.responsive then True else pAdm P (σ.p w)) ∧
    ∀ q' p', 0 ≤ q' → (if k.responsive then True else pAdm P p') →
      retailerProfit P k σ w q' p' ≤
        retailerProfit P k σ w (σ.q w) (σ.p w)) ∧
  wAdm P c k σ.w ∧
  ∀ w', wAdm P c k w' → supplierValue P c k σ w' ≤ supplierValue P c k σ σ.w

def surplus (P : Params) (p X : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(min (demand P p) X), ((P.a - t) / P.b - p)

def piR (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  retailerProfit P k σ σ.w (σ.q σ.w) (σ.p σ.w)

def piS (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  supplierValue P c k σ σ.w

def CS (P : Params) (_c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  E P (fun y =>
    let w := σ.w
    let q := σ.q w
    let x := delivered y (σ.Q w q) q
    surplus P (if k.responsive then σ.pr w q x else σ.p w) x)

def outcome (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : ℝ × ℝ × ℝ :=
  (piR P c k σ, piS P c k σ, CS P c k σ)

def cOA1 (P : Params) : ℝ :=
  P.a * P.α * (P.μ - P.α * P.θ - 2 * P.θ * Real.sqrt P.μ) /
    (P.b * (P.α + P.θ))

def what (P : Params) : ℝ :=
  P.a * P.α * (P.μ - P.θ * Real.sqrt P.μ) / (P.b * (P.α + P.θ))

def cOA2 (P : Params) : ℝ :=
  let A := P.α ^ 2 * P.b ^ 2
  let B := -(2 * P.α ^ 2 * P.a * P.μ * P.b) +
    4 * P.b * P.μ * (P.a * P.α - P.b * what P)
  let C := P.α ^ 2 * (P.a * P.μ) ^ 2 -
    4 * P.b * P.μ * (P.a * P.α - P.b * what P) * what P
  (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)

def cOR (P : Params) : ℝ :=
  (P.a / P.b) * P.α * (1 - P.θ) *
    ((1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)))

def cDA (P : Params) : ℝ :=
  P.a * P.α * (P.μ - P.θ * Real.sqrt P.μ) / (P.b * (P.α + P.θ))

def cDR1 (P : Params) : ℝ :=
  P.a * P.α * (1 - P.θ) *
    (P.μ ^ 2 + P.θ - 2 * P.θ *
      Real.sqrt (P.α * P.μ * (1 - P.α) * (1 - P.θ))) /
    (P.b * (P.α ^ 2 * (1 - P.θ) ^ 3 +
      4 * P.α * P.θ * (1 - P.θ) + P.θ * (1 + P.θ) ^ 2))

def cDR2 (P : Params) : ℝ :=
  P.a * P.α * P.μ * (1 - P.θ) / (P.b * (P.μ + P.θ))

def Ctil (P : Params) : ℝ :=
  P.a * P.α * (1 - Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ)) /
    (P.b * (1 + P.α))

def phiA (P : Params) : ℝ :=
  P.α * (1 - P.θ) *
    (P.α - P.α ^ 2 * (1 - P.θ) + 2 * P.θ * (1 - P.α)) + P.θ ^ 2

def phiB (P : Params) : ℝ :=
  phiA P + P.α * P.θ * (P.α + P.μ * (1 - P.α))

def phiC (P : Params) : ℝ :=
  P.α * (1 - P.θ) * (2 - P.α) + P.θ

def Cbar (P : Params) : ℝ :=
  (P.a * P.α / P.b) *
    ((phiA P - P.θ * P.μ * Real.sqrt (phiC P)) / phiB P)

def Theta (α : ℝ) : ℝ :=
  α * (3 * (1 - α - 4 * α ^ 2) +
    4 * Real.sqrt (α * (3 + 5 * α + α ^ 2))) /
    ((1 - α) * (3 + 4 * α) ^ 2)

def theta1 (α : ℝ) : ℝ :=
  (1 - 4 * α + Real.sqrt (1 + 8 * α)) / (8 * (1 - α))

def thetaCubic (α x : ℝ) : ℝ :=
  -α ^ 3 + α ^ 2 * (5 + α) * x +
    (16 - 19 * α - 6 * α ^ 2) * x ^ 2 -
    25 * (1 - α) * x ^ 3

def theta2 (α : ℝ) : ℝ := sSup {x : ℝ | thetaCubic α x = 0}

def H1 (α θ : ℝ) : Prop := 0 < θ ∧ θ < theta1 α
def H2 (α θ : ℝ) : Prop := theta1 α < θ ∧ θ < theta2 α
def H3 (α θ : ℝ) : Prop := theta2 α < θ ∧ θ < 1

end YieldPostpone.Payment


