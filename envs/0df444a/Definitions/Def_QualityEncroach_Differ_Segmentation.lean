-- Prove2me | Definitions.Def_QualityEncroach_Differ_Segmentation
-- name    : QualityEncroach_Differ_Segmentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:47.480485+00:00
-- url     : https://prove2.me/theorems/2cddac0d-2132-47ff-b15e-aa8436f2ecb3
-- title:
--   §6.1, p. 19 — segmentation through the retailer: two qualities u₁ > u₂ sold through the retailer only
-- statement:
--   In §6.1 there is no direct channel, and the manufacturer sells two products of qualities $u_1>u_2>0$ through the retailer at wholesale prices $w_1,w_2$. The retailer orders $q_1,q_2\ge 0$ and earns
--
--   $$
--   \Pi^{N2}_R = \bigl(u_2(1-q_2-q_1)-w_2\bigr)q_2 + \bigl(u_1-u_1q_1-u_2q_2-w_1\bigr)q_1 ,
--   $$
--
--   while the manufacturer earns
--
--   $$
--   \Pi^{N2}_M = (w_1-ku_1^2)\,q_1 + (w_2-ku_2^2)\,q_2 .
--   $$
--
--   A strategy profile $\tau$ consists of the manufacturer's choice $(w_1,w_2,u_1,u_2)$ and the retailer's rule $(w_1,w_2,u_1,u_2)\mapsto(q_1,q_2)$. It is a **subgame-perfect equilibrium** when (1) at every $w_1,w_2\in\mathbb R$ and $u_1>u_2>0$ the retailer's rule picks $q_1,q_2\ge 0$ maximizing his profit over $q_1,q_2\ge0$, and (2) the manufacturer's choice satisfies $u_1>u_2>0$ and maximizes her profit, evaluated at the retailer's rule, over all such choices.
--
--   This is the second benchmark of the paper, used in Proposition 5.
--
--   **Formalization Note.** The page labels the products so that $u_1>u_2$ "without loss of generality"; the manufacturer's choice set is accordingly $u_1>u_2>0$. The retailer's quantities are restricted to be nonnegative; the page's formulas for $q_1,q_2$ are the interior best replies.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 19, §6.1

import Mathlib

namespace QualityEncroach.Differ

/-!
# Segmentation through the retailer (§6.1, p. 19)

There is no direct channel. The manufacturer offers two products of qualities `u₁ > u₂ > 0` at
wholesale prices `w₁`, `w₂`; the retailer orders `q₁, q₂ ≥ 0` and sells them at the
market-clearing prices `u₁ − u₁ q₁ − u₂ q₂` and `u₂ (1 − q₂ − q₁)`.
-/

/-- An outcome of the two-product game without a direct channel. -/
structure SegOutcome where
  w1 : ℝ
  w2 : ℝ
  u1 : ℝ
  u2 : ℝ
  q1 : ℝ
  q2 : ℝ

/-- The retailer's profit `(u₂ (1 − q₂ − q₁) − w₂) q₂ + (u₁ − u₁ q₁ − u₂ q₂ − w₁) q₁` (p. 19). -/
def segRetailerPayoff (o : SegOutcome) : ℝ :=
  (o.u2 * (1 - o.q2 - o.q1) - o.w2) * o.q2 + (o.u1 - o.u1 * o.q1 - o.u2 * o.q2 - o.w1) * o.q1

/-- The manufacturer's profit `(w₁ − k u₁²) q₁ + (w₂ − k u₂²) q₂` (p. 19). -/
def segMfrPayoff (k : ℝ) (o : SegOutcome) : ℝ :=
  (o.w1 - k * o.u1 ^ 2) * o.q1 + (o.w2 - k * o.u2 ^ 2) * o.q2

/-- A strategy profile: the manufacturer's `(w₁, w₂, u₁, u₂)` and the retailer's rule
`order w₁ w₂ u₁ u₂ = (q₁, q₂)`. -/
structure SegProfile where
  w1 : ℝ
  w2 : ℝ
  u1 : ℝ
  u2 : ℝ
  order : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ

/-- The outcome after the manufacturer chose `(w₁, w₂, u₁, u₂)` and the retailer follows `τ`. -/
def SegProfile.outcomeAt (τ : SegProfile) (w1 w2 u1 u2 : ℝ) : SegOutcome :=
  ⟨w1, w2, u1, u2, (τ.order w1 w2 u1 u2).1, (τ.order w1 w2 u1 u2).2⟩

/-- The equilibrium path of `τ`. -/
def SegProfile.path (τ : SegProfile) : SegOutcome :=
  τ.outcomeAt τ.w1 τ.w2 τ.u1 τ.u2

/-- `τ` is a subgame-perfect equilibrium of the §6.1 game (`w₁, w₂ ∈ ℝ`, `u₁ > u₂ > 0`,
`q₁, q₂ ≥ 0`). -/
def IsSegSPE (k : ℝ) (τ : SegProfile) : Prop :=
  (∀ w1 w2 u1 u2 : ℝ, 0 < u2 → u2 < u1 →
      0 ≤ (τ.order w1 w2 u1 u2).1 ∧ 0 ≤ (τ.order w1 w2 u1 u2).2 ∧
      ∀ q1 q2 : ℝ, 0 ≤ q1 → 0 ≤ q2 →
        segRetailerPayoff ⟨w1, w2, u1, u2, q1, q2⟩ ≤ segRetailerPayoff (τ.outcomeAt w1 w2 u1 u2)) ∧
  (0 < τ.u2 ∧ τ.u2 < τ.u1 ∧
      ∀ w1 w2 u1 u2 : ℝ, 0 < u2 → u2 < u1 →
        segMfrPayoff k (τ.outcomeAt w1 w2 u1 u2) ≤ segMfrPayoff k τ.path)

end QualityEncroach.Differ


