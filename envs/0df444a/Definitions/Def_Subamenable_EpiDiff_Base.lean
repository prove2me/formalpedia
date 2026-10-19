-- Prove2me | Definitions.Def_Subamenable_EpiDiff_Base
-- name    : Subamenable_EpiDiff_Base
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:40.214409+00:00
-- url     : https://prove2.me/theorems/3747fb42-161c-45be-81d9-74c2f6026b82
-- title:
--   §2 and §4 — tangent sets, subderivatives, twice epi-differentiability, and critical directions
-- statement:
--   This module defines the basic first and second order objects for an extended-real function $\varphi:\mathbb R^n\to(-\infty,+\infty]$. Its finite domain is $\operatorname{dom}\varphi=\{x:\varphi(x)<+\infty\}$. Tangent directions and second-order tangent vectors use positive null sequences, as in (2.1) and (2.17).
--
--   The subderivative and second subderivative are lower limits of the paper's difference quotients. In particular,
--
--   $$d^2\varphi(\bar x,\bar v)(w)=\liminf_{t\downarrow0,\,u\to w}\frac{\varphi(\bar x+tu)-\varphi(\bar x)-t\langle\bar v,u\rangle}{\tfrac12t^2}.$$
--
--   Proper twice epi-differentiability uses the equivalent sequential recovery criterion (2.16), together with the properness of $d^2\varphi$. The module also defines the proximal subdifferential, critical cone, and parabolic subderivative used later in the paper. These objects are reusable beyond this composite model.
--
--   **Formalization Note** Values live in `EReal`; hypotheses on uses of these definitions exclude $-\infty$ where the source codomain does. Every quotient subtracts a finite real base value, and the factor $2/t^2$ is evaluated only through a positive-time filter or sequence.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, pp. 4, 6–7, 15–16, 20, (2.1), (2.11), (2.15)–(2.17), (4.1), (4.4), (4.11)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions

open Filter Topology
open scoped InnerProductSpace

namespace Subamenable.EpiDiff

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Local notation for the published effective-domain definition. -/
abbrev dom {n : ℕ} (phi : E n → EReal) : Set (E n) :=
  DupacovaWets.Consistency.effDom phi

/-- Bouligand tangent directions, equation (2.1). -/
def tangentCone {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Omega : Set X) (xbar : X) : Set X :=
  {w | ∃ (t : ℕ → ℝ) (u : ℕ → X),
    (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto u atTop (𝓝 w) ∧ ∀ k, xbar + t k • u k ∈ Omega}

/-- The second-order tangent set, equation (2.17). -/
def secondTangentSet {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Omega : Set X) (xbar w : X) : Set X :=
  {z | ∃ (t : ℕ → ℝ) (u : ℕ → X),
    (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto u atTop (𝓝 z) ∧
    ∀ k, xbar + t k • w + (t k ^ 2 / 2) • u k ∈ Omega}

/-- The first subderivative, equation (2.11), at a finite base value. -/
noncomputable def subderiv {n : ℕ} (phi : E n → EReal) (xbar w : E n) : EReal :=
  Filter.liminf
    (fun p : ℝ × E n =>
      (phi (xbar + p.1 • p.2) - (((phi xbar).toReal : ℝ) : EReal)) *
        ((p.1⁻¹ : ℝ) : EReal))
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)

/-- The second-order difference quotient from (2.15). -/
noncomputable def delta2 {n : ℕ} (phi : E n → EReal) (xbar vbar w : E n)
    (t : ℝ) : EReal :=
  (phi (xbar + t • w) -
    (((phi xbar).toReal + t * ⟪vbar, w⟫_ℝ : ℝ) : EReal)) *
      ((2 / t ^ 2 : ℝ) : EReal)

/-- The second subderivative, equation (2.15). -/
noncomputable def secondSubderiv {n : ℕ} (phi : E n → EReal)
    (xbar vbar w : E n) : EReal :=
  Filter.liminf (fun p : ℝ × E n => delta2 phi xbar vbar p.2 p.1)
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)

/-- Proper twice epi-differentiability, through the equivalent sequential test (2.16). -/
def IsProperlyTwiceEpiDiff {n : ℕ} (phi : E n → EReal) (xbar vbar : E n) : Prop :=
  (∀ w : E n, ∀ t : ℕ → ℝ,
      (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
      ∃ u : ℕ → E n, Tendsto u atTop (𝓝 w) ∧
        Tendsto (fun k => delta2 phi xbar vbar (u k) (t k)) atTop
          (𝓝 (secondSubderiv phi xbar vbar w))) ∧
    (∀ w : E n, secondSubderiv phi xbar vbar w ≠ ⊥) ∧
    ∃ w : E n, secondSubderiv phi xbar vbar w ≠ ⊤

/-- The proximal subdifferential of (4.1). -/
def proxSubdiff {n : ℕ} (phi : E n → EReal) (xbar : E n) : Set (E n) :=
  {vbar | phi xbar ≠ ⊤ ∧ ∃ gamma r : ℝ, 0 < gamma ∧ 0 < r ∧
    ∀ x : E n, ‖x - xbar‖ ≤ gamma →
      (((phi xbar).toReal + ⟪vbar, x - xbar⟫_ℝ -
        r / 2 * ‖x - xbar‖ ^ 2 : ℝ) : EReal) ≤ phi x}

/-- The critical cone of (4.4). -/
def criticalCone {n : ℕ} (phi : E n → EReal) (xbar vbar : E n) : Set (E n) :=
  {w | subderiv phi xbar w = ((⟪vbar, w⟫_ℝ : ℝ) : EReal)}

/-- Parabolic subderivative of (4.11); the base and first subderivative are finite
in every use of this definition. -/
noncomputable def parabolicSubderiv {n : ℕ} (phi : E n → EReal)
    (xbar w z : E n) : EReal :=
  Filter.liminf
    (fun p : ℝ × E n =>
      (phi (xbar + p.1 • w + (p.1 ^ 2 / 2) • p.2) -
        (((phi xbar).toReal + p.1 * (subderiv phi xbar w).toReal : ℝ) : EReal)) *
          ((2 / p.1 ^ 2 : ℝ) : EReal))
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 z)

end Subamenable.EpiDiff


