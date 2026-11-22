-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_StatementE
-- name    : Formalism_ThetaSupremumBounds_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:56:25.167061+00:00
-- url     : https://prove2.me/theorems/4970abcb-5dbc-4a47-b272-124709b78702
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/StatementE.lean

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real
noncomputable section
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
def liftBlock {Pl ι W : Type} [Fintype Pl] [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (c : (Pl × ι → ℕ) → ℂ) (Rc : (Pl × ι → ℕ) →₀ W) (lam : Pl → ℂ) : W :=
  Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x, lam x.1 ^ e x) • A)
def liftOp {Cl Cl' A B : Type} [Fintype Cl] [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (γ : Cl → ℝ) (ε : Cl → Cl' → ℂ)
    (T : Cl → Cl' → A →L[ℂ] B) (fn : Cl → A) (L' : Cl') : B :=
  ∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)
def liftNormSq {Cl Cl' A B : Type} [Fintype Cl] [Fintype Cl'] [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ)
    (T : Cl → Cl' → A →L[ℂ] B) : ℝ :=
  sInf {X : ℝ | 0 ≤ X ∧ ∀ fn : Cl → A,
    (∑ L', γ' L' * ‖liftOp γ ε T fn L'‖ ^ 2) ≤ X * ∑ L, γ L * ‖fn L‖ ^ 2}
def LiftOperatorBound : Prop :=
  ∀ (Pl ι Cl Cl' : Type) [Fintype Pl] [Fintype ι] [Fintype Cl] [Fintype Cl'] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : Cl → Cl' → (Pl × ι → ℂ) → ℂ) (c : Cl → Cl' → (Pl × ι → ℕ) → ℂ)
    (Rc : (Pl × ι → ℕ) →₀ (A →L[ℂ] B)) (lam : Pl → ℂ) (Om : Pl → ℝ) (S : ℝ)
    (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ, ∑ i, ν τ i = n τ) →
    (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    (∀ L L', Continuous (Th L L')) →
    (∀ L L' u, HasSum (fun e => c L L' e * mono u e) (Th L L' u)) →
    (∀ L L' u, ‖Th L L' u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ e ∈ Rc.support, ∀ τ, ∑ x, e (τ, x) = n τ) →
    (∀ u, ‖Rc.sum (fun e X => mono (cj u) e • X)‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    (∀ τ, 0 < Om τ) → (∀ τ, ‖lam τ‖ ^ 2 = (Om τ)⁻¹) →
    (∀ L, 0 < γ L ∧ γ L ≤ 1) → (∀ L', 0 < γ' L' ∧ γ' L' ≤ 1) → (∀ L L', ‖ε L L'‖ = 1) →
    liftNormSq γ γ' ε (fun L L' => liftBlock (c L L') Rc lam) ≤
      ((Fintype.card Cl : ℝ) * (Fintype.card Cl' : ℝ)) *
        (S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ n τ *
          (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i)))))
end Formalism.DimensionVariation


