-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:20.46826+00:00
-- url     : https://prove2.me/theorems/191563b2-e91a-403f-824c-40a0ad35cfd0
-- title:
--   Comp Right Eq Zero
-- statement:
--   Definitions and structural lemmas for Comp Right Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/CompRightEqZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
universe u
open Polynomial
def mix {V : Type*} {n : ℕ} (k : ℕ) (x y : V) : Fin n → V :=
  fun i => if (i : ℕ) < k then x else y
def IsSymmForm {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), I (v ∘ σ) = I v
def word {VW : Type*} (D k i : ℕ) (x₁ x₂ a : VW) : Fin D → VW :=
  fun j => if (j : ℕ) = 0 then x₂ else if (j : ℕ) < 1 + 2 * i then x₁ else
    if (j : ℕ) < 2 * k - 1 then x₂ else a
noncomputable def volPoly (D : ℕ) (J : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (D + 1), C ((D.choose j : ℝ) * J j) * (-X) ^ j
noncomputable def tsgPoly (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    if Odd n then C (((D : ℝ) + 1) * κ ((n + 1) / 2) / (((n + 1) / 2 : ℕ) : ℝ) * P.coeff n) * X ^ (n + 1)
    else 0
structure FibreSquare (D : ℕ) where
  V : Type u
  [acgV : AddCommGroup V]
  [modV : Module ℝ V]
  VW : Type u
  [acgW : AddCommGroup VW]
  [modW : Module ℝ VW]
  I : MultilinearMap ℝ (fun _ : Fin (D + 1) => V) ℝ
  IW : MultilinearMap ℝ (fun _ : Fin (D + 2) => VW) ℝ
  p₁ : V →ₗ[ℝ] VW
  p₂ : V →ₗ[ℝ] VW
  ξ : V
  A : V
  Φ : MultilinearMap ℝ (fun _ : Fin D => VW) ℝ
  symm : IsSymmForm I
  symmW : IsSymmForm IW
  comp_right_eq_zero_alt : ∀ v : Fin (D + 2) → V, IW (fun j => p₂ (v j)) = 0
  cons_comp_left : ∀ v : Fin (D + 1) → V, IW (Fin.cons (-(p₂ ξ)) (fun j => p₁ (v j))) = I v
  base : p₁ A = p₂ A
  diag : ∀ T : Fin D → VW,
    IW (Fin.cons (p₁ ξ) (Fin.cons (p₁ ξ) T)) - IW (Fin.cons (p₂ ξ) (Fin.cons (p₂ ξ) T)) = Φ T
attribute [instance] FibreSquare.acgV FibreSquare.modV FibreSquare.acgW FibreSquare.modW
def FibreSquare.F {D : ℕ} (S : FibreSquare D) (c : ℝ) : ℝ :=
  S.I (fun _ => S.A - c • S.ξ)
def APrimeStatement : Prop :=
  ∀ (D : ℕ) (S : FibreSquare.{u} D) (k : ℕ), 1 ≤ k → 2 * k ≤ D + 1 →
    S.I (mix (2 * k) S.ξ S.A) =
      -∑ i ∈ Finset.range k, S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A))
def ThmAIffStatement : Prop :=
  ∀ (D : ℕ) (S : FibreSquare.{u} D) (J κ : ℕ → ℝ),
    (∀ c : ℝ, S.F c + S.F (-c) = (tsgPoly D κ (volPoly D J)).eval c) ↔
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
        ∑ i ∈ Finset.range k, S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A)) = κ k * J (2 * k - 1)
def InhabitStatement : Prop :=
  ∃ S : FibreSquare.{0} 1, S.I (fun _ => S.ξ) ≠ 0
end ReciprocityTheory.ChartRestriction.G.AI


