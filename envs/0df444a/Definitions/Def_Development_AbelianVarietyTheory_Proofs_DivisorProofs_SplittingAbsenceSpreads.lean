-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:14.96223+00:00
-- url     : https://prove2.me/theorems/b7c4c854-69ed-4be7-bf77-7926c7e83641
-- title:
--   Splitting Absence Spreads
-- statement:
--   Definitions and structural lemmas for Splitting Absence Spreads, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
namespace GlobalTheory.SplitSpread
open MvPolynomial
abbrev Mon (σ : Type) (D : ℕ) := {m : σ →₀ ℕ // m.degree ≤ D}
instance instFiniteMon (σ : Type) [Finite σ] (D : ℕ) : Finite (Mon σ D) :=
  (Finsupp.finite_of_degree_le (σ := σ) D).to_subtype
noncomputable instance instFintypeMon (σ : Type) [Finite σ] (D : ℕ) : Fintype (Mon σ D) :=
  Fintype.ofFinite _
abbrev Var (σ : Type) (D : ℕ) := (Bool × Mon σ D) ⊕ (Bool × σ) ⊕ Bool
variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)
noncomputable def gen (b : Bool) : MvPolynomial σ (MvPolynomial (Var σ D) A) :=
  ∑ m : Mon σ D, monomial m.1 (X (Sum.inl (b, m)))
noncomputable def eqs (f g : MvPolynomial σ A) :
    ((σ →₀ ℕ) ⊕ Bool ⊕ Bool) → MvPolynomial (Var σ D) A
  | Sum.inl n => coeff n (gen A D true * gen A D false - MvPolynomial.map C f)
  | Sum.inr (Sum.inl b) => MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (gen A D b)
  | Sum.inr (Sum.inr b) =>
      X (Sum.inr (Sum.inr b)) * MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map C g) - 1
variable {A D}
end GlobalTheory.SplitSpread
namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A] {D : ℕ}
noncomputable def spec {k : Type} [CommRing k] (z : Var σ D → k) (b : Bool) : MvPolynomial σ k :=
  ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m)))
end GlobalTheory.SplitSpread
namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A]
def Bad (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) : Prop :=
  ∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧
    u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧
      MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧
      MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0
end GlobalTheory.SplitSpread


