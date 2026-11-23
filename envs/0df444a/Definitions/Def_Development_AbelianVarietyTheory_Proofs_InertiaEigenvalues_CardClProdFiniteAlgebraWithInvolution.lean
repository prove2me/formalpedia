-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolution
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:27.17294+00:00
-- url     : https://prove2.me/theorems/e4cf45d6-2cce-4cbf-828b-5c804955ba74
-- title:
--   Card Cl Prod Finite Algebra With Involution
-- statement:
--   Definitions and structural lemmas for Card Cl Prod Finite Algebra With Involution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardClProdFiniteAlgebraWithInvolution.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
namespace GlobalTheory.UnitLemma.InvAlg.ClProd
variable {K : UQ} (B₁ B₂ : InvAlg K)
def mkU (a : B₁.Aˣ) (b : B₂.Aˣ) : (B₁.prod B₂).Aˣ where
  val := ((a : B₁.A), (b : B₂.A))
  inv := (((a⁻¹ : B₁.Aˣ) : B₁.A), ((b⁻¹ : B₂.Aˣ) : B₂.A))
  val_inv := Prod.ext a.mul_inv b.mul_inv
  inv_val := Prod.ext a.inv_mul b.inv_mul
def u₁ (x : (B₁.prod B₂).Aˣ) : B₁.Aˣ := Units.map (RingHom.fst B₁.A B₂.A).toMonoidHom x
def u₂ (x : (B₁.prod B₂).Aˣ) : B₂.Aˣ := Units.map (RingHom.snd B₁.A B₂.A).toMonoidHom x
def toPair : (B₁.prod B₂).Cl → B₁.Cl × B₂.Cl :=
  Quot.lift (fun x => (Quot.mk _ ⟨u₁ B₁ B₂ x.1, congrArg Prod.fst x.2⟩,
      Quot.mk _ ⟨u₂ B₁ B₂ x.1, congrArg Prod.snd x.2⟩)) (by
    rintro x y ⟨u, hu⟩
    refine Prod.ext (Quot.sound ⟨u₁ B₁ B₂ u, congrArg Prod.fst hu⟩)
      (Quot.sound ⟨u₂ B₁ B₂ u, congrArg Prod.snd hu⟩))
def ofPair : B₁.Cl × B₂.Cl → (B₁.prod B₂).Cl := fun p =>
  Quot.lift₂ (r := _) (s := _) (fun (a : {x : B₁.Aˣ // B₁.σ (x : B₁.A) = x})
      (b : {x : B₂.Aˣ // B₂.σ (x : B₂.A) = x}) =>
      (Quot.mk _ ⟨mkU B₁ B₂ a.1 b.1, Prod.ext a.2 b.2⟩ : (B₁.prod B₂).Cl))
    (by
      rintro a b c ⟨u, hu⟩
      exact Quot.sound ⟨mkU B₁ B₂ 1 u, Prod.ext
        (show ((a.1 : B₁.Aˣ) : B₁.A) = a.1 * (((1 : B₁.Aˣ) : B₁.A) * B₁.σ ((1 : B₁.Aˣ) : B₁.A)) by simp) hu⟩)
    (by
      rintro a b c ⟨u, hu⟩
      exact Quot.sound ⟨mkU B₁ B₂ u 1, Prod.ext hu
        (show ((c.1 : B₂.Aˣ) : B₂.A) = c.1 * (((1 : B₂.Aˣ) : B₂.A) * B₂.σ ((1 : B₂.Aˣ) : B₂.A)) by simp)⟩) p.1 p.2
def clEquiv : (B₁.prod B₂).Cl ≃ B₁.Cl × B₂.Cl where
  toFun := toPair B₁ B₂
  invFun := ofPair B₁ B₂
  left_inv := by
    intro k
    induction k using Quot.ind with
    | mk x => rfl
  right_inv := by
    rintro ⟨k₁, k₂⟩
    induction k₁ using Quot.ind with
    | mk a => induction k₂ using Quot.ind with
      | mk b => rfl
end GlobalTheory.UnitLemma.InvAlg.ClProd


