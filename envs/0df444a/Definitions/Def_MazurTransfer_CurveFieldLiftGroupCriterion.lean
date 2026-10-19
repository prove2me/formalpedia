-- Prove2me | Definitions.Def_MazurTransfer_CurveFieldLiftGroupCriterion
-- name    : MazurTransfer_CurveFieldLiftGroupCriterion
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:34:58.432979+00:00
-- url     : https://prove2.me/theorems/c5a2d98c-360b-4415-91eb-408d1ec8a7f1
-- title:
--   The original group criterion for generic-compatible curve lifts
-- statement:
--   Let a specified generic embedding into a curve detect morphisms over the base. Curve lifts of field automorphisms satisfying the original base and generic composition laws form a monoid homomorphism. If the generic embedding is a monomorphism, the lift is injective: $$L(1)=1,\quad L(\sigma\tau)=L(\sigma)L(\tau),\quad L\ \text{injective}.$$ This criterion supplies the actual curve field-lift group structure.
-- source:
--   Original complete declarations and bodies from MazurTheorem CurveFieldLiftGroupCriterion.lean, Apache-2.0, Vas and contributors. 4 complete original closed types and 1 data values are kernel-compared. Public imports alone replace dependencies. The original generic criterion is reused byte-for-byte without native rebuilding. Named downstream consumer: actual generic-compatible Picard action and arithmetic pullback naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: curve lifts of field automorphisms, specified at a generic
embedding that detects morphisms over the base, form a monoid homomorphism.
A monic generic embedding makes the lift injective. Named downstream
consumer: the actual order-13 curve's checked generic-stalk lift over Q.
-/
import Mathlib

noncomputable section
universe u
namespace MazurTransfer.CurveFieldLiftGroupCriterion
open CategoryTheory AlgebraicGeometry
variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  (ι : Spec (CommRingCat.of F) ⟶ C)
  (L : (F ≃ₐ[K] F) → Aut C)
  (hbase : ∀ σ, (L σ).hom ≫ c = c)
  (hgeneric : ∀ σ, ι ≫ (L σ).hom = Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ ι)
  (hext : ∀ (f g : C ⟶ C), f ≫ c = c → g ≫ c = c → ι ≫ f = ι ≫ g → f = g)

include hbase hgeneric hext in
theorem lift_one : L 1 = 1 := by
  apply Iso.ext
  apply hext _ _ (hbase 1) (Category.id_comp _)
  rw [hgeneric]
  change Spec.map (𝟙 (CommRingCat.of F)) ≫ ι = ι ≫ 𝟙 C
  rw [Spec.map_id, Category.id_comp, Category.comp_id]

include hbase hgeneric hext in
theorem lift_mul (σ τ : F ≃ₐ[K] F) : L (σ * τ) = L σ * L τ := by
  apply Iso.ext
  have hover : (L σ * L τ).hom ≫ c = c := by
    change (L τ).hom ≫ (L σ).hom ≫ c = c
    rw [hbase, hbase]
  apply hext _ _ (hbase (σ * τ)) hover
  change ι ≫ (L (σ * τ)).hom = ι ≫ ((L τ).hom ≫ (L σ).hom)
  rw [hgeneric, ← Category.assoc, hgeneric τ, Category.assoc, hgeneric σ, ← Category.assoc]
  apply congrArg (fun g : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of F) => g ≫ ι)
  rw [← Spec.map_comp]
  rfl

def liftHom : (F ≃ₐ[K] F) →* Aut C where
  toFun := L
  map_one' := lift_one c ι L hbase hgeneric hext
  map_mul' := lift_mul c ι L hbase hgeneric hext

include hgeneric in
theorem lift_injective [Mono ι] : Function.Injective L := by
  intro σ τ h
  have hg := congrArg (fun e : Aut C => ι ≫ e.hom) h
  rw [hgeneric, hgeneric] at hg
  have hr := Spec.map_injective ((cancel_mono ι).mp hg)
  have hinv : σ.symm = τ.symm := by
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun f : CommRingCat.of F ⟶ CommRingCat.of F => f.hom x) hr
  have hs := congrArg (fun f : F ≃ₐ[K] F => f.symm) hinv
  simpa only [AlgEquiv.symm_symm] using hs

end MazurTransfer.CurveFieldLiftGroupCriterion
#print axioms MazurTransfer.CurveFieldLiftGroupCriterion.liftHom
#print axioms MazurTransfer.CurveFieldLiftGroupCriterion.lift_injective


