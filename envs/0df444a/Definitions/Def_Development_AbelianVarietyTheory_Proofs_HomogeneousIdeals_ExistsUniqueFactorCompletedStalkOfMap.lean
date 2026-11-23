-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:58.361818+00:00
-- url     : https://prove2.me/theorems/960a222c-a713-45c2-a0c1-c44087bc41bb
-- title:
--   Exists Unique Factor Completed Stalk Of Map
-- statement:
--   Definitions and structural lemmas for Exists Unique Factor Completed Stalk Of Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
namespace GlobalTheory
section Completion
variable {A R : Type*} [CommRing A] [CommRing R]
end Completion
section Local
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
noncomputable def fromSpecCompletedStalk (X : Scheme.{u}) (x : X) :
    Spec (.of (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))) ≫
    X.fromSpecStalk x
end Local
section Limit
variable {R : Type u} [CommRing R] (I : Ideal R)
noncomputable abbrev adicLevelι (n : ℕ) : Spec (.of (R ⧸ I ^ n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
noncomputable abbrev adicLevelMap {m n : ℕ} (h : m ≤ n) :
    Spec (.of (R ⧸ I ^ m)) ⟶ Spec (.of (R ⧸ I ^ n)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h))
def IsAdicFamily {X : Scheme.{u}} (f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X) : Prop :=
  ∀ n, adicLevelMap I (Nat.le_succ (n + 1)) ≫ f (n + 1) = f n
variable {I}
theorem isAdicFamily_restrict {X : Scheme.{u}} (g : Spec (.of R) ⟶ X) :
    IsAdicFamily I fun n => adicLevelι I (n + 1) ≫ g :=
  fun _ => by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
variable [IsLocalRing R]
theorem isLocalRing_quotient_pow (hI : I ≠ ⊤) (n : ℕ) : IsLocalRing (R ⧸ I ^ (n + 1)) :=
  have : Nontrivial (R ⧸ I ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => hI (top_le_iff.mp (h ▸ Ideal.pow_le_self n.succ_ne_zero)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
variable (I)
omit [IsLocalRing R] in

noncomputable def adicRestrict (X : Scheme.{u}) (g : Spec (.of R) ⟶ X) :
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X // IsAdicFamily I f} :=
  ⟨fun n => adicLevelι I (n + 1) ≫ g, isAdicFamily_restrict g⟩
omit [IsLocalRing R] in

noncomputable def adicRestrictOver {X S : Scheme.{u}} (s : Spec (.of R) ⟶ S) (p : X ⟶ S)
    (g : {g : Spec (.of R) ⟶ X // g ≫ p = s}) :
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X //
      IsAdicFamily I f ∧ ∀ n, f n ≫ p = adicLevelι I (n + 1) ≫ s} :=
  ⟨fun n => adicLevelι I (n + 1) ≫ g.1, isAdicFamily_restrict g.1,
    fun n => by rw [Category.assoc, g.2]⟩
end Limit
end GlobalTheory


