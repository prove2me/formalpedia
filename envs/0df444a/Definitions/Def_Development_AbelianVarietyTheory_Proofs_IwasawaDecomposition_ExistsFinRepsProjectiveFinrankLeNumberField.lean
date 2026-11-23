-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:41.718318+00:00
-- url     : https://prove2.me/theorems/e99a41bf-5adc-4c58-904b-0e68ed81c2e6
-- title:
--   Exists Fin Reps Projective Finrank Le Number Field
-- statement:
--   Definitions and structural lemmas for Exists Fin Reps Projective Finrank Le Number Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFinRepsProjectiveFinrankLeNumberField.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace GlobalTheory
namespace ProjModClasses
variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
noncomputable def rep (c : ClassGroup R) : Ideal R :=
  ((ClassGroup.mk0_surjective (R := R) c).choose : Ideal R)
theorem rep_mem (c : ClassGroup R) : rep c ∈ nonZeroDivisors (Ideal R) :=
  (ClassGroup.mk0_surjective (R := R) c).choose.2
instance ideal_projective (I : Ideal R) : Module.Projective R I := by
  have : Module.FinitePresentation R I := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation
theorem map_mulLeft_eq (x : R) (I : Ideal R) :
    Submodule.map (LinearMap.mulLeft R x) I = Ideal.span {x} * I := by
  ext z
  rw [Ideal.mem_span_singleton_mul, Submodule.mem_map]
  simp [LinearMap.mulLeft_apply]
noncomputable def mulEquiv {x : R} (hx : x ≠ 0) (I : Ideal R) :
    I ≃ₗ[R] (Ideal.span {x} * I : Ideal R) :=
  (Submodule.equivMapOfInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) I).trans
    (LinearEquiv.ofEq _ _ (map_mulLeft_eq x I))
abbrev Model {r : ℕ} (c : Fin r → ClassGroup R) : Type := ∀ j, (rep (c j) : Ideal R)
noncomputable def consLin {r : ℕ} (d : ClassGroup R) (c : Fin r → ClassGroup R) :
    (↥(rep d) × Model c) ≃ₗ[R] Model (Fin.cons d c : Fin (r + 1) → ClassGroup R) :=
  { Fin.consEquiv (fun j => ↥(rep ((Fin.cons d c : Fin (r + 1) → ClassGroup R) j))) with
    map_add' := fun a b => by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    map_smul' := fun s a => by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl }
end ProjModClasses
end GlobalTheory


