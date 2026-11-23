-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_InfRes
-- name    : GroundTheory_TateCohomology_InfRes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:03.334835+00:00
-- url     : https://prove2.me/theorems/f3e460cd-ab84-4924-9c18-44db83e922e3
-- title:
--   Inf Res
-- statement:
--   Definitions and structural lemmas for Inf Res, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
theorem map_one_succ {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : res (1 : G →* H) A ⟶ B) (n : ℕ) : map 1 φ (n + 1) = 0 := by
  let f : PUnit.{u + 1} →* H := 1
  let g : G →* PUnit.{u + 1} := 1
  let ψ : res g (res f A) ⟶ B := ofHom ⟨φ.hom.toLinearMap, fun x => φ.hom.isIntertwining' x⟩
  have h : map 1 φ (n + 1) = map (f.comp g) ((resFunctor g).map (𝟙 (res f A)) ≫ ψ) (n + 1) :=
    map_congr (by ext; rfl) rfl (n + 1)
  rw [h, map_comp, (isZero_groupCohomology_succ_of_subsingleton (res f A) n).eq_zero_of_src
    (map g ψ (n + 1)), Limits.comp_zero]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
noncomputable abbrev inflation (n : ℕ) :
    groupCohomology (A.quotientToInvariants S) n ⟶ groupCohomology A n :=
  map (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) n
noncomputable abbrev restriction (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology (res S.subtype A) n :=
  map S.subtype (𝟙 _) n
theorem inflation_comp_restriction (n : ℕ) :
    inflation A S (n + 1) ≫ restriction A S (n + 1) = 0 := by
  rw [← map_comp, Category.comp_id, groupCohomology.congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ (n + 1)), map_one_succ]
@[simps X₁ X₂ X₃ f g]
noncomputable def infResShortComplex (n : ℕ) : ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) (n + 1)
  X₂ := groupCohomology A (n + 1)
  X₃ := groupCohomology (res S.subtype A) (n + 1)
  f := inflation A S (n + 1)
  g := restriction A S (n + 1)
  zero := inflation_comp_restriction A S n
noncomputable def toCoindOne : A ⟶ coindOne k G A :=
  ofHom ⟨LinearMap.pi fun x => A.ρ x, fun g => by ext a x; simp⟩
lemma toCoindOne_injective : Function.Injective (toCoindOne A).hom := fun a b h => by
  have h' : A.ρ 1 a = A.ρ 1 b := congrFun h 1
  simpa using h'
instance : Mono (toCoindOne A) := (Rep.mono_iff_injective _).2 (toCoindOne_injective A)
noncomputable abbrev shiftSC : ShortComplex (Rep k G) :=
  ShortComplex.mk (toCoindOne A) (cokernel.π (toCoindOne A)) (cokernel.condition _)
instance : (quotientToInvariantsFunctor k S).PreservesZeroMorphisms where
  map_zero _ _ := by ext; rfl
noncomputable abbrev shiftSCQ : ShortComplex (Rep k (G ⧸ S)) :=
  (shiftSC A).map (quotientToInvariantsFunctor k S)
variable {A S}
end GroundTheory.GroupCoh


