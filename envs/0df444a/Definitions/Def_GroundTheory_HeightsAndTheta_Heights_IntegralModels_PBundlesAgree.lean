-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:43.486603+00:00
-- url     : https://prove2.me/theorems/8e567d37-be80-477b-a2a8-62c89b3d96ac
-- title:
--   PBundles Agree
-- statement:
--   Definitions and structural lemmas for PBundles Agree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBundlesAgree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsHeightOneSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace BundlesAgree
variable {X : Scheme.{0}} [IsIntegral X]
lemma section_eq_zero (E : X.Modules) {U : X.Opens} (hU : genericPoint X ∉ U) (s : Γ(E, U)) :
    s = 0 := by
  have hU' : U = ⊥ := by
    by_contra h
    obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty U).mp h
    exact hU (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩)
  have ht := TopCat.Sheaf.isTerminalOfEqEmpty ⟨E.presheaf, E.isSheaf⟩ hU'
  have h0 : (𝟙 (E.presheaf.obj (op U))) = 0 := ht.hom_ext _ _
  simpa using ConcreteCategory.congr_hom h0 s
lemma section_ext (E : X.Modules)
    (hE : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E.presheaf.germ U (genericPoint X) hU))
    {U : X.Opens} {a b : Γ(E, U)}
    (h : ∀ hU : genericPoint X ∈ U,
      E.presheaf.germ U (genericPoint X) hU a = E.presheaf.germ U (genericPoint X) hU b) :
    a = b := by
  by_cases hU : genericPoint X ∈ U
  · exact hE U hU (h hU)
  · rw [section_eq_zero E hU a, section_eq_zero E hU b]
omit [IsIntegral X] in

lemma germ_smul' (E : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(E, U)) :
    E.presheaf.germ U x hx (r • s) = X.presheaf.germ U x hx r • E.presheaf.germ U x hx s :=
  PresheafOfModules.germ_smul (R := X.presheaf) (M := E.val) x U hx r s
def lift (E E' : X.Modules)
    (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X))
    (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
      E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
    (U : X.Opens) (s : Γ(E, U)) : Γ(E', U) :=
  haveI := Classical.dec (genericPoint X ∈ U)
  if hU : genericPoint X ∈ U then (hex U hU s).choose else 0
variable (E E' : X.Modules)
  (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
    E'.presheaf.stalk (genericPoint X))
  (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
    E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
  (hE' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E'.presheaf.germ U (genericPoint X) hU))
lemma germ_lift (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U (genericPoint X) hU (lift E E' φ hex U s) =
      φ (E.presheaf.germ U (genericPoint X) hU s) := by
  rw [lift, dif_pos hU]
  exact (hex U hU s).choose_spec
include hE' in
lemma lift_add (U : X.Opens) (a b : Γ(E, U)) :
    lift E E' φ hex U (a + b) = lift E E' φ hex U a + lift E E' φ hex U b :=
  section_ext E' hE' fun hU => by
    rw [map_add, germ_lift, germ_lift, germ_lift, map_add, map_add]
include hE' in
lemma lift_zero (U : X.Opens) : lift E E' φ hex U 0 = 0 :=
  section_ext E' hE' fun hU => by
    rw [germ_lift, map_zero, map_zero, map_zero]
include hE' in
lemma lift_smul (U : X.Opens) (r : Γ(X, U)) (s : Γ(E, U)) :
    lift E E' φ hex U (r • s) = r • lift E E' φ hex U s :=
  section_ext E' hE' fun hU => by
    rw [germ_lift, germ_smul', germ_smul', map_smul, germ_lift]
include hE' in
lemma lift_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(E, U)) :
    lift E E' φ hex V (E.presheaf.map i.op s) = E'.presheaf.map i.op (lift E E' φ hex U s) :=
  section_ext E' hE' fun hV => by
    rw [germ_lift, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, germ_lift]
include hE' in

def homOfGeneric : E ⟶ E' :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := lift E E' φ hex U.unop
          map_zero' := lift_zero E E' φ hex hE' U.unop
          map_add' := lift_add E E' φ hex hE' U.unop }
      naturality := fun U V i => by
        ext s
        exact lift_res E E' φ hex hE' i.unop s }
    (fun U r s => lift_smul E E' φ hex hE' U.unop r s)
end BundlesAgree
end
end GroundTheory.Heights₂.Heights.Model


