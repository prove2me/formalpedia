-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:27.881048+00:00
-- url     : https://prove2.me/theorems/f9c512f0-9a4a-4fe0-b17d-abf0b0586eaa
-- title:
--   PDescend Hom
-- statement:
--   Definitions and structural lemmas for PDescend Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace DescendHom
section General
variable {T Y Z : Scheme.{0}}
lemma hom_app_res {M N : Y.Modules} (χ : M ⟶ N) {U V : Y.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    χ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (χ.app U x) := by
  have h := congrArg (fun f => f.hom x) (χ.mapPresheaf.naturality i.op)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h
end General
section Descend
variable {T Y Z : Scheme.{0}} (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) {F G : Y.Modules}
  (φ : (Scheme.Modules.pullback (g' ≫ ι)).obj F ⟶ (Scheme.Modules.pullback (g' ≫ ι)).obj G)
  (hinj : ∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn (g' ≫ ι) G V))
  (t : ∀ V : Y.Opens, V ≤ ι.opensRange → Γ(F, V) → Γ(G, V))
  (ht : ∀ (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)),
    pullSectionOn (g' ≫ ι) G V (t V hV s) =
      φ.app ((g' ≫ ι) ⁻¹ᵁ V) (pullSectionOn (g' ≫ ι) F V s))
include hinj ht
lemma t_res {V W : Y.Opens} (hV : V ≤ ι.opensRange) (h : W ≤ V) (s : Γ(F, V)) :
    t W (h.trans hV) (F.presheaf.map (homOfLE h).op s) =
      G.presheaf.map (homOfLE h).op (t V hV s) := by
  apply hinj W (h.trans hV)
  rw [ht, pullSectionOn_res (g' ≫ ι) F h (homOfLE ((Opens.map (g' ≫ ι).base).monotone h)),
    pullSectionOn_res (g' ≫ ι) G h (homOfLE ((Opens.map (g' ≫ ι).base).monotone h)), ht,
    hom_app_res]
lemma t_add {V : Y.Opens} (hV : V ≤ ι.opensRange) (a b : Γ(F, V)) :
    t V hV (a + b) = t V hV a + t V hV b := by
  apply hinj V hV
  rw [map_add, ht, ht, ht, map_add, map_add]
lemma t_zero {V : Y.Opens} (hV : V ≤ ι.opensRange) : t V hV 0 = 0 := by
  apply hinj V hV
  rw [ht, map_zero, map_zero, map_zero]
lemma t_smul {V : Y.Opens} (hV : V ≤ ι.opensRange) (r : Γ(Y, V)) (a : Γ(F, V)) :
    t V hV (r • a) = r • t V hV a := by
  apply hinj V hV
  rw [ht, pullSectionOn_smul, Scheme.Modules.Hom.app_smul, ← ht, pullSectionOn_smul]
def restrictHom : F.restrict ι ⟶ G.restrict ι :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => t (ι ''ᵁ U.unop) (ι.image_le_opensRange _) s
          map_zero' := t_zero ι g' φ hinj t ht _
          map_add' := t_add ι g' φ hinj t ht _ }
      naturality := fun U V i => by
        ext s
        exact t_res ι g' φ hinj t ht (ι.image_le_opensRange _) (ι.image_mono (leOfHom i.unop)) s }
    (fun U r s => t_smul ι g' φ hinj t ht _ ((ι.appIso U.unop).inv r) s)
def descendPsi : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G :=
  (Scheme.Modules.restrictFunctorIsoPullback ι).inv.app F ≫ restrictHom ι g' φ hinj t ht ≫
    (Scheme.Modules.restrictFunctorIsoPullback ι).hom.app G
end Descend
end DescendHom
end
end GroundTheory.Heights₂.Heights.Model


