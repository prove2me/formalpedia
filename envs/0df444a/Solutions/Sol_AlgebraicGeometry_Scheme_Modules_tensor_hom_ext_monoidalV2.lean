-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.tensor_hom_ext_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d5b1d378-99fe-510c-a05c-95e65a3b3b76

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2.AlgebraicGeometry Opposite TensorProduct"
p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.tensorSections"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Hom Γ Hom.app Modules.Hom Modules.Hom.app Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom Hom.app tensor sheafify tensorIsoSheafify tensorSections"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace TensorHomExtV2

abbrev adj (Z : Scheme.{u}) := SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property

abbrev ι (Z : Scheme.{u}) := SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property

def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W : Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) = shUnit A' W (g.app (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

variable {Y : Scheme.{u}}

def cmpIso (L M : Y.Modules) : (Modules.sheafify Y).obj ((ι Y).obj L ⊗ (ι Y).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)).symm ≪≫
    ((asIso (adj Y).counit).app L ⊗ᵢ (asIso (adj Y).counit).app M)

lemma cmpIso_hom (L M : Y.Modules) :
    (cmpIso L M).hom = δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M) ≫
      ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) := rfl

lemma tensorSections_eq (L M : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Modules.tensorSections s t = Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))) := rfl

theorem tensor_hom_ext {M P N : Y.Modules} {θ θ' : M ⊗ P ⟶ N}
    (h : ∀ (U : Y.Opens) (m : Γ(M, U)) (p : Γ(P, U)),
      Scheme.Modules.Hom.app θ U (Modules.tensorSections m p) =
        Scheme.Modules.Hom.app θ' U (Modules.tensorSections m p)) : θ = θ' := by
  rw [← cancel_epi (cmpIso M P).hom]
  apply ((adj Y).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m p
  have hV := h V.unop m p
  simp only [tensorSections_eq] at hV
  exact hV

end TensorHomExtV2

end AlgebraicGeometry.Scheme.Modules

end

theorem solution
    {X : Scheme.{u}} {M P N : X.Modules} {θ θ' : M ⊗ P ⟶ N}
    (h : ∀ (U : X.Opens) (m : Γ(M, U)) (p : Γ(P, U)),
      θ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections m p) =
        θ'.app U (AlgebraicGeometry.Scheme.Modules.tensorSections m p)) :
    θ = θ' := by
  exact AlgebraicGeometry.Scheme.Modules.TensorHomExtV2.tensor_hom_ext h

end S_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2 (solution)
