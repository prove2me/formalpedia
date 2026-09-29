-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
-- name    : AlgebraicGeometry_ModulesPullbackMonoidal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/24a233c3-f1aa-5b5c-a7f2-bc6fcf1e02d7
-- title:
--   Monoidality of pullback for sheaves of modules on schemes
-- statement:
--   Fix a morphism of schemes $f\colon X\to Y$. Three instances record that the inverse-image functor on opens, $(\mathrm{Opens.map}\ f.\mathrm{base})\colon \mathrm{Opens}(Y)\to\mathrm{Opens}(X)$, preserves binary products (i.e. $f^{-1}(V_1\cap V_2)=f^{-1}V_1\cap f^{-1}V_2$), preserves the terminal object ($f^{-1}(Y)=X$), and hence preserves all finite products; since the categories of opens are posets, the required cone comparisons are determined by inequalities.
--
--   `pullback₀ f` is the inverse image of presheaves of modules, $Y.\mathrm{PresheafOfModules}\to X.\mathrm{PresheafOfModules}$, namely `PresheafOfModules.pullback` along the comparison map $f.c\colon \mathcal{O}_Y\to f_*\mathcal{O}_X$ read as a morphism $\mathcal{O}_Y\to(\mathrm{Opens.map}\ f.\mathrm{base})^{\mathrm{op}}\!\cdot\mathcal{O}_X$; it agrees with Mathlib's presheaf-level pullback along the induced morphism of sheaves of rings. Because the functor on opens preserves finite products, `pullback₀ f` carries a strong monoidal structure: the left adjoint of the lax monoidal pushforward has invertible oplax structure maps.
--
--   On the sheaf side, `Modules.sheafify Y` is recorded as a localization of presheaves of $\mathcal{O}_Y$-modules at [`SheafOfModules.presheafW`](../def/SheafOfModules_Monoidal.html#L23), the class of morphisms whose underlying morphism of presheaves of abelian groups lies in the class $J.W$ for the topology of opens; a `Localization.Lifting` instance records that $f^*$ on sheaves of modules lifts the composite of `pullback₀ f` with sheafification on $X$. Transporting monoidality through this monoidal localization yields the main instance `pullback_monoidal`: $f^*\colon Y.\mathrm{Modules}\to X.\mathrm{Modules}$ is strong monoidal. The two final definitions name the resulting isomorphisms, $f^*(L\otimes M)\cong f^*L\otimes f^*M$ and $f^*\mathcal{O}_Y\cong\mathcal{O}_X$, as the inverses of the structural maps $\mu$ and $\varepsilon$.
--
--   **Relation to Mathlib.** Mathlib supplies the pullback of presheaves and of sheaves of modules, sheafification and the theory of localized monoidal categories; the monoidal structure on sheaves of modules over a scheme and the monoidality of pullback are supplied by this project's definition modules and assembled here for schemes.
--
--   **Where it is used.** These isomorphisms are what makes $f^*$ compatible with tensor products of invertible sheaves, hence what makes pullback induce homomorphisms of Picard groups and keeps rigidified line bundles stable under tensor product; this is used in the construction of the relative Picard functor and the Jacobian of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesPullbackMonoidal.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_PresheafOfModules_PullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance preservesBinaryProducts_opensMap :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have hinf : K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩ ≤ c.pt := leOfHom (hc.lift
          { pt := K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩
            π := Discrete.natTrans (fun j => match j with
              | ⟨.left⟩ => homOfLE inf_le_left
              | ⟨.right⟩ => homOfLE inf_le_right) })
        have h₁ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.left⟩) := leOfHom (s.π.app ⟨.left⟩)
        have h₂ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.right⟩) := leOfHom (s.π.app ⟨.right⟩)
        exact (le_inf h₁ h₂).trans (leOfHom ((Opens.map f.base).map (homOfLE hinf))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesTerminal_opensMap :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have htop : (⊤ : Y.Opens) ≤ c.pt := leOfHom (hc.lift
          { pt := ⊤, π := Discrete.natTrans (fun j => j.as.elim) })
        exact le_top.trans (leOfHom ((Opens.map f.base).map (homOfLE htop))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesFiniteProducts_opensMap : PreservesFiniteProducts (Opens.map f.base) :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

abbrev pullback₀ : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

instance pullback₀_monoidal : (pullback₀ f).Monoidal :=
  inferInstanceAs (PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).Monoidal

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

variable (Y) in
instance sheafify_isLocalization' : (Modules.sheafify Y).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
  inferInstanceAs ((SheafOfModules.sheafifyFunctor Y.sheaf.obj Y.ringCatSheaf.property).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj))

instance : Localization.Lifting (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩

instance pullback_monoidal : (Modules.pullback f).Monoidal :=
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  Localization.Monoidal.functorMonoidalOfComp (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)

def pullbackTensorObjIso (L M : Y.Modules) :
    (Modules.pullback f).obj (L ⊗ M) ≅ (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj M :=
  (Functor.Monoidal.μIso (Modules.pullback f) L M).symm

def pullbackTensorUnitObjIso : (Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (Functor.Monoidal.εIso (Modules.pullback f)).symm

end AlgebraicGeometry.Scheme.Modules

end


