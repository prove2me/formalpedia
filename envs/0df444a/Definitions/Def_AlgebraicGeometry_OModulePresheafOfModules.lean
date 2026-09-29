-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
-- name    : AlgebraicGeometry_OModulePresheafOfModules
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/c811baff-ae0b-5ead-bf12-9f58e6e5717b
-- title:
--   The O-module presheaf attached to a sheaf of modules
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi \colon V \to \operatorname{Spec} R$, and let $M$ be a sheaf of modules over the structure sheaf of $V$ in Mathlib's sense (`V.Modules`). The definition `ofModules` packages the sections of $M$ as an `OModulePresheaf` over $\pi$, i.e. as the following data: to each open $U \subseteq V$ the abelian group $\Gamma(M, U)$, its module structure over the ring of functions $\Gamma(V, U)$, its $R$-module structure obtained by restricting scalars along the algebra map $R \to \Gamma(V, U)$ induced by $\pi$ (the algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom`, whose scalars act through $\pi^\sharp$ on global sections composed with restriction to $U$), the resulting scalar-tower compatibility between the two actions, and, for each inclusion $U \le U'$, the restriction map $\Gamma(M, U') \to \Gamma(M, U)$ of $M$ viewed as an $R$-linear map. The three axioms of the structure are supplied by the corresponding properties of $M$: restriction is semilinear for the module action, in the sense that $\operatorname{res}(a \cdot x) = (a|_U) \cdot \operatorname{res}(x)$ for $a \in \Gamma(V, U')$, restriction along the identity inclusion is the identity, and restriction along a composite inclusion is the composite of the restrictions.
--
--   The accompanying lemmas record that this datum is definitionally the expected one: the value at $U$ is $\Gamma(M, U)$; the restriction map sends $x$ to $M.\mathrm{presheaf}$ applied to the opposite of the inclusion; the $\Gamma(V, U)$-action on the datum agrees with that on $\Gamma(M, U)$; the $R$-action is given by multiplication by the image of $r$ under the algebra map; and, for a two-affine open cover $\mathcal V$ of $V$, the two-chart Čech sections datum of `ofModules` coincides with the two-chart sections datum `sectionsOf` built directly from $M$, so that the two descriptions of $H^0$ and $H^1$ for a two-chart cover agree.
--
--   **Relation to Mathlib.** Mathlib supplies sheaves of modules on a scheme (`Scheme.Modules`, with `Γ(M, U)` notation and `Scheme.Modules.map_smul`); `OModulePresheaf` is the project's own open-by-open presheaf-of-modules datum, and `ofModules` is the passage from the Mathlib notion to it.
--
--   **Where it is used.** Through this construction the project's Čech machinery for an ordered affine cover — the cochain complex, its cohomology modules $H^0$ and $H^{i+1}$, the finiteness predicate `CechFinite`, and the two-chart sections used for base change — becomes available for an arbitrary sheaf of $\mathcal O_V$-modules on a scheme over $\operatorname{Spec} R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafOfModules.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)

def ofModules : OModulePresheaf π where
  obj U := Γ(M, U)
  addCommGroup _ := inferInstance
  module U := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
  moduleSections _ := inferInstance
  isScalarTower U := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
  res h := Scheme.TwoAffineOpenCover.restrictSections π M h
  res_smul h a x := Scheme.Modules.map_smul M (homOfLE h) a x
  res_refl U := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (le_refl U)).op x = x
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), M.presheaf.map_id]
    rfl
  res_comp {U U' U''} h h' := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U''
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (h.trans h')).op x
      = M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x)
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

theorem ofModules_obj (U : V.Opens) : (ofModules π M).obj U = Γ(M, U) := rfl

theorem ofModules_res_apply {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) :
    (ofModules π M).res h (show (ofModules π M).obj U' from x) = M.presheaf.map (homOfLE h).op x :=
  rfl

theorem ofModules_smul (U : V.Opens) (a : Γ(V, U)) (x : Γ(M, U)) :
    (show (ofModules π M).obj U from a • x) = a • (show (ofModules π M).obj U from x) := rfl

theorem ofModules_algebraMap_smul (U : V.Opens) (r : R) (x : (ofModules π M).obj U) :
    r • x = (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r • x :=
  rfl

theorem ofModules_twoChartSections (𝒱 : V.TwoAffineOpenCover) :
    (ofModules π M).twoChartSections 𝒱 = 𝒱.sectionsOf π M := rfl

end AlgebraicGeometry.OModulePresheaf

end


