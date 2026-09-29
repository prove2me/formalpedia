-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
-- name    : AlgebraicGeometry_TwoChartCechSectionsOf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/4616a23b-80f1-5a5a-b89e-fe9e9c37303a
-- title:
--   Čech sections of a module on a two-affine cover
-- statement:
--   Fix a commutative ring $R$, a scheme $X$ and a morphism $c \colon X \to \operatorname{Spec} R$. For an open $U \subseteq X$ the notion `algebraOfHom` makes $\Gamma(X, U)$ an $R$-algebra via the inverse of the canonical iso $R \cong \Gamma(\operatorname{Spec} R, \top)$ followed by $c^\sharp \colon \Gamma(\operatorname{Spec} R, \top) \to \Gamma(X, U)$. Against this background, for a sheaf of $\mathcal O_X$-modules $M$ (an `X.Modules`), `moduleSectionsOfHom` is the $R$-module structure on the sections $\Gamma(M, U)$ obtained by restriction of scalars along $R \to \Gamma(X, U)$, and `isScalarTower_sections` records that this structure, the $\Gamma(X,U)$-structure and the $R$-algebra structure form a scalar tower, the $R$-action being literally the action of the image of $r$ under the structure map. For $V \le U$, `restrictSections` packages the presheaf restriction $\Gamma(M, U) \to \Gamma(M, V)$ as an $R$-linear map; $R$-linearity comes from the fact that restriction of functions is an $R$-algebra map, and `restrictSections_apply` identifies the underlying function with the presheaf map on $(V \le U)^{\mathrm{op}}$.
--
--   The main construction, `sectionsOf`, takes a two-affine open cover $\mathcal V$ of $X$ (affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine) together with $c$ and $M$, and produces a [`TwoChartCech.Sections`](../def/AlgebraicGeometry_TwoChartCech.html#L38) datum over the cover of $R$-algebras $\mathcal V.\mathrm{cover}\ c$ given by $\Gamma(X, U_0)$, $\Gamma(X, U_1)$, $\Gamma(X, U_0 \sqcap U_1)$ with the two restriction algebra maps. Its three modules are $\Gamma(M, U_0)$, $\Gamma(M, U_1)$ and $\Gamma(M, U_0 \sqcap U_1)$, each with its module structure over the corresponding ring of functions and over $R$; the two maps $r_0, r_1$ are the restrictions to $U_0 \sqcap U_1$, and the semilinearity identities $r_i(a \cdot m) = \rho_i(a) \cdot r_i(m)$, which the `Sections` structure carries as fields, hold because presheaf restriction for a sheaf of modules is compatible with restriction of scalars. Accompanying identification lemmas name the three modules and the two restriction maps. The Čech differential, $\check H^0$ and $\check H^1$ of this datum are those of the general two-chart formalism: $\check H^0$ is the kernel of $(s_0, s_1) \mapsto r_1 s_1 - r_0 s_0$ and $\check H^1$ the quotient of $\Gamma(M, U_0 \sqcap U_1)$ by its image.
--
--   **Relation to Mathlib.** Mathlib supplies the schemes, the sections notation $\Gamma(M, U)$ for a sheaf of modules on a scheme and the restriction maps; the two-chart Čech formalism ([`TwoChartCech.Cover`](../def/AlgebraicGeometry_TwoChartCech.html#L17), [`TwoChartCech.Sections`](../def/AlgebraicGeometry_TwoChartCech.html#L38)) and the two-affine-cover structure are the project's own, and this module is the bridge transporting a sheaf of $\mathcal O_X$-modules into that formalism.
--
--   **Where it is used.** These definitions feed sheaves of modules on a scheme covered by two affine opens into the project's two-chart Čech machinery, so that $\check H^0$ and $\check H^1$ of such a module are available as $R$-modules, with the $R$-algebra structures coming from a fixed morphism to $\operatorname{Spec} R$. They are the geometric input for computations of cohomology and its base change behaviour for modules on curves over a base, as needed in the study of modular curves and modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoChartCechSectionsOf.lean

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

@[reducible] def moduleSectionsOfHom (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) :
    Module R Γ(M, U) :=
  letI := algebraOfHom c U
  Module.compHom Γ(M, U) (algebraMap R Γ(X, U))

theorem isScalarTower_sections (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) :
    letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
    IsScalarTower R Γ(X, U) Γ(M, U) :=
  letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def restrictSections (c : X ⟶ Spec (.of R)) (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
    Γ(M, U) →ₗ[R] Γ(M, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c V
  letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
  { toFun := fun x => M.presheaf.map (homOfLE h).op x
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      show M.presheaf.map (homOfLE h).op ((algebraMap R Γ(X, U) r) • x)
        = (algebraMap R Γ(X, V) r) • M.presheaf.map (homOfLE h).op x
      rw [Scheme.Modules.map_smul]
      congr 1
      exact (restrictAlgHom c h).commutes r }

theorem restrictSections_apply (c : X ⟶ Spec (.of R)) (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
    restrictSections c M h x = M.presheaf.map (homOfLE h).op x := rfl

variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) (M : X.Modules)

def sectionsOf : TwoChartCech.Sections (𝒱.cover c) :=
  letI : Module (𝒱.cover c).A0 Γ(M, 𝒱.U0) := inferInstanceAs (Module Γ(X, 𝒱.U0) Γ(M, 𝒱.U0))
  letI : Module (𝒱.cover c).A1 Γ(M, 𝒱.U1) := inferInstanceAs (Module Γ(X, 𝒱.U1) Γ(M, 𝒱.U1))
  letI : Module (𝒱.cover c).A01 Γ(M, 𝒱.U0 ⊓ 𝒱.U1) :=
    inferInstanceAs (Module Γ(X, 𝒱.U0 ⊓ 𝒱.U1) Γ(M, 𝒱.U0 ⊓ 𝒱.U1))
  letI : Module R Γ(M, 𝒱.U0) := moduleSectionsOfHom c M 𝒱.U0
  letI : Module R Γ(M, 𝒱.U1) := moduleSectionsOfHom c M 𝒱.U1
  letI : Module R Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := moduleSectionsOfHom c M (𝒱.U0 ⊓ 𝒱.U1)
  haveI : IsScalarTower R (𝒱.cover c).A0 Γ(M, 𝒱.U0) := isScalarTower_sections c M 𝒱.U0
  haveI : IsScalarTower R (𝒱.cover c).A1 Γ(M, 𝒱.U1) := isScalarTower_sections c M 𝒱.U1
  haveI : IsScalarTower R (𝒱.cover c).A01 Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := isScalarTower_sections c M (𝒱.U0 ⊓ 𝒱.U1)
  { M0 := Γ(M, 𝒱.U0)
    M1 := Γ(M, 𝒱.U1)
    M01 := Γ(M, 𝒱.U0 ⊓ 𝒱.U1)
    r0 := restrictSections c M inf_le_left
    r1 := restrictSections c M inf_le_right
    r0_smul := fun a m => by
      exact Scheme.Modules.map_smul M (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)) a m
    r1_smul := fun a m => by
      exact Scheme.Modules.map_smul M (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)) a m }

theorem sectionsOf_M0 : (𝒱.sectionsOf c M).M0 = Γ(M, 𝒱.U0) := rfl
theorem sectionsOf_M1 : (𝒱.sectionsOf c M).M1 = Γ(M, 𝒱.U1) := rfl
theorem sectionsOf_M01 : (𝒱.sectionsOf c M).M01 = Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem sectionsOf_r0_apply (x : Γ(M, 𝒱.U0)) :
    (𝒱.sectionsOf c M).r0 (show (𝒱.sectionsOf c M).M0 from x)
      = M.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op x := rfl
theorem sectionsOf_r1_apply (x : Γ(M, 𝒱.U1)) :
    (𝒱.sectionsOf c M).r1 (show (𝒱.sectionsOf c M).M1 from x)
      = M.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op x := rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end


