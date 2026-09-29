-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesDet
-- name    : AlgebraicGeometry_ModulesDet
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f359a05f-f29b-59d7-a802-e0844962c839
-- title:
--   Exterior powers and determinants of sheaves of modules
-- statement:
--   Fix a scheme $X$. The module introduces the exterior power operations on modules over $X$, first at the level of presheaves and then for sheaves.
--
--   `presheafExteriorPower X n` is the endofunctor of `X.PresheafOfModules` obtained from the project's presheaf-level construction [`PresheafOfModules.exteriorPowerFunctor`](../def/PresheafOfModules_ExteriorPower.html#L178) applied to the presheaf of commutative rings `X.sheaf.obj` underlying the structure sheaf. Concretely, a presheaf of $\mathcal{O}_X$-modules $M$ is sent to the presheaf whose value on an open $U$ is the $\mathcal{O}_X(U)$-module $\bigwedge^{n}_{\mathcal{O}_X(U)} M(U)$; for an inclusion $V \subseteq U$ the transition map is the unique $\mathcal{O}_X(U)$-linear map (the target being viewed as an $\mathcal{O}_X(U)$-module by restriction of scalars along $\mathcal{O}_X(U) \to \mathcal{O}_X(V)$) sending $m_1 \wedge \dots \wedge m_n$ to the wedge of the restrictions $m_i|_V$, which is semilinear over the restriction map of rings; a morphism $\varphi$ of presheaves of modules is sent to the morphism whose component on $U$ is $\bigwedge^{n}$ of the $\mathcal{O}_X(U)$-linear map $\varphi_U$.
--
--   `exteriorPower X n : X.Modules ⥤ X.Modules` is the composite of the forgetful functor from sheaves of modules over $\mathcal{O}_X$ to presheaves of modules, the above presheaf-level functor, and the sheafification of presheaves of modules taken along the identity of the presheaf of rings underlying $\mathcal{O}_X$. Thus $\bigwedge^{n}\mathcal{M}$ is the sheafification of $U \mapsto \bigwedge^{n}_{\mathcal{O}_X(U)}\mathcal{M}(U)$, functorially in $\mathcal{M}$.
--
--   `det n M` is notation for $(\bigwedge^{n})(\mathcal{M})$; it is defined for every natural number $n$ and every sheaf of modules $\mathcal{M}$, with no local freeness or rank hypothesis, so no invertibility is asserted at this point. A further lemma records that the value of `exteriorPower X n` on $\mathcal{M}$ is the sheafification of the presheaf exterior power of the underlying presheaf of modules of $\mathcal{M}$.
--
--   **Relation to Mathlib.** Mathlib supplies exterior powers $\bigwedge[R]^n M$ of a module, the category of sheaves of modules on a scheme, and the sheafification of presheaves of modules; the exterior power functor on presheaves of modules over a presheaf of commutative rings is the project's own construction, and the scheme-level exterior power and determinant defined here are assembled from it.
--
--   **Where it is used.** These are the geometric input for determinant line bundles: for a sheaf that is locally free of rank $n$, $\det_n$ is an invertible sheaf, and such determinants of pushforwards of Poincaré-type bundles produce the theta line bundle used in the quasi-projectivity of relative Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesDet.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

noncomputable abbrev presheafExteriorPower (n : ℕ) : X.PresheafOfModules ⥤ X.PresheafOfModules :=
  _root_.PresheafOfModules.exteriorPowerFunctor X.sheaf.obj n

noncomputable def exteriorPower (n : ℕ) : X.Modules ⥤ X.Modules :=
  Modules.toPresheafOfModules X ⋙ presheafExteriorPower X n ⋙
    _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

variable {X} in

noncomputable abbrev det (n : ℕ) (M : X.Modules) : X.Modules := (exteriorPower X n).obj M

variable {X} in
@[simp] lemma exteriorPower_obj (n : ℕ) (M : X.Modules) :
    (exteriorPower X n).obj M =
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((presheafExteriorPower X n).obj M.val) := rfl

end AlgebraicGeometry.Scheme.Modules


