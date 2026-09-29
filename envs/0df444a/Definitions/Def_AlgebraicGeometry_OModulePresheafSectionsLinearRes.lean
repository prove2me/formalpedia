-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
-- name    : AlgebraicGeometry_OModulePresheafSectionsLinearRes
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/3c55c21e-93f5-5117-a414-fd185f249ba0
-- title:
--   Restriction maps of an O-module presheaf as linear maps
-- statement:
--   Throughout, $R$ is a commutative ring, $V$ a scheme, $\pi\colon V \to \operatorname{Spec} R$ a morphism, and $F$ an element of the project's structure `OModulePresheaf` for $\pi$: a family of types $F.obj\,U$ indexed by the opens $U$ of $V$, each an abelian group carrying both an $R$-module structure and a $\Gamma(V,U)$-module structure forming a scalar tower over $R$ (via the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$), together with $R$-linear restriction maps $F.res\,h \colon F.obj\,U' \to F.obj\,U$ for $h \colon U \le U'$ satisfying $F.res\,h(a \cdot x) = a|_U \cdot F.res\,h(x)$, $F.res(\mathrm{id}) = \mathrm{id}$ and compatibility with composition.
--
--   For opens $U \le U'$, `moduleRestrict` is the $\Gamma(V,U')$-module structure on $F.obj\,U$ obtained by restriction of scalars along the ring homomorphism $\Gamma(V,U') \to \Gamma(V,U)$ given by the structure presheaf of $V$, so that $a \cdot x = a|_U \cdot x$ for $a \in \Gamma(V,U')$ and $x \in F.obj\,U$; this is recorded as the equation `moduleRestrict_smul_def`. With that structure in place, `resₗ` packages the restriction map $F.res\,h$ as a $\Gamma(V,U')$-linear map $F.obj\,U' \to F.obj\,U$, its additivity coming from $R$-linearity of $F.res\,h$ and its semilinearity-turned-linearity from the `res_smul` field of `OModulePresheaf`. The lemma `resₗ_apply` states that the underlying function of `resₗ h` is $F.res\,h$. Nothing beyond these structural identifications is asserted here: the content is the observation that a restriction map, which is only semilinear over the sections on the smaller open, becomes honestly linear over $\Gamma(V,U')$ once the target is viewed as a $\Gamma(V,U')$-module by restriction of scalars.
--
--   **Relation to Mathlib.** The scalar restriction is Mathlib's `Module.compHom` applied to the presheaf restriction ring map; the ambient notion `OModulePresheaf` of a presheaf of modules over the structure sheaf, indexed by the opens of a scheme and carrying a compatible $R$-module structure, is the project's own.
--
--   **Where it is used.** This is the shape in which Mathlib's localisation and finiteness API can be applied to restriction along an inclusion $D(f) \subseteq U$ of a basic open into an affine open: the statement that such a restriction map is a localisation at the powers of $f$ for a quasi-coherent $F$ is a linearity statement over $\Gamma(V,U)$. It feeds the finiteness results for the ordered affine Čech complex used in the coherent-cohomology input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)

@[reducible] def moduleRestrict {U U' : V.Opens} (h : U ≤ U') : Module Γ(V, U') (F.obj U) :=
  Module.compHom (F.obj U) (V.presheaf.map (homOfLE h).op).hom

def resₗ {U U' : V.Opens} (h : U ≤ U') :
    letI := F.moduleRestrict h
    F.obj U' →ₗ[Γ(V, U')] F.obj U :=
  letI := F.moduleRestrict h
  { toFun := F.res h
    map_add' := map_add _
    map_smul' := fun a x => F.res_smul h a x }

theorem resₗ_apply {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
    letI := F.moduleRestrict h
    F.resₗ h x = F.res h x := rfl

theorem moduleRestrict_smul_def {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : F.obj U) :
    letI := F.moduleRestrict h
    a • x = (V.presheaf.map (homOfLE h).op).hom a • x := rfl

end AlgebraicGeometry.OModulePresheaf

end


