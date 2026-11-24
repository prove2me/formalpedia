-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:35.705947+00:00
-- url     : https://prove2.me/theorems/3b512081-dea8-4718-9d9f-b85560101997
-- title:
--   Chart Algebra
-- statement:
--   Definitions and structural lemmas for Chart Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}
noncomputable def chartCoeffHom (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    Γ(X, W) →+* Γ(Y, V) :=
  (W.topIso.inv ≫ (g ≫ (AffineSpace n W.toScheme ↘ W.toScheme)).appTop ≫ V.topIso.hom).hom
noncomputable def chartVar (g : V.toScheme ⟶ AffineSpace n W.toScheme) (j : n) : Γ(Y, V) :=
  V.topIso.hom.hom (g.appTop.hom (AffineSpace.coord (S := W.toScheme) j))
noncomputable def chartEvalHom (_hW : IsAffineOpen W) (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    MvPolynomial n Γ(X, W) →+* Γ(Y, V) :=
  MvPolynomial.eval₂Hom (chartCoeffHom g) (chartVar g)
@[reducible]
noncomputable def chartAlgebra (hW : IsAffineOpen W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) :=
  (chartEvalHom hW g).toAlgebra
noncomputable def affineOpenIsoSpec {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W') :
    W'.toScheme ≅ Spec Γ(X', W') :=
  haveI : IsAffine W'.toScheme := hW
  W'.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso W'.topIso.symm.op
noncomputable def affineSpaceOpenIsoSpecMvPolynomial {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W')
    (m : Type u) :
    AffineSpace m W'.toScheme ≅ Spec (CommRingCat.of (MvPolynomial m Γ(X', W'))) :=
  (AffineSpace.functor.obj (Opposite.op m)).mapIso (affineOpenIsoSpec hW) ≪≫
    AffineSpace.SpecIso m Γ(X', W')
end FunctorialResolution.EmbeddedResolution


