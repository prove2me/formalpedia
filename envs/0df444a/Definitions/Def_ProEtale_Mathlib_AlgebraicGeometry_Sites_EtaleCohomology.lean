-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology
-- name    : ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:11:04.57708+00:00
-- url     : https://prove2.me/theorems/63598e98-ac3b-4e0c-8289-a8bd1f236405
-- title:
--   Abelian sheaves on the small étale site; the constant sheaf $\mathbb{Z}$
-- statement:
--   The category of abelian sheaves on the small étale site of a scheme is a Grothendieck abelian category, and `etaleConstantUnit S` denotes the constant sheaf $\mathbb Z$ on it, the object out of which $\operatorname{Ext}$ groups compute cohomology.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/Sites/EtaleCohomology.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# The étale cohomology system of the constant sheaves `ℤ/ℓⁿℤ`

For a scheme `X`, a prime `ℓ` and a cohomological degree `m`, we spell out the inverse
system

`n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)`

of étale cohomology groups of the constant sheaves `ℤ/ℓⁿℤ` on the small étale site of
`X`, with transition maps induced by the reduction maps `ℤ/ℓⁿ⁺¹ℤ → ℤ/ℓⁿℤ`. This is the
étale side of the `ℓ`-adic comparison: `ℓ`-adic cohomology
(`AlgebraicGeometry.Scheme.EllAdicCohomology`) is, under a finiteness hypothesis, the
inverse limit of this system.

The degree-`m` étale cohomology of the constant sheaf on `M` is
`Ext ((constantSheaf X.smallEtaleTopology Ab).obj (.of (ULift ℤ)))
  ((constantSheaf X.smallEtaleTopology Ab).obj (.of M)) m`,
which is mathlib's `CategoryTheory.Sheaf.H` of the constant sheaf, and the functoriality
in the system direction is `extFunctorObj`, which agrees with mathlib's
`CategoryTheory.Sheaf.H.map`.

## Main definitions

* `AlgebraicGeometry.zmodAbSystem`: the inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian
  groups, with the reduction maps as transition maps.
* `AlgebraicGeometry.Scheme.etaleCohomologySystem`: the inverse system
  `n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)` of étale cohomology groups.
-/

universe u

open CategoryTheory Limits Opposite Abelian


namespace AlgebraicGeometry


namespace Scheme

variable (X : Scheme.{u})

/-- The category of abelian sheaves on the small étale site of `X : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. In particular it has enough
injectives and `Ext`-groups (`HasExt`). -/
instance isGrothendieckAbelianSheafSmallEtaleTopologyAb :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- The constant abelian sheaf `ℤ` on the small étale site (the unit for sheaf
cohomology, see `CategoryTheory.Sheaf.H`). -/
noncomputable abbrev etaleConstantUnit : Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  (constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))


end Scheme

end AlgebraicGeometry


