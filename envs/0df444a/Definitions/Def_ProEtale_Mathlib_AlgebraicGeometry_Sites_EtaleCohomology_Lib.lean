-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology_Lib
-- name    : ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:29.181966+00:00
-- url     : https://prove2.me/theorems/74d4eceb-7b91-589d-8533-2806fa84614f
-- title:
--   The inverse system of étale cohomology groups with coefficients in the constant sheaves $\mathbb Z/\ell^n$
-- statement:
--   This file continues the published file on étale cohomology of constant sheaves. Fix a scheme $X$, a natural number $\ell$ (in applications a prime) and a degree $m$.
--
--   **Definitions.**
--
--   - The inverse system of abelian groups $n \mapsto \mathbb Z/\ell^n\mathbb Z$, with transition maps the reductions $\mathbb Z/\ell^{n+1} \to \mathbb Z/\ell^n$.
--   - The inverse system of étale cohomology groups, with transition maps induced by the reductions:
--   $$n \longmapsto H^m(X_{\mathrm{et}}, \mathbb Z/\ell^n\mathbb Z) = \operatorname{Ext}^m\big(\underline{\mathbb Z}, \underline{\mathbb Z/\ell^n\mathbb Z}\big).$$
--   Here $\underline{A}$ denotes the constant sheaf with value $A$ on the small étale site of $X$, and $\operatorname{Ext}$ is computed in the category of abelian sheaves.
--
--   **Results.**
--
--   1. The category of abelian groups in universe $u+1$ has filtered colimits of size $u$ and satisfies AB5 for size $u$.
--   2. The value of the cohomology system at level $n$ is, by definition, Mathlib's sheaf cohomology $H^m$ of the constant sheaf $\underline{\mathbb Z/\ell^n\mathbb Z}$.
--
--   This is the étale side of the $\ell$-adic comparison: under a finiteness hypothesis, $\ell$-adic cohomology is the inverse limit of this system.
--
--   **Formalization Note** The declarations are `AlgebraicGeometry.zmodAbSystem ℓ : ℕᵒᵖ ⥤ AddCommGrpCat.{u+1}` (values `ULift (ZMod (ℓ ^ n))`), `AlgebraicGeometry.Scheme.etaleCohomologySystem X ℓ m`, defined as `zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab` followed by `extFunctorObj (etaleConstantUnit X) m`, and `etaleCohomologySystem_obj`, which holds by `rfl` with `Sheaf.H`. Coefficients are lifted to universe `u + 1` because the small étale site of a scheme in universe `u` is a large category. The file places no primality assumption on `ℓ`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/Sites/EtaleCohomology.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology of the same module.

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Functor.OfSequence
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology

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

instance inst_MathlibAlgebraicGeometrySitesEtaleCohomology_L42 : HasFilteredColimitsOfSize.{u, u + 1} Ab.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

instance inst_MathlibAlgebraicGeometrySitesEtaleCohomology_L45 : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}

namespace AlgebraicGeometry

/-- The inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian groups, with the reduction maps as
transition maps. -/
noncomputable def zmodAbSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.ofSequence
    (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)).leftOp


namespace Scheme

variable (X : Scheme.{u})


/-- The inverse system `n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)` of étale cohomology groups of the constant
sheaves `ℤ/ℓⁿℤ` on the small étale site of `X`, with transition maps induced by the
reduction maps. Its value at `n` is
`AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab).obj
  (AddCommGrpCat.of (ULift (ZMod (ℓ ^ n))))) m)`. -/
noncomputable def etaleCohomologySystem (ℓ : ℕ) (m : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙
    extFunctorObj (etaleConstantUnit X) m

/-- The value of `etaleCohomologySystem` at level `n` is the étale cohomology
`Hᵐ(X_ét, ℤ/ℓⁿℤ)` in the sense of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem etaleCohomologySystem_obj (ℓ m n : ℕ) :
    (etaleCohomologySystem X ℓ m).obj (op n) =
      AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) m) :=
  rfl

end Scheme

end AlgebraicGeometry


