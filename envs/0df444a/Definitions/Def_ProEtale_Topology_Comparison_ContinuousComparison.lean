-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_ContinuousComparison
-- name    : ProEtale_Topology_Comparison_ContinuousComparison
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:26:21.792491+00:00
-- url     : https://prove2.me/theorems/44d9c41f-97c9-534a-8fda-d7be7c4e7cfb
-- title:
--   Continuous étale cohomology of an inverse system of sheaves
-- statement:
--   For an inverse system $(F_n)$ of abelian sheaves on the small étale site of $S$, `continuousH S F i` is the group $\operatorname{Ext}^i$ from the constant system on the constant sheaf $\mathbb Z$ to $(F_n)$, computed in the abelian category of inverse systems. Since maps out of that object compute $H^0(S_{\text{ét}}, \varprojlim F_n)$, these groups are the right derived functors of $(F_n) \mapsto H^0(S_{\text{ét}}, \varprojlim F_n)$, which is how the paper defines continuous étale cohomology after Jannsen.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 5.6.1. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/ContinuousComparison.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_WContractible
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Topology_Comparison_Affine
import Definitions.Def_ProEtale_Topology_Comparison_CohomologyComparison
import Definitions.Def_ProEtale_Topology_Comparison_RepleteExact
import Definitions.Def_ProEtale_Topology_Comparison_WeaklyContractible
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Comparison of continuous étale cohomology with pro-étale cohomology

Let `S` be a scheme and let `(Fₙ)ₙ` be an inverse system of abelian sheaves on the small
étale site of `S` with epimorphic transition maps. We compare the *continuous étale
cohomology* of `(Fₙ)ₙ` in the sense of Jannsen with the pro-étale cohomology of the
sheaf `lim ν^* Fₙ` on the pro-étale site (BS, Proposition 5.6.2; blueprint
`thm:comparison-continuous`).

## Definitions

- `AlgebraicGeometry.Scheme.continuousH F n`: continuous étale cohomology of the inverse
  system `F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab`, defined as the `Ext`-group
  `Ext (Δℤ) F n` in the abelian category of inverse systems, from the constant system on
  the constant sheaf `ℤ` (blueprint `def:continuous-etale-cohomology`). Since
  `Hom(Δℤ, F) ≅ Γ(X, lim Fₙ)` (see `continuousHZeroAddEquiv`), this `Ext`-group is the
  `n`-th right derived functor of `(Fₙ)ₙ ↦ Γ(X, lim Fₙ)` in the sense of Jannsen.

## Main result

- `AlgebraicGeometry.Scheme.nonempty_continuousH_addEquiv_H_limit`:
  `H^i_cont(X, (Fₙ)) ≅ H^i(X_proét, lim ν^* Fₙ)` for systems with epimorphic transition
  maps.

The proof is by dimension shifting. Embed `F` into an injective system `I` with quotient
`Q`. Injective systems have split epimorphic transitions and injective levels
(`Proetale.Mathlib.CategoryTheory.Abelian.SequentialSystem`), so `lim ν^* Iₙ` is acyclic:
by the Milnor sequence (`ProEt.shortExact_telescope`) this reduces to acyclicity of
countable products of the sheaves `ν^* Iₙ` (`Ext.subsingleton_pi`,
`ProEt.epi_piMap`), which in turn follows from the levelwise comparison with étale
cohomology (`ProEt.mapExt_bijective_sheafPullback`). The functor `lim ν^* (-)` sends the
short exact sequence `0 → F → I → Q → 0` to a short exact sequence
(`ProEt.shortExact_limMap`, using repleteness of the pro-étale topos via weakly
contractible objects). In degree `0` the comparison map is induced by the adjunction
`const ⊣ lim` and full faithfulness of `ν^*`; in degree `1` it is constructed from the
five-term exact sequences (`Ext.oneEquivOfHomEquiv`), and in higher degrees by the
connecting isomorphisms (`Ext.connectingEquiv`) and induction applied to `Q`.
-/

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

namespace ProEt

/-! ### Instances for the category of inverse systems -/

instance : HasProductsOfShape ℕ (Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  Sheaf.instHasLimitsOfShape

instance : EnoughInjectives (Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

instance : EnoughInjectives (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  inferInstance

instance : HasExt.{u + 1} (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  hasExt_of_enoughInjectives _


end ProEt


/-- **Continuous étale cohomology** (Jannsen; blueprint
`def:continuous-etale-cohomology`): for an inverse system `F` of abelian sheaves on the
small étale site of `S`, this is the `Ext`-group from the constant system on the constant
sheaf `ℤ` to `F` in the category of inverse systems. Since morphisms out of that object
compute `Γ(X, lim Fₙ)` (see `continuousHZeroAddEquiv`), these `Ext`-groups are the right
derived functors of `(Fₙ)ₙ ↦ Γ(X, lim Fₙ)`. -/
noncomputable abbrev continuousH (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1})
    (n : ℕ) : Type (u + 1) :=
  Ext ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) F n


end AlgebraicGeometry.Scheme


