-- Prove2me | Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
-- name    : ProEtale_FiniteFields_Etale_IndEtaleStructural
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:36:32.699588+00:00
-- url     : https://prove2.me/theorems/a2ae144e-a44b-522f-b671-82b72ea88f13
-- title:
--   Étale ring maps as a morphism property stable under cobase change (auxiliary for ind-étale structure)
-- statement:
--   This file belongs to a module on structural properties of ind-étale ring maps, given by a literal filtered-colimit presentation. According to its docstring, the module proves flatness and right cancellation for such maps.
--
--   The part extracted here contains only auxiliary private declarations:
--
--   1. The class of étale ring homomorphisms, viewed as a class of morphisms in the category of commutative rings in universe $u$.
--   2. The fact that this class is stable under cobase change: if $R \to S$ is étale and $R \to R'$ is arbitrary, then $R' \to R' \otimes_R S$ is étale.
--
--   These are used in the module's proofs of the structural properties of ind-étale maps. The flatness and cancellation results themselves are not part of this file.
--
--   **Formalization Note** Both declarations are `private`: `FiniteFields.Etale.etaleMorphismProperty := RingHom.toMorphismProperty RingHom.Etale` and an instance of `IsStableUnderCobaseChange`, derived from `RingHom.Etale.isStableUnderBaseChange`. The file was ported from a Weil-conjectures formalization (`WeilConjectures.Etale.IndEtaleStructural`). It imports the published file `FiniteFields_Etale_IndEtale`, which provides the presentation-based notion of ind-étale.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/FiniteFields/Etale/IndEtaleStructural.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 The Weil Conjectures formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures formalization contributors
-/
-- Ported from finite_fields (`WeilConjectures.Etale.IndEtaleStructural`, Lean 4.31) to Lean 4.33.1 / Mathlib 0df444a.
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u


/-!
# Structural properties of ind-etale ring maps

This module proves flatness and right cancellation for the literal filtered-colimit presentation
from `IndEtale.lean`.  The cancellation proof first handles a finite etale source, then assembles
those witnesses through filtered categorical pushouts and flattens `ind (ind etale)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace FiniteFields
namespace Etale


variable {A B C E : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing E]


private def etaleMorphismProperty : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty RingHom.Etale


private instance inst_FiniteFieldsEtaleIndEtaleStructural_L257 : etaleMorphismProperty.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := RingHom.Etale)).mpr
    RingHom.Etale.isStableUnderBaseChange

/-! The remaining global layer is the filtered diagram of pushouts `B ⊔_{Pᵢ} C`.  The
following generic construction proves directly that its colimit is the literal object `C`. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


end Etale
end FiniteFields


