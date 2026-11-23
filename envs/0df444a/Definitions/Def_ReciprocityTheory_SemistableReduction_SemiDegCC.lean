-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
-- name    : ReciprocityTheory_SemistableReduction_SemiDegCC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:55.449799+00:00
-- url     : https://prove2.me/theorems/e7a9d8e3-d7a0-4695-88ae-be8f3a20b889
-- title:
--   Semi Deg CC
-- statement:
--   Definitions and structural lemmas for Semi Deg CC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCC.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Definitions.Def_Lemmata_MiscLemmasR_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
def intInv {K : Type} [Field K] [NumberField K] (c : K →+* K) : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom c
def cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K) :
    Submodule (𝓞 K) K := Bl.ThirdBlockLemmaC.goal1 c C
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx


