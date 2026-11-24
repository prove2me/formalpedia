-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:50.281749+00:00
-- url     : https://prove2.me/theorems/7214c562-4f7c-4f99-a198-ea4246266781
-- title:
--   Exists Different Pair
-- statement:
--   Definitions and structural lemmas for Exists Different Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
namespace GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
abbrev Int' (E : Type) [Field E] : Subring E := (algebraMap (𝓞 E) E).range
def std (E : Type) [Field E] : Submodule (𝓞 E) (Fin 2 → E) :=
  Submodule.span (𝓞 E) {![0, 1], ![1, 1]}
abbrev dOne (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)
def splitJ (E : Type) [Field E] : Matrix (Fin 8) (Fin 8) E :=
  !![0, 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, -1]
def splitLat (E : Type) [Field E] [NumberField E] : Submodule (𝓞 E) (Fin 8 → E) :=
  Submodule.pi Set.univ fun i =>
    ((![dInv E 1, dOne E, 1, 1, 1, 1, 1, 1] : Fin 8 → FractionalIdeal (𝓞 E)⁰ E) i : Submodule (𝓞 E) E)
def splitP (E : Type) [Field E] : Matrix (Fin 8) (Fin (1 + 1)) E :=
  !![1, 0; 0, 0; 0, 0; 0, 0; 0, 0; 0, 0; 0, 0; 0, 1]
def splitC (σ : E →+* E) (g : ℕ) (a b : E) : E := -(g * (a * σ a + b * σ b))
def splitQ (σ : E →+* E) (g : ℕ) (a b : E) : Matrix (Fin 8) (Fin (1 + 1)) E :=
  !![1, 0; g * splitC σ g a b, 0; g * a, 0; g * a, 0; g * b, 0; g * b, 0; 0, g; 0, 1 + g]
end GlobalTheory.SgGlob.Inhab


