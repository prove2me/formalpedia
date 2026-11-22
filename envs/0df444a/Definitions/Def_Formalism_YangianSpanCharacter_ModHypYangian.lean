-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_ModHypYangian
-- name    : Formalism_YangianSpanCharacter_ModHypYangian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:03.670313+00:00
-- url     : https://prove2.me/theorems/601bdd22-3363-4d1c-8331-f3170e6615cf
-- title:
--   Mod Hyp Yangian
-- statement:
--   Definitions and structural lemmas for Mod Hyp Yangian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/ModHypYangian.lean

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.YangianSpanCharacter.Y
open Matrix Formalism.YangianSpanCharacter.T
def GaussDecomp : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S →
      t Y = !![1, mf t τinv (Y + 1); 0, 1] * !![q Y • τinv (Y + 1), 0; 0, t Y 1 1] *
        !![1, 0; lf t τinv Y, 1]
def tE (u : ℚ) : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℚ) :=
  !![!![u + 1, 0; 0, u], !![0, 1; 0, 0]; !![0, 0; 1, 0], !![u, 0; 0, u + 1]]
def τE (u : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![u⁻¹, 0; 0, (u + 1)⁻¹]
def qE (Y : ℚ) : ℚ := Y * (Y + 2)
def SE : Set ℚ := {u | u ≠ 0 ∧ u + 1 ≠ 0}
def ModHypYangian : Prop :=
  ModHyp tE τE qE SE ∧ tE 0 1 1 ≠ tE 1 1 1 ∧
    tE 0 0 1 * tE 0 1 0 - tE 0 1 0 * tE 0 0 1 ≠ 0 ∧ (1 : ℚ) ∈ SE
end Formalism.YangianSpanCharacter.Y


