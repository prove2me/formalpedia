-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_StatementF
-- name    : Formalism_YangianSpanCharacter_StatementF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:58.180265+00:00
-- url     : https://prove2.me/theorems/fef04417-1032-4042-84a1-79d956b4a738
-- title:
--   Statement F
-- statement:
--   Definitions and structural lemmas for Statement F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/StatementF.lean

import Definitions.Def_Formalism_YangianSpanCharacter_ExchangeGen
import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.YangianSpanCharacter.F
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
def blk {A : Type*} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun k l => M (i, k) (j, l)
def sc {A : Type*} [Ring A] (x : A) : Matrix (Fin 2) (Fin 2) A := Matrix.diagonal fun _ => x
def PlusFrame : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y Ya : 𝕜, Y ∈ S → Ya ∈ S → Y - Ya ≠ 0 → Y - Ya - 1 ≠ 0 →
      let D := Y - Ya
      let tn := E1 (t Y) * ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A))
      let l := lf t τinv Y
      let M : Matrix (Fin 2) (Fin 2) A := !![algebraMap 𝕜 A D, 0; -l, algebraMap 𝕜 A (D - 1)]
      let N : Matrix (Fin 2) (Fin 2) A := !![(D - 1) • l, -1; 0, D • l]
      let G : Matrix (Fin 2) (Fin 2) A := !![1, 0; lf t τinv Ya, 1]
      let Ginv : Matrix (Fin 2) (Fin 2) A := !![1, 0; -lf t τinv Ya, 1]
      blk tn 1 1 = (D - 1)⁻¹ • (sc (t Y 1 1) * M) ∧
      blk tn 1 0 = (D - 1)⁻¹ • (sc (t Y 1 1) * N) ∧
      G * Ginv = 1 ∧
      G * (sc (t Y 1 1) * M) =
        sc (t Y 1 1) * !![algebraMap 𝕜 A D, 0; 0, algebraMap 𝕜 A (D - 1)] * G ∧
      N * Ginv = M * Ginv *
        !![l - eta t τinv Y Ya, -algebraMap 𝕜 A D⁻¹; 0, l + eta t τinv Y Ya]
def MinusFrame : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y Yb : 𝕜, Y ∈ S → Y + 1 ∈ S → Yb ∈ S → Yb + 1 ∈ S → Yb - 1 ∈ S →
      Yb - Y ≠ 0 → Yb - Y - 1 ≠ 0 →
      let d := Yb - Y
      let tn := ((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) *
        E1 (t Y)
      let τn : Matrix (Fin 2) (Fin 2) A := !![d • t Y 1 1, 0; -t Y 0 1, (d - 1) • t Y 1 1]
      let Ln : Matrix (Fin 2) (Fin 2) A :=
        !![lf t τinv Y, 0; -((d - 1)⁻¹ • hf τinv q Y), lf t τinv Y]
      let Gb : Matrix (Fin 2) (Fin 2) A := !![1, 0; mf t τinv Yb, 1]
      blk tn 1 1 = (d - 1)⁻¹ • τn ∧
      blk tn 1 0 = (d - 1)⁻¹ • !![d • t Y 1 0, 0; -t Y 0 0, (d - 1) • t Y 1 0] ∧
      τn * Ln = !![d • t Y 1 0, 0; -t Y 0 0, (d - 1) • t Y 1 0] ∧
      Gb * τn = !![d • t Y 1 1, 0; 0, (d - 1) • t Y 1 1] * Gb ∧
      Gb * Ln = !![lf t τinv Y, 0; -((d - 1)⁻¹ • hf τinv q (Yb - 1)), lf t τinv Y] * Gb
end Formalism.YangianSpanCharacter.F


