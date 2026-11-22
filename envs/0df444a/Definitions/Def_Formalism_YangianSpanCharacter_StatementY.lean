-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_StatementY
-- name    : Formalism_YangianSpanCharacter_StatementY
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:14.455833+00:00
-- url     : https://prove2.me/theorems/4f0d15d3-4702-4577-a86d-e8627b424f39
-- title:
--   Statement Y
-- statement:
--   Definitions and structural lemmas for Statement Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/StatementY.lean

import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
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
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
def lf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 1 0
def mf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 0 1
def hf (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (u : 𝕜) : A := q u • (τinv u * τinv (u + 1))
def eta (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (lf t τinv u - lf t τinv v)
def mu (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (mf t τinv u - mf t τinv v)
def ModHyp (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜) : Prop :=
  (∀ (u v : 𝕜) (i j k l : Fin 2),
      (u - v) • (t u i j * t v k l - t v k l * t u i j) = t u k j * t v i l - t v k j * t u i l) ∧
    (∀ Y : 𝕜, (t (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J A * t Y = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ u ∈ S, t u 1 1 * τinv u = 1 ∧ τinv u * t u 1 1 = 1) ∧
    (∀ u v : 𝕜, Commute (t u 1 1) (t v 1 1)) ∧
    (∀ u v : 𝕜, Commute (t u 1 0) (t v 1 0))
def MShift : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S → mf t τinv (Y + 1) = t Y 0 1 * τinv Y
def QuasiDet : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S → t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0 = q Y • τinv (Y + 1)
def Y1 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * lf t τinv v - lf t τinv v * t u 1 1 = -(t u 1 1 * eta t τinv u v)
def Y1' : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v
def Y2 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      lf t τinv u * lf t τinv v - lf t τinv v * lf t τinv u =
        eta t τinv u v * (lf t τinv u - lf t τinv v)
def Y3 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → u + 1 ∈ S → u - 1 ∈ S → v ∈ S → v + 1 ∈ S → u ≠ v →
      (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
        hf τinv q v - hf τinv q (u - 1)
def ModHypModel : Prop :=
  ModHyp (𝕜 := ℚ) (A := ℚ) (fun _ => !![2, 1; 1, 1]) (fun _ => 1) (fun _ => 1) Set.univ
end Formalism.YangianSpanCharacter.Y


