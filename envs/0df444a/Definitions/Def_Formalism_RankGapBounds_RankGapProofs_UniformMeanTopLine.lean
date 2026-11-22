-- Prove2me | Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
-- name    : Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:57.562981+00:00
-- url     : https://prove2.me/theorems/d0bd2971-d8d5-4d18-b273-0b09c092a30d
-- title:
--   Uniform Mean Top Line
-- statement:
--   Definitions and structural lemmas for Uniform Mean Top Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/UniformMeanTopLine.lean

import Definitions.Def_Formalism_RankGapBounds_UniformMeanBound
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.RankGapBounds.UniformMeanTopLine
open Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
def SlopesWith (Lw : ∀ u0, W u0 → ℝ) : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - Lw u0 u ≤ D.muN u0 u
def K7v4 : ℝ :=
  C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L) + 1
end
def C0 : Consts := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
noncomputable def D0 : Data Unit (fun _ => Unit) Unit 1 1 where
  x := 1
  ε := 0
  a := 1
  b := 1
  b' := 0
  k := 1
  L := 0
  La := 0
  B0 := 0
  Nc := 0
  gam := 0
  LpL := 0
  v := π
  lg := 0
  logGam := 0
  aT := fun _ => 1
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 1
  muMaxN := fun _ _ => 1
  h := fun _ _ => -1
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 2
  muMinCC := fun _ => 2
  Fo := fun _ => 2
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0
end Formalism.RankGapBounds.UniformMeanTopLine


