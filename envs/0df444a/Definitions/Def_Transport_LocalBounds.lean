-- Prove2me | Definitions.Def_Transport_LocalBounds
-- name    : Transport_LocalBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:25.754399+00:00
-- url     : https://prove2.me/theorems/761046cb-93d9-4aba-b1d2-67b0324618b6
-- title:
--   Local Bounds
-- statement:
--   Definitions and structural lemmas for Local Bounds, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean

import Definitions.Def_Transport_Geometry
set_option autoImplicit false
namespace RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
inductive DenominatorTerm where
  | r | v | d
def denominatorPower (term : DenominatorTerm) (s z : ℝ) : ℝ :=
  match term with
  | .r => 4 - 6 * s - 6 * z
  | .v => -6 * z
  | .d => -s
def denominatorCap (term : DenominatorTerm) (p : ℝ) : ℝ :=
  match term with
  | .r => -56 / 25 + 3 * p / 2
  | .v => -99 / 100
  | .d => -boundary p
inductive GoodTerm where
  | dv | dw | dvw | vw | r | strictFamily
def goodPower (term : GoodTerm) (s w z : ℝ) : ℝ :=
  match term with
  | .dv => -s - 6 * z
  | .dw => -s - w
  | .dvw => -s - w - 6 * z
  | .vw => -w - 6 * z
  | .r => 4 - 6 * s - 6 * z
  | .strictFamily => 1 - s - w - 6 * z
def goodCap (p : ℝ) : ℝ := -363 / 200 + p / 4
inductive RamifiedTerm where
  | r | strictFamily | j1 | j2 | j3First | j3Second | j4 | j5
def ramifiedPower (term : RamifiedTerm) (s w z : ℝ) : ℝ :=
  match term with
  | .r => 4 - 6 * s - 6 * z
  | .strictFamily => 1 - s - w
  | .j1 => -s - w
  | .j2 => 3 / 2 - 3 * s
  | .j3First => 2 - 3 * s - w
  | .j3Second => 2 - 4 * s
  | .j4 => 5 / 2 - 4 * s - w
  | .j5 => 3 - 6 * s
def ramifiedCap (p : ℝ) : ℝ := -33 / 40 + p / 4
inductive PrincipalTerm where
  | inverse | sixthPower | mixed | numerator
def principalPower (term : PrincipalTerm) (s w z : ℝ) : ℝ :=
  match term with
  | .inverse => -s
  | .sixthPower => -6 * z
  | .mixed => 4 - 5 * s - 6 * z
  | .numerator => 1 - w - 6 * z
def goodTailDecay (p : ℝ) : ℝ := 163 / 200 - p / 4
inductive SmallRamifiedTerm where
  | strictFamily | j1 | j2OrJ3First | j3SecondOrJ4 | j5 | r
def smallRamifiedPower (term : SmallRamifiedTerm) (s : ℝ) : ℝ :=
  match term with
  | .strictFamily => 1 / 2
  | .j1 => -1 / 2
  | .j2OrJ3First => 3 / 2 - 2 * s
  | .j3SecondOrJ4 => 2 - 3 * s
  | .j5 => 3 - 5 * s
  | .r => 4 - 5 * s - 6 * (17 / 50)
end
end RH.Transport.LocalBounds


