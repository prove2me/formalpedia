-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundOfConditionsWithErrorForFrames
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundOfConditionsWithErrorForFrames
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:55.749472+00:00
-- url     : https://prove2.me/theorems/0d316593-6859-47fc-abff-4388d3abe49c
-- title:
--   Slope Bound Of Conditions With Error For Frames
-- statement:
--   Definitions and structural lemmas for Slope Bound Of Conditions With Error For Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundOfConditionsWithErrorForFrames.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
namespace Formalism.L2.Indef.Tree
def addY (C2 : ℝ) (P : SlopeBoundParameters) : ℝ := C2 * P.f * P.m * P.b * Real.log P.x
def slopeBoundConstantWithError (Ca Cb Cf Cc C1 Cm C2 : ℝ) : ℝ := slopeBoundConstant Ca Cb Cf Cc C1 Cm + 16 * C2
section Leaves
variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}
def LeafMeans4 (Ca Cb C2 : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.X ∧ -F.X ≤ (∑ c, F.sl c) / (Fintype.card F.ι : ℝ) ∧
    F.T * F.X ≤ Ca * P.LL0 * (F.U + F.E0) ∧
    F.T * F.cc ≤ Cb * P.LL0 * (F.U + F.E0) + F.T * F.Qcc + addY C2 P
end Leaves
def CompParams4 {K : Type} [Field K] [NumberField K] [StarRing K] (Ca Cb C2 : ℝ) {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P) :
    Prop :=
  2 ≤ F.DY ∧ 20 * F.DY ≤ F.T ∧ F.DY ^ 2 / F.T ≤ 1 / 28 ∧ F.DY * F.ρ ≤ 1 / 28 ∧ 0 ≤ F.cs ∧ 0 < F.Bn ∧ 0 < F.δ' ∧
  F.cs * (6 * F.DY + 10 + F.T * (F.z + 2 * F.ρ)) + (F.A * Real.log (max F.A 1) + 4) + F.R1 + 2 * F.z * F.R2 +
    F.PPf + F.e1 Ca + F.e2 Cb ≤ P.b / 8 + addY C2 P
def exampleSlopeParameters : SlopeBoundParameters :=
  { Pl := Unit, fPl := inferInstance, x := Real.exp 1, eps := 3, rd := 4, v := 2, dN := 1, dimNeZero := inferInstance,
    χ := 1, Z := 0, logOmK := 0, logOm := 0, f := 1, m := 1, k := 1, S := 0, η := 0, R := 0, PPp := 0, PPpp := 0,
    PP := 0, PPT := 6, Zpg := 0, nV := 0, Nr := 0, g12 := 1 }
def exampleFac4 (K : Type) [Field K] [NumberField K] [StarRing K] (cc R1 : ℝ) : SlopeBoundLiftData K exampleSlopeParameters :=
  { w := fun _ => 0, w0 := fun _ => 0, c1 := fun _ => 0, ua := fun _ => 1, kap := 1, q' := 1, pq := 1, ι := Unit,
    fι := inferInstance, nι := inferInstance, DY := 2, A := 1, cs := 0, X := 0, cc := cc, E0 := 0, Qcc := 0, ρ := 0,
    R1 := R1, R2 := 0, Bn := 1, δ' := 1, h := fun _ => 0, sl := fun _ => 0, δc := fun _ => 1, dc := fun _ => 1,
    degc := fun _ => 0, PPf := 0, mv := 0, muU := 0, nA := 0, nB := 0, nN := 0, XA := fun _ => 1, XB := fun _ => 1,
    XN := fun _ => 1, LA := ⊥, LB := ⊥, NN := ⊥, Mk := ⊥, φ := 0, e := 0, g := 1, PPh := 0, abelian₂ := 0, δ := 0, o' := 0,
    n2 := 0 }
end Formalism.L2.Indef.Tree


