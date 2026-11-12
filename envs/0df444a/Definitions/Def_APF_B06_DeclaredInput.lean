-- Prove2me | Definitions.Def_APF_B06_DeclaredInput
-- name    : APF_B06_DeclaredInput
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-06T20:54:27.907037+00:00
-- url     : https://prove2.me/theorems/67b0b53b-07e8-4fa1-b10e-c6f0ec36b828
-- title:
--   Declared input — B06 — Occupancy
-- statement:
--   The world is instantiated: distinctions are actually drawn, including irreducibly joint distinctions. For at least one actually instantiated irreducibly joint structural alignment o in its original context Gamma, let S be its entire nonempty carried family. In addition to the original held-family bound kappa_Gamma(S) <= C_Gamma, there exist a whole protocol p in the unchanged original joint class J_Gamma(S) and an original raw input x such that the same complete p belongs to Cont_Gamma(x). The original full task conditions, support, whole-resource accounting, calibration and context budget are retained.
-- source:
--   APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-10-04.1; SHA-256 bb3b59f6011dd70c5d34c9c830ab65aad0a224b11e26d4d438c4e1ab2ad445c4; declared input B06.

import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic

/-! B06 is exactly the amended ORIGINAL joint occupancy input.
This uses R1's exact B01 quotient definition, not a duplicate or alternate one.
The shared source correspondence binds J to the unchanged original joint class,
wholeResource/calibration to the same original complete process account, and
actualJoint to actual irreducibly joint alignments. Support/task metadata stays
in those original source referents; no generic JointService/SourceB06 is assumed.
No T, same-use boundary, qualified admission or all-protocol availability is added.
Source: Supplement v9.27:1824-1876; author B06 current_wording.
-/
set_option autoImplicit false
namespace APFB06

abbrev Task {X Q : Type*} (Cont : X → Q → Prop)
    (D : Set (APFB01.PhysicalState Cont → Bool)) :=
  {d : APFB01.PhysicalState Cont → Bool // d ∈ D}

/-- The original carrier and its entire finite active carried family.
The active clause is the definition of an alignment (P1:1831-1836),
not HeldSource membership-faithfulness or an additional physical law. -/
structure OriginalAlignment {X Q : Type*} (Cont : X → Q → Prop)
    (D : Set (APFB01.PhysicalState Cont → Bool)) where
  carrier : APFB01.PhysicalState Cont
  carried : Finset (Task Cont D)
  active : ∀ d ∈ carried, d.val carrier = true

noncomputable def originalCost
    {D P R : Type*} (J : Finset D → Set P)
    (wholeResource : P → R) (calibration : R → NNReal) (S : Finset D) : ENNReal :=
  sInf {c : ENNReal | ∃ p ∈ J S, (calibration (wholeResource p) : ENNReal) = c}

def AmendedB06_20260914
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g))) : Prop :=
  ∃ o : Sigma fun g => OriginalAlignment (Cont g) (D g),
    o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
    originalCost (J o.1) (wholeResource o.1) (calibration o.1) o.2.carried ≤
      (C o.1 : ENNReal) ∧
    ∃ p : {p // p ∈ protocols o.1}, p ∈ J o.1 o.2.carried ∧
      ∃ x : Raw o.1, Cont o.1 x p.val

end APFB06


