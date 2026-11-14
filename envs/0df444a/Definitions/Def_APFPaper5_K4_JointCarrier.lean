-- Prove2me | Definitions.Def_APFPaper5_K4_JointCarrier
-- name    : APFPaper5_K4_JointCarrier
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:52:43.458711+00:00
-- url     : https://prove2.me/theorems/84bb5652-8256-4694-9e7d-a16a21320ed0
-- title:
--   A supplied joint carrier and two extension conditions
-- statement:
--   Defines eight real joint coordinates, complex-product formulas, quadratic record weights, and recDiag-compatible extension conditions. pair already fixes synchronized complex multiplication. ExtendsToJoint and ExtendsToJointMap require agreement of recDiag on products, not equality of maps on products, full channel positivity or physical composite embeddings.
--
--   **Meaning and scope.** Faithful as the stated mathematical encoding with this exposure: pair already fixes synchronized complex multiplication. ExtendsToJoint and ExtendsToJointMap require agreement of recDiag on products, not equality of maps on products, full channel positivity or physical composite embeddings.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K4.Joint', 'statement_and_binders': '@[ext] structure Joint'}
--   - {'declaration': 'APFPaper5.K4.pair', 'statement_and_binders': 'def pair (h k : Held2) : Joint'}
--   - {'declaration': 'APFPaper5.K4.jointQuarter', 'statement_and_binders': 'def jointQuarter (p : Joint) : Joint'}
--   - {'declaration': 'APFPaper5.K4.jointFlip', 'statement_and_binders': 'def jointFlip (p : Joint) : Joint'}
--   - {'declaration': 'APFPaper5.K4.jointSub', 'statement_and_binders': 'def jointSub (p q : Joint) : Joint'}
--   - {'declaration': 'APFPaper5.K4.antisym', 'statement_and_binders': 'def antisym : Joint'}
--   - {'declaration': 'APFPaper5.K4.recDiag', 'statement_and_binders': 'def recDiag (p : Joint) : ℝ'}
--   - {'declaration': 'APFPaper5.K4.RecordWeights', 'statement_and_binders': 'structure RecordWeights'}
--   - {'declaration': 'APFPaper5.K4.linearRecord', 'statement_and_binders': 'def linearRecord (w : RecordWeights) (p : Joint) : ℝ'}
--   - {'declaration': 'APFPaper5.K4.ExtendsToJoint', 'statement_and_binders': 'def ExtendsToJoint (T : Held2 → Held2) : Prop'}
--   - {'declaration': 'APFPaper5.K4.jointAdd', 'statement_and_binders': 'def jointAdd (p q : Joint) : Joint'}
--   - {'declaration': 'APFPaper5.K4.jointSmul', 'statement_and_binders': 'def jointSmul (r : ℝ) (p : Joint) : Joint'}
--   - {'declaration': 'APFPaper5.K4.JointAdditiveHomogeneous', 'statement_and_binders': 'def JointAdditiveHomogeneous (F : Joint → Joint) : Prop'}
--   - {'declaration': 'APFPaper5.K4.ExtendsToJointMap', 'statement_and_binders': 'def ExtendsToJointMap (T : Held2 → Held2) : Prop'}
--   - {'declaration': 'APFPaper5.K4.actOnFirst', 'statement_and_binders': 'def actOnFirst (u v : Held2) (z : Joint) : Joint'}
--
--   **Limits**
--
--   - Q44-01
--   - Q44-04
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K4_JointCarrier.lean; Sib v44 / pullbacks v1, SHA-256 cf2a6416e44611d1dcaf2c1d1e75101ccc689c56166f318e06940a1f759cbca0. {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2213-2235,2722-2735,3034-3076'}; {'path': 'source/Definitions/Def_APFPaper5_K4_JointCarrier.lean', 'sha256': 'cf2a6416e44611d1dcaf2c1d1e75101ccc689c56166f318e06940a1f759cbca0'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_JointCarrier
title: A joint carrier of two systems of two held components: four joint components, products, the joint record book, and extension of a map of one part
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:2445-2466 (blockwise Choi criterion), 2722-2732 (Choi-faithful same-type
 reference theorem: an independently maintained same-type reference block, the full Choi corner, a local
 process acting as the identity on the reference, and joint positivity give complete positivity), 2960-2966
 (without those, positive but not completely positive maps may survive), 3092 (K4: commuting, unital,
 orientation-synchronized, generating embeddings). Codebank graded_orientation_closure.py
 (check_T_odd_fixed_sheet_map_not_CP).
standing: a supplied MODEL of composition. Nothing here is a declared input. The composition clause itself is
 not typed; this file supplies one carrier on which its consequences can be tested.
statement: Joint is a value and a rate for each of the four joint components AA', AB', BA', BB'. pair h k is
 the joint state of a state h of the first system and a state k of the second. jointQuarter is the quarter
 turn of every joint component; jointFlip reverses every rate. antisym is AB' minus BA'. recDiag is the cost
 of AA' and BB' recombined. linearRecord w is a reading that is linear in the joint record book: the four
 costs and the two cross terms of each of the six pairs of joint components, with weights w.
 ExtendsToJoint T says: there is a map of joint states after which the cost recDiag is linear in the joint
 record book, and which on every product reads as T applied to the first part with the second untouched.
 actOnFirst u v is the map of joint states that acts on the first part alone and leaves the second
 untouched, for a map of the first part given by the images u and v of its two unit states.
 ExtendsToJointMap T says the same with "linear in the joint record book" replaced by: the map of joint
 states is additive and homogeneous, and the quarter turn of the joint state is unseen by recDiag after it.
-/
import Definitions.Def_APFPaper5_K3_HeldMaps

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

/-- A value and a rate for each of the four joint components AA', AB', BA', BB'. -/
@[ext] structure Joint where
  x1 : ℝ
  y1 : ℝ
  x2 : ℝ
  y2 : ℝ
  x3 : ℝ
  y3 : ℝ
  x4 : ℝ
  y4 : ℝ

/-- The joint state of a state of the first system and a state of the second. -/
def pair (h k : Held2) : Joint :=
  ⟨h.a1 * k.a1 - h.a2 * k.a2, h.a1 * k.a2 + h.a2 * k.a1,
   h.a1 * k.b1 - h.a2 * k.b2, h.a1 * k.b2 + h.a2 * k.b1,
   h.b1 * k.a1 - h.b2 * k.a2, h.b1 * k.a2 + h.b2 * k.a1,
   h.b1 * k.b1 - h.b2 * k.b2, h.b1 * k.b2 + h.b2 * k.b1⟩

/-- The quarter turn of every joint component. -/
def jointQuarter (p : Joint) : Joint := ⟨-p.y1, p.x1, -p.y2, p.x2, -p.y3, p.x3, -p.y4, p.x4⟩

/-- Every rate reversed. -/
def jointFlip (p : Joint) : Joint := ⟨p.x1, -p.y1, p.x2, -p.y2, p.x3, -p.y3, p.x4, -p.y4⟩

/-- Entrywise difference. -/
def jointSub (p q : Joint) : Joint :=
  ⟨p.x1 - q.x1, p.y1 - q.y1, p.x2 - q.x2, p.y2 - q.y2, p.x3 - q.x3, p.y3 - q.y3, p.x4 - q.x4,
   p.y4 - q.y4⟩

/-- AB' minus BA'. -/
def antisym : Joint := ⟨0, 0, 1, 0, -1, 0, 0, 0⟩

/-- The cost of AA' and BB' recombined. -/
def recDiag (p : Joint) : ℝ := (p.x1 + p.x4) * (p.x1 + p.x4) + (p.y1 + p.y4) * (p.y1 + p.y4)

/-- Weights for a reading that is linear in the joint record book. -/
structure RecordWeights where
  d1 : ℝ
  d2 : ℝ
  d3 : ℝ
  d4 : ℝ
  u12 : ℝ
  v12 : ℝ
  u13 : ℝ
  v13 : ℝ
  u14 : ℝ
  v14 : ℝ
  u23 : ℝ
  v23 : ℝ
  u24 : ℝ
  v24 : ℝ
  u34 : ℝ
  v34 : ℝ

/-- A reading that is linear in the four costs and the twelve cross terms of a joint state. -/
def linearRecord (w : RecordWeights) (p : Joint) : ℝ :=
  w.d1 * (p.x1 * p.x1 + p.y1 * p.y1) + w.d2 * (p.x2 * p.x2 + p.y2 * p.y2) +
  w.d3 * (p.x3 * p.x3 + p.y3 * p.y3) + w.d4 * (p.x4 * p.x4 + p.y4 * p.y4) +
  w.u12 * (p.x1 * p.x2 + p.y1 * p.y2) + w.v12 * (p.y1 * p.x2 - p.x1 * p.y2) +
  w.u13 * (p.x1 * p.x3 + p.y1 * p.y3) + w.v13 * (p.y1 * p.x3 - p.x1 * p.y3) +
  w.u14 * (p.x1 * p.x4 + p.y1 * p.y4) + w.v14 * (p.y1 * p.x4 - p.x1 * p.y4) +
  w.u23 * (p.x2 * p.x3 + p.y2 * p.y3) + w.v23 * (p.y2 * p.x3 - p.x2 * p.y3) +
  w.u24 * (p.x2 * p.x4 + p.y2 * p.y4) + w.v24 * (p.y2 * p.x4 - p.x2 * p.y4) +
  w.u34 * (p.x3 * p.x4 + p.y3 * p.y4) + w.v34 * (p.y3 * p.x4 - p.x3 * p.y4)

/-- A map of the first part extends to joint states: there is a map of joint states after which the cost
`recDiag` is linear in the joint record book, and which on products reads as `T` on the first part. -/
def ExtendsToJoint (T : Held2 → Held2) : Prop :=
  ∃ (F : Joint → Joint) (w : RecordWeights), (∀ p : Joint, recDiag (F p) = linearRecord w p) ∧
    ∀ h k : Held2, recDiag (F (pair h k)) = recDiag (pair (T h) k)

/-- Entrywise sum. -/
def jointAdd (p q : Joint) : Joint :=
  ⟨p.x1 + q.x1, p.y1 + q.y1, p.x2 + q.x2, p.y2 + q.y2, p.x3 + q.x3, p.y3 + q.y3, p.x4 + q.x4,
   p.y4 + q.y4⟩

/-- Entrywise scaling. -/
def jointSmul (r : ℝ) (p : Joint) : Joint :=
  ⟨r * p.x1, r * p.y1, r * p.x2, r * p.y2, r * p.x3, r * p.y3, r * p.x4, r * p.y4⟩

def JointAdditiveHomogeneous (F : Joint → Joint) : Prop :=
  (∀ p q : Joint, F (jointAdd p q) = jointAdd (F p) (F q)) ∧
    ∀ (r : ℝ) (p : Joint), F (jointSmul r p) = jointSmul r (F p)

/-- A map of the first part extends to an additive homogeneous map of joint states, after which the quarter
turn of the joint state is unseen by the cost `recDiag`, and which on products reads as `T` on the first
part. -/
def ExtendsToJointMap (T : Held2 → Held2) : Prop :=
  ∃ F : Joint → Joint, JointAdditiveHomogeneous F ∧
    (∀ p : Joint, recDiag (F (jointQuarter p)) = recDiag (F p)) ∧
    ∀ h k : Held2, recDiag (F (pair h k)) = recDiag (pair (T h) k)

/-- The map of joint states that acts on the first part alone, by the additive homogeneous map commuting
with the quarter turn that sends the two unit states of the first part to `u` and `v`. -/
def actOnFirst (u v : Held2) (z : Joint) : Joint :=
  ⟨u.a1 * z.x1 - u.a2 * z.y1 + v.a1 * z.x3 - v.a2 * z.y3,
   u.a1 * z.y1 + u.a2 * z.x1 + v.a1 * z.y3 + v.a2 * z.x3,
   u.a1 * z.x2 - u.a2 * z.y2 + v.a1 * z.x4 - v.a2 * z.y4,
   u.a1 * z.y2 + u.a2 * z.x2 + v.a1 * z.y4 + v.a2 * z.x4,
   u.b1 * z.x1 - u.b2 * z.y1 + v.b1 * z.x3 - v.b2 * z.y3,
   u.b1 * z.y1 + u.b2 * z.x1 + v.b1 * z.y3 + v.b2 * z.x3,
   u.b1 * z.x2 - u.b2 * z.y2 + v.b1 * z.x4 - v.b2 * z.y4,
   u.b1 * z.y2 + u.b2 * z.x2 + v.b1 * z.y4 + v.b2 * z.x4⟩

end APFPaper5.K4


