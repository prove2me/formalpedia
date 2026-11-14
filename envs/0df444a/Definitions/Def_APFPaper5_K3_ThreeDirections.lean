-- Prove2me | Definitions.Def_APFPaper5_K3_ThreeDirections
-- name    : APFPaper5_K3_ThreeDirections
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:13:03.825963+00:00
-- url     : https://prove2.me/theorems/d6386dec-5cea-45fc-8bc7-3e305f598e9c
-- title:
--   Three-real vector formulas for axis turns and a two-by-two determinant
-- statement:
--   Defines V3, dot and cross products, vector arithmetic, quarterTurn, flipAbout and det2.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   **Claim boundaries.** K3-07
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_ThreeDirections.lean; Sib v15, SHA-256 144fbbb58c0cd640a66461b1af87b72ae253ab1204296d47a5caa4f9d46d008c. P5:1621-1649;3049-3056

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_ThreeDirections
title: Directions in a space of three dimensions, the quarter turn about an axis, and the flip about an axis; the determinant of a two-mark array
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's ruling of 2026-11-12: the three meant is the three dimensions of space (codebank
 apf/spacetime.py, check_T8), and the bridge from turning a mark to directions of space is to be stated and
 tested. Ordinary vector arithmetic.
standing: a MODEL for testing that bridge. Nothing here is ledger data, and nothing here derives that space
 has three dimensions. The structure has data fields only.
statement: V3 is a triple of reals with dot3, cross3, add3, sub3, smul3. quarterTurn b v is the quarter turn of
 v about the axis b. flipAbout a v is the flip of v about the axis a. det2 is the determinant of an M2 array.
-/
import Definitions.Def_APFPaper5_K3_TwoMarkModel

set_option autoImplicit false
namespace APFPaper5.K3

/-- A direction in three dimensions, as a triple of reals. -/
@[ext] structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

def dot3 (a b : V3) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z

def cross3 (a b : V3) : V3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def add3 (a b : V3) : V3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def sub3 (a b : V3) : V3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

def smul3 (r : ℝ) (a : V3) : V3 := ⟨r * a.x, r * a.y, r * a.z⟩

/-- The quarter turn of `v` about the axis `b`. -/
def quarterTurn (b v : V3) : V3 := add3 (smul3 (dot3 b v) b) (cross3 b v)

/-- The flip of `v` about the axis `a`. -/
noncomputable def flipAbout (a v : V3) : V3 := sub3 (smul3 (2 * dot3 a v / dot3 a a) a) v

/-- The determinant of a two-mark array. -/
def det2 (m : M2) : ℝ := m.a * m.d - m.b * m.c

end APFPaper5.K3


