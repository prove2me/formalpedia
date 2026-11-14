-- Prove2me | Definitions.Def_APFPaper5_K3_TwoMarkModel
-- name    : APFPaper5_K3_TwoMarkModel
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:11:16.082198+00:00
-- url     : https://prove2.me/theorems/f3848ba7-cbd9-43bf-b69d-8ab772f8db71
-- title:
--   Supplied real two-by-two array model of marks and planar turns
-- statement:
--   Defines M2, multiplication, transpose, unit, scaling, fixed mark, parameterized mark and turn array.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_TwoMarkModel.lean; Sib v15, SHA-256 c4afffeb2fb31e51c9c21bb25c770f3d8548aaa87e7db97ae65aa92f7fa16b67. P5:3049-3056;P1:6276-6280

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_TwoMarkModel
title: The two-mark model: real two-by-two arrays, a fixed mark, a turned mark, and a turn
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's remark of 2026-11-12, "Smooth reversible held states describe the relation between
 distinctions perfectly". Paper 5 Supplement v7.33:3049-3058 (K3). The standard picture of two projections.
standing: a MODEL written out for a conditional instance. It is supplied mathematics, not ledger data, and no
 declared input produces it. The structure has data fields only.
statement: M2 is a real two-by-two array with its product, transpose, unit and scaling. markP is the fixed mark,
 markQ u v the mark along the pair (u, v), and turn u v the array that carries one to the other.
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K3

/-- A real two-by-two array, rows `(a b)` and `(c d)`. -/
@[ext] structure M2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def mul (x y : M2) : M2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def tr (x : M2) : M2 := ⟨x.a, x.c, x.b, x.d⟩

def one : M2 := ⟨1, 0, 0, 1⟩

def smul (r : ℝ) (x : M2) : M2 := ⟨r * x.a, r * x.b, r * x.c, r * x.d⟩

/-- The fixed mark. -/
def markP : M2 := ⟨1, 0, 0, 0⟩

/-- The mark along the pair `(u, v)`. -/
def markQ (u v : ℝ) : M2 := ⟨u * u, u * v, u * v, v * v⟩

/-- The turn by the pair `(u, v)`. -/
def turn (u v : ℝ) : M2 := ⟨u, -v, v, u⟩

end APFPaper5.K3


