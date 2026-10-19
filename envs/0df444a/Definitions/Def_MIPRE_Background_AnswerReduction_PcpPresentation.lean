-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
-- name    : MIPRE_Background_AnswerReduction_PcpPresentation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:23.150763+00:00
-- url     : https://prove2.me/theorems/f4e7edcb-36bb-483d-930a-9cd5ac812343
-- title:
--   Definitions of PcpPresentation: The PCP sampler of answer reduction, over `F_q` Piece AR-3a of `planning/answer-reduction.md`: the typed PCP sampler…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.PcpPresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The PCP sampler of answer reduction, over `F_q`. Piece AR-3a of `planning/answer-reduction.md`: the typed PCP sampler `Ŝ^pcp` of the paper's `sec:ar-verifier` (`ld_compiler.tex`, `eq:V-pcp`), as CL presentations over `F_q`. The ambient space is `V^pcp = ⊕_{i≤5} (V_{i,pt} ⊕ V_{i,coord} ⊕ V_{i,dir}) ⊕ V_{aux,pt} ⊕ V_{6,coord} ⊕ V_{aux,dir}`, with coordinates `Coord P` (`10m + 2s + 16` of them, `card_coord`). There are six copies of the seeded low-degree test on it (`regs`, `regs6`): * copy `i ≤ 5` is the test in `m` variables on its own three registers; * copy `6` is the test in `m' = 5m + 5 +…
--
--   **Definitions** (9): `MIPRE.AnswerReduction.Pcp.Coord` (The coordinates of `V^pcp`.); `MIPRE.AnswerReduction.Pcp.Coord.equivSum` (The coordinates as a sum.); `MIPRE.AnswerReduction.Pcp.Coord.instFintype`; `MIPRE.AnswerReduction.Pcp.PcpTy` (The PCP types: a copy and a low-degree test type.); `MIPRE.AnswerReduction.Pcp.dir6` (The `k`-th coordinate of the concatenated direction register `V_{6,dir}`.); `MIPRE.AnswerReduction.Pcp.pres` (**The three-level presentation** of the PCP type `t`.); `MIPRE.AnswerReduction.Pcp.pt6` (The `k`-th coordinate of the concatenated point register `V_{6,pt}`: the `(k mod m)`-th coordinate of `V_{⌊k/m⌋,pt}` for `k < 5m`, and of…); `MIPRE.AnswerReduction.Pcp.regs` (The registers of copy `i ≤ 5`.); `MIPRE.AnswerReduction.Pcp.regs6` (The registers of copy `6`.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `dir6_injective`, `instNeZeroNatM'`, `pt6_injective`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.PcpPresentation` (`MIPRE/Background/AnswerReduction/PcpPresentation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/PcpPresentation.lean; blueprint def:ar-pcp-sampler

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/PcpPresentation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp

/-!
# The PCP sampler of answer reduction, over `F_q`

Piece AR-3a of `planning/answer-reduction.md`: the typed PCP sampler `Ŝ^pcp` of the paper's
`sec:ar-verifier` (`ld_compiler.tex`, `eq:V-pcp`), as CL presentations over `F_q`.

The ambient space is
`V^pcp = ⊕_{i≤5} (V_{i,pt} ⊕ V_{i,coord} ⊕ V_{i,dir}) ⊕ V_{aux,pt} ⊕ V_{6,coord} ⊕ V_{aux,dir}`,
with coordinates `Coord P` (`10m + 2s + 16` of them, `card_coord`). There are six copies of the
seeded low-degree test on it (`regs`, `regs6`):

* copy `i ≤ 5` is the test in `m` variables on its own three registers;
* copy `6` is the test in `m' = 5m + 5 + s` variables whose point and direction registers are the
  *concatenations* `V_{6,pt} = ⊕_{i≤5} V_{i,pt} ⊕ V_{aux,pt}` and `V_{6,dir}` likewise, with its
  own seed coordinate.

The overlap is the point of the construction: the `i`-th block of the sixth copy's point, in the
block order `SAT.PcpParams.block` of the PCP, is the `i`-th copy's point (`block_ptOf_regs6`).
That is what the answer-reduced decider's consistency subtests compare.

The types are `Fin 6 × LIDT.CL.Ty`, eighteen of them, each presented in three levels (`pres`),
exactly on the whole space (`pres_exactlyOn`), with full evaluation the seeded question of its
copy (`question_eval`).
-/

noncomputable section

namespace MIPRE.AnswerReduction.Pcp

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT

/-! ## The coordinates -/

/-- The coordinates of `V^pcp`. -/
inductive Coord (P : PcpParams)
  /-- `V_{i,pt}`, `i ≤ 5`. -/
  | pt (i : Fin 5) (j : Fin P.m)
  /-- `V_{i,dir}`, `i ≤ 5`. -/
  | dir (i : Fin 5) (j : Fin P.m)
  /-- `V_{i,coord}`, `i ≤ 6`. -/
  | coord (i : Fin 6)
  /-- `V_{aux,pt}`. -/
  | auxPt (j : Fin (5 + P.s))
  /-- `V_{aux,dir}`. -/
  | auxDir (j : Fin (5 + P.s))
  deriving DecidableEq

namespace Coord

variable (P : PcpParams)

/-- The coordinates as a sum. -/
def equivSum : Coord P ≃ (Fin 5 × Fin P.m) ⊕ (Fin 5 × Fin P.m) ⊕ Fin 6 ⊕ Fin (5 + P.s) ⊕
    Fin (5 + P.s) where
  toFun
    | .pt i j => .inl (i, j)
    | .dir i j => .inr (.inl (i, j))
    | .coord i => .inr (.inr (.inl i))
    | .auxPt j => .inr (.inr (.inr (.inl j)))
    | .auxDir j => .inr (.inr (.inr (.inr j)))
  invFun
    | .inl (i, j) => .pt i j
    | .inr (.inl (i, j)) => .dir i j
    | .inr (.inr (.inl i)) => .coord i
    | .inr (.inr (.inr (.inl j))) => .auxPt j
    | .inr (.inr (.inr (.inr j))) => .auxDir j
  left_inv c := by cases c <;> rfl
  right_inv c := by rcases c with ⟨i, j⟩ | ⟨i, j⟩ | i | j | j <;> rfl

instance : Fintype (Coord P) := Fintype.ofEquiv _ (equivSum P).symm

end Coord

/-! ## The six copies -/

variable (P : PcpParams)

/-- The registers of copy `i ≤ 5`. -/
def regs (i : Fin 5) : Regs (Coord P) P.m where
  pt j := .pt i j
  dir j := .dir i j
  coord := .coord i.castSucc
  pt_injective _ _ h := by cases h; rfl
  dir_injective _ _ h := by cases h; rfl
  pt_ne_dir _ _ h := by cases h
  pt_ne_coord _ h := by cases h
  dir_ne_coord _ h := by cases h

/-- The `k`-th coordinate of the concatenated point register `V_{6,pt}`: the `(k mod m)`-th
coordinate of `V_{⌊k/m⌋,pt}` for `k < 5m`, and of `V_{aux,pt}` beyond. -/
def pt6 (k : Fin P.m') : Coord P :=
  if h : (k : ℕ) < 5 * P.m then
    .pt ⟨k / P.m, by
      have hm : 0 < P.m := by omega
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h)⟩ ⟨k % P.m, Nat.mod_lt _ (by omega)⟩
  else .auxPt ⟨k - 5 * P.m, by have := k.isLt; simp only [PcpParams.m'] at this; omega⟩

/-- The `k`-th coordinate of the concatenated direction register `V_{6,dir}`. -/
def dir6 (k : Fin P.m') : Coord P :=
  if h : (k : ℕ) < 5 * P.m then
    .dir ⟨k / P.m, by
      have hm : 0 < P.m := by omega
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h)⟩ ⟨k % P.m, Nat.mod_lt _ (by omega)⟩
  else .auxDir ⟨k - 5 * P.m, by have := k.isLt; simp only [PcpParams.m'] at this; omega⟩

theorem pt6_injective : Function.Injective (pt6 P) := by
  intro k k' h
  apply Fin.ext
  by_cases h1 : (k : ℕ) < 5 * P.m <;> by_cases h2 : (k' : ℕ) < 5 * P.m <;>
    simp only [pt6, h1, h2, dite_true, dite_false, reduceCtorEq, Coord.pt.injEq,
      Coord.auxPt.injEq, Fin.mk.injEq] at h
  · rw [← Nat.div_add_mod (k : ℕ) P.m, ← Nat.div_add_mod (k' : ℕ) P.m, h.1, h.2]
  · omega

theorem dir6_injective : Function.Injective (dir6 P) := by
  intro k k' h
  apply Fin.ext
  by_cases h1 : (k : ℕ) < 5 * P.m <;> by_cases h2 : (k' : ℕ) < 5 * P.m <;>
    simp only [dir6, h1, h2, dite_true, dite_false, reduceCtorEq, Coord.dir.injEq,
      Coord.auxDir.injEq, Fin.mk.injEq] at h
  · rw [← Nat.div_add_mod (k : ℕ) P.m, ← Nat.div_add_mod (k' : ℕ) P.m, h.1, h.2]
  · omega

/-- The registers of copy `6`. -/
def regs6 : Regs (Coord P) P.m' where
  pt := pt6 P
  dir := dir6 P
  coord := .coord 5
  pt_injective := pt6_injective P
  dir_injective := dir6_injective P
  pt_ne_dir k k' h := by unfold pt6 dir6 at h; split_ifs at h
  pt_ne_coord k h := by unfold pt6 at h; split_ifs at h
  dir_ne_coord k h := by unfold dir6 at h; split_ifs at h

/-! ## The eighteen types -/

/-- The PCP types: a copy and a low-degree test type. -/
abbrev PcpTy := Fin 6 × LIDT.CL.Ty

instance : NeZero P.m' := ⟨by simp [PcpParams.m']⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm')

/-- **The three-level presentation** of the PCP type `t`. -/
def pres (t : PcpTy) : MIPRE.CL.CLFun F (Coord P) 3 :=
  if h : (t.1 : ℕ) < 5 then (regs P ⟨t.1, h⟩).pres S t.2 else (regs6 P).pres S' t.2

end MIPRE.AnswerReduction.Pcp

end


