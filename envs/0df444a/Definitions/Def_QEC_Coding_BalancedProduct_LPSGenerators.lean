-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
-- name    : QEC_Coding_BalancedProduct_LPSGenerators
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T06:50:55.740223+00:00
-- url     : https://prove2.me/theorems/9ea5f33d-3f7f-40d4-aee7-c5801256c733
-- title:
--   LPSGenerators
-- statement:
--   Definitions and structural lemmas for LPSGenerators, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGenerators.lean

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
structure ShellIndex401 where
  aIndex : Fin 10
  bIndex : Fin 41
  cIndex : Fin 41
  dIndex : Fin 41
  deriving DecidableEq, Fintype
@[ext]
theorem ShellIndex401.ext {t u : ShellIndex401}
    (ha : t.aIndex = u.aIndex)
    (hb : t.bIndex = u.bIndex)
    (hc : t.cIndex = u.cIndex)
    (hd : t.dIndex = u.dIndex) : t = u := by
  cases t
  cases u
  simp_all
def ShellIndex401.a (t : ShellIndex401) : ℤ := 2 * t.aIndex.val + 1
def ShellIndex401.b (t : ShellIndex401) : ℤ := t.bIndex.val - 20
def ShellIndex401.c (t : ShellIndex401) : ℤ := t.cIndex.val - 20
def ShellIndex401.d (t : ShellIndex401) : ℤ := t.dIndex.val - 20
def ShellIndex401.HasNorm401 (t : ShellIndex401) : Prop :=
  t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = 401
instance (t : ShellIndex401) : Decidable t.HasNorm401 :=
  by
    unfold ShellIndex401.HasNorm401
    infer_instance
def shell401 : Finset ShellIndex401 :=
  Finset.univ.filter ShellIndex401.HasNorm401
theorem mem_shell401_iff (t : ShellIndex401) :
    t ∈ shell401 ↔ t.HasNorm401 := by
  simp [shell401]
def lpsShell401Summand (a : Fin 10) (b c d : Fin 41) : ℕ :=
  if (2 * (a.val : ℤ) + 1)^2 + ((b.val : ℤ)-20)^2 +
    ((c.val : ℤ)-20)^2 + ((d.val : ℤ)-20)^2 = 401 then 1 else 0
def lpsShell401Chunk (a : Fin 10) : ℕ :=
  ∑ b : Fin 41, ∑ c : Fin 41, ∑ d : Fin 41, lpsShell401Summand a b c d
def ShellIndex401.conj (t : ShellIndex401) : ShellIndex401 where
  aIndex := t.aIndex
  bIndex := Fin.rev t.bIndex
  cIndex := Fin.rev t.cIndex
  dIndex := Fin.rev t.dIndex
@[simp] theorem ShellIndex401.a_conj (t : ShellIndex401) : t.conj.a = t.a := rfl
@[simp] theorem ShellIndex401.b_conj (t : ShellIndex401) : t.conj.b = -t.b := by
  simp [ShellIndex401.conj, ShellIndex401.b, Fin.rev]
  omega
@[simp] theorem ShellIndex401.c_conj (t : ShellIndex401) : t.conj.c = -t.c := by
  simp [ShellIndex401.conj, ShellIndex401.c, Fin.rev]
  omega
@[simp] theorem ShellIndex401.d_conj (t : ShellIndex401) : t.conj.d = -t.d := by
  simp [ShellIndex401.conj, ShellIndex401.d, Fin.rev]
  omega
@[simp] theorem ShellIndex401.conj_conj (t : ShellIndex401) : t.conj.conj = t := by
  cases t
  simp [ShellIndex401.conj]
theorem ShellIndex401.hasNorm401_conj_iff (t : ShellIndex401) :
    t.conj.HasNorm401 ↔ t.HasNorm401 := by
  simp [ShellIndex401.HasNorm401]
@[simp] theorem ShellIndex401.conj_mem_shell401_iff (t : ShellIndex401) :
    t.conj ∈ shell401 ↔ t ∈ shell401 := by
  simp [mem_shell401_iff, ShellIndex401.hasNorm401_conj_iff]
noncomputable def lpsX (q : ℕ) [Fact q.Prime] : ZMod q :=
  Classical.choose (ZMod.sq_add_sq q (-1))
noncomputable def lpsY (q : ℕ) [Fact q.Prime] : ZMod q :=
  Classical.choose (Classical.choose_spec (ZMod.sq_add_sq q (-1)))
theorem lpsX_sq_add_lpsY_sq_add_one (q : ℕ) [Fact q.Prime] :
    lpsX q ^ 2 + lpsY q ^ 2 + 1 = 0 := by
  have h := Classical.choose_spec
    (Classical.choose_spec (ZMod.sq_add_sq q (-1)))
  dsimp [lpsX, lpsY]
  linear_combination h
noncomputable def lpsMatrix401 (q : ℕ) [Fact q.Prime]
    (t : ShellIndex401) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  let a : ZMod q := t.a
  let b : ZMod q := t.b
  let c : ZMod q := t.c
  let d : ZMod q := t.d
  let x := lpsX q
  let y := lpsY q
  !![a + b * x + d * y, -b * y + c + d * x;
     -b * y - c + d * x, a - b * x - d * y]
theorem det_lpsMatrix401
    (q : ℕ) [Fact q.Prime]
    (t : ShellIndex401) (ht : t ∈ shell401) :
    (lpsMatrix401 q t).det = (401 : ZMod q) := by
  have hnorm : t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = 401 :=
    (mem_shell401_iff t).mp ht
  have hnormq := congrArg (fun z : ℤ => (z : ZMod q)) hnorm
  push_cast at hnormq
  have hroot := lpsX_sq_add_lpsY_sq_add_one q
  simp only [lpsMatrix401, Matrix.det_fin_two_of]
  linear_combination hnormq -
    ((t.b : ZMod q) ^ 2 + (t.d : ZMod q) ^ 2) * hroot
noncomputable def lpsGL401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    GL (Fin 2) (ZMod q) :=
  Matrix.GeneralLinearGroup.mk'' (lpsMatrix401 q t) <| by
    rw [det_lpsMatrix401 q t ht]
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hnonsquare : ¬ IsSquare (401 : ZMod q) :=
      (legendreSym.eq_neg_one_iff' (p := q) (a := 401)).mp hq
    apply hnonsquare
    rw [hzero]
    exact IsSquare.zero
noncomputable def lpsGenerator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) : PGL(2, ZMod q) :=
  Matrix.ProjGenLinGroup.mk (lpsGL401 q hq t ht)
noncomputable def lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Finset PGL(2, ZMod q) :=
  by
    classical
    exact shell401.attach.image fun t => lpsGenerator401 q hq t.1 t.2
end QEC.Coding.BalancedProduct.LPSGenerators


