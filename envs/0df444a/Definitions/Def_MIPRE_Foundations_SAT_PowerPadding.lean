-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_PowerPadding
-- name    : MIPRE_Foundations_SAT_PowerPadding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:58:15.282282+00:00
-- url     : https://prove2.me/theorems/e7042847-15af-4cf3-98d9-a5063fecae4c
-- title:
--   Definitions of PowerPadding: Power-of-two padding with unary output The inner PCP dimension must itself be a power of two
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.PowerPadding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Power-of-two padding with unary output. The inner PCP dimension must itself be a power of two. `ceilPower` is the least power of two at least its input, with value one at zero. `ceilPowerProg` produces that many unary slots in polynomial time in the number of input slots. Its loop explicitly caps intermediate vectors, rather than assuming that unrestricted unary exponentiation has polynomial cost.
--
--   **Definitions** (4): `MIPRE.SAT.ceilPower` (The least power of two at least `n`, including `ceilPower 0 = 1`.); `MIPRE.SAT.ceilPowerProg` (Uniform power-of-two padding, with polynomial cost in the supplied unary length.); `_private.MIPRE.Foundations.SAT.PowerPadding.0.MIPRE.SAT.growStep`; `_private.MIPRE.Foundations.SAT.PowerPadding.0.MIPRE.SAT.growStepProg`.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ceilPowerProg_apply`, `ceilPower_le_twice`, `esize_unary_list`, `growStep_bounded`, `grow_bound`, `grow_length`, `min_mul_min`, `unary_eq_length`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.PowerPadding` (`MIPRE/Foundations/SAT/PowerPadding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 16 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/PowerPadding.lean; blueprint lem:pcp-padding-programs

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PowerPadding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg

/-!
# Power-of-two padding with unary output

The inner PCP dimension must itself be a power of two. `ceilPower` is the least
power of two at least its input, with value one at zero. `ceilPowerProg` produces
that many unary slots in polynomial time in the number of input slots. Its loop
explicitly caps intermediate vectors, rather than assuming that unrestricted
unary exponentiation has polynomial cost.
-/

namespace MIPRE.SAT

open Cost Cost.PolyTimeFun Polynomial

/-- The least power of two at least `n`, including `ceilPower 0 = 1`. -/
def ceilPower (n : ℕ) : ℕ := 2 ^ Nat.size (n - 1)

theorem ceilPower_le_twice (n : ℕ) : ceilPower n ≤ 2 * n + 1 := by
  by_cases h : Nat.size (n - 1) = 0
  · simp [ceilPower, h]
  · have hp : 0 < Nat.size (n - 1) := by omega
    have he : Nat.size (n - 1) = (Nat.size (n - 1) - 1) + 1 := by omega
    have hb := Nat.lt_size.mp (show Nat.size (n - 1) - 1 < Nat.size (n - 1) by omega)
    rw [ceilPower, he, pow_succ]
    omega

theorem unary_eq_length (u : Unary) : u = unary u.length := by
  induction u with
  | nil => rfl
  | cons x u ih => cases x; simpa [unary, List.replicate_succ] using congrArg (List.cons ()) ih

theorem esize_unary_list (u : Unary) : esize u = 2 * u.length + 1 := by
  conv_lhs => rw [unary_eq_length u]
  exact esize_unary _

def growStep (s : Unary × Unary) (_ : Bool) : Unary × Unary :=
  (s.1, (s.2 ++ s.2).take s.1.length)

theorem grow_bound (fuel : BitStr) (cap acc : Unary) :
    (fuel.foldl growStep (cap, acc)).1 = cap ∧
      (fuel.foldl growStep (cap, acc)).2.length ≤ max cap.length acc.length := by
  induction fuel generalizing acc with
  | nil => exact ⟨rfl, Nat.le_max_right _ _⟩
  | cons b fuel ih =>
    have h := ih ((acc ++ acc).take cap.length)
    refine ⟨h.1, h.2.trans ?_⟩
    simp only [List.length_take, List.length_append]
    omega

theorem min_mul_min (c p v : ℕ) (hp : 1 ≤ p) :
    min c (p * min c v) = min c (p * v) := by
  by_cases h : c ≤ v
  · have hpc : c ≤ p * c := by nlinarith
    have hpv : c ≤ p * v := hpc.trans (Nat.mul_le_mul_left p h)
    rw [min_eq_left h, min_eq_left hpc, min_eq_left hpv]
  · rw [min_eq_right (by omega : v ≤ c)]

theorem grow_length (fuel : BitStr) (cap acc : Unary) (ha : acc.length ≤ cap.length) :
    (fuel.foldl growStep (cap, acc)).2.length = min cap.length (2 ^ fuel.length * acc.length) := by
  induction fuel generalizing acc with
  | nil => simp [min_eq_right ha]
  | cons b fuel ih =>
    change (fuel.foldl growStep (cap, (acc ++ acc).take cap.length)).2.length = _
    rw [ih _ (by simp), List.length_take, List.length_append]
    rw [min_mul_min _ _ _ (Nat.one_le_iff_ne_zero.mpr (Nat.two_pow_pos _).ne')]
    simp only [List.length_cons, pow_succ]
    congr 1
    ring

noncomputable def growStepProg : PolyTimeFun ((Unary × Unary) × Bool) (Unary × Unary) :=
  (fst.comp fst).pair (ap₂ take (ap₂ append (snd.comp fst) (snd.comp fst)) (fst.comp fst))

theorem growStep_bounded : FoldBounded growStepProg (2 * X + 4) := by
  rintro fuel ⟨cap, acc⟩ pre post h
  have hb := grow_bound pre cap acc
  change esize (pre.foldl growStep (cap, acc)) ≤ _
  change esize ((pre.foldl growStep (cap, acc)).1, (pre.foldl growStep (cap, acc)).2) ≤ _
  rw [esize_prod, hb.1]
  simp only [esize_unary_list, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- Uniform power-of-two padding, with polynomial cost in the supplied unary length. -/
noncomputable def ceilPowerProg : PolyTimeFun Unary Unary :=
  let fuel : PolyTimeFun Unary BitStr := natBits.comp (unaryToBin.comp tail)
  let cap : PolyTimeFun Unary Unary :=
    ap₂ append (ap₂ append (PolyTimeFun.id _) (PolyTimeFun.id _)) (const [()])
  let run := (foldl growStepProg (2 * X + 4) growStep_bounded).comp
    (fuel.pair (cap.pair (const [()])))
  congr (snd.comp run) (fun u => unary (ceilPower u.length)) (by
    intro u
    have hcap : (cap u).length = 2 * u.length + 1 := by simp [cap]; omega
    have hfuel : (fuel u).length = Nat.size (u.length - 1) := by
      simp [fuel, Nat.size_eq_bits_len]
    have hlen := grow_length (fuel u) (cap u) [()] (by simp [hcap])
    rw [hfuel, List.length_singleton, Nat.mul_one, hcap, ← ceilPower,
      min_eq_right (ceilPower_le_twice u.length)] at hlen
    change (List.foldl growStep (cap u, [()]) (fuel u)).2 = _
    exact (unary_eq_length _).trans (congrArg unary hlen))

@[simp] theorem ceilPowerProg_apply (u : Unary) :
    ceilPowerProg u = unary (ceilPower u.length) := rfl

end MIPRE.SAT


