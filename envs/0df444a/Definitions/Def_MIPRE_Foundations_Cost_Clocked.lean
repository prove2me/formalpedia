-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Clocked
-- name    : MIPRE_Foundations_Cost_Clocked
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:08:10.63178+00:00
-- url     : https://prove2.me/theorems/3a08d3e6-d8d1-470a-a309-b9f5c0fd0e01
-- title:
--   Clocked simulation as a polynomial-time predicate: does $e$ halt within $|n|$ steps?
-- statement:
--   This bundle turns a clocked universal machine into the polynomial-time Boolean predicate "run $e$ for $\log n$ steps" of the recursive compression argument.
--
--   `MIPRE.Cost.Prog.haltsWithinProg` $\mathrm{univT}$, for a clocked universal program $\mathrm{univT}$, is the program that on the input $\mathtt{cons}(\mathrm{encode}\ e, \mathrm{encode}\ n)$, a program $e$ and a number $n$ in binary, extracts $n$, converts the binary numeral into the unary budget $k = |n|$ (its bit length, computed by `lenProg` as the length of the list of bits), extracts $e$, assembles the machine input $\mathtt{cons}(\mathrm{ofNat}\ k, \mathtt{cons}(\mathrm{encode}\ e, \mathtt{nil}))$, runs $\mathrm{univT}$ on it, and returns the halting flag of the clocked result: true if the simulation reported a halt, false on timeout.
--
--   `MIPRE.Cost.PolyTimeFun.haltsWithin` $UT$, for a clocked universal machine $UT$ with overhead polynomial $p_{UT}$, is the polynomial-time function $\mathrm{Prog} \times \mathbb{N} \to \mathrm{Bool}$
--   $$(e, n) \longmapsto \bigl[\, e \text{ halts on the empty input } \mathtt{nil} \text{ within cost } |n| \,\bigr],$$
--   that is, whether $\mathrm{evalWithin}\ e\ \mathtt{nil}\ |n|$ is defined, computed by `haltsWithinProg` with time bound $p_{UT} + (X + 2)(4X + 14) + 9X + 40$.
--
--   The lemmas proved in the bundle are the well-scopedness of `haltsWithinProg` given that of $\mathrm{univT}$, its run with the explicit cost bound $p_{UT}(|n| + \mathrm{esize}(e) + 1) + (|n| + 2)(\mathrm{esize}(n) + 2|n| + 14) + 3\,\mathrm{esize}(e) + 4|n| + 2\,\mathrm{esize}(n) + 40$, and the application equation of `haltsWithin`.
--
--   **Formalization Note**. "Steps" are units of cost of the ambient model, and $\log n$ is realized as $|n|$, Mathlib's `Nat.size n`, the number of binary digits of $n$ ($\lfloor \log_2 n \rfloor + 1$ for $n > 0$): the budget is exactly the length of the bit string that encodes $n$, which is why the length loop computes it. The simulated program is run on the empty input $\mathtt{nil}$, matching the halting problem "does $e$ halt on the empty input" of the compression lemma. The predicate is total, and its cost is polynomial in $\mathrm{esize}(e) + \mathrm{esize}(n)$, hence polylogarithmic in $n$; this is the "run $e$ for $\log n$ steps" of [MNY, Lemma 5.1].
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Clocked.lean; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 5.1 (the clocked simulation used in its proof)

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Clocked.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

/-!
# Clocked simulation as a polynomial-time predicate

Given a clocked universal machine `UT`, `PolyTimeFun.haltsWithin UT : PolyTimeFun (Prog × ℕ)
Bool` decides whether `e` halts on the empty input within `Nat.size n` steps: it computes
the budget in unary from the binary `n` (`lenProg`), assembles the machine's input
`(ofNat k, (encode e, nil))`, runs `UT.univT`, and reads the halting flag of
`clockedResult`. This is the "run `e` for `log n` steps" of [MNY, Lemma 5.1].
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- The program of `PolyTimeFun.haltsWithin`. Input: `cons (encode e) (encode n)`. -/
def haltsWithinProg (univT : Prog) : Prog :=
  .let_ (.elim 0 .nil (.var 1))
    (.let_ (callVar 0 lenProg)
      (.let_ (.elim 2 .nil (.var 0))
        (.let_ (.cons (.var 1) (.cons (.var 0) .nil))
          (.let_ (callVar 0 univT)
            (.elim 0 .nil (.const (.cons .nil .nil)))))))

theorem haltsWithinProg_wellScoped {univT : Prog} (hU : univT.WellScoped 1) :
    (haltsWithinProg univT).WellScoped 1 :=
  ⟨⟨by decide, trivial, by simp [WellScoped]⟩,
    ⟨callVar_wellScoped (by decide) lenProg_wellScoped,
      ⟨⟨by decide, trivial, by simp [WellScoped]⟩,
        ⟨⟨by simp [WellScoped], by simp [WellScoped], trivial⟩,
          ⟨callVar_wellScoped (by decide) hU, ⟨by decide, trivial, trivial⟩⟩⟩⟩⟩⟩

/-- The run of `haltsWithinProg`, in terms of the clocked machine's result. -/
theorem haltsWithinProg_runs (UT : ClockedUniversalMachine) (e : Prog) (n : ℕ) :
    ∃ t ≤ UT.bound.eval (Nat.size n + esize e + 1) +
        (Nat.size n + 1 + 1) * (esize n + 1 + 2 * Nat.size n + 13) +
        3 * esize e + 4 * Nat.size n + 2 * esize n + 40,
      (haltsWithinProg UT.univT).Runs (.cons (encode e) (encode n))
        (encode (evalWithin e .nil (Nat.size n)).isSome) t := by
  have hLen : (n.bits.map Data.ofBool).length = Nat.size n := by
    rw [List.length_map, Nat.size_eq_bits_len]
  have hne : encode n = Data.list (n.bits.map Data.ofBool) := encode_bitStr_eq_list n.bits
  have hnesz : (encode n).size = esize n := rfl
  have heesz : (encode e).size = esize e := rfl
  -- step 1: the second component
  have s1 : Eval [Data.cons (encode e) (encode n)] (.elim 0 .nil (.var 1)) (encode n)
      ((encode n).size + 1 + 1) :=
    Eval.elim_cons (i := 0) (a := encode e) (b := encode n) (by simp)
      (Eval.var_of_get (i := 1) (v := encode n) (by simp))
  -- step 2: the budget in unary
  obtain ⟨t₂, ht₂, h₂⟩ := lenProg_runs (n.bits.map Data.ofBool)
  rw [hLen] at ht₂ h₂
  rw [← hne] at ht₂ h₂
  rw [hnesz] at ht₂
  have s2 := callVar_eval (env := [encode n, Data.cons (encode e) (encode n)]) (i := 0)
    lenProg_wellScoped (v := encode n) (by simp) h₂
  -- step 3: the first component
  have s3 : Eval [Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)]
      (.elim 2 .nil (.var 0)) (encode e) ((encode e).size + 1 + 1) :=
    Eval.elim_cons (i := 2) (a := encode e) (b := encode n) (by simp)
      (Eval.var_of_get (i := 0) (v := encode e) (by simp))
  -- step 4: the machine's input
  have s4 : Eval [encode e, Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)]
      (.cons (.var 1) (.cons (.var 0) .nil))
      (.cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil)) _ :=
    Eval.cons (Eval.var_of_get (i := 1) (v := Data.ofNat (Nat.size n)) (by simp))
      (Eval.cons (Eval.var_of_get (i := 0) (v := encode e) (by simp)) (Eval.nil _))
  -- step 5: the simulation
  obtain ⟨t₅, ht₅, h₅⟩ := UT.run e .nil (Nat.size n)
  rw [Data.size_nil] at ht₅
  have s5 := callVar_eval
    (env := [Data.cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil), encode e,
      Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)])
    (i := 0) UT.closed (v := .cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil))
    (by simp) h₅
  -- step 6: the flag
  have s6 : ∃ t₆ ≤ 4, Eval (clockedResult e .nil (Nat.size n) ::
      [Data.cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil), encode e,
        Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)])
      (.elim 0 .nil (.const (.cons .nil .nil)))
      (encode (evalWithin e .nil (Nat.size n)).isSome) t₆ := by
    unfold clockedResult
    rcases hres : evalWithin e .nil (Nat.size n) with _ | r
    · exact ⟨2, by omega, Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
    · exact ⟨4, le_rfl, Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := r) (by simp)
        (Eval.const _ (.cons .nil .nil))⟩
  obtain ⟨t₆, ht₆, h₆⟩ := s6
  refine ⟨_, ?_, Eval.let_ s1 (Eval.let_ s2 (Eval.let_ s3 (Eval.let_ s4 (Eval.let_ s5 h₆))))⟩
  simp only [Data.size_cons, Data.size_nil, Data.size_ofNat]
  omega

end Prog

/-- Decides "`e` halts on the empty input within `Nat.size n` steps", in polynomial time,
given a clocked universal machine. -/
noncomputable def PolyTimeFun.haltsWithin (UT : ClockedUniversalMachine) :
    PolyTimeFun (Prog × ℕ) Bool where
  toFun p := (evalWithin p.1 .nil (Nat.size p.2)).isSome
  code := Prog.haltsWithinProg UT.univT
  closed := Prog.haltsWithinProg_wellScoped UT.closed
  timeBound := UT.bound + (X + C 2) * (C 4 * X + C 14) + C 9 * X + C 40
  computes p := by
    obtain ⟨e, n⟩ := p
    obtain ⟨t, ht, h⟩ := Prog.haltsWithinProg_runs UT e n
    refine ⟨t, ?_, h⟩
    have h1 : Nat.size n ≤ esize n := size_le_esize_nat n
    have h2 : Nat.size n + esize e + 1 ≤ esize e + esize n + 1 := by omega
    have hmono := polynomial_eval_mono UT.bound h2
    have hp : (Nat.size n + 1 + 1) * (esize n + 1 + 2 * Nat.size n + 13) ≤
        (esize e + esize n + 1 + 2) * (4 * (esize e + esize n + 1) + 14) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      esize_prod]
    omega

@[simp] theorem PolyTimeFun.haltsWithin_apply (UT : ClockedUniversalMachine) (e : Prog) (n : ℕ) :
    PolyTimeFun.haltsWithin UT (e, n) = (evalWithin e .nil (Nat.size n)).isSome := rfl

end MIPRE.Cost


