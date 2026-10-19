-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_FmlProg
-- name    : MIPRE_Foundations_SAT_FmlProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:14.859861+00:00
-- url     : https://prove2.me/theorems/9fd1be1d-3de0-4513-add1-5d955adc583f
-- title:
--   Definitions of FmlProg: The formula builders as programs Every builder of `FmlLib.lean` as a polynomial-time function of the ambient model,…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.FmlProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The formula builders as programs. Every builder of `FmlLib.lean` as a polynomial-time function of the ambient model, with its `toFun` the builder itself. Nothing here reasons about post-order lists: the encoding of a formula *is* the encoding of its post-order list (`SizedEncoding Fml`), so the constructors are appends (`andF`, `orF`, `notF` of `Formula.lean`) and each builder is a `foldl` over a list, whose Cobham condition is the additivity of `esize` under the constructors (`esize_and_fml` and friends) (`planning/succinct-cook-levin.md`, S3).
--
--   **Definitions** (31): `MIPRE.SAT.addBitsP` (`Fml.addBits`.); `MIPRE.SAT.addConstBitsP` (`Fml.addConstBits`.); `MIPRE.SAT.addConstCarryP` (`Fml.addConstCarry`.); `MIPRE.SAT.addConstRelP` (`Fml.addConstRel`.); `MIPRE.SAT.addStep` (The step of the adder: the carry and the reversed sum bits.); `MIPRE.SAT.addStepF` (The step of the adder, as a program.); `MIPRE.SAT.andListP` (`Fml.andList`.); `MIPRE.SAT.constBitsP` (`Fml.constBits`.); `MIPRE.SAT.eqConstP` (`Fml.eqConst`.); `MIPRE.SAT.eqFStepP` (`Fml.eqFStep`.); `MIPRE.SAT.eqFieldsP` (`Fml.eqFields`.); `MIPRE.SAT.eqStepP` (`Fml.eqStep`.); `MIPRE.SAT.fieldP` (`Fml.field`, the width in unary.); `MIPRE.SAT.incBitsP` (The successor on bit strings.); `MIPRE.SAT.ltConstP` (`Fml.ltConst`.); `MIPRE.SAT.ltFStepP` (`Fml.ltFStep`.); `MIPRE.SAT.ltFieldsP` (`Fml.ltFields`.); `MIPRE.SAT.ltStepP` (`Fml.ltStep`.); `MIPRE.SAT.maj3P` (`Fml.maj3`.); `MIPRE.SAT.muxP` (`Fml.mux`.); `MIPRE.SAT.notBoolP` (Negation on booleans.); `MIPRE.SAT.orListP` (`Fml.orList`.); `MIPRE.SAT.padP` (`padBits`, the width in unary.); `MIPRE.SAT.range'P` (`List.range'`, the length in unary.); `MIPRE.SAT.rangeStep` (The step building a range of indices, from the top down.); `MIPRE.SAT.rangeStepF` (The step of the range, as a program.); `MIPRE.SAT.subConstBitsP` (`Fml.subConstBits`.); `MIPRE.SAT.sum3P` (`Fml.sum3`.); `MIPRE.SAT.twosCompP` (`twosComp`.); `MIPRE.SAT.xnorP` (`Fml.xnor`.); `MIPRE.SAT.xorP` (`Fml.xor`.).
--
--   **Embedded lemmas** (51): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `addBitsP_apply`, `addBits_carry_le`, `addBits_mem_le`, `addConstBitsP_apply`, `addConstCarryP_apply`, `addConstRelP_apply`, `addStepF_apply`, `addStepF_bounded`, `andListP_apply`, `constBitsP_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.FmlProg` (`MIPRE/Foundations/SAT/FmlProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 14 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/FmlProg.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FmlProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_esize_list_reverse
import Theorems.Thm_MIPRE_SAT_esize_nat_add_le

/-!
# The formula builders as programs

Every builder of `FmlLib.lean` as a polynomial-time function of the ambient model, with its
`toFun` the builder itself. Nothing here reasons about post-order lists: the encoding of a
formula *is* the encoding of its post-order list (`SizedEncoding Fml`), so the constructors
are appends (`andF`, `orF`, `notF` of `Formula.lean`) and each builder is a `foldl` over a
list, whose Cobham condition is the additivity of `esize` under the constructors
(`esize_and_fml` and friends) (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.SAT

open Cost PolyTimeFun Polynomial

/-! ## The size of a constructed formula -/

theorem esize_and_fml (f g : Fml) : esize (Fml.and f g) = esize f + esize g + 7 := by
  show esize (Fml.and f g).rpn = esize f.rpn + esize g.rpn + 7
  rw [Fml.rpn]
  have h1 := esize_list_append (f.rpn ++ g.rpn) [Fml.Node.and]
  have h2 := esize_list_append f.rpn g.rpn
  have h3 : esize ([Fml.Node.and] : List Fml.Node) = 9 := rfl
  omega

theorem esize_or_fml (f g : Fml) : esize (Fml.or f g) = esize f + esize g + 9 := by
  show esize (Fml.or f g).rpn = esize f.rpn + esize g.rpn + 9
  rw [Fml.rpn]
  have h1 := esize_list_append (f.rpn ++ g.rpn) [Fml.Node.or]
  have h2 := esize_list_append f.rpn g.rpn
  have h3 : esize ([Fml.Node.or] : List Fml.Node) = 11 := rfl
  omega

theorem esize_not_fml (f : Fml) : esize (Fml.not f) = esize f + 12 := by
  show esize (Fml.not f).rpn = esize f.rpn + 12
  rw [Fml.rpn]
  have h1 := esize_list_append f.rpn [Fml.Node.not]
  have h2 : esize ([Fml.Node.not] : List Fml.Node) = 13 := rfl
  omega

/-! ## Folding with a constructor -/

/-- `Fml.andList`. -/
noncomputable def andListP : PolyTimeFun (List Fml) Fml :=
  congr ((foldlAdd Fml.andF (X + C 7) (by
      intro s a
      simp only [Fml.andF_apply, esize_and_fml, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
      omega)).comp ((PolyTimeFun.id (List Fml)).pair (const (Fml.const true))))
    Fml.andList fun _ => rfl

@[simp] theorem andListP_apply (l : List Fml) : andListP l = Fml.andList l := rfl

/-- `Fml.orList`. -/
noncomputable def orListP : PolyTimeFun (List Fml) Fml :=
  congr ((foldlAdd Fml.orF (X + C 9) (by
      intro s a
      simp only [Fml.orF_apply, esize_or_fml, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
      omega)).comp ((PolyTimeFun.id (List Fml)).pair (const (Fml.const false))))
    Fml.orList fun _ => rfl

@[simp] theorem orListP_apply (l : List Fml) : orListP l = Fml.orList l := rfl

/-! ## Equality and comparison with a constant -/

/-- `Fml.eqStep`. -/
noncomputable def eqStepP : PolyTimeFun (Fml × (Fml × Bool)) Fml :=
  Fml.andF.comp (fst.pair (PolyTimeFun.ite (snd.comp snd) (fst.comp snd)
    (Fml.notF.comp (fst.comp snd))))

@[simp] theorem eqStepP_apply (p : Fml × (Fml × Bool)) : eqStepP p = Fml.eqStep p.1 p.2 := rfl

/-- The step of `eqConst` grows the accumulator by at most the size of the pair plus 20. -/
theorem eqStepP_bound (s : Fml) (a : Fml × Bool) :
    esize (eqStepP (s, a)) ≤ esize s + (X + C 20).eval (esize a) := by
  obtain ⟨f, bb⟩ := a
  simp only [eqStepP_apply, Fml.eqStep, esize_and_fml, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, esize_prod]
  have h1 : esize (if bb then f else Fml.not f) ≤ esize f + 12 := by
    split_ifs
    · omega
    · rw [esize_not_fml]
  omega

/-- `Fml.eqConst`. -/
noncomputable def eqConstP : PolyTimeFun (List Fml × BitStr) Fml :=
  congr ((foldlAdd eqStepP (X + C 20) eqStepP_bound).comp
      (zip.pair (const (Fml.const true))))
    (fun p => Fml.eqConst p.1 p.2) fun _ => rfl

@[simp] theorem eqConstP_apply (p : List Fml × BitStr) : eqConstP p = Fml.eqConst p.1 p.2 := rfl

/-! ## Sizes of the derived builders -/

theorem esize_constFml_le (b : Bool) : esize (Fml.const b) ≤ 9 := by cases b <;> decide

theorem esize_xnor_fml (f g : Fml) : esize (Fml.xnor f g) = 2 * esize f + 2 * esize g + 47 := by
  simp only [Fml.xnor, esize_or_fml, esize_and_fml, esize_not_fml]
  omega

/-! ## The derived combinators -/

/-- `Fml.xnor`. -/
noncomputable def xnorP : PolyTimeFun (Fml × Fml) Fml :=
  Fml.orF.comp (Fml.andF.pair (Fml.andF.comp ((Fml.notF.comp fst).pair (Fml.notF.comp snd))))

@[simp] theorem xnorP_apply (p : Fml × Fml) : xnorP p = Fml.xnor p.1 p.2 := rfl

/-- `Fml.xor`. -/
noncomputable def xorP : PolyTimeFun (Fml × Fml) Fml :=
  Fml.orF.comp ((Fml.andF.comp (fst.pair (Fml.notF.comp snd))).pair
    (Fml.andF.comp ((Fml.notF.comp fst).pair snd)))

@[simp] theorem xorP_apply (p : Fml × Fml) : xorP p = Fml.xor p.1 p.2 := rfl

/-- `Fml.mux`. -/
noncomputable def muxP : PolyTimeFun (Fml × Fml × Fml) Fml :=
  Fml.orF.comp ((Fml.andF.comp (fst.pair (fst.comp snd))).pair
    (Fml.andF.comp ((Fml.notF.comp fst).pair (snd.comp snd))))

@[simp] theorem muxP_apply (p : Fml × Fml × Fml) : muxP p = Fml.mux p.1 p.2.1 p.2.2 := rfl

/-- `Fml.sum3`. -/
noncomputable def sum3P : PolyTimeFun (Fml × Fml × Fml) Fml :=
  xorP.comp ((xorP.comp (fst.pair (fst.comp snd))).pair (snd.comp snd))

@[simp] theorem sum3P_apply (p : Fml × Fml × Fml) : sum3P p = Fml.sum3 p.1 p.2.1 p.2.2 := rfl

/-- `Fml.maj3`. -/
noncomputable def maj3P : PolyTimeFun (Fml × Fml × Fml) Fml :=
  Fml.orF.comp ((Fml.andF.comp (fst.pair (fst.comp snd))).pair
    (Fml.andF.comp ((Fml.orF.comp (fst.pair (fst.comp snd))).pair (snd.comp snd))))

@[simp] theorem maj3P_apply (p : Fml × Fml × Fml) : maj3P p = Fml.maj3 p.1 p.2.1 p.2.2 := rfl

/-! ## Comparison with a constant -/

/-- `Fml.ltStep`. -/
noncomputable def ltStepP : PolyTimeFun (Fml × (Fml × Bool)) Fml :=
  Fml.orF.comp
    ((Fml.andF.comp ((Fml.notF.comp (fst.comp snd)).pair (Fml.constF.comp (snd.comp snd)))).pair
      (Fml.andF.comp ((xnorP.comp ((fst.comp snd).pair (Fml.constF.comp (snd.comp snd)))).pair fst)))

@[simp] theorem ltStepP_apply (p : Fml × (Fml × Bool)) : ltStepP p = Fml.ltStep p.1 p.2 := rfl

theorem ltStepP_bound (s : Fml) (a : Fml × Bool) :
    esize (ltStepP (s, a)) ≤ esize s + (C 3 * X + C 200).eval (esize a) := by
  obtain ⟨f, bb⟩ := a
  have hc := esize_constFml_le bb
  simp only [ltStepP_apply, Fml.ltStep, esize_or_fml, esize_and_fml, esize_not_fml,
    esize_xnor_fml, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, esize_prod]
  omega

/-- `Fml.ltConst`. -/
noncomputable def ltConstP : PolyTimeFun (List Fml × BitStr) Fml :=
  congr ((foldlAdd ltStepP (C 3 * X + C 200) ltStepP_bound).comp
      (zip.pair (const (Fml.const false))))
    (fun p => Fml.ltConst p.1 p.2) fun _ => rfl

@[simp] theorem ltConstP_apply (p : List Fml × BitStr) : ltConstP p = Fml.ltConst p.1 p.2 := rfl

/-! ## Comparison of two fields -/

/-- `Fml.eqFStep`. -/
noncomputable def eqFStepP : PolyTimeFun (Fml × (Fml × Fml)) Fml :=
  Fml.andF.comp (fst.pair (xnorP.comp snd))

@[simp] theorem eqFStepP_apply (p : Fml × (Fml × Fml)) : eqFStepP p = Fml.eqFStep p.1 p.2 := rfl

theorem eqFStepP_bound (s : Fml) (a : Fml × Fml) :
    esize (eqFStepP (s, a)) ≤ esize s + (C 2 * X + C 60).eval (esize a) := by
  obtain ⟨f, g⟩ := a
  simp only [eqFStepP_apply, Fml.eqFStep, esize_and_fml, esize_xnor_fml, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, esize_prod]
  omega

/-- `Fml.eqFields`. -/
noncomputable def eqFieldsP : PolyTimeFun (List Fml × List Fml) Fml :=
  congr ((foldlAdd eqFStepP (C 2 * X + C 60) eqFStepP_bound).comp
      (zip.pair (const (Fml.const true))))
    (fun p => Fml.eqFields p.1 p.2) fun _ => rfl

@[simp] theorem eqFieldsP_apply (p : List Fml × List Fml) : eqFieldsP p = Fml.eqFields p.1 p.2 := rfl

/-- `Fml.ltFStep`. -/
noncomputable def ltFStepP : PolyTimeFun (Fml × (Fml × Fml)) Fml :=
  Fml.orF.comp ((Fml.andF.comp ((Fml.notF.comp (fst.comp snd)).pair (snd.comp snd))).pair
    (Fml.andF.comp ((xnorP.comp snd).pair fst)))

@[simp] theorem ltFStepP_apply (p : Fml × (Fml × Fml)) : ltFStepP p = Fml.ltFStep p.1 p.2 := rfl

theorem ltFStepP_bound (s : Fml) (a : Fml × Fml) :
    esize (ltFStepP (s, a)) ≤ esize s + (C 4 * X + C 100).eval (esize a) := by
  obtain ⟨f, g⟩ := a
  simp only [ltFStepP_apply, Fml.ltFStep, esize_or_fml, esize_and_fml, esize_not_fml,
    esize_xnor_fml, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, esize_prod]
  omega

/-- `Fml.ltFields`. -/
noncomputable def ltFieldsP : PolyTimeFun (List Fml × List Fml) Fml :=
  congr ((foldlAdd ltFStepP (C 4 * X + C 100) ltFStepP_bound).comp
      (zip.pair (const (Fml.const false))))
    (fun p => Fml.ltFields p.1 p.2) fun _ => rfl

@[simp] theorem ltFieldsP_apply (p : List Fml × List Fml) :
    ltFieldsP p = Fml.ltFields p.1 p.2 := rfl

/-! ## Constant and input vectors -/

/-- `Fml.constBits`. -/
noncomputable def constBitsP : PolyTimeFun BitStr (List Fml) :=
  congr (map Fml.constF) Fml.constBits fun _ => rfl

@[simp] theorem constBitsP_apply (c : BitStr) : constBitsP c = Fml.constBits c := rfl

/-! ## The vector of input formulas -/

theorem esize_list_le_of_forall {α : Type*} [SizedEncoding α] (k : ℕ) : ∀ l : List α,
    (∀ a ∈ l, esize a ≤ k) → esize l ≤ l.length * (k + 1) + 1
  | [], _ => by simp
  | a :: l, h => by
    rw [esize_list_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := esize_list_le_of_forall k l fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h3 : (l.length + 1) * (k + 1) = l.length * (k + 1) + (k + 1) := by ring
    omega

theorem esize_mem_range'_le {a n x : ℕ} (h : x ∈ List.range' a n) : esize x ≤ 4 * esize (a + n) + 1 := by
  rw [List.mem_range'] at h
  obtain ⟨i, hi, rfl⟩ := h
  have h1 := esize_nat_le (a + 1 * i)
  have h2 : Nat.size (a + 1 * i) ≤ Nat.size (a + n) := Nat.size_le_size (by omega)
  have h3 := size_le_esize_nat (a + n)
  omega

/-- The step building a range of indices, from the top down. -/
def rangeStep (st : ℕ × List ℕ) (_ : Unit) : ℕ × List ℕ := (st.1 + 1, st.1 :: st.2)

theorem foldl_rangeStep : ∀ (u : Unary) (a : ℕ) (acc : List ℕ),
    u.foldl rangeStep (a, acc) = (a + u.length, (List.range' a u.length).reverse ++ acc)
  | [], a, acc => by simp
  | () :: u, a, acc => by
    show u.foldl rangeStep (a + 1, a :: acc) = _
    rw [foldl_rangeStep u]
    have h1 : List.range' a (u.length + 1) = a :: List.range' (a + 1) u.length := List.range'_succ ..
    simp only [List.length_cons, h1, List.reverse_cons, List.append_assoc, List.singleton_append,
      Prod.mk.injEq]
    exact ⟨by omega, trivial⟩

/-- The step of the range, as a program. -/
noncomputable def rangeStepF : PolyTimeFun ((ℕ × List ℕ) × Unit) (ℕ × List ℕ) :=
  (inc.comp (fst.comp fst)).pair (cons (fst.comp fst) (snd.comp fst))

@[simp] theorem rangeStepF_apply (p : (ℕ × List ℕ) × Unit) : rangeStepF p = rangeStep p.1 p.2 := rfl

theorem rangeStepF_bounded : FoldBounded rangeStepF (C 30 * (X + 1) * (X + 1)) := by
  intro l s₀ pre xs hl
  obtain ⟨a, acc⟩ := s₀
  set N := esize (l, ((a, acc) : ℕ × List ℕ)) with hN
  have hNe : N = esize l + (esize a + esize acc + 1) + 1 := by simp [hN]
  have hpre : pre.length ≤ esize l := by
    have := congrArg List.length hl
    have := length_le_esize_list l
    simp only [List.length_append] at *; omega
  show esize (List.foldl (fun s b => rangeStepF (s, b)) (a, acc) pre) ≤ _
  rw [show (fun (s : ℕ × List ℕ) (b : Unit) => rangeStepF (s, b)) = rangeStep from rfl,
    foldl_rangeStep pre a acc]
  have h1 : esize (a + pre.length) ≤ 5 * N := by
    have := esize_nat_add_le a pre.length
    omega
  have h2 : ∀ x ∈ List.range' a pre.length, esize x ≤ 20 * N + 1 := by
    intro x hx
    have := esize_mem_range'_le hx
    omega
  have h3 := esize_list_le_of_forall (20 * N + 1) (List.range' a pre.length) h2
  rw [List.length_range'] at h3
  have h4 : pre.length * (20 * N + 1 + 1) ≤ N * (20 * N + 2) := by
    exact Nat.mul_le_mul (by omega) (by omega)
  have h5 : N * (20 * N + 2) = 20 * (N * N) + 2 * N := by ring
  have h6 := esize_list_append (List.range' a pre.length).reverse acc
  rw [esize_list_reverse] at h6
  have h7 : esize ((a + pre.length, (List.range' a pre.length).reverse ++ acc) :
      ℕ × List ℕ) = esize (a + pre.length) +
      esize ((List.range' a pre.length).reverse ++ acc) + 1 := rfl
  have hexp : (C 30 * (X + 1) * (X + 1)).eval N = 30 * (N * N) + 60 * N + 30 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  rw [hexp]
  omega

/-- `List.range'`, the length in unary. -/
noncomputable def range'P : PolyTimeFun (ℕ × Unary) (List ℕ) :=
  congr (reverse.comp (snd.comp
      ((foldl rangeStepF (C 30 * (X + 1) * (X + 1)) rangeStepF_bounded).comp
        (snd.pair (fst.pair (const []))))))
    (fun p => List.range' p.1 p.2.length) (by
      rintro ⟨a, u⟩
      simp only [comp_apply, reverse_apply, snd_apply, foldl_apply, pair_apply,
        fst_apply, const_apply, rangeStepF_apply]
      rw [foldl_rangeStep u a []]
      simp only [List.append_nil, List.reverse_reverse])

@[simp] theorem range'P_apply (p : ℕ × Unary) : range'P p = List.range' p.1 p.2.length := rfl

/-- `Fml.field`, the width in unary. -/
noncomputable def fieldP : PolyTimeFun (ℕ × Unary) (List Fml) :=
  congr ((map Fml.inpF).comp range'P) (fun p => Fml.field p.1 p.2.length) (by
    rintro ⟨a, u⟩
    simp only [comp_apply, map_apply, range'P_apply]
    rfl)

@[simp] theorem fieldP_apply (p : ℕ × Unary) : fieldP p = Fml.field p.1 p.2.length := rfl

/-! ## The adder -/

theorem esize_xor_fml (f g : Fml) : esize (Fml.xor f g) = 2 * esize f + 2 * esize g + 47 := by
  simp only [Fml.xor, esize_or_fml, esize_and_fml, esize_not_fml]
  omega

theorem esize_maj3_fml (f g h : Fml) :
    esize (Fml.maj3 f g h) = 2 * esize f + 2 * esize g + esize h + 32 := by
  simp only [Fml.maj3, esize_or_fml, esize_and_fml]
  omega

theorem esize_sum3_fml (f g h : Fml) :
    esize (Fml.sum3 f g h) = 4 * esize f + 4 * esize g + 2 * esize h + 141 := by
  simp only [Fml.sum3, esize_xor_fml]
  omega

/-- The carry out of the adder grows linearly in the width. -/
theorem addBits_carry_le (E : ℕ) : ∀ (fs : List Fml) (c : BitStr) (cin : Fml),
    (∀ f ∈ fs, esize f ≤ E) →
      esize (Fml.addBits fs c cin).2 ≤ esize cin + fs.length * (2 * E + 50)
  | [], c, cin, _ => by simp [Fml.addBits]
  | f :: fs, [], cin, _ => by
    simp only [Fml.addBits, List.length_cons]
    have : (fs.length + 1) * (2 * E + 50) = fs.length * (2 * E + 50) + (2 * E + 50) := by ring
    omega
  | f :: fs, b :: c, cin, h => by
    have hf : esize f ≤ E := h f (List.mem_cons_self ..)
    have hcb := esize_constFml_le b
    have hstep : esize (Fml.maj3 f (Fml.const b) cin) ≤ esize cin + (2 * E + 50) := by
      rw [esize_maj3_fml]; omega
    have hIH := addBits_carry_le E fs c (Fml.maj3 f (Fml.const b) cin)
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hlen : (fs.length + 1) * (2 * E + 50) = fs.length * (2 * E + 50) + (2 * E + 50) := by ring
    show esize (Fml.addBits fs c (Fml.maj3 f (Fml.const b) cin)).2 ≤ _
    rw [List.length_cons]
    omega

/-- Every sum bit of the adder is bounded by the carry bound. -/
theorem addBits_mem_le (E : ℕ) : ∀ (fs : List Fml) (c : BitStr) (cin : Fml),
    (∀ f ∈ fs, esize f ≤ E) → ∀ s ∈ (Fml.addBits fs c cin).1,
      esize s ≤ 4 * E + 2 * (esize cin + fs.length * (2 * E + 50)) + 200
  | [], c, cin, _ => by simp [Fml.addBits]
  | f :: fs, [], cin, _ => by simp [Fml.addBits]
  | f :: fs, b :: c, cin, h => by
    have hf : esize f ≤ E := h f (List.mem_cons_self ..)
    have hcb := esize_constFml_le b
    have hstep : esize (Fml.maj3 f (Fml.const b) cin) ≤ esize cin + (2 * E + 50) := by
      rw [esize_maj3_fml]; omega
    have hIH := addBits_mem_le E fs c (Fml.maj3 f (Fml.const b) cin)
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hlen : (fs.length + 1) * (2 * E + 50) = fs.length * (2 * E + 50) + (2 * E + 50) := by ring
    intro s hs
    rw [List.length_cons]
    show esize s ≤ 4 * E + 2 * (esize cin + (fs.length + 1) * (2 * E + 50)) + 200
    have hmem : s = Fml.sum3 f (Fml.const b) cin ∨
        s ∈ (Fml.addBits fs c (Fml.maj3 f (Fml.const b) cin)).1 := by
      have : (Fml.addBits (f :: fs) (b :: c) cin).1 = Fml.sum3 f (Fml.const b) cin ::
          (Fml.addBits fs c (Fml.maj3 f (Fml.const b) cin)).1 := rfl
      rw [this, List.mem_cons] at hs
      exact hs
    rcases hmem with rfl | hs'
    · rw [esize_sum3_fml]; omega
    · have := hIH s hs'
      omega

/-- The step of the adder: the carry and the reversed sum bits. -/
def addStep (st : Fml × List Fml) (p : Fml × Bool) : Fml × List Fml :=
  (Fml.maj3 p.1 (Fml.const p.2) st.1, Fml.sum3 p.1 (Fml.const p.2) st.1 :: st.2)

theorem foldl_addStep : ∀ (fs : List Fml) (c : BitStr) (cin : Fml) (acc : List Fml),
    (fs.zip c).foldl addStep (cin, acc) =
      ((Fml.addBits fs c cin).2, (Fml.addBits fs c cin).1.reverse ++ acc)
  | [], c, cin, acc => by simp [Fml.addBits]
  | f :: fs, [], cin, acc => by simp [Fml.addBits]
  | f :: fs, b :: c, cin, acc => by
    rw [List.zip_cons_cons, List.foldl_cons]
    show (fs.zip c).foldl addStep (Fml.maj3 f (Fml.const b) cin,
      Fml.sum3 f (Fml.const b) cin :: acc) = _
    rw [foldl_addStep fs c (Fml.maj3 f (Fml.const b) cin)]
    show _ = ((Fml.addBits fs c (Fml.maj3 f (Fml.const b) cin)).2,
      (Fml.sum3 f (Fml.const b) cin :: (Fml.addBits fs c (Fml.maj3 f (Fml.const b) cin)).1).reverse
        ++ acc)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The step of the adder, as a program. -/
noncomputable def addStepF : PolyTimeFun ((Fml × List Fml) × (Fml × Bool)) (Fml × List Fml) :=
  (maj3P.comp ((fst.comp snd).pair ((Fml.constF.comp (snd.comp snd)).pair (fst.comp fst)))).pair
    (cons (sum3P.comp ((fst.comp snd).pair ((Fml.constF.comp (snd.comp snd)).pair (fst.comp fst))))
      (snd.comp fst))

@[simp] theorem addStepF_apply (p : (Fml × List Fml) × (Fml × Bool)) :
    addStepF p = addStep p.1 p.2 := rfl

theorem zip_map_fst_snd {α β : Type*} : ∀ l : List (α × β),
    (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | q :: l => by rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_map_fst_snd l]

theorem length_addBits_le : ∀ (fs : List Fml) (c : BitStr) (cin : Fml),
    (Fml.addBits fs c cin).1.length ≤ fs.length
  | [], _, _ => by simp [Fml.addBits]
  | f :: fs, [], _ => by simp [Fml.addBits]
  | f :: fs, b :: c, cin => by
    show (Fml.sum3 f (Fml.const b) cin ::
      (Fml.addBits fs c (Fml.maj3 f (Fml.const b) cin)).1).length ≤ (f :: fs).length
    rw [List.length_cons, List.length_cons]
    have := length_addBits_le fs c (Fml.maj3 f (Fml.const b) cin)
    omega

theorem addStepF_bounded : FoldBounded addStepF (C 400 * (X + 1) * (X + 1) * (X + 1)) := by
  intro l s₀ pre xs hl
  obtain ⟨cin, acc⟩ := s₀
  set N := esize (l, ((cin, acc) : Fml × List Fml)) with hN
  have hNe : N = esize l + (esize cin + esize acc + 1) + 1 := by simp [hN]
  clear_value N
  have hpre : pre.length ≤ esize l := by
    have := congrArg List.length hl
    have := length_le_esize_list l
    simp only [List.length_append] at *; omega
  have hE : ∀ q ∈ pre, esize q.1 ≤ N := by
    intro q hq
    have h1 := esize_mem_le (show q ∈ l by rw [hl]; exact List.mem_append_left _ hq)
    have h2 : esize q.1 + esize q.2 + 1 = esize q := by
      obtain ⟨u, v⟩ := q; rfl
    omega
  show esize (List.foldl (fun s b => addStepF (s, b)) (cin, acc) pre) ≤ _
  rw [show (fun (s : Fml × List Fml) (b : Fml × Bool) => addStepF (s, b)) = addStep from rfl,
    ← zip_map_fst_snd pre, foldl_addStep (pre.map Prod.fst) (pre.map Prod.snd) cin acc]
  have hfsE : ∀ f ∈ pre.map Prod.fst, esize f ≤ N := by
    intro f hf
    rw [List.mem_map] at hf
    obtain ⟨q, hq, rfl⟩ := hf
    exact hE q hq
  have hcar := addBits_carry_le N (pre.map Prod.fst) (pre.map Prod.snd) cin hfsE
  have hmem := addBits_mem_le N (pre.map Prod.fst) (pre.map Prod.snd) cin hfsE
  rw [List.length_map] at hcar hmem
  have hprodN : pre.length * (2 * N + 50) ≤ N * (2 * N + 50) := Nat.mul_le_mul (by omega) le_rfl
  have hcar' : esize (Fml.addBits (pre.map Prod.fst) (pre.map Prod.snd) cin).2 ≤
      N + N * (2 * N + 50) := by omega
  have hmem' : ∀ s ∈ (Fml.addBits (pre.map Prod.fst) (pre.map Prod.snd) cin).1,
      esize s ≤ 4 * N + 2 * (N + N * (2 * N + 50)) + 200 := by
    intro s hs
    have := hmem s hs
    omega
  have hlist := esize_list_le_of_forall (4 * N + 2 * (N + N * (2 * N + 50)) + 200)
    (Fml.addBits (pre.map Prod.fst) (pre.map Prod.snd) cin).1 hmem'
  have hlen1 : (Fml.addBits (pre.map Prod.fst) (pre.map Prod.snd) cin).1.length ≤ N := by
    have := length_addBits_le (pre.map Prod.fst) (pre.map Prod.snd) cin
    rw [List.length_map] at this
    omega
  have hprod2 : (Fml.addBits (pre.map Prod.fst) (pre.map Prod.snd) cin).1.length *
      (4 * N + 2 * (N + N * (2 * N + 50)) + 200 + 1) ≤
      N * (4 * N + 2 * (N + N * (2 * N + 50)) + 200 + 1) := Nat.mul_le_mul hlen1 le_rfl
  have happ := esize_list_append
    (Fml.addBits (pre.map Prod.fst) (pre.map Prod.snd) cin).1.reverse acc
  rw [esize_list_reverse] at happ
  obtain ⟨P, hP⟩ : ∃ P, P = N * N := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = N * N * N := ⟨_, rfl⟩
  have hexp : (C 400 * (X + 1) * (X + 1) * (X + 1)).eval N =
      400 * Q + 1200 * P + 1200 * N + 400 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [hP, hQ]; ring
  have hNpos : 0 < N := by omega
  have hNN : P ≤ Q := by
    rw [hP, hQ]
    calc N * N = N * N * 1 := by ring
      _ ≤ N * N * N := Nat.mul_le_mul_left _ hNpos
  have hN1 : N ≤ P := by
    rw [hP]
    calc N = N * 1 := by ring
      _ ≤ N * N := Nat.mul_le_mul_left _ hNpos
  have he1 : N * (2 * N + 50) = 2 * P + 50 * N := by rw [hP]; ring
  have he2 : N * (4 * N + 2 * (N + N * (2 * N + 50)) + 200 + 1) =
      106 * P + 4 * Q + 201 * N := by rw [hP, hQ]; ring
  clear hP hQ
  rw [hexp, esize_prod]
  omega

/-- `Fml.addBits`. -/
noncomputable def addBitsP : PolyTimeFun ((List Fml × BitStr) × Fml) (List Fml × Fml) :=
  let F : PolyTimeFun ((List Fml × BitStr) × Fml) (Fml × List Fml) :=
    (foldl addStepF (C 400 * (X + 1) * (X + 1) * (X + 1)) addStepF_bounded).comp
      ((zip.comp fst).pair (snd.pair (const [])))
  congr ((reverse.comp (snd.comp F)).pair (fst.comp F))
    (fun p => Fml.addBits p.1.1 p.1.2 p.2) (by
      intro p
      show ((((zip p.1).foldl (fun s b => addStepF (s, b)) (p.2, [])).2).reverse,
        (((zip p.1).foldl (fun s b => addStepF (s, b)) (p.2, [])).1)) = _
      rw [show (fun (s : Fml × List Fml) (b : Fml × Bool) => addStepF (s, b)) = addStep from rfl,
        zip_apply, foldl_addStep]
      simp only [List.append_nil, List.reverse_reverse])

@[simp] theorem addBitsP_apply (p : (List Fml × BitStr) × Fml) :
    addBitsP p = Fml.addBits p.1.1 p.1.2 p.2 := rfl

/-- `Fml.addConstBits`. -/
noncomputable def addConstBitsP : PolyTimeFun (List Fml × BitStr) (List Fml) :=
  fst.comp (addBitsP.comp ((PolyTimeFun.id _).pair (const (Fml.const false))))

@[simp] theorem addConstBitsP_apply (p : List Fml × BitStr) :
    addConstBitsP p = Fml.addConstBits p.1 p.2 := rfl

/-- `Fml.addConstCarry`. -/
noncomputable def addConstCarryP : PolyTimeFun (List Fml × BitStr) Fml :=
  snd.comp (addBitsP.comp ((PolyTimeFun.id _).pair (const (Fml.const false))))

@[simp] theorem addConstCarryP_apply (p : List Fml × BitStr) :
    addConstCarryP p = Fml.addConstCarry p.1 p.2 := rfl

/-- `Fml.addConstRel`. -/
noncomputable def addConstRelP : PolyTimeFun ((List Fml × List Fml) × BitStr) Fml :=
  Fml.andF.comp
    ((eqFieldsP.comp ((snd.comp fst).pair (addConstBitsP.comp ((fst.comp fst).pair snd)))).pair
      (Fml.notF.comp (addConstCarryP.comp ((fst.comp fst).pair snd))))

@[simp] theorem addConstRelP_apply (p : (List Fml × List Fml) × BitStr) :
    addConstRelP p = Fml.addConstRel p.1.1 p.1.2 p.2 := rfl

/-! ## Padding -/

/-- `padBits`, the width in unary. -/
noncomputable def padP : PolyTimeFun (Unary × BitStr) BitStr :=
  congr (ap₂ append snd (ap₂ replicate (ap₂ drop fst (ap₁ length snd)) (const false)))
    (fun p => padBits p.1.length p.2) (by
      rintro ⟨u, l⟩
      simp only [ap₂_apply, ap₁_apply, append_apply, replicate_apply, drop_apply, snd_apply,
        fst_apply, length_apply, length_unary, List.length_drop, padBits, const_apply])

@[simp] theorem padP_apply (p : Unary × BitStr) : padP p = padBits p.1.length p.2 := rfl

/-! ## The two's complement -/

/-- The successor on bit strings. -/
noncomputable def incBitsP : PolyTimeFun BitStr BitStr where
  toFun := incBits
  code := Prog.incBitsProg
  closed := Prog.incBitsProg_wellScoped
  timeBound := (X + 2) * (3 * X + 32)
  computes l := by
    obtain ⟨t, ht, hrun⟩ := Prog.incBitsProg_runs l
    refine ⟨t, ?_, hrun⟩
    refine ht.trans ?_
    have h1 : l.length ≤ esize l := length_le_esize_bitStr _
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    exact Nat.mul_le_mul (by omega) le_rfl

@[simp] theorem incBitsP_apply (l : BitStr) : incBitsP l = incBits l := rfl

/-- Negation on booleans. -/
noncomputable def notBoolP : PolyTimeFun Bool Bool :=
  congr (PolyTimeFun.ite (PolyTimeFun.id Bool) (const false) (const true)) Bool.not (by
    intro b
    cases b <;> rfl)

@[simp] theorem notBoolP_apply (b : Bool) : notBoolP b = !b := rfl

/-- `twosComp`. -/
noncomputable def twosCompP : PolyTimeFun BitStr BitStr :=
  congr (take.comp ((incBitsP.comp (map notBoolP)).pair length)) twosComp (by
    intro c
    simp only [comp_apply, take_apply, pair_apply, incBitsP_apply, map_apply, length_apply,
      length_unary]
    rfl)

@[simp] theorem twosCompP_apply (c : BitStr) : twosCompP c = twosComp c := rfl

/-- `Fml.subConstBits`. -/
noncomputable def subConstBitsP : PolyTimeFun (List Fml × BitStr) (List Fml) :=
  congr (addConstBitsP.comp (fst.pair (twosCompP.comp snd)))
    (fun p => Fml.subConstBits p.1 p.2) fun _ => rfl

@[simp] theorem subConstBitsP_apply (p : List Fml × BitStr) :
    subConstBitsP p = Fml.subConstBits p.1 p.2 := rfl

end MIPRE.SAT


