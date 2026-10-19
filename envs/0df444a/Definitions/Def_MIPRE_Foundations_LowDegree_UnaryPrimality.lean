-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
-- name    : MIPRE_Foundations_LowDegree_UnaryPrimality
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:17.305391+00:00
-- url     : https://prove2.me/theorems/6394c99c-c044-476a-8091-e5059eb09f6b
-- title:
--   Definitions of UnaryPrimality: Polynomial-time trial primality for unary degree parameters
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.UnaryPrimality` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial-time trial primality for unary degree parameters
--
--   **Definitions** (8): `MIPRE.LowDegree.DegreeArithmetic.primeUnary` (The raw trial-division predicate.); `MIPRE.LowDegree.DegreeArithmetic.primeUnaryProg` (One polynomial-time primality program on every unary input.); `MIPRE.LowDegree.DegreeArithmetic.trialCheck` (Ignore candidate divisors zero and one, and reject every other actual divisor.); `_private.MIPRE.Foundations.LowDegree.UnaryPrimality.0.MIPRE.LowDegree.DegreeArithmetic.PrimeState`; `_private.MIPRE.Foundations.LowDegree.UnaryPrimality.0.MIPRE.LowDegree.DegreeArithmetic.allTrialsProg`; `_private.MIPRE.Foundations.LowDegree.UnaryPrimality.0.MIPRE.LowDegree.DegreeArithmetic.primeStep`; `_private.MIPRE.Foundations.LowDegree.UnaryPrimality.0.MIPRE.LowDegree.DegreeArithmetic.primeStepProg`; `_private.MIPRE.Foundations.LowDegree.UnaryPrimality.0.MIPRE.LowDegree.DegreeArithmetic.trialCheckProg`.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `primeUnaryProg_apply`, `primeUnary_eq`, `fold_primeStep`, `primeStep_growth`, `tail_empty_iff`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.UnaryPrimality` (`MIPRE/Foundations/LowDegree/UnaryPrimality.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 9 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/UnaryPrimality.lean; blueprint lem:binary-degree-decomposition

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/UnaryPrimality.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Theorems.Thm_MIPRE_LowDegree_DegreeArithmetic_mem_descendingUnary_iff

/-! # Polynomial-time trial primality for unary degree parameters -/

noncomputable section

namespace MIPRE.LowDegree.DegreeArithmetic

open Cost Cost.PolyTimeFun Polynomial

theorem tail_empty_iff (u : Unary) : u.tail.isEmpty = true ↔ u.length ≤ 1 := by
  rw [List.isEmpty_iff_length_eq_zero, List.length_tail, Nat.sub_eq_zero_iff_le]

/-- Ignore candidate divisors zero and one, and reject every other actual divisor. -/
def trialCheck (q d : Unary) : Bool := decide (d.length ≤ 1 ∨ ¬d.length ∣ q.length)

def trialCheckProg : PolyTimeFun (Unary × Unary) Bool :=
  congr (ite (isEmptyProg.comp (tail.comp snd)) (const true)
    (ite (dvdUnaryProg.comp (snd.pair fst)) (const false) (const true)))
    (fun s => trialCheck s.1 s.2) (by
      rintro ⟨q, d⟩
      change (if d.tail.isEmpty then true else if decide (d.length ∣ q.length) then false else true) = _
      by_cases hd : d.length ≤ 1
      · have he := (tail_empty_iff d).mpr hd
        simp [he, trialCheck, hd]
      · have he : d.tail.isEmpty = false := Bool.eq_false_iff.mpr (fun h => hd ((tail_empty_iff d).mp h))
        simp [he, trialCheck, hd])

abbrev PrimeState := Unary × Bool

def primeStep (s : PrimeState) (d : Unary) : PrimeState :=
  (s.1, s.2 && trialCheck s.1 d)

theorem fold_primeStep (ds : List Unary) (q : Unary) (b : Bool) :
    ds.foldl primeStep (q, b) = (q, b && ds.all (trialCheck q)) := by
  induction ds generalizing b with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons]
    change ds.foldl primeStep (q, b && trialCheck q d) = _
    rw [ih, List.all_cons, Bool.and_assoc]

def primeStepProg : PolyTimeFun (PrimeState × Unary) PrimeState :=
  let q := fst.comp fst
  congr (q.pair (ite (snd.comp fst) (trialCheckProg.comp (q.pair snd)) (const false)))
    (fun s => primeStep s.1 s.2) (by
      rintro ⟨⟨q, b⟩, d⟩
      cases b <;> rfl)

theorem primeStep_growth (s : PrimeState) (d : Unary) :
    esize (primeStepProg (s, d)) ≤ esize s + (2 : Polynomial ℕ).eval (esize d) := by
  rcases s with ⟨q, b⟩
  change esize (q, b && trialCheck q d) ≤ _
  have hb : esize (b && trialCheck q d) ≤ 3 := by cases b && trialCheck q d <;> decide
  have hb₀ : 1 ≤ esize b := by cases b <;> decide
  simp only [esize_prod, eval_ofNat]
  omega

def allTrialsProg : PolyTimeFun (List Unary × Unary) Bool :=
  let scan := foldlAdd primeStepProg 2 primeStep_growth
  congr (snd.comp (scan.comp (fst.pair (snd.pair (const true)))))
    (fun s => s.1.all (trialCheck s.2)) (by
      rintro ⟨ds, q⟩
      change (ds.foldl primeStep (q, true)).2 = _
      rw [fold_primeStep]
      rfl)

/-- The raw trial-division predicate. -/
def primeUnary (q : Unary) : Bool :=
  if q.tail.isEmpty then false else (descendingUnary q.tail).all (trialCheck q)

/-- Trial division through all smaller unary candidates is exactly primality. -/
theorem primeUnary_eq (q : Unary) : primeUnary q = decide q.length.Prime := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, Nat.prime_def_lt']
  unfold primeUnary
  by_cases hq : q.length ≤ 1
  · have he : q.tail.isEmpty = true := (tail_empty_iff q).mpr hq
    simp [he]
    omega
  · have he : q.tail.isEmpty = false := by
      exact Bool.eq_false_iff.mpr (fun h => hq ((tail_empty_iff q).mp h))
    simp only [he, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, trialCheck, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨by omega, ?_⟩
      intro m hm hmq
      have hd : unary m ∈ descendingUnary q.tail :=
        (mem_descendingUnary_iff _ _).mpr (by simp; omega)
      have hh := h (unary m) hd
      simp only [length_unary] at hh
      exact hh.resolve_left (by omega)
    · rintro ⟨hq₂, h⟩ d hd
      have hlt := (mem_descendingUnary_iff _ _).mp hd
      simp only [List.length_tail] at hlt
      by_cases hd₁ : d.length ≤ 1
      · exact Or.inl hd₁
      · exact Or.inr (h d.length (by omega) (by omega))

/-- One polynomial-time primality program on every unary input. -/
def primeUnaryProg : PolyTimeFun Unary Bool :=
  congr (ite (isEmptyProg.comp tail) (const false)
    (allTrialsProg.comp ((descendingUnaryProg.comp tail).pair (PolyTimeFun.id _))))
    (fun q => decide q.length.Prime) (by
      intro q
      change primeUnary q = _
      exact primeUnary_eq q)

@[simp] theorem primeUnaryProg_apply (q : Unary) : primeUnaryProg q = decide q.length.Prime := rfl

end MIPRE.LowDegree.DegreeArithmetic

end


