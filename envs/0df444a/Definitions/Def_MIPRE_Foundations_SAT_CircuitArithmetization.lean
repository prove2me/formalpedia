-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
-- name    : MIPRE_Foundations_SAT_CircuitArithmetization
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:12.590141+00:00
-- url     : https://prove2.me/theorems/2244f061-9c34-4895-ae62-48995462643f
-- title:
--   Definitions of CircuitArithmetization: Bounded-degree circuit consistency polynomials In characteristic two, `1 + w + rhs` is the indicator of Boolean gate…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.CircuitArithmetization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bounded-degree circuit consistency polynomials. In characteristic two, `1 + w + rhs` is the indicator of Boolean gate consistency. Input-copy routing bounds the uses of external variables as well as gate variables. The output literal is included explicitly.
--
--   **Definitions** (5): `MIPRE.SAT.Circuit.consistencyFactor` (The consistency factor for gate `k`.); `MIPRE.SAT.Circuit.gateArith` (A gate's right-hand-side polynomial, with routed input copies.); `MIPRE.SAT.Circuit.inputWeight` (Contribution from an external-input copy link.); `MIPRE.SAT.Circuit.refWeight` (Contribution from ordinary gate references, counting repeated references.); `MIPRE.SAT.Circuit.routedArith` (All gate-consistency factors, together with the output literal.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `count_pair`, `degree_one_sub`, `prod_zero_or_one`, `sum_getD`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.CircuitArithmetization` (`MIPRE/Foundations/SAT/CircuitArithmetization.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/CircuitArithmetization.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitArithmetization.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting

/-!
# Bounded-degree circuit consistency polynomials

In characteristic two, `1 + w + rhs` is the indicator of Boolean gate
consistency. Input-copy routing bounds the uses of external variables as well
as gate variables. The output literal is included explicitly.
-/

noncomputable section

namespace MIPRE.SAT.Circuit

open MvPolynomial LowDegree Finset

variable {F : Type*} [Field F]

/-- A gate's right-hand-side polynomial, with routed input copies. -/
def gateArith (C : Circuit) (k : ℕ) : Gate → MvPolynomial (ℕ ⊕ ℕ) F
  | .input i => X (C.inputRef k i)
  | .const b => MvPolynomial.C (ofBool b)
  | .and u v => X (.inr u) * X (.inr v)
  | .or u v => 1 - (1 - X (.inr u)) * (1 - X (.inr v))
  | .not u => 1 - X (.inr u)

/-- The consistency factor for gate `k`. -/
def consistencyFactor (C : Circuit) (k : ℕ) : MvPolynomial (ℕ ⊕ ℕ) F :=
  1 + X (.inr k) + C.gateArith k (C.gates.getD k (.const false))

/-- All gate-consistency factors, together with the output literal. -/
def routedArith (C : Circuit) : MvPolynomial (ℕ ⊕ ℕ) F :=
  (∏ k ∈ range C.size, C.consistencyFactor k) * X (.inr (C.size - 1))

/-- Contribution from an external-input copy link. -/
def inputWeight (C : Circuit) (k : ℕ) (v : ℕ ⊕ ℕ) : ℕ :=
  match C.gates.getD k (.const false) with
  | .input i => if v = C.inputRef k i then 1 else 0
  | _ => 0

/-- Contribution from ordinary gate references, counting repeated references. -/
def refWeight (g : Gate) : ℕ ⊕ ℕ → ℕ
  | .inl _ => 0
  | .inr j => g.refs.count j

theorem count_pair (u w j : ℕ) :
    [u, w].count j = (if j = u then 1 else 0) + (if j = w then 1 else 0) := by
  by_cases hu : u = j <;> by_cases hw : w = j <;> simp [hu, hw, eq_comm]

theorem degree_one_sub (p : MvPolynomial (ℕ ⊕ ℕ) F) (v : ℕ ⊕ ℕ) :
    (1 - p).degreeOf v ≤ p.degreeOf v := by simpa using degreeOf_sub_le v 1 p

theorem sum_getD (l : List Gate) (f : Gate → ℕ) :
    ∑ k ∈ range l.length, f (l.getD k (.const false)) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, ih, List.map_cons, List.sum_cons]
    omega

variable [CharP F 2]

omit [CharP F 2] in
theorem prod_zero_or_one {ι : Type*} (s : Finset ι) (f : ι → F)
    (h : ∀ i ∈ s, f i = 0 ∨ f i = 1) : (∏ i ∈ s, f i) = 0 ∨ (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rcases h a (mem_insert_self _ _) with h₀ | h₁
    · simp [h₀]
    · rw [h₁, one_mul]
      exact ih (fun i hi => h i (mem_insert_of_mem hi))

end MIPRE.SAT.Circuit

end


