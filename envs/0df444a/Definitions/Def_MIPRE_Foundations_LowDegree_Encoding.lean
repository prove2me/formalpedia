-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
-- name    : MIPRE_Foundations_LowDegree_Encoding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:21.543442+00:00
-- url     : https://prove2.me/theorems/c751a651-ebda-467b-a258-683de9e73071
-- title:
--   Definitions of Encoding: The low-degree code The paper's `sec:ld-encoding`: the multilinear indicator polynomials of the Boolean subcube, the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.Encoding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The low-degree code. The paper's `sec:ld-encoding`: the multilinear indicator polynomials of the Boolean subcube, the *low-degree encoding* `g_a` of a vector indexed by the subcube, and the decoding map `Coded_H`. This is the code the PCP of `thm:pcp-decider` commits to, and the `a = Coded(g₁)` of its soundness conclusion. * `ind y = ∏_{i : yᵢ = 1} Xᵢ · ∏_{i : yᵢ = 0} (1 - Xᵢ)` — on the subcube, `1` at `y` and `0` elsewhere (`eval_ind`); * `pt y` is the subcube point of `y : Fin m → Bool`, identifying `{0,1}` with `{0, 1} ⊆ F`; * `ldEnc a = ∑_y a y · ind y` — the multilinear polynomial with…
--
--   **Definitions** (6): `MIPRE.LowDegree.coded` (The Boolean decoding map `Coded = Coded_{0,1}`.); `MIPRE.LowDegree.codedOn` (`Coded_H g`: read `g` off the subcube, replacing any value outside `H` by `0`.); `MIPRE.LowDegree.ind` (`ind y`, the multilinear polynomial that is `1` at the subcube point `y` and `0` at every other subcube point.); `MIPRE.LowDegree.ldEnc` (The **low-degree encoding** of `a : {0,1}^m → F`: the multilinear polynomial with `g_a(y) = a y` on the subcube.); `MIPRE.LowDegree.ofBool` (`{0,1} ⊆ F` on single bits.); `MIPRE.LowDegree.pt` (The point of `F^m` corresponding to `y ∈ {0,1}^m`, under `{0,1} ⊆ F`.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_ind`, `eval_ldEnc`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.Encoding` (`MIPRE/Foundations/LowDegree/Encoding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/Encoding.lean; blueprint def:ld-encoding

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/Encoding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# The low-degree code

The paper's `sec:ld-encoding`: the multilinear indicator polynomials of the Boolean subcube,
the *low-degree encoding* `g_a` of a vector indexed by the subcube, and the decoding map
`Coded_H`. This is the code the PCP of `thm:pcp-decider` commits to, and the `a = Coded(g₁)`
of its soundness conclusion.

* `ind y = ∏_{i : yᵢ = 1} Xᵢ · ∏_{i : yᵢ = 0} (1 - Xᵢ)` — on the subcube, `1` at `y` and `0`
  elsewhere (`eval_ind`);
* `pt y` is the subcube point of `y : Fin m → Bool`, identifying `{0,1}` with `{0, 1} ⊆ F`;
* `ldEnc a = ∑_y a y · ind y` — the multilinear polynomial with `g_a(y) = a y`
  (`eval_ldEnc`), of individual degree at most `1` (`degreeOf_ldEnc_le`);
* `codedOn H g` reads `g` back off the subcube, replacing a value outside `H` by `0`. It is a
  left inverse of `ldEnc` on `H`-valued vectors (`codedOn_ldEnc`), and `coded = codedOn {0,1}`
  is the Boolean decoding map, which always returns a `{0,1}`-valued vector (`coded_eq`).

Nothing here is about the cost model: these are polynomials, and the verifier's arithmetic on
their bit representations is a separate matter (the admissible field of `lem:self-dual-basis`).
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [CommRing F] {m : ℕ}

/-! ## The subcube -/

/-- `{0,1} ⊆ F` on single bits. -/
def ofBool (b : Bool) : F := if b then 1 else 0

/-- The point of `F^m` corresponding to `y ∈ {0,1}^m`, under `{0,1} ⊆ F`. -/
def pt (y : Fin m → Bool) : Fin m → F := fun i => ofBool (y i)

/-! ## The indicator polynomials -/

/-- `ind y`, the multilinear polynomial that is `1` at the subcube point `y` and `0` at every
other subcube point. -/
def ind (y : Fin m → Bool) : MvPolynomial (Fin m) F :=
  ∏ i, if y i then X i else 1 - X i

theorem eval_ind (y z : Fin m → Bool) :
    eval (pt z) (ind y) = if y = z then (1 : F) else 0 := by
  have key : ∀ i : Fin m, eval (pt z) (if y i then X i else 1 - X i)
      = if y i = z i then (1 : F) else 0 := by
    intro i
    cases hy : y i <;> cases hz : z i <;> simp [pt, ofBool, hz]
  rw [ind, map_prod]
  simp only [key]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

/-! ## The encoding -/

/-- The **low-degree encoding** of `a : {0,1}^m → F`: the multilinear polynomial with
`g_a(y) = a y` on the subcube. -/
def ldEnc (a : (Fin m → Bool) → F) : MvPolynomial (Fin m) F :=
  ∑ y : Fin m → Bool, C (a y) * ind y

@[simp] theorem eval_ldEnc (a : (Fin m → Bool) → F) (y : Fin m → Bool) :
    eval (pt y) (ldEnc a) = a y := by
  rw [ldEnc, map_sum]
  simp only [map_mul, eval_C, eval_ind]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz; simp [if_neg (fun h : z = y => hz h)]
  · intro h; exact absurd (mem_univ y) h

/-! ## The decoding map -/

variable [DecidableEq F]

/-- `Coded_H g`: read `g` off the subcube, replacing any value outside `H` by `0`. -/
def codedOn (H : Finset F) (g : MvPolynomial (Fin m) F) : (Fin m → Bool) → F :=
  fun y => if eval (pt y) g ∈ H then eval (pt y) g else 0

/-- The Boolean decoding map `Coded = Coded_{0,1}`. -/
def coded (g : MvPolynomial (Fin m) F) : (Fin m → Bool) → F :=
  codedOn {0, 1} g

end MIPRE.LowDegree

end


