-- Prove2me | Definitions.Def_MIPRE_Foundations_Weyl
-- name    : MIPRE_Foundations_Weyl
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:57.534058+00:00
-- url     : https://prove2.me/theorems/1915cb2c-db05-4b73-8070-a006bf6f130f
-- title:
--   Definitions of Weyl: Generalized Pauli operators over a field of characteristic two The paper's `sec:generalized-pauli`: for `a ∈ F_q^n` the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Weyl` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Generalized Pauli operators over a field of characteristic two. The paper's `sec:generalized-pauli`: for `a ∈ F_q^n` the `X`-type operator shifts the computational basis of `(C^q)^{⊗ n}` by `a`, the `Z`-type operator is diagonal with the phase `ω^{tr(a · b)}`, and the two families *twisted-commute*, `τ^X(a) τ^Z(b) = ω^{-tr(a · b)} τ^Z(b) τ^X(a)`. This is the missing half of the Pauli basis test's infrastructure. `MIPRE/LCS/Pauli.lean` is the `2 × 2` Pauli matrices for the Magic Square; what the appendix's expansion stage and its swap isometry both run on is the `F_q` Weyl system, and that is…
--
--   **Definitions** (11): `MIPRE.Weyl.IsWeylFamily` (A family of self-adjoint operators indexed by `F_q^n` representing its additive group.); `MIPRE.Weyl.dotF` (The `F_q`-valued pairing, before the trace.); `MIPRE.Weyl.proj` (**The spectral projector** of a Weyl family at the eigenvalue pattern `e`: the Fourier average of the family against the character of `e`.); `MIPRE.Weyl.syn` (**The syndrome projector**: onto the eigenvectors whose pairing with `v` is `a`.); `MIPRE.Weyl.synOf` (**A coarse-graining of the eigenbasis measurement**: the sum of the spectral projectors over a level set of an arbitrary label `φ`.); `MIPRE.Weyl.trDot` (`tr_{q → 2}(a · b)` for `a, b ∈ F_q^n`.); `MIPRE.Weyl.trDotL` (The form against a fixed `b`, as an `F_2`-linear functional.); `MIPRE.Weyl.trMulL` (The trace against a fixed field element, as an `F_2`-linear functional on `F_q`.); `MIPRE.Weyl.wX` (**The `X`-type Weyl operator**: the shift of the computational basis by `a`.); `MIPRE.Weyl.wZ` (**The `Z`-type Weyl operator**: diagonal, with the sign `(-1)^{tr(b · i)}`.); `MIPRE.Weyl.zProj` (The rank-one projector onto the computational basis vector `c`.).
--
--   **Embedded lemmas** (20): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `add_add_cancel`, `add_add_cancel_vec`, `add_self`, `add_self_vec`, `trDotL_apply`, `trDot_add_left`, `trDot_zero_left`, `trDot_zero_right`, `two_eq_zero`, `wX_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Weyl` (`MIPRE/Foundations/Weyl.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Weyl.lean; blueprint def:generalized-pauli, def:weyl-epr

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Theorems.Thm_MIPRE_sgn_add
import Theorems.Thm_MIPRE_star_sgn

/-!
# Generalized Pauli operators over a field of characteristic two

The paper's `sec:generalized-pauli`: for `a ∈ F_q^n` the `X`-type operator shifts the
computational basis of `(C^q)^{⊗ n}` by `a`, the `Z`-type operator is diagonal with the phase
`ω^{tr(a · b)}`, and the two families *twisted-commute*,
`τ^X(a) τ^Z(b) = ω^{-tr(a · b)} τ^Z(b) τ^X(a)`.

This is the missing half of the Pauli basis test's infrastructure. `MIPRE/LCS/Pauli.lean` is the
`2 × 2` Pauli matrices for the Magic Square; what the appendix's expansion stage and its swap
isometry both run on is the `F_q` Weyl system, and that is this file.

## Two deliberate restrictions

**Characteristic two.** The paper states the construction over `F_p` with `ω = e^{2πi/p}` and
then specializes. This file is only the `p = 2` case, where `ω = -1` and every phase is the real
sign `MIPRE.sgn` of `MIPRE/Foundations/Sign.lean`. That is not a loss for this project: the
Pauli basis test's parameters are *admissible* (`def:admissible`), which means `q = 2^k`, and no
consumer instantiates it elsewhere. What it buys is large — there are no roots of unity, the
operators are self-adjoint involutions rather than order-`p` unitaries, so they are genuine
`±1`-observables, and `(τ^W(a))² = 1` is where the paper needs `(σ^W(a))^p = I`.

**One matrix, not an iterated Kronecker product.** `(C^q)^{⊗ n}` is presented as
`Matrix (n → F) (n → F) C`: the basis of the `n`-fold tensor power is indexed by the functions
`n → F`, which *is* `F_q^n`. So `τ^W(a)` is a single matrix and the `n`-register statements are
the one-register statements with no associativity bookkeeping. The index type `n` is an arbitrary
finite type rather than `Fin n`, which is what lets the Pauli basis test use it at
`n = (Fin m → Bool)`, the indexing `MIPRE.LowDegree` already uses for `F_q^M` with `M = 2^m`.

## What is here

`wX`, `wZ`, the group laws, self-adjointness, involutivity, unitarity, and the twisted
commutation `wX_mul_wZ`. Then the `Z`-eigenbasis projectors, the expansion of `wZ` in them, and
the Fourier inversion that recovers a projector from an average of operators --- the identity the
expansion stage's `E_r (-1)^{tr(ar)} Ŵ^r(u)` is an instance of. The `X` side and the maximally
entangled state come next; they go through the Fourier transform conjugating one family into the
other.
-/

noncomputable section

namespace MIPRE.Weyl

open Finset Matrix

/-! ## Characteristic two

`Algebra (ZMod 2) F` is the whole of the hypothesis: the algebra map from a field is injective,
so `F` has characteristic two, and every element is its own additive inverse. -/

section CharTwo

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}

theorem two_eq_zero : (2 : F) = 0 := by
  have h : ((2 : ℕ) : F) = 0 := by
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    calc ((2 : ℕ) : F) = algebraMap (ZMod 2) F ((2 : ℕ) : ZMod 2) := (map_natCast _ 2).symm
      _ = 0 := by rw [h2, map_zero]
  simpa using h

theorem add_self (x : F) : x + x = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem add_add_cancel (x y : F) : x + y + y = x := by
  rw [add_assoc, add_self, add_zero]

theorem add_self_vec (a : n → F) : a + a = 0 := by
  funext l; exact add_self (a l)

theorem add_add_cancel_vec (a b : n → F) : a + b + b = a := by
  funext l; exact add_add_cancel (a l) (b l)

end CharTwo

/-! ## The bilinear form

`trDot a b = tr_{q → 2}(a · b)`, the `F_2`-valued form the phases are built from. It is the
symmetric bilinear form that decides commutation, and `trDotL` is it as a linear functional,
which is the shape `card_filter_ker_mul_prime` consumes. -/

section Form

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]

/-- `tr_{q → 2}(a · b)` for `a, b ∈ F_q^n`. -/
def trDot (a b : n → F) : ZMod 2 := Algebra.trace (ZMod 2) F (∑ l, a l * b l)

@[simp] theorem trDot_zero_left (b : n → F) : trDot (0 : n → F) b = 0 := by
  simp [trDot]

@[simp] theorem trDot_zero_right (a : n → F) : trDot a (0 : n → F) = 0 := by
  simp [trDot]

theorem trDot_add_left (a a' b : n → F) : trDot (a + a') b = trDot a b + trDot a' b := by
  rw [trDot, trDot, trDot, ← map_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp [add_mul]

/-- The form against a fixed `b`, as an `F_2`-linear functional. -/
def trDotL (b : n → F) : (n → F) →ₗ[ZMod 2] ZMod 2 where
  toFun a := trDot a b
  map_add' a a' := trDot_add_left a a' b
  map_smul' c a := by
    rcases (show c = 0 ∨ c = 1 from by revert c; decide) with rfl | rfl
    · simp
    · simp

@[simp] theorem trDotL_apply (b a : n → F) : trDotL b a = trDot a b := rfl

end Form

section Operators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The operators

The section's variables are what `Matrix (n → F) (n → F) ℂ` needs in order to exist at all ---
`DecidableEq (n → F)` for the diagonal and the identity, `Fintype (n → F)` for a matrix product ---
so the `rfl`-level lemmas below do not each use all of them. The linter is silenced for the
section rather than `omit`-ed a dozen times. -/

set_option linter.unusedSectionVars false

/-- **The `X`-type Weyl operator**: the shift of the computational basis by `a`. -/
def wX (a : n → F) : Matrix (n → F) (n → F) ℂ :=
  Matrix.of fun j i => if j = i + a then 1 else 0

/-- **The `Z`-type Weyl operator**: diagonal, with the sign `(-1)^{tr(b · i)}`. -/
def wZ (b : n → F) : Matrix (n → F) (n → F) ℂ :=
  Matrix.diagonal fun i => sgn (trDot b i)

@[simp] theorem wX_apply (a : n → F) (j i : n → F) :
    wX a j i = if j = i + a then 1 else 0 := rfl

@[simp] theorem wZ_apply (b : n → F) (j i : n → F) :
    wZ b j i = if j = i then sgn (trDot b i) else 0 := by
  rw [wZ, Matrix.diagonal_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-! ### The group laws -/

@[simp] theorem wX_zero : wX (0 : n → F) = 1 := by
  ext j i
  rw [wX_apply, add_zero, Matrix.one_apply]

@[simp] theorem wZ_zero : wZ (0 : n → F) = 1 := by
  ext j i
  rw [wZ_apply, trDot_zero_left, sgn_zero, Matrix.one_apply]

theorem wX_mul_wX (a a' : n → F) : wX a * wX a' = wX (a + a') := by
  ext j i
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (i + a') (fun k _ hk => by
      rw [show wX a' k i = 0 from by rw [wX_apply, if_neg hk], mul_zero])
    fun h => absurd (Finset.mem_univ _) h]
  rw [wX_apply, wX_apply, if_pos rfl, mul_one, wX_apply]
  congr 1
  rw [add_comm a a', add_assoc]

theorem wZ_mul_wZ (b b' : n → F) : wZ b * wZ b' = wZ (b + b') := by
  rw [wZ, wZ, wZ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [trDot_add_left, sgn_add]

@[simp] theorem wX_mul_self (a : n → F) : wX a * wX a = 1 := by
  rw [wX_mul_wX, add_self_vec, wX_zero]

@[simp] theorem wZ_mul_self (b : n → F) : wZ b * wZ b = 1 := by
  rw [wZ_mul_wZ, add_self_vec, wZ_zero]

/-! ### Self-adjointness and unitarity -/

@[simp] theorem wX_conjTranspose (a : n → F) : (wX a)ᴴ = wX a := by
  ext j i
  rw [Matrix.conjTranspose_apply, wX_apply, wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, if_pos (by rw [h, add_add_cancel_vec]), star_one]
  · rw [if_neg h, if_neg (fun hh : i = j + a => h (by rw [hh, add_add_cancel_vec])), star_zero]

@[simp] theorem wZ_conjTranspose (b : n → F) : (wZ b)ᴴ = wZ b := by
  ext j i
  rw [Matrix.conjTranspose_apply, wZ_apply, wZ_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, h, star_sgn]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

/-! ### Within a family the operators commute -/

/-! ### The twisted commutation relation

The paper's `eq:twisted-fq`. In characteristic two the phase `ω^{-tr(a·b)}` is `(-1)^{tr(a·b)}`
and there is no sign to track on the exponent. -/

/-! ## The cancellation lemma

The paper's `lem:cancellation` (Fact 3.2 of `NW19`) in the case that matters here: the character
`a ↦ (-1)^{tr(a · c)}` of `F_q^n` is trivial exactly when `c = 0`, and a nontrivial character sums
to zero. Its `\cnote` warns that the ambient space must be a subspace over the *base* field; here
it is the whole of `F_q^n` over `F_2`, so the hypothesis is met with nothing to check.

The count comes from `card_filter_ker_mul_prime`, which says the kernel of a nonzero `F_2`-functional
has index two --- exactly half the vectors give each sign, so they cancel. -/

/-! ## The `Z`-eigenbasis projectors, and the Fourier inversion

`zProj c` projects onto the computational basis vector `c`, and `wZ` expands in them with the
sign coefficients (`eq:pauli-obs-proj`). The inversion `eq:pauli-inversion-0` recovers a
projector from an average of operators; it is the identity `E_r (-1)^{tr(ar)} Ŵ^r(u)` of the
expansion stage, with the average over a *line* `r ↦ r · v` rather than over the whole space. -/

/-- The rank-one projector onto the computational basis vector `c`. -/
def zProj (c : n → F) : Matrix (n → F) (n → F) ℂ :=
  Matrix.diagonal fun i => if i = c then 1 else 0

@[simp] theorem zProj_apply (c j i : n → F) :
    zProj c j i = if j = i then (if i = c then 1 else 0) else 0 := by
  by_cases h : j = i
  · subst h
    rw [zProj, Matrix.diagonal_apply_eq, if_pos rfl]
  · rw [zProj, Matrix.diagonal_apply_ne _ h, if_neg h]

/-! ## The spectral projectors, once for both families

Everything the appendix does with the eigenbasis projectors of one family uses only three facts
about it: it represents the additive group of `F_q^n`, its operators are self-adjoint, and the
identity sits at `0`. `IsWeylFamily` is those three, `proj` is the Fourier average that builds the
projectors out of them, and the spectral statements are then proved once. `wZ` is one instance and
`wX` the other, so the paper's Fourier transform conjugating one family into the other is not
needed to reach the `X`-side projectors --- worth avoiding, since that transform carries a
`q^{-1/2}` and would put a square root into matrix entries. -/

/-- A family of self-adjoint operators indexed by `F_q^n` representing its additive group. The
two Weyl families are the instances, and the spectral theory needs nothing else. -/
structure IsWeylFamily (w : (n → F) → Matrix (n → F) (n → F) ℂ) : Prop where
  /-- The family is a homomorphism from the additive group. -/
  map_add : ∀ a a', w (a + a') = w a * w a'
  /-- The identity sits at `0`. -/
  map_zero : w 0 = 1
  /-- Every operator is self-adjoint. -/
  selfAdjoint : ∀ a, (w a)ᴴ = w a

/-- **The spectral projector** of a Weyl family at the eigenvalue pattern `e`: the Fourier average
of the family against the character of `e`. For `wZ` it is `zProj e` (`proj_wZ`); for `wX` it is
the projector onto the `X`-eigenbasis vector the paper writes `|e_X⟩`. -/
def proj (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    Matrix (n → F) (n → F) ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a

variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}

/-! ## The syndrome projectors

The expansion stage does not average the Weyl family over the whole of `F_q^n`: it averages over
the *line* `r ↦ r · v` for a fixed `v ∈ F_q^n`, against the character of a field element `a`. What
comes out is the projector onto the eigenvectors whose `F_q`-valued pairing with `v` is `a` --- the
paper's `τ^{W,u}_a = τ^W_{[g_·(u) = a]}` of `eq:qld-point-obs-def`, at `v = ind_m(u)`. -/

/-- The `F_q`-valued pairing, before the trace. -/
def dotF (a b : n → F) : F := ∑ l, a l * b l

/-- The trace against a fixed field element, as an `F_2`-linear functional on `F_q`. -/
def trMulL (x : F) : F →ₗ[ZMod 2] ZMod 2 where
  toFun r := Algebra.trace (ZMod 2) F (r * x)
  map_add' r r' := by rw [add_mul, map_add]
  map_smul' c r := by
    rcases (show c = 0 ∨ c = 1 from by revert c; decide) with rfl | rfl
    · simp
    · simp

/-- **A coarse-graining of the eigenbasis measurement**: the sum of the spectral projectors over
a level set of an arbitrary label `φ`. The syndrome projector below is this at
`φ = ⟨·, v⟩`, and the expansion stage's line measurements are this at the label ``restriction of
the low-degree encoding to the line''. -/
def synOf {C : Type*} [DecidableEq C] (w : (n → F) → Matrix (n → F) (n → F) ℂ)
    (φ : (n → F) → C) (o : C) : Matrix (n → F) (n → F) ℂ :=
  ∑ e ∈ univ.filter fun e => φ e = o, proj w e

/-- **The syndrome projector**: onto the eigenvectors whose pairing with `v` is `a`. The paper's
`eq:qld-point-obs-def`. -/
def syn (w : (n → F) → Matrix (n → F) (n → F) ℂ) (v : n → F) (a : F) :
    Matrix (n → F) (n → F) ℂ :=
  ∑ e ∈ univ.filter fun e => dotF e v = a, proj w e

end Operators

end MIPRE.Weyl

end


