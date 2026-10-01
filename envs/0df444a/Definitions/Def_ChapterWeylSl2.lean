-- Prove2me | Definitions.Def_ChapterWeylSl2
-- name    : ChapterWeylSl2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:05:43.186085+00:00
-- url     : https://prove2.me/theorems/c06ce17c-61fa-4bfd-abde-b70fd359cc93
-- title:
--   Chapter WeylSl2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWeylSl2.lean`): generated def bundle for ChapterWeylSl2. See BookProof/ChapterWeylSl2.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWeylSl2.lean

import Mathlib


/-!
# Weyl's complete reducibility theorem for `sl(2,ℂ)`

`book.tex` states (Note 23, "Weyl theorem"):

> *All finite-dimensional representations of a semi-simple Lie group (such as SL(2,C))
> are completely reducible.*

and `BookProof.ChapterA3w` carries this as the named external hypothesis
`WeylCompleteReducibility`.  This file **proves** the theorem for the Lie algebra
`sl(2,ℂ)`, i.e. for every finite-dimensional complex vector space carrying operators
`E`, `F`, `H` with the `sl₂` commutation relations

`[H, E] = 2E`,  `[H, F] = -2F`,  `[E, F] = H`,

every invariant subspace has an invariant complement (`weyl_complete_reducibility`).

The proof is the classical Casimir argument, developed from scratch (Mathlib has no
Casimir element and no Weyl theorem):

* `cas` — the Casimir operator `2(EF + FE) + H²`, shown to commute with `E`, `F`, `H`;
* `exists_highestWeight` — every nonzero invariant subspace contains a vector `w ≠ 0`
  with `E w = 0` and `H w = lam • w`;
* `sl2_string_H`, `sl2_string_E` — the `sl₂`-string relations for `Fᵏ w`, giving
  `lam = m` for a natural number `m` and `F^(m+1) w = 0`;
* `cas_highestWeight` — the Casimir acts on such a `w` by `m² + 2m`, which vanishes
  only for the trivial module;
* `codim_one` — the codimension-one case, by induction on the dimension using
  quotient and sub-representations;
* `weyl_complete_reducibility` — the general case, via the `sl₂`-action
  `X · f = X f - f X` on `End V` applied to the space of operators that map `V` into
  `W` and act on `W` by a scalar.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A representation of the Lie algebra `sl(2,ℂ)` on `V`: a triple of operators with the
standard commutation relations. -/
structure Sl2Rep (V : Type u) [AddCommGroup V] [Module ℂ V] where
  /-- The raising operator. -/
  E : Module.End ℂ V
  /-- The lowering operator. -/
  F : Module.End ℂ V
  /-- The Cartan (weight) operator. -/
  H : Module.End ℂ V
  /-- `[H, E] = 2E`. -/
  he : H * E - E * H = 2 • E
  /-- `[H, F] = -2F`. -/
  hf : H * F - F * H = -(2 • F)
  /-- `[E, F] = H`. -/
  hef : E * F - F * E = H

namespace Sl2Rep

variable (R : Sl2Rep V)

/-- A subspace is **invariant** iff it is stable under `E`, `F` and `H`. -/
def IsInv (W : Submodule ℂ V) : Prop :=
  (∀ x ∈ W, R.E x ∈ W) ∧ (∀ x ∈ W, R.F x ∈ W) ∧ (∀ x ∈ W, R.H x ∈ W)

/-- The **Casimir operator** `2(EF + FE) + H²`. -/
def cas : Module.End ℂ V := 2 • (R.E * R.F + R.F * R.E) + R.H * R.H

variable {R}









/-! ### The Casimir operator is central -/







/-! ### Sub- and quotient representations -/

/-- The restriction of a representation to an invariant subspace. -/
def restr (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) : Sl2Rep ↥W where
  E := R.E.restrict hW.1
  F := R.F.restrict hW.2.1
  H := R.H.restrict hW.2.2
  he := by
    ext x
    have h := congrArg (fun T : Module.End ℂ V => T (x : V)) R.he
    simpa [LinearMap.restrict_coe_apply] using h
  hf := by
    ext x
    have h := congrArg (fun T : Module.End ℂ V => T (x : V)) R.hf
    simpa [LinearMap.restrict_coe_apply] using h
  hef := by
    ext x
    have h := congrArg (fun T : Module.End ℂ V => T (x : V)) R.hef
    simpa [LinearMap.restrict_coe_apply] using h







/-- The quotient representation on `V ⧸ W` for an invariant subspace `W`. -/
def quot (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) : Sl2Rep (V ⧸ W) where
  E := W.mapQ W R.E hW.1
  F := W.mapQ W R.F hW.2.1
  H := W.mapQ W R.H hW.2.2
  he := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun v => ?_
    have h := congrArg (fun T : Module.End ℂ V => T v) R.he
    simp only [Module.End.mul_apply, LinearMap.sub_apply, two_nsmul, LinearMap.add_apply] at h
    simp only [Submodule.Quotient.mk''_eq_mk, Module.End.mul_apply, LinearMap.sub_apply,
      two_nsmul, LinearMap.add_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub,
      ← Submodule.Quotient.mk_add, h]
  hf := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun v => ?_
    have h := congrArg (fun T : Module.End ℂ V => T v) R.hf
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, two_nsmul,
      LinearMap.add_apply] at h
    simp only [Submodule.Quotient.mk''_eq_mk, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.neg_apply, two_nsmul, LinearMap.add_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_neg, h]
  hef := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun v => ?_
    have h := congrArg (fun T : Module.End ℂ V => T v) R.hef
    simp only [Module.End.mul_apply, LinearMap.sub_apply] at h
    simp only [Submodule.Quotient.mk''_eq_mk, Module.End.mul_apply, LinearMap.sub_apply,
      Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, h]







/-! ### Weights, highest-weight vectors and `sl₂`-strings -/

section Weights

variable {R : Sl2Rep V}





















end Weights

/-! ### Invariance of the kernel of the Casimir, and trivial modules -/

section Structure

variable {R : Sl2Rep V}



















/-! ### The codimension-one case -/



/-! ### The adjoint action on operators -/

/-- The adjoint action `ad a : f ↦ a f - f a` of an operator on all operators. -/
def ad (a : Module.End ℂ V) : Module.End ℂ (Module.End ℂ V) :=
  LinearMap.mulLeft ℂ a - LinearMap.mulRight ℂ a

@[simp] theorem ad_apply (a f : Module.End ℂ V) : ad a f = a * f - f * a := by
  simp [ad, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]

theorem ad_add (a b : Module.End ℂ V) : ad (a + b) = ad a + ad b := by
  refine LinearMap.ext fun f => ?_
  simp only [ad_apply, LinearMap.add_apply]
  noncomm_ring

theorem ad_neg (a : Module.End ℂ V) : ad (-a) = -ad a := by
  refine LinearMap.ext fun f => ?_
  simp only [ad_apply, LinearMap.neg_apply]
  noncomm_ring

theorem ad_two_nsmul (a : Module.End ℂ V) : ad (2 • a) = 2 • ad a := by
  rw [two_nsmul, ad_add, two_nsmul]

/-- `ad` is a homomorphism of Lie algebras. -/
theorem ad_bracket (a b : Module.End ℂ V) : ad a * ad b - ad b * ad a = ad (a * b - b * a) := by
  refine LinearMap.ext fun f => ?_
  simp only [Module.End.mul_apply, LinearMap.sub_apply, ad_apply]
  noncomm_ring

/-- The `sl₂`-representation induced on the space of all operators. -/
def adRep (R : Sl2Rep V) : Sl2Rep (Module.End ℂ V) where
  E := ad R.E
  F := ad R.F
  H := ad R.H
  he := by rw [ad_bracket, R.he, ad_two_nsmul]
  hf := by rw [ad_bracket, R.hf, ad_neg, ad_two_nsmul]
  hef := by rw [ad_bracket, R.hef]







/-- The operators that map `V` into `W` and act on `W` by a scalar. -/
def scalarOps (W : Submodule ℂ V) : Submodule ℂ (Module.End ℂ V) where
  carrier := {f | (∀ v : V, f v ∈ W) ∧ ∃ c : ℂ, ∀ w ∈ W, f w = c • w}
  add_mem' := by
    rintro f g ⟨hf1, cf, hf2⟩ ⟨hg1, cg, hg2⟩
    exact ⟨fun v => W.add_mem (hf1 v) (hg1 v), cf + cg, fun w hw => by
      simp [hf2 w hw, hg2 w hw, add_smul]⟩
  zero_mem' := ⟨fun _ => W.zero_mem, 0, fun w _ => by simp⟩
  smul_mem' := by
    rintro a f ⟨hf1, cf, hf2⟩
    exact ⟨fun v => W.smul_mem a (hf1 v), a * cf, fun w hw => by
      simp [hf2 w hw, mul_smul]⟩





/-! ### Weyl's theorem -/



end Structure

end Sl2Rep

end BookProof.ChapterWeylSl2


