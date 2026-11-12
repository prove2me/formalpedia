-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutation
-- name    : OddOrder_GroupTheory_RepresentationTheory_BrauerPermutation
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:06:00.299726+00:00
-- url     : https://prove2.me/theorems/4e547558-637d-4b33-ad5a-10a2b96c59d7
-- title:
--   Brauer's permutation lemma
-- statement:
--   Formalizes Brauer's permutation lemma, Isaacs, *Character Theory of Finite Groups* (1976), Thm 6.32: the number of real irreducible characters of $G$ equals the number of self-inverse conjugacy classes. The classical proof uses invertibility of the character table and compatibility of two involutions: $C\mapsto C^{-1}$ on conjugacy classes and $\chi\mapsto\bar\chi$ on $\mathrm{Irr}\,G$.
--
--   Main definitions: `inv` (the inversion involution on conjugacy classes), `IsReal` and `RealClass` (self-inverse classes), `classInvPerm` (the class-inversion permutation pulled back to irreducible characters) and `classPerm` (the pullback of an arbitrary permutation of conjugacy classes).
--
--   The bundle also proves 24 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterRowOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IsReal
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SecondOrthogonality
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

namespace ConjClasses

variable {G : Type*} [Group G]

private theorem commute_of_sq_commute_of_odd_card [Finite G] (hodd : Odd (Nat.card G))
    {x g : G} (hcomm : Commute (x ^ 2) g) : Commute x g := by
  have hcop_card : Nat.Coprime 2 (Nat.card G) := hodd.coprime_two_left
  have hcop_order : Nat.Coprime 2 (orderOf x) :=
    hcop_card.coprime_dvd_right (orderOf_dvd_natCard x)
  rcases exists_pow_eq_self_of_coprime (x := x) hcop_order with ⟨m, hm⟩
  rw [← hm]
  exact hcomm.pow_left m

/-- In a finite group of odd order, an element conjugate to its inverse is trivial. -/
theorem eq_one_of_isConj_inv_of_odd_card [Finite G] (hodd : Odd (Nat.card G)) {g : G}
    (hg : IsConj g⁻¹ g) : g = 1 := by
  rw [isConj_iff] at hg
  rcases hg with ⟨x, hx⟩
  have hx_inv : x * g * x⁻¹ = g⁻¹ := by
    have h := congrArg Inv.inv hx
    simpa [mul_assoc] using h
  have hx_sq_conj : x ^ 2 * g * (x ^ 2)⁻¹ = g := by
    calc
      x ^ 2 * g * (x ^ 2)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by
        rw [pow_two]
        group
      _ = x * g⁻¹ * x⁻¹ := by rw [hx_inv]
      _ = g := hx
  have hx_sq_comm : Commute (x ^ 2) g := by
    rw [commute_iff_eq]
    calc
      x ^ 2 * g = (x ^ 2 * g * (x ^ 2)⁻¹) * x ^ 2 := by group
      _ = g * x ^ 2 := by rw [hx_sq_conj]
  have hx_comm : Commute x g := commute_of_sq_commute_of_odd_card hodd hx_sq_comm
  have hg_self_inv : g = g⁻¹ := by
    calc
      g = x * g⁻¹ * x⁻¹ := hx.symm
      _ = g⁻¹ := by
        rw [(hx_comm.inv_right).eq]
        group
  have hg_sq : g ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (fun y : G => g * y) hg_self_inv).trans (mul_inv_cancel g)
  have hcop_card : Nat.Coprime 2 (Nat.card G) := hodd.coprime_two_left
  have hcop_order : Nat.Coprime 2 (orderOf g) :=
    hcop_card.coprime_dvd_right (orderOf_dvd_natCard g)
  have horder_dvd_two : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg_sq
  have horder_one : orderOf g = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_order horder_dvd_two (dvd_refl (orderOf g))
  exact orderOf_eq_one_iff.mp horder_one

/-- Conjugacy is preserved by inversion: if `a ~ b`, then `a⁻¹ ~ b⁻¹`. -/
theorem isConj_inv {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  rw [isConj_iff] at h ⊢
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, by group⟩

/-- The inversion involution on conjugacy classes: `⟦g⟧ ↦ ⟦g⁻¹⟧`. -/
def inv : ConjClasses G → ConjClasses G :=
  Quotient.lift (fun g : G => ConjClasses.mk g⁻¹) fun _ _ h =>
    mk_eq_mk_iff_isConj.2 (isConj_inv h)

@[simp] theorem inv_mk (g : G) : inv (ConjClasses.mk g) = ConjClasses.mk g⁻¹ := rfl

@[simp] theorem inv_one : inv (1 : ConjClasses G) = 1 := by
  change inv (ConjClasses.mk 1) = ConjClasses.mk 1
  simp [inv_mk]

@[simp] theorem inv_inv (C : ConjClasses G) : inv (inv C) = C := by
  induction C using Quotient.inductionOn with
  | _ g =>
    change inv (inv (ConjClasses.mk g)) = ConjClasses.mk g
    simp [inv_mk]

theorem inv_involutive : Function.Involutive (inv : ConjClasses G → ConjClasses G) :=
  inv_inv

/-- A conjugacy class is **real** (self-inverse) when its inversion equals itself,
i.e. `g` and `g⁻¹` are conjugate for any representative `g`. -/
def IsReal (C : ConjClasses G) : Prop := inv C = C

theorem isReal_mk_iff (g : G) : IsReal (ConjClasses.mk g) ↔ IsConj g⁻¹ g := by
  unfold IsReal
  rw [inv_mk, mk_eq_mk_iff_isConj]

@[simp] theorem isReal_one : IsReal (1 : ConjClasses G) := inv_one

/-- The type of real (self-inverse) conjugacy classes of `G`. -/
abbrev RealClass (G : Type*) [Group G] :=
  {C : ConjClasses G // IsReal C}

namespace RealClass

instance : Coe (RealClass G) (ConjClasses G) :=
  ⟨fun C => C.1⟩

@[simp] theorem coe_mk (C : ConjClasses G) (hC : IsReal C) :
    ((⟨C, hC⟩ : RealClass G) : ConjClasses G) = C :=
  rfl

@[simp] theorem isReal (C : RealClass G) : IsReal (C : ConjClasses G) :=
  C.2

@[ext] theorem ext {C D : RealClass G}
    (h : (C : ConjClasses G) = (D : ConjClasses G)) : C = D :=
  Subtype.ext h

end RealClass

/-- In a finite group of odd order, the only real conjugacy class is the
identity class. -/
theorem eq_one_of_isReal_of_odd_card [Finite G] (hodd : Odd (Nat.card G))
    {C : ConjClasses G} (hC : IsReal C) : C = 1 := by
  induction C using Quotient.inductionOn with
  | _ g =>
    have hg_conj : IsConj g⁻¹ g := (isReal_mk_iff g).mp hC
    have hg_one : g = 1 := eq_one_of_isConj_inv_of_odd_card hodd hg_conj
    change ConjClasses.mk g = ConjClasses.mk (1 : G)
    simp [hg_one]

/-- In a finite group of odd order, the subtype of real conjugacy classes is
subsingleton. -/
theorem subsingleton_realClasses_of_odd_card [Finite G] (hodd : Odd (Nat.card G)) :
    Subsingleton (RealClass G) where
  allEq A B := by
    exact Subtype.ext (by
      rw [eq_one_of_isReal_of_odd_card hodd A.property,
        eq_one_of_isReal_of_odd_card hodd B.property])

/-- In a finite group of odd order, there is exactly one real conjugacy class:
the identity class. -/
theorem card_realClasses_eq_one_of_odd_card [Finite G] (hodd : Odd (Nat.card G)) :
    Nat.card (RealClass G) = 1 := by
  let := subsingleton_realClasses_of_odd_card (G := G) hodd
  exact Nat.card_of_subsingleton ⟨1, isReal_one⟩

end ConjClasses

namespace OddOrder.RepresentationTheory

/-- The class-inversion permutation pulled back to the `IrreducibleCharacter G`
side via a `CharacterTableIndexing` row-column equivalence. -/
noncomputable def classInvPerm {G : Type*} [Group G] (idx : CharacterTableIndexing G) :
    Equiv.Perm (IrreducibleCharacter G) :=
  (idx.rowColumnEquiv.trans
    (Function.Involutive.toPerm
      (ConjClasses.inv : ConjClasses G → ConjClasses G) ConjClasses.inv_involutive)).trans
    idx.rowColumnEquiv.symm

@[simp] theorem classInvPerm_apply {G : Type*} [Group G]
    (idx : CharacterTableIndexing G) (ψ : IrreducibleCharacter G) :
    classInvPerm idx ψ = idx.rowColumnEquiv.symm (ConjClasses.inv (idx.rowColumnEquiv ψ)) :=
  rfl

/-- The pullback to `IrreducibleCharacter G` of an arbitrary permutation `π` of the conjugacy
classes, via a `CharacterTableIndexing` row-column equivalence.  This generalizes `classInvPerm`
(the `π = ConjClasses.inv` case) to an arbitrary class permutation, as needed for Brauer's
permutation lemma applied to a conjugation (rather than inversion) action. -/
noncomputable def classPerm {G : Type*} [Group G] (idx : CharacterTableIndexing G)
    (π : Equiv.Perm (ConjClasses G)) : Equiv.Perm (IrreducibleCharacter G) :=
  (idx.rowColumnEquiv.trans π).trans idx.rowColumnEquiv.symm

@[simp] theorem classPerm_apply {G : Type*} [Group G]
    (idx : CharacterTableIndexing G) (π : Equiv.Perm (ConjClasses G))
    (ψ : IrreducibleCharacter G) :
    classPerm idx π ψ = idx.rowColumnEquiv.symm (π (idx.rowColumnEquiv ψ)) :=
  rfl

theorem rowColumnEquiv_classPerm {G : Type*} [Group G]
    (idx : CharacterTableIndexing G) (π : Equiv.Perm (ConjClasses G))
    (ψ : IrreducibleCharacter G) :
    idx.rowColumnEquiv (classPerm idx π ψ) = π (idx.rowColumnEquiv ψ) := by
  simp

theorem classInvPerm_involutive {G : Type*} [Group G]
    (idx : CharacterTableIndexing G) : Function.Involutive (classInvPerm idx) := by
  intro ψ
  simp [ConjClasses.inv_involutive _]

theorem classInvPerm_symm {G : Type*} [Group G]
    (idx : CharacterTableIndexing G) : (classInvPerm idx).symm = classInvPerm idx :=
  Function.Involutive.symm_eq_self_of_involutive _ (classInvPerm_involutive idx)

/-- Fixed points of `classInvPerm idx` are in bijection with real conjugacy classes
via the row-column equivalence. -/
noncomputable def realClassEquivFixedPointsClassInv {G : Type*} [Group G]
    (idx : CharacterTableIndexing G) :
    ConjClasses.RealClass G ≃ {ψ : IrreducibleCharacter G // classInvPerm idx ψ = ψ} where
  toFun C := ⟨idx.rowColumnEquiv.symm (C : ConjClasses G), by
    have h : ConjClasses.inv (C : ConjClasses G) = (C : ConjClasses G) := C.2
    simp [h]⟩
  invFun ψ := ⟨idx.rowColumnEquiv (ψ : IrreducibleCharacter G), by
    have hψ : classInvPerm idx (ψ : IrreducibleCharacter G) =
        (ψ : IrreducibleCharacter G) := ψ.2
    have h := congrArg idx.rowColumnEquiv hψ
    simp only [classInvPerm_apply, Equiv.apply_symm_apply] at h
    exact h⟩
  left_inv C := by ext; simp
  right_inv ψ := by ext; simp

/-- Fixed points of `classPerm idx π` are in bijection with `π`-fixed conjugacy classes via the
row-column equivalence.  Generalizes `realClassEquivFixedPointsClassInv` (the inversion case). -/
noncomputable def fixedPointsClassPermEquiv {G : Type*} [Group G]
    (idx : CharacterTableIndexing G) (π : Equiv.Perm (ConjClasses G)) :
    {ψ : IrreducibleCharacter G // classPerm idx π ψ = ψ} ≃
      {C : ConjClasses G // π C = C} where
  toFun ψ := ⟨idx.rowColumnEquiv (ψ : IrreducibleCharacter G), by
    have hψ : classPerm idx π (ψ : IrreducibleCharacter G) = (ψ : IrreducibleCharacter G) := ψ.2
    have h := congrArg idx.rowColumnEquiv hψ
    rwa [rowColumnEquiv_classPerm] at h⟩
  invFun C := ⟨idx.rowColumnEquiv.symm (C : ConjClasses G), by
    have hC : π (C : ConjClasses G) = (C : ConjClasses G) := C.2
    simp [hC]⟩
  left_inv ψ := by ext; simp
  right_inv C := by ext; simp

/-- Fixed points of a permutation and its inverse are naturally equivalent. -/
noncomputable def fixedPointsPermSymmEquiv {α : Type*} (e : Equiv.Perm α) :
    Function.fixedPoints e.symm ≃ Function.fixedPoints e where
  toFun x := ⟨x.1, ((Equiv.symm_apply_eq e).1 x.2).symm⟩
  invFun x := ⟨x.1, (Equiv.symm_apply_eq e).2 x.2.symm⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- **Matrix-algebra core of Brauer's permutation lemma.**

If the permutation matrices of `σ` and `τ` are conjugate via an invertible matrix `A`
(`σ.permMatrix * A = A * τ.permMatrix`), then `σ` and `τ` have the same number of fixed points:
their permutation matrices, being conjugate, share a trace, and the trace of a permutation matrix
over `ℂ` counts fixed points (`Matrix.trace_permutation`).

This is the reusable matrix kernel shared by the inversion form `brauer_permutation_lemma` and the
conjugation form `brauer_permutation_lemma_general`. -/
theorem ncard_fixedPoints_eq_of_permMatrix_conj {n : Type*} [Fintype n] [DecidableEq n]
    (σ τ : Equiv.Perm n) (A : Matrix n n ℂ) [Invertible A]
    (hmat : σ.permMatrix ℂ * A = A * τ.permMatrix ℂ) :
    (Function.fixedPoints σ).ncard = (Function.fixedPoints τ).ncard := by
  have hσ_conj : σ.permMatrix ℂ = A * τ.permMatrix ℂ * A⁻¹ := by
    have h := congrArg (fun M => M * A⁻¹) hmat
    rwa [Matrix.mul_assoc (σ.permMatrix ℂ), Matrix.mul_inv_of_invertible, Matrix.mul_one] at h
  have htrace : Matrix.trace (σ.permMatrix ℂ) = Matrix.trace (τ.permMatrix ℂ) := by
    rw [hσ_conj, Matrix.trace_mul_cycle, Matrix.inv_mul_of_invertible, Matrix.one_mul]
  have hσ_tr : Matrix.trace (σ.permMatrix ℂ) = ((Function.fixedPoints σ).ncard : ℂ) :=
    Matrix.trace_permutation σ
  have hτ_tr : Matrix.trace (τ.permMatrix ℂ) = ((Function.fixedPoints τ).ncard : ℂ) :=
    Matrix.trace_permutation τ
  have hncard_cast :
      ((Function.fixedPoints σ).ncard : ℂ) = ((Function.fixedPoints τ).ncard : ℂ) := by
    rw [← hσ_tr, ← hτ_tr]; exact htrace
  exact_mod_cast hncard_cast

/-- **Brauer's permutation lemma** (Isaacs, *Character Theory of Finite Groups*, Thm 6.32).

For a finite group `G`, the number of real irreducible complex characters equals the
number of self-inverse conjugacy classes:

`# { χ ∈ Irr G | χ̄ = χ } = # { C ∈ ConjClasses G | C⁻¹ = C }`.

The classical proof uses the invertibility of the character table (Schur orthogonality)
to relate the two compatible involutions `χ ↦ χ̄` on `Irr G` and `C ↦ C⁻¹` on
`ConjClasses G`.

The signature takes a `CharacterTableIndexing` package, the weighted row orthogonality
hypothesis (which yields character-table invertibility), the conjugation permutation `σ`
on `IrreducibleCharacter G`, the equivalence `σ χ = χ ↔ χ.IsReal`, and the compatibility
identity
`characterTableEntry (σ χ) C = characterTableEntry χ (inv C)`.  Bridging these
hypotheses to mathlib's representation theory (complex conjugation of unitary
representations, `χ ↦ χ̄`) is the remaining external gap.

The proof itself is the matrix-algebra core of Brauer's lemma: the trace of a permutation
matrix counts fixed points, and conjugate permutation matrices share traces. -/
theorem brauer_permutation_lemma {G : Type*} [Group G] [Finite G]
    (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (σ : Equiv.Perm (IrreducibleCharacter G))
    (h_real_irr : ∀ χ : IrreducibleCharacter G,
      σ χ = χ ↔ ClassFunction.IsReal (χ : ClassFunction G ℂ))
    (h_compat : ∀ (χ : IrreducibleCharacter G) (C : ConjClasses G),
      characterTableEntry (σ χ) C = characterTableEntry χ (ConjClasses.inv C)) :
    Nat.card (RealIrreducibleCharacter G) = Nat.card (ConjClasses.RealClass G) := by
  let := idx.irrFintype
  let := idx.classFintype
  let := Classical.decEq (IrreducibleCharacter G)
  let := Classical.decEq (ConjClasses G)
  let := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  -- Class-inversion permutation, pulled back to IrreducibleCharacter G via rowColumnEquiv.
  set τ : Equiv.Perm (IrreducibleCharacter G) := classInvPerm idx with hτ_def
  have hτ_symm : τ.symm = τ := classInvPerm_symm idx
  -- Matrix identity (entry form): A (σ χ) ψ = A χ (τ ψ).
  have hentry : ∀ (χ ψ : IrreducibleCharacter G),
      characterTableSquareMatrix idx (σ χ) ψ =
        characterTableSquareMatrix idx χ (τ ψ) := by
    intro χ ψ
    simp [characterTableSquareMatrix_apply, hτ_def, classInvPerm_apply, h_compat]
  -- Matrix product identity: σ.permMatrix * A = A * τ.permMatrix.
  have hmat : σ.permMatrix ℂ * characterTableSquareMatrix idx =
      characterTableSquareMatrix idx * τ.permMatrix ℂ := by
    ext χ ψ
    rw [show σ.permMatrix ℂ = σ.toPEquiv.toMatrix from rfl,
      show τ.permMatrix ℂ = τ.toPEquiv.toMatrix from rfl,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
      Matrix.submatrix_apply, Matrix.submatrix_apply, id, id, hτ_symm]
    exact hentry χ ψ
  -- Conjugate permutation matrices share their fixed-point count (matrix-algebra core).
  have hncard : (Function.fixedPoints σ).ncard = (Function.fixedPoints τ).ncard :=
    ncard_fixedPoints_eq_of_permMatrix_conj σ τ (characterTableSquareMatrix idx) hmat
  -- Translate to Nat.card.
  have hσ_nat : Nat.card (Function.fixedPoints σ) = Nat.card (RealIrreducibleCharacter G) := by
    rw [Nat.card_coe_set_eq]
    refine Eq.symm ?_
    apply Nat.card_congr
    exact (Equiv.subtypeEquivRight h_real_irr).symm
  have hτ_nat : Nat.card (Function.fixedPoints τ) = Nat.card (ConjClasses.RealClass G) := by
    rw [Nat.card_coe_set_eq]
    refine Eq.symm ?_
    apply Nat.card_congr
    -- realClassEquivFixedPointsClassInv idx : RealClass G ≃ {ψ // classInvPerm idx ψ = ψ}
    -- need: RealClass G ≃ Function.fixedPoints τ = {ψ // τ ψ = ψ}
    -- These are the same since τ = classInvPerm idx.
    exact (realClassEquivFixedPointsClassInv idx).trans
      (Equiv.subtypeEquivRight (fun ψ => Iff.rfl))
  calc Nat.card (RealIrreducibleCharacter G)
      = Nat.card (Function.fixedPoints σ) := hσ_nat.symm
    _ = (Function.fixedPoints σ).ncard := Nat.card_coe_set_eq _
    _ = (Function.fixedPoints τ).ncard := hncard
    _ = Nat.card (Function.fixedPoints τ) := (Nat.card_coe_set_eq _).symm
    _ = Nat.card (ConjClasses.RealClass G) := hτ_nat

/-- **Brauer's permutation lemma, general (arbitrary class permutation) form.**

For a finite group `G`, given a permutation `σ` of `Irr G` and a permutation `π` of
`ConjClasses G` compatible at the level of character-table entries
(`(σ χ)(C) = χ(π C)`), the number of `σ`-fixed irreducible characters equals the number of
`π`-fixed conjugacy classes:

`# { χ ∈ Irr G | σ χ = χ } = # { C ∈ ConjClasses G | π C = C }`.

This generalizes `brauer_permutation_lemma` (the `π = ConjClasses.inv` case) to an arbitrary
class permutation `π`, the form needed for an automorphism / conjugation action `θ ↦ θ^g`.

The matrix identity `σ.permMatrix * A = A * τ.permMatrix` permutes columns of `A` by `τ.symm`;
pulling `π` back as `τ = classPerm idx π.symm` makes `τ.symm = classPerm idx π` match the supplied
compatibility `(σ χ)(C) = χ(π C)`. -/
theorem brauer_permutation_lemma_general {G : Type*} [Group G] [Finite G]
    (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (σ : Equiv.Perm (IrreducibleCharacter G))
    (π : Equiv.Perm (ConjClasses G))
    (h_compat : ∀ (χ : IrreducibleCharacter G) (C : ConjClasses G),
      characterTableEntry (σ χ) C = characterTableEntry χ (π C)) :
    Nat.card (Function.fixedPoints σ) = Nat.card (Function.fixedPoints π) := by
  let := idx.irrFintype
  let := idx.classFintype
  let := Classical.decEq (IrreducibleCharacter G)
  let := Classical.decEq (ConjClasses G)
  let := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  set τ : Equiv.Perm (IrreducibleCharacter G) := (classPerm idx π).symm with hτ_def
  -- `τ.symm = classPerm idx π`, so the columns of `A * τ.permMatrix` match `h_compat`.
  have hτ_symm : τ.symm = classPerm idx π := by
    simp [hτ_def]
  have hentry : ∀ (χ ψ : IrreducibleCharacter G),
      characterTableSquareMatrix idx (σ χ) ψ =
        characterTableSquareMatrix idx χ ((classPerm idx π) ψ) := by
    intro χ ψ
    simp only [characterTableSquareMatrix_apply, rowColumnEquiv_classPerm]
    exact h_compat χ (idx.rowColumnEquiv ψ)
  have hmat : σ.permMatrix ℂ * characterTableSquareMatrix idx =
      characterTableSquareMatrix idx * τ.permMatrix ℂ := by
    ext χ ψ
    rw [show σ.permMatrix ℂ = σ.toPEquiv.toMatrix from rfl,
      show τ.permMatrix ℂ = τ.toPEquiv.toMatrix from rfl,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
      Matrix.submatrix_apply, Matrix.submatrix_apply, id, id, hτ_symm]
    exact hentry χ ψ
  have hncard : (Function.fixedPoints σ).ncard = (Function.fixedPoints τ).ncard :=
    ncard_fixedPoints_eq_of_permMatrix_conj σ τ (characterTableSquareMatrix idx) hmat
  have hτ_nat : Nat.card (Function.fixedPoints τ) = Nat.card (Function.fixedPoints π) := by
    subst τ
    apply Nat.card_congr
    exact (fixedPointsPermSymmEquiv (classPerm idx π)).trans (fixedPointsClassPermEquiv idx π)
  calc Nat.card (Function.fixedPoints σ)
      = (Function.fixedPoints σ).ncard := Nat.card_coe_set_eq _
    _ = (Function.fixedPoints τ).ncard := hncard
    _ = Nat.card (Function.fixedPoints τ) := (Nat.card_coe_set_eq _).symm
    _ = Nat.card (Function.fixedPoints π) := hτ_nat

/-- Conjugation form of Brauer's permutation lemma, unconditional (no character-table
hypotheses; the indexing and weighted row orthogonality are discharged internally for the
finite group `G`). -/
theorem brauer_permutation_lemma_general' {G : Type*} [Group G] [Finite G]
    (σ : Equiv.Perm (IrreducibleCharacter G)) (π : Equiv.Perm (ConjClasses G))
    (h_compat : ∀ (χ : IrreducibleCharacter G) (C : ConjClasses G),
      characterTableEntry (σ χ) C = characterTableEntry χ (π C)) :
    Nat.card (Function.fixedPoints σ) = Nat.card (Function.fixedPoints π) := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact brauer_permutation_lemma_general (instCharacterTableIndexingOfFinite (G := G))
    (CharacterTableWeightedRowOrthogonality.ofRowOrthogonality
      (instCharacterTableIndexingOfFinite (G := G)) (characterTableRowOrthogonality_holds (G := G)))
    σ π h_compat

end OddOrder.RepresentationTheory


