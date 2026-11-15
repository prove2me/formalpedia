-- Prove2me | Definitions.Def_RPLib_S4_PicDescentD1
-- name    : RPLib_S4_PicDescentD1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:19:06.672261+00:00
-- url     : https://prove2.me/theorems/9f6193f6-a182-4a3d-8095-4e04c63cf75b
-- title:
--   The Galois action of $\operatorname{Gal}(L/\mathbb{F}_q)$ on a constant field extension
-- statement:
--   For a constant field extension $F'$ of $F$ with $F$-basis the images of an $\mathbb{F}_q$-basis of $L$, the file constructs $L \otimes_{\mathbb{F}_q} F \cong F'$ and the action of $\tau \in \operatorname{Gal}(L/\mathbb{F}_q)$ on $F'$ by $\tau \otimes \mathrm{id}$, an injective group homomorphism into $\operatorname{Aut}_F(F')$, proves that the common fixed field is $F$ (Artin), and transports the action to rings $A' \cong L \otimes A$, where the fixed elements of $A'$ come from $A$: $$(A')^{\operatorname{Gal}(L/\mathbb{F}_q)} = A.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6

import Definitions.Def_RPLib_S4_PicDescentC1

/-!
# S4-PicDescent, part D1: the Galois action of `Gal(L/Fq)` on a constant field extension

Generic setting of C1 (`F'` with an `F`-basis `c'_j = algebraMap L F' (c j)`, `c` an `Fq`-basis of `L`).
* `fieldEquiv : L ⊗[Fq] F ≃ₐ[L] F'`; `gal τ : F' ≃ₐ[F] F'` acts by `τ ⊗ id`; `galHom` is an injective group hom;
  `gal_algebraMap_L : gal τ l' = (τ l)'`.
* `mem_range_of_forall_gal`: the fixed field of all `gal τ` is `F` (Artin, `[F' : F] = [L : Fq] = #Gal(L/Fq)`).
* On a ring `A' ≃ L ⊗ A` (C1 `tensorEquiv`): `galA' τ` with `algebraMap_galA'`, `galA'Hom`, `toA' : A → A'`,
  `exists_toA'_eq` (fixed elements of `A'` come from `A`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace RamanujanPetersson.PicDescent

section Galois

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))

theorem hcF (f : ι → F) : (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap F' F').range ↔
    ∀ j, f j ∈ (algebraMap F F).range :=
  ⟨fun _ j => ⟨f j, rfl⟩, fun _ => ⟨_, rfl⟩⟩

/-- `L ⊗[Fq] F ≃ F'`. -/
noncomputable def fieldEquiv : L ⊗[Fq] F ≃ₐ[L] F' :=
  tensorEquiv (A := F) (A' := F') (F := F) (F' := F') (algebraMap F F).injective
    (algebraMap F' F').injective hli hsp hcF

theorem fieldEquiv_apply (t : L ⊗[Fq] F) : fieldEquiv hli hsp t = tensorMap Fq L F F' F t :=
  algebraMap_tensorToA' (A := F) (F := F) (c := c) (algebraMap F' F').injective hcF t

theorem tensorMap_one_tmul (f : F) : tensorMap Fq L F F' F (1 ⊗ₜ f) = algebraMap F F' f := by
  rw [tensorMap_tmul, map_one, Algebra.smul_def, mul_one]
  rfl

theorem tensorMap_tmul_one {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
    (l : L) : tensorMap Fq L F F' A (l ⊗ₜ[Fq] (1 : A)) = algebraMap L F' l := by
  rw [tensorMap_tmul, map_one, one_smul]

/-- `τ ⊗ id` on `F'`, as a ring automorphism. -/
noncomputable def galRing (τ : L ≃ₐ[Fq] L) : F' ≃+* F' :=
  ((fieldEquiv hli hsp).toRingEquiv.symm.trans
    (Algebra.TensorProduct.congr τ (AlgEquiv.refl : F ≃ₐ[Fq] F)).toRingEquiv).trans
    (fieldEquiv hli hsp).toRingEquiv

theorem galRing_fieldEquiv (τ : L ≃ₐ[Fq] L) (t : L ⊗[Fq] F) :
    galRing hli hsp τ (fieldEquiv hli hsp t) =
      fieldEquiv hli hsp (Algebra.TensorProduct.congr τ (AlgEquiv.refl : F ≃ₐ[Fq] F) t) := by
  show fieldEquiv hli hsp (Algebra.TensorProduct.congr τ AlgEquiv.refl
    ((fieldEquiv hli hsp).symm (fieldEquiv hli hsp t))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem galRing_algebraMap_F (τ : L ≃ₐ[Fq] L) (f : F) :
    galRing hli hsp τ (algebraMap F F' f) = algebraMap F F' f := by
  rw [← tensorMap_one_tmul (Fq := Fq) (L := L), ← fieldEquiv_apply hli hsp, galRing_fieldEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  simp

/-- **The Galois action**: `gal τ = τ ⊗ id` on `F' = L ⊗ F`. -/
noncomputable def gal (τ : L ≃ₐ[Fq] L) : F' ≃ₐ[F] F' :=
  AlgEquiv.ofRingEquiv (f := galRing hli hsp τ) (galRing_algebraMap_F hli hsp τ)

theorem gal_fieldEquiv (τ : L ≃ₐ[Fq] L) (t : L ⊗[Fq] F) :
    gal hli hsp τ (fieldEquiv hli hsp t) =
      fieldEquiv hli hsp (Algebra.TensorProduct.congr τ (AlgEquiv.refl : F ≃ₐ[Fq] F) t) :=
  galRing_fieldEquiv hli hsp τ t

theorem gal_algebraMap_L (τ : L ≃ₐ[Fq] L) (l : L) :
    gal hli hsp τ (algebraMap L F' l) = algebraMap L F' (τ l) := by
  rw [← tensorMap_tmul_one (Fq := Fq) (F := F) (A := F) l,
    ← tensorMap_tmul_one (Fq := Fq) (F := F) (A := F) (τ l), ← fieldEquiv_apply hli hsp,
    ← fieldEquiv_apply hli hsp, gal_fieldEquiv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

/-- `τ ↦ gal τ` as a group hom. -/
noncomputable def galHom : (L ≃ₐ[Fq] L) →* (F' ≃ₐ[F] F') where
  toFun := gal hli hsp
  map_one' := AlgEquiv.ext fun x => by
    obtain ⟨t, rfl⟩ := (fieldEquiv hli hsp).surjective x
    rw [gal_fieldEquiv, AlgEquiv.one_apply]
    congr 1
    exact DFunLike.congr_fun (Algebra.TensorProduct.congr_refl (S := Fq) (R := Fq) (A := L) (B := F)) t
  map_mul' τ1 τ2 := AlgEquiv.ext fun x => by
    obtain ⟨t, rfl⟩ := (fieldEquiv hli hsp).surjective x
    rw [AlgEquiv.mul_apply, gal_fieldEquiv, gal_fieldEquiv, gal_fieldEquiv]
    congr 1
    exact DFunLike.congr_fun
      (Algebra.TensorProduct.congr_trans τ2 τ1 (AlgEquiv.refl : F ≃ₐ[Fq] F) AlgEquiv.refl) t

theorem galHom_apply (τ : L ≃ₐ[Fq] L) : galHom hli hsp τ = gal hli hsp τ := rfl

theorem galHom_injective : Function.Injective (galHom hli hsp) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  ext l
  have h := congrArg (fun g : F' ≃ₐ[F] F' => g (algebraMap L F' l)) hτ
  simp only [galHom_apply, gal_algebraMap_L, AlgEquiv.one_apply] at h
  exact (algebraMap L F').injective h

include hli hsp in
theorem finrank_F' : Module.finrank F F' = Module.finrank Fq L := by
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_basis c]

/-- **The fixed field of `Gal(L/Fq)` acting on `F'` is `F`.** -/
theorem mem_range_of_forall_gal [Finite L] (x : F') (hx : ∀ τ : L ≃ₐ[Fq] L, gal hli hsp τ x = x) :
    x ∈ (algebraMap F F').range := by
  have : FiniteDimensional F F' := Module.Finite.of_basis (Module.Basis.mk hli hsp)
  have hcard : Nat.card (galHom hli hsp).range = Module.finrank F F' := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (galHom_injective hli hsp)).toEquiv,
      IsGalois.card_aut_eq_finrank, finrank_F' hli hsp]
  have h1 : Module.finrank (IntermediateField.fixedField (galHom hli hsp).range) F' =
      Module.finrank F F' := by
    rw [IntermediateField.finrank_fixedField_eq_card, hcard]
  have h2 := Module.finrank_mul_finrank F (IntermediateField.fixedField (galHom hli hsp).range) F'
  rw [h1] at h2
  have hpos : 0 < Module.finrank F F' := Module.finrank_pos
  have h3 : Module.finrank F (IntermediateField.fixedField (galHom hli hsp).range) = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans (one_mul _).symm)
  rw [IntermediateField.finrank_eq_one_iff] at h3
  have hmem : x ∈ IntermediateField.fixedField (galHom hli hsp).range := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro g ⟨τ, rfl⟩
    exact hx τ
  rw [h3, IntermediateField.mem_bot] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

/-- `f' = Σ_j (d_j f) • c'_j` where `1 = Σ d_j c_j`. -/
theorem algebraMap_F_eq_sum (f : F) :
    algebraMap F F' f = ∑ j, (algebraMap Fq F (c.repr 1 j) * f) • algebraMap L F' (c j) := by
  conv_lhs => rw [← mul_one (algebraMap F F' f), ← map_one (algebraMap L F'), ← c.sum_repr 1]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def (c.repr 1 j) (c j), Algebra.smul_def (algebraMap Fq F (c.repr 1 j) * f)]
  simp only [map_mul, ← IsScalarTower.algebraMap_apply]
  ring

section Rings

variable {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']
  (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)

theorem algebraMap_tensorEquiv (t : L ⊗[Fq] A) :
    algebraMap A' F' (tensorEquiv hA hA' hli hsp hc t) = tensorMap Fq L F F' A t :=
  algebraMap_tensorToA' hA' hc t

theorem gal_tensorMap (τ : L ≃ₐ[Fq] L) (t : L ⊗[Fq] A) :
    gal hli hsp τ (tensorMap Fq L F F' A t) =
      tensorMap Fq L F F' A (Algebra.TensorProduct.congr τ (AlgEquiv.refl : A ≃ₐ[Fq] A) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, tensorMap_tmul, tensorMap_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes, gal_algebraMap_L]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

/-- `τ ⊗ id` on `A' ≃ L ⊗ A`. -/
noncomputable def galA' (τ : L ≃ₐ[Fq] L) : A' ≃+* A' :=
  ((tensorEquiv hA hA' hli hsp hc).toRingEquiv.symm.trans
    (Algebra.TensorProduct.congr τ (AlgEquiv.refl : A ≃ₐ[Fq] A)).toRingEquiv).trans
    (tensorEquiv hA hA' hli hsp hc).toRingEquiv

theorem algebraMap_galA' (τ : L ≃ₐ[Fq] L) (y : A') :
    algebraMap A' F' (galA' hli hsp hA hA' hc τ y) = gal hli hsp τ (algebraMap A' F' y) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv hA hA' hli hsp hc).surjective y
  have e1 : galA' hli hsp hA hA' hc τ (tensorEquiv hA hA' hli hsp hc t) =
      tensorEquiv hA hA' hli hsp hc (Algebra.TensorProduct.congr τ AlgEquiv.refl t) := by
    show tensorEquiv hA hA' hli hsp hc (Algebra.TensorProduct.congr τ AlgEquiv.refl
      ((tensorEquiv hA hA' hli hsp hc).symm (tensorEquiv hA hA' hli hsp hc t))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e1, algebraMap_tensorEquiv, algebraMap_tensorEquiv]
  exact (gal_tensorMap hli hsp τ t).symm

/-- `τ ↦ galA' τ` as a group hom into `RingAut A'`. -/
noncomputable def galA'Hom : (L ≃ₐ[Fq] L) →* RingAut A' where
  toFun := galA' hli hsp hA hA' hc
  map_one' := RingEquiv.ext fun y => hA' (by
    rw [algebraMap_galA', show gal hli hsp 1 = 1 from (galHom hli hsp).map_one]
    rfl)
  map_mul' τ1 τ2 := RingEquiv.ext fun y => hA' (by
    rw [algebraMap_galA', show gal hli hsp (τ1 * τ2) = gal hli hsp τ1 * gal hli hsp τ2 from
      (galHom hli hsp).map_mul τ1 τ2]
    show _ = algebraMap A' F' (galA' hli hsp hA hA' hc τ1 (galA' hli hsp hA hA' hc τ2 y))
    rw [algebraMap_galA', algebraMap_galA']
    rfl)

/-- `A → A'`, `a ↦ 1 ⊗ a`. -/
noncomputable def toA' : A →+* A' :=
  (tensorEquiv hA hA' hli hsp hc).toRingHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[Fq] L ⊗[Fq] A).toRingHom

theorem algebraMap_toA' (a : A) :
    algebraMap A' F' (toA' hli hsp hA hA' hc a) = algebraMap F F' (algebraMap A F a) := by
  show algebraMap A' F' (tensorEquiv hA hA' hli hsp hc (1 ⊗ₜ a)) = _
  rw [algebraMap_tensorEquiv, tensorMap_tmul, map_one, Algebra.smul_def, mul_one]

/-- **Fixed elements of `A'` come from `A`.** -/
theorem exists_toA'_eq [Finite L] (y : A') (hy : ∀ τ, galA' hli hsp hA hA' hc τ y = y) :
    ∃ a : A, toA' hli hsp hA hA' hc a = y := by
  have hx : ∀ τ, gal hli hsp τ (algebraMap A' F' y) = algebraMap A' F' y := fun τ => by
    rw [← algebraMap_galA' hli hsp hA hA' hc, hy]
  obtain ⟨f, hf⟩ := mem_range_of_forall_gal hli hsp _ hx
  obtain ⟨t, rfl⟩ := (tensorEquiv hA hA' hli hsp hc).surjective y
  obtain ⟨a, rfl⟩ := exists_sum_tmul c t
  rw [algebraMap_tensorEquiv, tensorMap_sum, algebraMap_F_eq_sum (c := c)] at hf
  have hzero : ∑ j, (algebraMap Fq F (c.repr 1 j) * f - algebraMap A F (a j)) •
      algebraMap L F' (c j) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hf, sub_self]
  have hcoef := Fintype.linearIndependent_iff.1 hli _ hzero
  obtain ⟨j0, hj0⟩ : ∃ j, c.repr 1 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : L) = 0 := by rw [← c.sum_repr 1]; simp [hcon]
    exact one_ne_zero h1
  have hd : algebraMap Fq F (c.repr 1 j0) ≠ 0 := (map_ne_zero _).2 hj0
  have ha : algebraMap A F (a j0) = algebraMap Fq F (c.repr 1 j0) * f := (sub_eq_zero.1 (hcoef j0)).symm
  refine ⟨(c.repr 1 j0)⁻¹ • a j0, hA' ?_⟩
  rw [algebraMap_toA', algebraMap_tensorEquiv, tensorMap_sum, ← hf, ← algebraMap_F_eq_sum]
  congr 1
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply Fq A F, ha, map_inv₀,
    inv_mul_cancel_left₀ hd]

end Rings

end Galois

end RamanujanPetersson.PicDescent


