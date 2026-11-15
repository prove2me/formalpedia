-- Prove2me | Definitions.Def_RPLib_S4_PicDescentC1
-- name    : RPLib_S4_PicDescentC1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:16:26.061347+00:00
-- url     : https://prove2.me/theorems/fc5e6912-913a-4b72-b8a4-03e37511ccb7
-- title:
--   The rings of a constant field extension are tensor products
-- statement:
--   For a constant field extension $F'/L$ of a function field $F/\mathbb{F}_q$ (in coordinates), the rings of functions regular away from infinity and at infinity satisfy $$R_{fin}(F') \cong L \otimes_{\mathbb{F}_q} R_{fin}(F), \qquad R_\infty(F') \cong L \otimes_{\mathbb{F}_q} R_\infty(F),$$ by one generic statement for both rings. As a consequence the number of degree-one places of $F'$ equals $N_m(F)$, the number of places of $F \otimes \mathbb{F}_{q^m}$ of degree one, with $m = [L : \mathbb{F}_q]$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6

import Definitions.Def_RPLib_S4_PicDescentB4

/-!
# S4-PicDescent, part C1: the rings of a constant field extension are tensor products

For a constant field extension `F' / L` of `F / Fq` in the coordinates of `RR.IsConstExt`, the rings
of places are `Rfin L F' ≃ L ⊗[Fq] Rfin Fq F` and `Rinf L F' ≃ L ⊗[Fq] Rinf Fq F` (`tensorEquiv`, one
generic statement for both rings). Hence `B_1(F') = N_m(F)` with `m = [L : Fq]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial TensorProduct

namespace RamanujanPetersson.PicDescent

open Polynomial

section TensorIso

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']

variable (Fq L F F' A) in
/-- `l ⊗ a ↦ l a`, from `L ⊗[Fq] A` to `F'`. -/
noncomputable def tensorMap : L ⊗[Fq] A →ₐ[L] F' :=
  Algebra.TensorProduct.lift (Algebra.ofId L F')
    ((IsScalarTower.toAlgHom Fq F F').comp (IsScalarTower.toAlgHom Fq A F))
    (fun _ _ => Commute.all _ _)

theorem tensorMap_tmul (l : L) (a : A) :
    tensorMap Fq L F F' A (l ⊗ₜ a) = algebraMap A F a • algebraMap L F' l := by
  rw [tensorMap, Algebra.TensorProduct.lift_tmul, Algebra.smul_def, mul_comm]
  rfl

theorem exists_sum_tmul (c : Module.Basis ι Fq L) (t : L ⊗[Fq] A) :
    ∃ a : ι → A, t = ∑ j, c j ⊗ₜ a j := by
  obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_left c t
  exact ⟨b, Finsupp.sum_fintype _ _ (fun _ => TensorProduct.tmul_zero _ _)⟩

theorem tensorMap_sum (a : ι → A) :
    tensorMap Fq L F F' A (∑ j, c j ⊗ₜ a j) =
      ∑ j, algebraMap A F (a j) • algebraMap L F' (c j) := by
  rw [map_sum]
  simp only [tensorMap_tmul]

variable (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)

include hA hli in
theorem tensorMap_injective : Function.Injective (tensorMap Fq L F F' A) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨a, rfl⟩ := exists_sum_tmul c t
  rw [tensorMap_sum] at ht
  have h0 := Fintype.linearIndependent_iff.1 hli _ ht
  have : ∀ j, a j = 0 := fun j => hA (by rw [h0 j, map_zero])
  simp [this]

include hc in
theorem tensorMap_mem (t : L ⊗[Fq] A) :
    tensorMap Fq L F F' A t ∈ (IsScalarTower.toAlgHom L A' F').range := by
  obtain ⟨a, rfl⟩ := exists_sum_tmul c t
  rw [tensorMap_sum]
  obtain ⟨y, hy⟩ := (hc _).2 fun j => ⟨a j, rfl⟩
  exact ⟨y, hy⟩

include hsp hc in
theorem exists_tensorMap_eq (y : A') : ∃ t : L ⊗[Fq] A, tensorMap Fq L F F' A t = algebraMap A' F' y := by
  have hy : algebraMap A' F' y ∈ Submodule.span F (Set.range fun j => algebraMap L F' (c j)) :=
    hsp Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
  have hmem : ∀ j, f j ∈ (algebraMap A F).range := (hc f).1 (hf ▸ ⟨y, rfl⟩)
  choose a ha using hmem
  exact ⟨∑ j, c j ⊗ₜ a j, by rw [tensorMap_sum, ← hf]; simp only [ha]⟩

/-- The tensor map as an algebra map into `A'`. -/
noncomputable def tensorToA' : L ⊗[Fq] A →ₐ[L] A' :=
  (AlgEquiv.ofInjective (IsScalarTower.toAlgHom L A' F') hA').symm.toAlgHom.comp
    ((tensorMap Fq L F F' A).codRestrict _ (tensorMap_mem hc))

theorem algebraMap_tensorToA' (t : L ⊗[Fq] A) :
    algebraMap A' F' (tensorToA' hA' hc t) = tensorMap Fq L F F' A t := by
  have h1 := AlgEquiv.ofInjective_apply (IsScalarTower.toAlgHom L A' F') hA' (tensorToA' hA' hc t)
  have h2 : (AlgEquiv.ofInjective (IsScalarTower.toAlgHom L A' F') hA') (tensorToA' hA' hc t) =
      ⟨tensorMap Fq L F F' A t, tensorMap_mem hc t⟩ :=
    AlgEquiv.apply_symm_apply _ _
  rw [h2] at h1
  exact h1.symm

/-- **`L ⊗[Fq] A ≃ A'`** for a constant field extension in coordinates. -/
noncomputable def tensorEquiv : L ⊗[Fq] A ≃ₐ[L] A' :=
  AlgEquiv.ofBijective (tensorToA' hA' hc)
    ⟨fun s t h => tensorMap_injective hA hli (by
        rw [← algebraMap_tensorToA' hA' hc, ← algebraMap_tensorToA' hA' hc, h]),
      fun y => by
        obtain ⟨t, ht⟩ := exists_tensorMap_eq hsp hc y
        exact ⟨t, hA' (by rw [algebraMap_tensorToA', ht])⟩⟩

end TensorIso

section Instances

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (L : Type*) [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

variable {Fq F L F'}

/-- `L ⊗[Fq] Rfin(F) ≃ Rfin(F')` for a constant field extension. -/
noncomputable def e1 (h : RR.IsConstExt Fq F L F' c) :
    L ⊗[Fq] Places.Rfin Fq F ≃ₐ[L] Places.Rfin L F' :=
  tensorEquiv (F := F) (F' := F') (c := c) Subtype.val_injective Subtype.val_injective
    h.linearIndependent h.span h.fin

/-- `L ⊗[Fq] Rinf(F) ≃ Rinf(F')` for a constant field extension. -/
noncomputable def e2 (h : RR.IsConstExt Fq F L F' c) :
    L ⊗[Fq] Places.Rinf Fq F ≃ₐ[L] Places.Rinf L F' :=
  tensorEquiv (F := F) (F' := F') (c := c) Subtype.val_injective Subtype.val_injective
    h.linearIndependent h.span h.inf

/-- `B_1(F') = N_m(F)`, `m = [L : Fq]`. -/
theorem numPlaces_one_constExt (h : RR.IsConstExt Fq F L F' c) :
    Places.numPlaces L F' 1 = Places.numPoints Fq F (Module.finrank Fq L) :=
  Places.numPlaces_one_eq_numPoints Fq F L F' (e1 h) (e2 h)

variable (L' : Type*) [Field L'] [Algebra L L'] [Algebra Fq L'] [IsScalarTower Fq L L']

theorem card_algHom_Rfin_constExt (h : RR.IsConstExt Fq F L F' c) :
    Nat.card (Places.Rfin L F' →ₐ[L] L') = Nat.card (Places.Rfin Fq F →ₐ[Fq] L') :=
  Nat.card_congr ((AlgEquiv.arrowCongr (e1 h) AlgEquiv.refl).symm.trans
    (AlgHom.liftEquiv Fq L (Places.Rfin Fq F) L').symm)

theorem card_algHom_Rinf_constExt (h : RR.IsConstExt Fq F L F' c) :
    Nat.card (Places.Rinf L F' →ₐ[L] L') = Nat.card (Places.Rinf Fq F →ₐ[Fq] L') :=
  Nat.card_congr ((AlgEquiv.arrowCongr (e2 h) AlgEquiv.refl).symm.trans
    (AlgHom.liftEquiv Fq L (Places.Rinf Fq F) L').symm)

theorem numPoints_constExt_of [Finite L'] (h : RR.IsConstExt Fq F L F' c) :
    Places.numPoints L F' (Module.finrank L L') = Places.numPoints Fq F (Module.finrank Fq L') := by
  rw [Places.numPoints_eq_card_algHom L F' L', Places.numPoints_eq_card_algHom Fq F L',
    card_algHom_Rfin_constExt L' h, card_algHom_Rinf_constExt L' h]

/-- **`N_k(F') = N_{mk}(F)`** for a constant field extension `F' / L` of degree `m = [L : Fq]`. -/
theorem numPoints_constExt (h : RR.IsConstExt Fq F L F' c) {k : ℕ} (hk : k ≠ 0) :
    Places.numPoints L F' k = Places.numPoints Fq F (Module.finrank Fq L * k) := by
  have : Fact (ringChar L).Prime := ⟨CharP.char_is_prime L _⟩
  have : NeZero k := ⟨hk⟩
  let : Algebra Fq (FiniteField.Extension L (ringChar L) k) :=
    ((algebraMap L (FiniteField.Extension L (ringChar L) k)).comp (algebraMap Fq L)).toAlgebra
  have : IsScalarTower Fq L (FiniteField.Extension L (ringChar L) k) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 := numPoints_constExt_of (FiniteField.Extension L (ringChar L) k) h
  rwa [FiniteField.finrank_extension, ← Module.finrank_mul_finrank Fq L,
    FiniteField.finrank_extension] at h1

end Instances

end RamanujanPetersson.PicDescent


