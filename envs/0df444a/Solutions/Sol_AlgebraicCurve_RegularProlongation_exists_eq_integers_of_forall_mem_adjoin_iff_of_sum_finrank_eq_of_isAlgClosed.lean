-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b7d6e337-8ce8-5d46-89ee-a2dd4884f2ab

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed

set_option autoImplicit false

open IsLocalRing

namespace GST
namespace Rebase

section Transport

variable {k : Type*} [Field k] {B₁ : Type*} {B₂ : Type*} [Field B₁] [Field B₂]
  [Algebra k B₁] [Algebra k B₂]

theorem mem_adjoin_simple_of_algEquiv (e : B₁ ≃ₐ[k] B₂) (x : B₁) {y : B₁}
    (hy : y ∈ IntermediateField.adjoin k ({x} : Set B₁)) :
    e y ∈ IntermediateField.adjoin k ({e x} : Set B₂) := by
  have h : (IntermediateField.adjoin k ({x} : Set B₁)).map (e : B₁ →ₐ[k] B₂) =
      IntermediateField.adjoin k ({e x} : Set B₂) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, AlgEquiv.coe_algHom]
  rw [← h, IntermediateField.mem_map]
  exact ⟨y, hy, rfl⟩

theorem finrank_adjoin_simple_eq_of_algEquiv (e : B₁ ≃ₐ[k] B₂) (x : B₁) :
    Module.finrank (IntermediateField.adjoin k ({x} : Set B₁)) B₁ =
      Module.finrank (IntermediateField.adjoin k ({e x} : Set B₂)) B₂ := by
  have hfwd : ∀ y ∈ IntermediateField.adjoin k ({x} : Set B₁),
      e y ∈ IntermediateField.adjoin k ({e x} : Set B₂) :=
    fun y hy => mem_adjoin_simple_of_algEquiv e x hy
  have hbwd : ∀ z ∈ IntermediateField.adjoin k ({e x} : Set B₂),
      e.symm z ∈ IntermediateField.adjoin k ({x} : Set B₁) := by
    intro z hz
    have h := mem_adjoin_simple_of_algEquiv e.symm (e x) hz
    rwa [e.symm_apply_apply] at h
  let i : IntermediateField.adjoin k ({x} : Set B₁) ≃+* IntermediateField.adjoin k ({e x} : Set B₂) :=
    { toFun := fun y => ⟨e y, hfwd y.1 y.2⟩
      invFun := fun z => ⟨e.symm z, hbwd z.1 z.2⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply (y : B₁))
      right_inv := fun z => Subtype.ext (e.apply_symm_apply (z : B₂))
      map_mul' := fun a b => Subtype.ext (map_mul e (a : B₁) (b : B₁))
      map_add' := fun a b => Subtype.ext (map_add e (a : B₁) (b : B₁)) }
  exact Algebra.finrank_eq_of_equiv_equiv i e.toRingEquiv (RingHom.ext fun y => rfl)

end Transport

section Iso

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  {Fb₁ : Type*} {Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (ResidueField A) Fb₁] [Algebra (ResidueField A) Fb₂]

theorem exists_algEquiv_forall_apply_eq (O₁ O₂ : ValuationSubring F) (h : O₁ = O₂)
    (hO₁ : ∀ x : L, algebraMap L F x ∈ O₁ ↔ x ∈ A)
    (hO₂ : ∀ x : L, algebraMap L F x ∈ O₂ ↔ x ∈ A)
    (ρ₁ : O₁ →+* Fb₁) (ρ₂ : O₂ →+* Fb₂)
    (hs₁ : Function.Surjective ρ₁) (hs₂ : Function.Surjective ρ₂)
    (hk₁ : RingHom.ker ρ₁ = maximalIdeal O₁) (hk₂ : RingHom.ker ρ₂ = maximalIdeal O₂)
    (hc₁ : ∀ a : A, ρ₁ ⟨algebraMap L F a, (hO₁ a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fb₁ (residue A a))
    (hc₂ : ∀ a : A, ρ₂ ⟨algebraMap L F a, (hO₂ a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fb₂ (residue A a)) :
    ∃ e : Fb₁ ≃ₐ[ResidueField A] Fb₂,
      ∀ (x : F) (h₁ : x ∈ O₁) (h₂ : x ∈ O₂), e (ρ₁ ⟨x, h₁⟩) = ρ₂ ⟨x, h₂⟩ := by
  subst h
  have hker : RingHom.ker ρ₁ = RingHom.ker ρ₂ := hk₁.trans hk₂.symm
  let e₀ : Fb₁ ≃+* Fb₂ :=
    (RingHom.quotientKerEquivOfSurjective hs₁).symm.trans
      ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hs₂))
  have he₀ : ∀ x : O₁, e₀ (ρ₁ x) = ρ₂ x := by
    intro x
    have h1 : RingHom.quotientKerEquivOfSurjective hs₁ (Ideal.Quotient.mk _ x) = ρ₁ x := rfl
    have h2 : RingHom.quotientKerEquivOfSurjective hs₂ (Ideal.Quotient.mk _ x) = ρ₂ x := rfl
    simp only [e₀, RingEquiv.trans_apply]
    rw [← h1, RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk, h2]
  have hke : ∀ c : ResidueField A, e₀ (algebraMap (ResidueField A) Fb₁ c) =
      algebraMap (ResidueField A) Fb₂ c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← hc₁, he₀, hc₂]
  exact ⟨AlgEquiv.ofRingEquiv (f := e₀) hke, fun x h₁ _ => he₀ ⟨x, h₁⟩⟩

end Iso

end GST.Rebase

open AlgebraicCurve IsLocalRing

namespace GST
namespace Rebase

theorem exists_algEquiv_forall_residue_eq
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fb₁ : Type*} {Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (ResidueField A) Fb₁] [Algebra (ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (h : R₁.integers = R₂.integers) :
    ∃ e : Fb₁ ≃ₐ[ResidueField A] Fb₂,
      ∀ (x : F) (h₁ : x ∈ R₁.integers) (h₂ : x ∈ R₂.integers),
        e (R₁.residue ⟨x, h₁⟩) = R₂.residue ⟨x, h₂⟩ :=
  exists_algEquiv_forall_apply_eq A R₁.integers R₂.integers h R₁.algebraMap_mem_iff
    R₂.algebraMap_mem_iff R₁.residue R₂.residue R₁.residue_surjective R₂.residue_surjective
    R₁.ker_residue R₂.ker_residue R₁.residue_algebraMap R₂.residue_algebraMap

end GST.Rebase

open GST.Rebase in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i₀ : ι) (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ (R i₀).integers)) :
    ∃ j, V = (R j).integers := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _

  have hreb : ∀ i, ∃ (_ : Algebra (ResidueField A) (ResidueField (R i).integers))
      (R' : RegularProlongation A F (ResidueField (R i).integers)),
      R'.integers = (R i).integers ∧ ∃ hf' : f ∈ R'.integers,
        Transcendental (ResidueField A) (R'.residue ⟨f, hf'⟩) := fun i =>
    RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic A (R i) f (hf i) (htr i)
      (R i).integers (fun _ _ => Iff.rfl)
  choose inst R' hR'int hf' htr' using hreb

  obtain ⟨instV, RV, hRVint, hfV, htrV⟩ :=
    RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic A (R i₀) f (hf i₀) (htr i₀)
      V hV

  let Fb'' : Option ι → Type _ :=
    fun | none => ResidueField V | some i => ResidueField (R i).integers
  letI hFld'' : ∀ o, Field (Fb'' o) :=
    fun | none => (inferInstance : Field (ResidueField V))
        | some i => (inferInstance : Field (ResidueField (R i).integers))
  letI hAlg'' : ∀ o, Algebra (ResidueField A) (Fb'' o) :=
    fun | none => instV | some i => inst i
  let R'' : ∀ o, RegularProlongation A F (Fb'' o) := fun | none => RV | some i => R' i
  have hR'' : Function.Injective fun o => (R'' o).integers := by
    intro o₁ o₂ h
    match o₁, o₂, h with
    | none, none, _ => rfl
    | none, some i, h => exact absurd (hRVint.symm.trans (h.trans (hR'int i))) (hne i)
    | some i, none, h => exact absurd (hRVint.symm.trans (h.symm.trans (hR'int i))) (hne i)
    | some i, some i', h =>
        exact congrArg some (hR ((hR'int i).symm.trans (h.trans (hR'int i'))))
  have hf'' : ∀ o, f ∈ (R'' o).integers := fun | none => hfV | some i => hf' i
  have htr'' : ∀ o, Transcendental (ResidueField A) ((R'' o).residue ⟨f, hf'' o⟩) :=
    fun | none => htrV | some i => htr' i

  obtain ⟨hFD, hle⟩ :=
    RegularProlongation.sum_finrank_adjoin_residue_le A Fb'' R'' hR'' f hf'' htr''
  rw [Fintype.sum_option] at hle

  have hterm : ∀ i, Module.finrank
        (IntermediateField.adjoin (ResidueField A)
          ({(R'' (some i)).residue ⟨f, hf'' (some i)⟩} : Set (Fb'' (some i)))) (Fb'' (some i))
      = Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
        (Fb i) := by
    intro i
    obtain ⟨e, he⟩ := exists_algEquiv_forall_residue_eq A (R i) (R' i) (hR'int i).symm
    have h := finrank_adjoin_simple_eq_of_algEquiv e ((R i).residue ⟨f, hf i⟩)
    rw [he f (hf i) (hf' i)] at h
    exact h.symm
  rw [show (∑ i, Module.finrank
        (IntermediateField.adjoin (ResidueField A)
          ({(R'' (some i)).residue ⟨f, hf'' (some i)⟩} : Set (Fb'' (some i)))) (Fb'' (some i)))
      = ∑ i, Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
        (Fb i) from Finset.sum_congr rfl fun i _ => hterm i, heq] at hle

  have hFDV : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A)
        ({(R'' none).residue ⟨f, hf'' none⟩} : Set (Fb'' none))) (Fb'' none) := hFD none
  have hpos : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A)
        ({(R'' none).residue ⟨f, hf'' none⟩} : Set (Fb'' none))) (Fb'' none) :=
    Module.finrank_pos
  omega

end S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed (solution)
