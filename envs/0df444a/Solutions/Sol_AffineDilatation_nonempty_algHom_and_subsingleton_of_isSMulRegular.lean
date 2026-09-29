-- Prove2me | solution 1 for AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c46dea40-ceb1-5789-b431-149c2f01840d

import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular

set_option autoImplicit false

universe u v

namespace AffineDilatation
p2m_export "AffineDilatation" "subalgebra Ring divElem algebraMap_mul_divElem"
namespace UniversalProperty
p2m_open "AffineDilatation"

open scoped nonZeroDivisors

variable {A : Type u} [CommRing A]
variable {C : Type v} [CommRing C] [Algebra A C]

theorem algHom_ext (I : Ideal A) (a : A) (hreg : IsSMulRegular C a)
    (φ ψ : Ring I a →ₐ[A] C) : φ = ψ := by
  apply AlgHom.ext
  rintro ⟨x, hx⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      change φ (divElem I a g hg) = ψ (divElem I a g hg)
      have h := congrArg φ (algebraMap_mul_divElem I a g hg)
      have h' := congrArg ψ (algebraMap_mul_divElem I a g hg)
      rw [map_mul, φ.commutes, φ.commutes] at h
      rw [map_mul, ψ.commutes, ψ.commutes] at h'
      refine hreg (?_ : a • φ (divElem I a g hg) = a • ψ (divElem I a g hg))
      rw [Algebra.smul_def, Algebra.smul_def, h, h']
  | algebraMap r =>
      exact (φ.commutes r).trans (ψ.commutes r).symm
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

theorem subsingleton_algHom (I : Ideal A) (a : A) (hreg : IsSMulRegular C a) :
    Subsingleton (Ring I a →ₐ[A] C) :=
  ⟨algHom_ext I a hreg⟩

theorem nonempty_algHom (I : Ideal A) (a : A) (hreg : IsSMulRegular C a)
    (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
    Nonempty (Ring I a →ₐ[A] C) := by
  classical
  set b : C := algebraMap A C a with hb
  let Ca := Localization.Away b
  let j : C →+* Ca := algebraMap C Ca
  have hj : Function.Injective j := by
    refine IsLocalization.injective Ca (M := Submonoid.powers b) ?_
    rw [Submonoid.powers_le]
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    refine hreg (?_ : a • c = a • (0 : C))
    rw [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm]
    exact hc

  have hunit : IsUnit ((j.comp (algebraMap A C)) a) := by
    change IsUnit (j b)
    exact IsLocalization.Away.algebraMap_isUnit b
  let Φ : Localization.Away a →+* Ca := IsLocalization.Away.lift a hunit
  have hΦalg : ∀ g : A, Φ (algebraMap A (Localization.Away a) g) = j (algebraMap A C g) := by
    intro g
    exact IsLocalization.Away.lift_eq a hunit g
  have hΦmk : ∀ g : A, Φ (IsLocalization.mk' (Localization.Away a) g
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) * j b = j (algebraMap A C g) := by
    intro g
    have h := IsLocalization.mk'_spec (Localization.Away a) g
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
    have h' := congrArg Φ h
    rw [map_mul, hΦalg, hΦalg] at h'
    exact h'

  have hrange : ∀ x ∈ subalgebra I a, Φ x ∈ j.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hgC : algebraMap A C g ∈ Ideal.span {b} := hI (Ideal.mem_map_of_mem _ hg)
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hgC
        refine ⟨c, ?_⟩
        have h1 := hΦmk g
        rw [← hc, map_mul] at h1
        exact ((IsLocalization.Away.algebraMap_isUnit b).mul_left_injective h1).symm
    | algebraMap r => exact ⟨algebraMap A C r, (hΦalg r).symm⟩
    | add x y _ _ ihx ihy => rw [map_add]; exact Subring.add_mem _ ihx ihy
    | mul x y _ _ ihx ihy => rw [map_mul]; exact Subring.mul_mem _ ihx ihy

  let e : C ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective j⟩
  let ΦD : Ring I a →+* j.range :=
    (Φ.comp (subalgebra I a).val.toRingHom).codRestrict j.range (fun x => hrange x.1 x.2)
  let φ : Ring I a →+* C := e.symm.toRingHom.comp ΦD
  have hφ : ∀ x : Ring I a, j (φ x) = Φ x := by
    intro x
    have h1 : (e (φ x) : Ca) = (ΦD x : Ca) := by
      change (e (e.symm (ΦD x)) : Ca) = _
      rw [RingEquiv.apply_symm_apply]
    exact h1
  refine ⟨{ φ with commutes' := ?_ }⟩
  intro g
  apply hj
  change j (φ (algebraMap A (Ring I a) g)) = j (algebraMap A C g)
  rw [hφ]
  exact hΦalg g

end AffineDilatation.UniversalProperty

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    {C : Type v} [CommRing C] [Algebra A C] (hreg : IsSMulRegular C a)
    (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
    Nonempty (AffineDilatation.Ring I a →ₐ[A] C) ∧
      Subsingleton (AffineDilatation.Ring I a →ₐ[A] C) :=
  ⟨AffineDilatation.UniversalProperty.nonempty_algHom I a hreg hI,
    AffineDilatation.UniversalProperty.subsingleton_algHom I a hreg⟩

end S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular
end P2MW
export P2MW.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular (solution)
