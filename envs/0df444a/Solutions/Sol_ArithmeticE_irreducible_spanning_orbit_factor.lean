-- Prove2me | solution 1 for ArithmeticE.irreducible_spanning_orbit_factor
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T20:55:28.305603+00:00
-- url     : https://prove2.me/submissions/431b275c-0c08-4f36-9088-6ffd626b89a3

import Mathlib
set_option autoImplicit false
namespace BeukersOrbit

/-- The irreducibility step in the conjugate-product argument. -/
lemma factor_vanishes {H : Type*} [TopologicalSpace H] [IrreducibleSpace H]
    {ι : Type*} [Fintype ι] (v : ι → H → ℂ)
    (hclosed : ∀ i, IsClosed {g : H | v i g = 0})
    (hprod : ∀ g, ∏ i, v i g = 0) : ∃ i, ∀ g, v i g = 0 := by
  classical
  let Z : ι → Set H := fun i => {g | v i g = 0}
  obtain ⟨z, hz, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp
      (IrreducibleSpace.isIrreducible_univ H)) (Finset.univ.image Z) (by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact hclosed i) (by
        intro g hg
        obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp (hprod g)
        exact Set.mem_sUnion.mpr ⟨Z i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨i, fun g => hsub (Set.mem_univ g)⟩

/-- An orbit spanning its solution space upgrades the vanishing factor to an identically
zero evaluation functional on that space. -/
lemma spanning_factor {H : Type*} [TopologicalSpace H] [IrreducibleSpace H]
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (orbit : ∀ i, H → V i) (ev : ∀ i, V i →ₗ[ℂ] ℂ)
    (hspan : ∀ i, Submodule.span ℂ (Set.range (orbit i)) = ⊤)
    (hclosed : ∀ i, IsClosed {g : H | ev i (orbit i g) = 0})
    (hprod : ∀ g, ∏ i, ev i (orbit i g) = 0) :
    ∃ i, ev i = 0 := by
  obtain ⟨i, hi⟩ := factor_vanishes (fun i g => ev i (orbit i g)) hclosed hprod
  refine ⟨i, ?_⟩
  have hs : Submodule.span ℂ (Set.range (orbit i)) ≤ LinearMap.ker (ev i) := by
    rw [Submodule.span_le]
    rintro v ⟨g, rfl⟩
    exact hi g
  rw [hspan] at hs
  exact LinearMap.ker_eq_top.mp (top_le_iff.mp hs)
end BeukersOrbit

theorem solution {H : Type*} [TopologicalSpace H] [IrreducibleSpace H]
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (orbit : ∀ i, H → V i) (ev : ∀ i, V i →ₗ[ℂ] ℂ)
    (hspan : ∀ i, Submodule.span ℂ (Set.range (orbit i)) = ⊤)
    (hclosed : ∀ i, IsClosed {g : H | ev i (orbit i g) = 0})
    (hprod : ∀ g, ∏ i, ev i (orbit i g) = 0) :
    ∃ i, ev i = 0 := by
  exact BeukersOrbit.spanning_factor V orbit ev hspan hclosed hprod
#print axioms solution
