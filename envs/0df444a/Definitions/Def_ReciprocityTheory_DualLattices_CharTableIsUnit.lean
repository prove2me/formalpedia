-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
-- name    : ReciprocityTheory_DualLattices_CharTableIsUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:44.91286+00:00
-- url     : https://prove2.me/theorems/a29bb198-8470-40cf-b085-c433d50fc640
-- title:
--   Char Table Is Unit
-- statement:
--   Definitions and structural lemmas for Char Table Is Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/CharTableIsUnit.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
def HopfOrder.ofSpan (S : Set (N → C)) (hlat : IsLat R (Submodule.span R S))
    (hint : S ⊆ (intFun (C := C) R N : Set (N → C))) (h1 : (1 : N → C) ∈ Submodule.span R S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ Submodule.span R S)
    (hcomul : ∀ a ∈ S, addPull R N a ∈ tensorSpan R (Submodule.span R S))
    (hanti : ∀ a ∈ S, (fun x => a (-x)) ∈ Submodule.span R S) : HopfOrder (C := C) R N where
  carrier := Submodule.span R S
  lat := hlat
  le_int := Submodule.span_le.mpr hint
  one_mem := h1
  mul_mem f g hf hg := by
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    refine (Submodule.span_le.mpr ?_) h
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact hmul a ha b hb
  comul f hf := by
    have : Submodule.span R S ≤
        (tensorSpan R (Submodule.span R S)).comap (addPull R N) :=
      Submodule.span_le.mpr hcomul
    exact this hf
  antipode f hf := by
    have : Submodule.span R S ≤
        (Submodule.span R S).comap (LinearMap.funLeft R C (fun x : N => -x)) :=
      Submodule.span_le.mpr hanti
    exact this hf
def constOrder : HopfOrder (C := C) R N :=
  HopfOrder.ofSpan (Set.range fun a : N => (Pi.single a (1 : C) : N → C))
    ⟨1, by simp, by
      congr 1
      ext f
      simp only [Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by ext x; simp [Matrix.one_apply, Pi.single_apply]⟩
      · rintro ⟨a, rfl⟩; exact ⟨a, by ext x; simp [Matrix.one_apply, Pi.single_apply]⟩⟩
    (by
      rintro f ⟨a, rfl⟩ x
      by_cases h : x = a
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩)
    (by
      have : (1 : N → C) = ∑ a, (Pi.single a (1 : C) : N → C) := by
        ext x; simp [Pi.single_apply]
      rw [this]
      exact Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, rfl⟩)
    (by
      rintro f ⟨a, rfl⟩ g ⟨b, rfl⟩
      have : (Pi.single a (1 : C) : N → C) * Pi.single b 1 =
          (if a = b then (1 : R) else 0) • (Pi.single a (1 : C) : N → C) := by
        ext x; by_cases h : a = b <;> by_cases hx : x = a <;> simp_all [Pi.single_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    (by
      rintro f ⟨c, rfl⟩
      have : addPull R N (Pi.single c (1 : C) : N → C) =
          ∑ a, fun p : N × N => (Pi.single a (1 : C) : N → C) p.1 *
            (Pi.single (c - a) (1 : C) : N → C) p.2 := by
        ext ⟨x, y⟩
        simp only [addPull, LinearMap.funLeft_apply, Finset.sum_apply, Pi.single_apply,
          ite_mul, one_mul, zero_mul]
        by_cases h : x + y = c
        · have : y = c - x := by rw [← h]; abel
          simp [this]
        · have : ¬ y = c - x := by intro hy; apply h; rw [hy]; abel
          simp [h, this]
      rw [this]
      refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ?_
      exact ⟨_, Submodule.subset_span ⟨a, rfl⟩, _, Submodule.subset_span ⟨c - a, rfl⟩, rfl⟩)
    (by
      rintro f ⟨a, rfl⟩
      refine Submodule.subset_span ⟨-a, ?_⟩
      ext x; simp [Pi.single_apply, neg_eq_iff_eq_neg])
def negChar (ψ : AddChar N C) : AddChar N C where
  toFun x := ψ (-x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [neg_add, AddChar.map_add_eq_mul]
def multOrder (v : Valuation C NNReal) (hv : v.Integers R) (e : N ≃ AddChar N C)
    (hB : IsUnit (Matrix.of fun x j : N => e j x).det) : HopfOrder (C := C) R N :=
  HopfOrder.ofSpan (Set.range fun j : N => ((e j : AddChar N C) : N → C))
    ⟨_, hB, by simp [Matrix.of_apply]⟩
    (by
      rintro f ⟨j, rfl⟩ x
      refine hv.exists_of_le_one ?_
      have hn : (e j x) ^ Fintype.card N = 1 := by
        rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
      have : v (e j x) ^ Fintype.card N ≤ 1 := by rw [← map_pow, hn, map_one]
      exact (pow_le_one_iff_of_nonneg (by positivity) Fintype.card_ne_zero).mp this)
    (Submodule.subset_span ⟨e.symm 1, by simp⟩)
    (by
      rintro f ⟨a, rfl⟩ g ⟨b, rfl⟩
      exact Submodule.subset_span ⟨e.symm (e a * e b), by simp⟩)
    (by
      rintro f ⟨j, rfl⟩
      refine Submodule.subset_span ⟨_, Submodule.subset_span ⟨j, rfl⟩, _,
        Submodule.subset_span ⟨j, rfl⟩, ?_⟩
      ext p; simp [addPull, AddChar.map_add_eq_mul])
    (by
      rintro f ⟨j, rfl⟩
      exact Submodule.subset_span ⟨e.symm (negChar (e j)), by ext x; simp [negChar]⟩)
theorem charTable_isUnit (e : N ≃ AddChar N C) : IsUnit (Matrix.of fun x j : N => e j x).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
  have hinj : Function.Injective fun j : N => (e j).toMonoidHom := fun a b hab =>
    e.injective (DFunLike.ext _ _ fun x => DFunLike.congr_fun hab (Multiplicative.ofAdd x))
  exact (linearIndependent_monoidHom (Multiplicative N) C).comp _ hinj
def multOrder' (v : Valuation C NNReal) (hv : v.Integers R) (e : N ≃ AddChar N C) :
    HopfOrder (C := C) R N :=
  multOrder v hv e (charTable_isUnit e)
end ReciprocityTheory.PGsh.L2


