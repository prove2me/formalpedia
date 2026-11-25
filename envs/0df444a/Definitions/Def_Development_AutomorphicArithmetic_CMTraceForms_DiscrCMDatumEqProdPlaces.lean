-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_DiscrCMDatumEqProdPlaces
-- name    : Development_AutomorphicArithmetic_CMTraceForms_DiscrCMDatumEqProdPlaces
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:47.099791+00:00
-- url     : https://prove2.me/theorems/e38f30dd-7ddb-481f-a1e4-c1b01063d0f9
-- title:
--   Discr CMDatum Eq Prod Places
-- statement:
--   Definitions and structural lemmas for Discr CMDatum Eq Prod Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/DiscrCMDatumEqProdPlaces.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
noncomputable section
namespace UpperTheory.PlacesDiscr
section Emb
variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
theorem exists_lift_val (hv : v.Integers O) (φ : E →ₐ[ℚ] C) (a : 𝓞 E) :
    ∃ x : O, algebraMap O C x = φ (a : E) := by
  have h1 : IsIntegral ℤ (φ (a : E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe a).map φ.toRingHom.toIntAlgHom
  have h2 : IsIntegral O (φ (a : E)) := h1.tower_top
  exact hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.mp h2)
def restrEmb (hv : v.Integers O) (φ : E →ₐ[ℚ] C) : 𝓞 E →+* O where
  toFun a := (exists_lift_val hv φ a).choose
  map_one' := hv.hom_inj (by rw [(exists_lift_val hv φ _).choose_spec]; simp)
  map_mul' a b := hv.hom_inj (by
    rw [map_mul]; simp only [(exists_lift_val hv φ _).choose_spec]; simp)
  map_zero' := hv.hom_inj (by rw [(exists_lift_val hv φ _).choose_spec]; simp)
  map_add' a b := hv.hom_inj (by
    rw [map_add]; simp only [(exists_lift_val hv φ _).choose_spec]; simp)
variable {p : ℕ} [Fact p.Prime]
end Emb
section Split
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [StarRing R]
theorem sig_sig (x : ℤ_[p] ⊗[ℤ] R) : sig p R (sig p R x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sig]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
def sigEquiv : (ℤ_[p] ⊗[ℤ] R) ≃ₐ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] R) :=
  AlgEquiv.ofAlgHom (sig p R) (sig p R) (AlgHom.ext sig_sig) (AlgHom.ext sig_sig)
variable {s : ℕ} (w : Fin s → Place p R)
def sumMap : (∀ i, (w i).Ow) →ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] R) :=
  ∑ i, (w i).Ow.subtype ∘ₗ LinearMap.proj i
theorem sumMap_apply (x : ∀ i, (w i).Ow) :
    sumMap w x = ∑ i, (x i : ℤ_[p] ⊗[ℤ] R) := by
  simp [sumMap]
variable {w}
theorem e_mul_sum (h1 : ∀ i j, i ≠ j → (w i).e * (w j).e = 0) (i : Fin s)
    (x : ∀ i, (w i).Ow) : (w i).e * sumMap w x = x i := by
  have hx : ∀ j, ∃ y, (w j).e * y = (x j : ℤ_[p] ⊗[ℤ] R) := fun j => by
    have h : (x j : ℤ_[p] ⊗[ℤ] R) ∈ (LinearMap.mulLeft ℤ_[p] (w j).e).range := (x j).2
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  rw [sumMap_apply, Finset.mul_sum, Finset.sum_eq_single i]
  · obtain ⟨y, hy⟩ := hx i
    rw [← hy, ← mul_assoc, (w i).idem]
  · intro j _ hji
    obtain ⟨y, hy⟩ := hx j
    rw [← hy, ← mul_assoc, h1 i j (Ne.symm hji), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h
theorem e_mul_sig_sum (h3 : ∀ i j, (w i).e * (w j).bar = 0) (i : Fin s)
    (x : ∀ i, (w i).Ow) : (w i).e * sig p R (sumMap w x) = 0 := by
  have hx : ∀ j, ∃ y, (w j).e * y = (x j : ℤ_[p] ⊗[ℤ] R) := fun j => by
    have h : (x j : ℤ_[p] ⊗[ℤ] R) ∈ (LinearMap.mulLeft ℤ_[p] (w j).e).range := (x j).2
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  rw [sumMap_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨y, hy⟩ := hx j
  have hb : sig p R (w j).e = (w j).bar := rfl
  rw [← hy, map_mul, ← mul_assoc, hb, h3 i j, zero_mul]
def splitEquiv (h1 : ∀ i j, i ≠ j → (w i).e * (w j).e = 0)
    (h2 : (∑ i, (w i).e) + (∑ i, (w i).bar) = 1) (h3 : ∀ i j, (w i).e * (w j).bar = 0) :
    ((∀ i, (w i).Ow) × (∀ i, (w i).Ow)) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] R) :=
  LinearEquiv.ofBijective
    ((sumMap w).coprod ((sig p R).toLinearMap ∘ₗ sumMap w)) (by
      constructor
      · rw [injective_iff_map_eq_zero]
        rintro ⟨x, y⟩ hxy
        have k1 : sumMap w x + sig p R (sumMap w y) = 0 := hxy
        have k2 : x = 0 := by
          funext i
          have := congrArg ((w i).e * ·) k1
          simp only [mul_add, e_mul_sum h1, e_mul_sig_sum h3, add_zero, mul_zero] at this
          exact Subtype.ext this
        rw [k2, map_zero, zero_add] at k1
        have k4 := congrArg (sig p R) k1
        rw [sig_sig, map_zero] at k4
        have k5 : y = 0 := by
          funext i
          have := e_mul_sum h1 i y
          rw [k4, mul_zero] at this
          exact Subtype.ext this.symm
        exact Prod.ext k2 k5
      · intro a
        refine ⟨(fun i => ⟨(w i).e * a, a, rfl⟩,
          fun i => ⟨(w i).e * sig p R a, sig p R a, rfl⟩), ?_⟩
        change sumMap w _ + sig p R (sumMap w _) = a
        rw [sumMap_apply, sumMap_apply, map_sum]
        change ∑ i, (w i).e * a + ∑ i, sig p R ((w i).e * sig p R a) = a
        simp only [map_mul, sig_sig]
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
        change ((∑ i, (w i).e) + (∑ i, (w i).bar)) * a = a
        rw [h2, one_mul])
end Split
end UpperTheory.PlacesDiscr
end


