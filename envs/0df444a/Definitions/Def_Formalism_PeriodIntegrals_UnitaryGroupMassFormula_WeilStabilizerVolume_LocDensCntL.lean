-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:21.306362+00:00
-- url     : https://prove2.me/theorems/c0caaece-82a3-4e95-aea5-184b2e36f1f8
-- title:
--   Loc Dens Cnt L
-- statement:
--   Definitions and structural lemmas for Loc Dens Cnt L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCntL.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_red_add
import Theorems.Thm_PI_VolStabW_red_mul
import Theorems.Thm_PI_VolStabW_red_one
import Theorems.Thm_PI_VolStabW_red_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
structure AntiB (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) where
  δ : E
  D0 : F
  c : Module.Basis (Fin 2) F E
  hc0 : c 0 = 1
  hc1 : c 1 = δ
  hδ : δ * δ = algebraMap F E D0
  hσδ : σ δ = -δ
  hD0 : D0 ≠ 0
section Lat
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
variable {σ : E →ₐ[F] E} (A : AntiB F E σ)
abbrev Pt (x y : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ (1 : E) + y ⊗ₜ A.δ
abbrev Xc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 0
abbrev Yc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 1
theorem repr_Pt (x y : Fv F v) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (Pt v A x y) = Finsupp.single 0 x + Finsupp.single 1 y := by
  have h0 : (Algebra.TensorProduct.basis (Fv F v) A.c).repr (x ⊗ₜ (1 : E)) = Finsupp.single 0 x := by
    rw [← A.hc0, Algebra.TensorProduct.basis_repr_tmul, A.c.repr_self]
    simp [Finsupp.mapRange_single]
  have h1 : (Algebra.TensorProduct.basis (Fv F v) A.c).repr (y ⊗ₜ A.δ) = Finsupp.single 1 y := by
    rw [← A.hc1, Algebra.TensorProduct.basis_repr_tmul, A.c.repr_self]
    simp [Finsupp.mapRange_single]
  rw [map_add, h0, h1]
theorem Xc_Pt (x y : Fv F v) : Xc v A (Pt v A x y) = x := by
  rw [Xc, repr_Pt]; simp
theorem Yc_Pt (x y : Fv F v) : Yc v A (Pt v A x y) = y := by
  rw [Yc, repr_Pt]; simp
theorem decomp (z : Fv F v ⊗[F] E) : z = Pt v A (Xc v A z) (Yc v A z) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) A.c).sum_repr z]
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, A.hc0,
    A.hc1, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one,
    mul_one]
theorem Pt_mul (x y x' y' : Fv F v) :
    Pt v A x y * Pt v A x' y' =
      Pt v A (x * x' + y * y' * algebraMap F (Fv F v) A.D0) (x * y' + y * x') := by
  have e : (y * y') ⊗ₜ[F] (algebraMap F E A.D0) =
      (y * y' * algebraMap F (Fv F v) A.D0) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.algebraMap_eq_smul_one A.D0, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def]; ring
  simp only [Pt, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, A.hδ, e,
    TensorProduct.add_tmul]
  rw [mul_comm y x']
  abel
theorem one_eq_Pt : (1 : Fv F v ⊗[F] E) = Pt v A 1 0 := by
  rw [Pt, TensorProduct.zero_tmul, add_zero, Algebra.TensorProduct.one_def]
theorem sig_Pt (x y : Fv F v) : sigR (Fv F v) σ (Pt v A x y) = Pt v A x (-y) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (Pt v A x y) = _
  simp [Pt, Algebra.TensorProduct.map_tmul, A.hσδ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]
theorem Xc_mul (z w : Fv F v ⊗[F] E) :
    Xc v A (z * w) = Xc v A z * Xc v A w + Yc v A z * Yc v A w * algebraMap F (Fv F v) A.D0 := by
  conv_lhs => rw [decomp v A z, decomp v A w, Pt_mul, Xc_Pt]
theorem Yc_mul (z w : Fv F v ⊗[F] E) :
    Yc v A (z * w) = Xc v A z * Yc v A w + Yc v A z * Xc v A w := by
  conv_lhs => rw [decomp v A z, decomp v A w, Pt_mul, Yc_Pt]
theorem Xc_sig (z : Fv F v ⊗[F] E) : Xc v A (sigR (Fv F v) σ z) = Xc v A z := by
  conv_lhs => rw [decomp v A z, sig_Pt, Xc_Pt]
theorem Yc_sig (z : Fv F v ⊗[F] E) : Yc v A (sigR (Fv F v) σ z) = -Yc v A z := by
  conv_lhs => rw [decomp v A z, sig_Pt, Yc_Pt]
theorem Xc_one : Xc v A 1 = 1 := by rw [one_eq_Pt v A, Xc_Pt]
theorem Yc_one : Yc v A 1 = 0 := by rw [one_eq_Pt v A, Yc_Pt]
theorem Xc_add (z w : Fv F v ⊗[F] E) : Xc v A (z + w) = Xc v A z + Xc v A w := by
  rw [Xc, Xc, Xc, map_add, Finsupp.add_apply]
theorem Yc_add (z w : Fv F v ⊗[F] E) : Yc v A (z + w) = Yc v A z + Yc v A w := by
  rw [Yc, Yc, Yc, map_add, Finsupp.add_apply]
theorem Xc_neg (z : Fv F v ⊗[F] E) : Xc v A (-z) = -Xc v A z := by
  rw [Xc, Xc, map_neg, Finsupp.neg_apply]
theorem Yc_neg (z : Fv F v ⊗[F] E) : Yc v A (-z) = -Yc v A z := by
  rw [Yc, Yc, map_neg, Finsupp.neg_apply]
theorem Xc_zero : Xc v A 0 = 0 := by simp [Xc]
theorem Yc_zero : Yc v A 0 = 0 := by simp [Yc]
def InC (z : Fv F v ⊗[F] E) : Prop :=
  Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F
variable (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
def lamC : Subring (Fv F v ⊗[F] E) where
  carrier := {z | InC v A z}
  mul_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z * w)
    refine ⟨?_, ?_⟩
    · rw [Xc_mul]
      exact add_mem (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD)
    · rw [Yc_mul]
      exact add_mem (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1)
  one_mem' := by
    change InC v A 1
    refine ⟨?_, ?_⟩
    · rw [Xc_one]; exact one_mem _
    · rw [Yc_one]; exact zero_mem _
  add_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z + w)
    exact ⟨by rw [Xc_add]; exact add_mem hz.1 hw.1, by rw [Yc_add]; exact add_mem hz.2 hw.2⟩
  zero_mem' := by
    change InC v A 0
    exact ⟨by rw [Xc_zero]; exact zero_mem _, by rw [Yc_zero]; exact zero_mem _⟩
  neg_mem' {z} hz := by
    change InC v A z at hz
    change InC v A (-z)
    exact ⟨by rw [Xc_neg]; exact neg_mem hz.1, by rw [Yc_neg]; exact neg_mem hz.2⟩
theorem mem_lamC (z : Fv F v ⊗[F] E) : z ∈ lamC v A hD ↔
    Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F := Iff.rfl
theorem sig_mem {z : Fv F v ⊗[F] E} (hz : z ∈ lamC v A hD) : sigR (Fv F v) σ z ∈ lamC v A hD := by
  rw [mem_lamC, Xc_sig, Yc_sig]
  exact ⟨hz.1, neg_mem hz.2⟩
def sigC : lamC v A hD →+* lamC v A hD where
  toFun z := ⟨sigR (Fv F v) σ z, sig_mem v A hD z.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
include hr in

def rho : lamC v A hD →+* K where
  toFun z := algebraMap _ K (red v (Xc v A z)) + algebraMap _ K (red v (Yc v A z)) * r
  map_one' := by
    simp only [Subring.coe_one, Xc_one, Yc_one, red_one, red_zero, map_one, map_zero, zero_mul,
      add_zero]
  map_mul' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [Subring.coe_mul, Xc_mul, Yc_mul]
    rw [red_add v (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD),
      red_add v (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1), red_mul v hz.1 hw.1,
      red_mul v (mul_mem hz.2 hw.2) hD, red_mul v hz.2 hw.2, red_mul v hz.1 hw.2,
      red_mul v hz.2 hw.1]
    simp only [map_add, map_mul]
    linear_combination (-(algebraMap _ K (red v (Yc v A z)) * algebraMap _ K (red v (Yc v A w)))) * hr
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, Xc_zero, Yc_zero, red_zero, map_zero, zero_mul, add_zero]
  map_add' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [AddMemClass.coe_add, Xc_add, Yc_add]
    rw [red_add v hz.1 hw.1, red_add v hz.2 hw.2]
    simp only [map_add]
    ring
variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))
end Lat
end PI.VolStabW


