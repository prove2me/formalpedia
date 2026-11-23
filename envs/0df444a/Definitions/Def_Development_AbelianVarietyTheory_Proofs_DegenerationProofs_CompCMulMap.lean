-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompCMulMap
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompCMulMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:48.917337+00:00
-- url     : https://prove2.me/theorems/0bb58852-0305-4f5d-b4bd-309d3ff028cc
-- title:
--   Comp CMul Map
-- statement:
--   Definitions and structural lemmas for Comp CMul Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CompCMulMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
namespace GlobalTheory.PowerSeriesCompositionMap
variable {O O₁ K : Type} [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁]
noncomputable def comp {ι : Type} (b : Module.Basis ι O O₁) (j : ι) : PowerSeries O₁ →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => b.repr (coeff n f) j
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp
lemma coeff_comp {ι : Type} (b : Module.Basis ι O O₁) (j : ι) (f : PowerSeries O₁) (n : ℕ) :
    coeff n (comp b j f) = b.repr (coeff n f) j := by
  simp [comp]
lemma decomp {ι : Type} [Fintype ι] (b : Module.Basis ι O O₁) (f : PowerSeries O₁) :
    f = ∑ j, C (b j) * map (algebraMap O O₁) (comp b j f) := by
  ext n
  rw [map_sum]
  simp only [coeff_C_mul, coeff_map, coeff_comp]
  conv_lhs => rw [← b.sum_repr (coeff n f)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, mul_comm]
lemma comp_C_mul_map {ι : Type} (b : Module.Basis ι O O₁) (j : ι) (a : O₁) (g : PowerSeries O) :
    comp b j (C a * map (algebraMap O O₁) g) = C (b.repr a j) * g := by
  ext n
  rw [coeff_comp, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul]
  simp [mul_comm]
variable {ι : Type} [Fintype ι] (b : Module.Basis ι O O₁) (i : PowerSeries O →+* K) (io : O₁ →+* K)
noncomputable def ext : PowerSeries O₁ →+ K :=
  ∑ j, (AddMonoidHom.mulLeft (io (b j))).comp ((i : PowerSeries O →+ K).comp (comp b j))
lemma ext_apply (f : PowerSeries O₁) : ext b i io f = ∑ j, io (b j) * i (comp b j f) := by
  simp [ext, AddMonoidHom.finset_sum_apply]
variable {b i io}
lemma ext_C_mul_map (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) (a : O₁) (g : PowerSeries O) :
    ext b i io (C a * map (algebraMap O O₁) g) = io a * i g := by
  rw [ext_apply]
  simp only [comp_C_mul_map, map_mul, ← h, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  conv_rhs => rw [← b.sum_repr a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, mul_comm]
lemma ext_mul (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) (f g : PowerSeries O₁) :
    ext b i io (f * g) = ext b i io f * ext b i io g := by
  conv_lhs => rw [decomp b f, decomp b g, Finset.sum_mul_sum, map_sum]
  conv_rhs => rw [decomp b f, decomp b g, map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : C (b j) * map (algebraMap O O₁) (comp b j f) * (C (b k) * map (algebraMap O O₁) (comp b k g))
      = C (b j * b k) * map (algebraMap O O₁) (comp b j f * comp b k g) := by
    rw [map_mul, map_mul]; ring
  rw [e, ext_C_mul_map h, ext_C_mul_map h, ext_C_mul_map h, map_mul, map_mul]
  ring
theorem main (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁]
    [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K)
    (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a : O₁, Φ (C a) = io a) ∧ Φ X = i X ∧
      ∀ f : PowerSeries O₁, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  let b := Module.Free.chooseBasis O O₁
  have hC : ∀ a : O₁, ext b i io (C a) = io a := fun a => by
    simpa using ext_C_mul_map (b := b) h a 1
  let Φ : PowerSeries O₁ →+* K :=
    { ext b i io with
      map_one' := by simpa using hC 1
      map_mul' := ext_mul h }
  refine ⟨Φ, hC, ?_, fun f => ?_⟩
  · show ext b i io X = i X
    simpa using ext_C_mul_map (b := b) h 1 X
  · show ext b i io f ∈ _
    rw [ext_apply]
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
example : ∀ (O O₁ K : Type) [inst : CommRing O] [inst_1 : CommRing O₁] [inst_2 : CommRing K] [inst_3 : Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K), (∀ (a : O), (io : O₁ → K) ((Algebra.algebraMap O O₁ : O → O₁) a) = (i : PowerSeries O → K) ((PowerSeries.C : O → PowerSeries O) a)) → ∃ (Φ : PowerSeries O₁ →+* K), (∀ (a : O₁), (Φ : PowerSeries O₁ → K) ((PowerSeries.C : O₁ → PowerSeries O₁) a) = (io : O₁ → K) a) ∧ (Φ : PowerSeries O₁ → K) PowerSeries.X = (i : PowerSeries O → K) PowerSeries.X ∧ ∀ (f : PowerSeries O₁), (Φ : PowerSeries O₁ → K) f ∈ Subring.closure (Set.range (⇑i : PowerSeries O → K) ∪ Set.range (⇑io : O₁ → K)) := main
end GlobalTheory.PowerSeriesCompositionMap


