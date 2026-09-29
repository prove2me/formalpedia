-- Prove2me | solution 1 for AutomorphicForm.exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a7ac4515-d268-5e7b-83fc-4787d70a7c7e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option synthInstance.maxHeartbeats 1600000

open TopologicalSpace Filter Topology
open scoped TensorProduct.RightActions

noncomputable section

namespace CosetsGlue

section IntegralUnitsAlgebra

variable {A : Type*} [CommRing A]

theorem mul_mem_integralUnitsSet (B : Subring A) {g h : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (B : Set A)) (hh : h ∈ AutomorphicForm.integralUnitsSet (B : Set A)) :
    g * h ∈ AutomorphicForm.integralUnitsSet (B : Set A) := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (hh.2 i k) (hg.2 k j)

theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet U) : g⁻¹ ∈ AutomorphicForm.integralUnitsSet U := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem isClosed_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] {U : Set A} (hU : IsClosed U) :
    IsClosed (AutomorphicForm.integralUnitsSet (A := A) U) := by
  rw [AutomorphicForm.integralUnitsSet_eq_preimage]
  have hC : IsClosed (AutomorphicForm.integralMatrixSet (A := A) U) := by
    rw [AutomorphicForm.integralMatrixSet_eq_pi]
    exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hU
  exact (hC.prod (MulOpposite.opHomeomorph.isClosedMap _ hC)).preimage Units.continuous_embedProduct

theorem continuous_glMap {B : Type*} [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

end IntegralUnitsAlgebra

section Kgroup

set_option linter.unusedSectionVars false

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def semiLocalIntegersSubring : Subring (L ⊗[K] v.adicCompletion K) :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).toRingHom.range

theorem coe_semiLocalIntegersSubring :
    (semiLocalIntegersSubring K L v : Set (L ⊗[K] v.adicCompletion K)) = AutomorphicForm.semiLocalIntegers K L v := by
  ext x
  simp only [semiLocalIntegersSubring, AutomorphicForm.semiLocalIntegers, Set.mem_range, SetLike.mem_coe,
    RingHom.mem_range]
  exact Iff.rfl

theorem mul_mem_semiLocalIntegralSet {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) (hh : h ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    g * h ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  unfold AutomorphicForm.semiLocalIntegralSet at *
  rw [← coe_semiLocalIntegersSubring] at *
  exact mul_mem_integralUnitsSet _ hg hh

theorem inv_mem_semiLocalIntegralSet {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) : g⁻¹ ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
  inv_mem_integralUnitsSet _ hg

theorem indicator_inv_mul_mul_eq (a x : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    {k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)} (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (a⁻¹ * (x * k)) =
      (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (a⁻¹ * x) := by
  by_cases hx : a⁻¹ * x ∈ AutomorphicForm.semiLocalIntegralSet K L v
  · have : a⁻¹ * (x * k) ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
      rw [← mul_assoc]; exact mul_mem_semiLocalIntegralSet K L v hx hk
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem this]
  · have : a⁻¹ * (x * k) ∉ AutomorphicForm.semiLocalIntegralSet K L v := by
      intro h
      apply hx
      have := mul_mem_semiLocalIntegralSet K L v h (inv_mem_semiLocalIntegralSet K L v hk)
      rwa [← mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]

end Kgroup

section SmulSet

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem smul_semiLocalIntegralSet_eq {k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    k • AutomorphicForm.semiLocalIntegralSet K L v = AutomorphicForm.semiLocalIntegralSet K L v := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  constructor
  · intro h
    have := mul_mem_semiLocalIntegralSet K L v hk h
    rwa [mul_inv_cancel_left] at this
  · intro h
    exact mul_mem_semiLocalIntegralSet K L v (inv_mem_semiLocalIntegralSet K L v hk) h

theorem smul_smul_eq_smul_of_eq {G : Type*} [Group G] (S : Set G) (hS : ∀ k ∈ S, k • S = S)
    {x a z k : G} (hk : k ∈ S) (h : x • (a • k) = z) : x • (a • S) = z • S := by
  rw [smul_eq_mul, smul_eq_mul] at h
  subst h
  rw [smul_smul, ← mul_assoc, mul_smul (x * a) k S, hS k hk]

theorem smul_smul_eq_of_mem_of_mem {G : Type*} [Group G] (S : Set G) (hS : ∀ k ∈ S, k • S = S)
    {x y a z : G} (hz₁ : z ∈ x • (a • S)) (hz₂ : z ∈ y • (a • S)) : x • (a • S) = y • (a • S) := by
  obtain ⟨_, ⟨k₁, hk₁, rfl⟩, h₁⟩ := hz₁
  obtain ⟨_, ⟨k₂, hk₂, rfl⟩, h₂⟩ := hz₂
  rw [smul_smul_eq_smul_of_eq S hS hk₁ h₁, smul_smul_eq_smul_of_eq S hS hk₂ h₂]

end SmulSet

section GenericDecomp

open scoped ENNReal Pointwise

theorem exists_decomp {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (S : Set G) (hS : ∀ k ∈ S, k • S = S) (hSo : IsOpen S) (hSc : IsCompact S) (hμ : μ S = 1) (a : G) :
    ∃ (m : ℕ) (k : Fin m → G), (∀ i, k i ∈ S) ∧ S * {a} * S = ⋃ i, k i • (a • S) ∧
      (∀ i j, i ≠ j → Disjoint (k i • (a • S)) (k j • (a • S))) ∧ μ (S * {a} * S) = m := by
  classical
  have hCopen : ∀ x : G, IsOpen (x • (a • S)) := fun x => (hSo.smul a).smul x
  have hCsub : ∀ x ∈ S, x • (a • S) ⊆ S * {a} * S := by
    rintro x hx _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨x * a, ⟨x, hx, a, rfl, rfl⟩, k, hk, ?_⟩
    simp only [smul_eq_mul, mul_assoc]
  have hcover : S * {a} * S ⊆ ⋃ x : ↥S, (x : G) • (a • S) := by
    rintro _ ⟨_, ⟨x, hx, a', ha', rfl⟩, k, hk, rfl⟩
    rw [Set.mem_singleton_iff.mp ha']
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ⟨a * k, ⟨k, hk, rfl⟩, by simp only [smul_eq_mul, mul_assoc]⟩⟩
  have hcpt : IsCompact (S * {a} * S) := (hSc.mul isCompact_singleton).mul hSc
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover (fun x : ↥S => (x : G) • (a • S)) (fun x => hCopen x) hcover
  obtain ⟨F, hF⟩ : ∃ F : Finset (Set G), F = t.image fun x : ↥S => (x : G) • (a • S) := ⟨_, rfl⟩
  have hFrep : ∀ s : ↥F, ∃ x : ↥S, (x : G) • (a • S) = s := by
    rintro ⟨s, hs⟩
    rw [hF] at hs
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hs
    exact ⟨x, hx⟩
  choose rep hrep using hFrep
  obtain ⟨e, -⟩ : ∃ e : ↥F ≃ Fin F.card, True := ⟨F.equivFin, trivial⟩
  have hunion : S * {a} * S = ⋃ i : Fin F.card, (rep (e.symm i) : G) • (a • S) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
      have hs : (x : G) • (a • S) ∈ F := hF ▸ Finset.mem_image.mpr ⟨x, hxt, rfl⟩
      refine Set.mem_iUnion.mpr ⟨e ⟨_, hs⟩, ?_⟩
      rw [Equiv.symm_apply_apply, hrep]
      exact hyx
    · exact Set.iUnion_subset fun i => hCsub _ (rep _).2
  have hdisj : ∀ i j : Fin F.card, i ≠ j →
      Disjoint ((rep (e.symm i) : G) • (a • S)) ((rep (e.symm j) : G) • (a • S)) := by
    intro i j hij
    by_contra hnd
    obtain ⟨z, hz₁, hz₂⟩ := Set.not_disjoint_iff_nonempty_inter.mp hnd
    have hne : ((e.symm i : ↥F) : Set G) ≠ ((e.symm j : ↥F) : Set G) := fun h =>
      hij (e.symm.injective (Subtype.ext h))
    apply hne
    rw [← hrep (e.symm i), ← hrep (e.symm j)]
    exact smul_smul_eq_of_mem_of_mem _ hS hz₁ hz₂
  have hmeasC : ∀ x : G, μ (x • (a • S)) = 1 := by
    intro x
    rw [measure_smul, measure_smul]
    exact hμ
  refine ⟨F.card, fun i => (rep (e.symm i) : G), fun i => (rep _).2, hunion, hdisj, ?_⟩
  rw [hunion, measure_iUnion (fun i j hij => hdisj i j hij) (fun i => (hCopen _).measurableSet), tsum_fintype]
  simp only [hmeasC, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end GenericDecomp

end CosetsGlue

end

open AutomorphicForm CosetsGlue

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ (m : ℕ) (k : Fin m → GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (∀ i, k i ∈ semiLocalIntegralSet K L v) ∧
      semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v =
        ⋃ i, k i • (a • semiLocalIntegralSet K L v) ∧
      (∀ i j, i ≠ j → Disjoint (k i • (a • semiLocalIntegralSet K L v)) (k j • (a • semiLocalIntegralSet K L v))) ∧
      AutomorphicForm.semiLocalHaar K L v (semiLocalIntegralSet K L v * {a} * semiLocalIntegralSet K L v) = m := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI hG := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  exact exists_decomp (AutomorphicForm.semiLocalHaar K L v) (semiLocalIntegralSet K L v)
    (fun k hk => smul_semiLocalIntegralSet_eq K L v hk) (isOpen_semiLocalIntegralSet K L v)
    (isCompact_semiLocalIntegralSet K L v) (semiLocalHaar_semiLocalIntegralSet K L v) a

end S_AutomorphicForm_exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card
end P2MW
export P2MW.S_AutomorphicForm_exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card (solution)
