-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Restricted
-- name    : GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Restricted
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:41:01.607893+00:00
-- url     : https://prove2.me/theorems/20d877ea-3c44-4887-8351-87e45ad3a05c
-- title:
--   Restricted
-- statement:
--   Definitions and structural lemmas for Restricted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Restricted.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_map
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_mem_latticeStabilizer_iff
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply


set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (K) in

def finiteAdeleEval (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
theorem continuous_finiteAdeleEval (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteAdeleEval K v) :=
  RestrictedProduct.continuous_eval (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) v
abbrev localIntegral (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (unitaryPoints K E H (v.adicCompletion K)) :=
  latticeStabilizer H (v.adicCompletion K) b (v.adicCompletionIntegers K).toSubring
theorem eventually_isAdapted :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      IsAdapted b (v.adicCompletionIntegers K).toSubring := by
  have h : ∀ c : K, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      algebraMap K (v.adicCompletion K) c ∈ (v.adicCompletionIntegers K).toSubring :=
    fun c => (algebraMap K (FiniteAdeleRing (𝓞 K) K) c).2
  exact (eventually_all.2 fun k => h _).and
    (eventually_all.2 fun k => eventually_all.2 fun l => eventually_all.2 fun m => h _)
theorem unitaryCoords_finiteAdeleEval (g : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) (p : ι × ι × κ) :
    unitaryCoords H (v.adicCompletion K) b (unitaryMap K E H (finiteAdeleEval K v) g) p =
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g p v := by
  rw [unitaryCoords_unitaryMap]
  rfl
theorem eventually_mem_localIntegral (g : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      unitaryMap K E H (finiteAdeleEval K v) g ∈ localIntegral H b v := by
  have h₁ : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ p,
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g p v ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun p => (unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g p).2
  have h₂ : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ p,
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g⁻¹ p v ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun p => (unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g⁻¹ p).2
  filter_upwards [eventually_isAdapted b, h₁, h₂] with v hv hv₁ hv₂
  rw [mem_latticeStabilizer_iff hv]
  refine ⟨fun p => ?_, fun p => ?_⟩
  · rw [unitaryCoords_finiteAdeleEval]
    exact hv₁ p
  · rw [← map_inv, unitaryCoords_finiteAdeleEval]
    exact hv₂ p
def toRestrictedUnitary : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K) →*
    Πʳ v : HeightOneSpectrum (𝓞 K),
      [unitaryPoints K E H (v.adicCompletion K), localIntegral H b v] where
  toFun g := ⟨fun v => unitaryMap K E H (finiteAdeleEval K v) g, eventually_mem_localIntegral H b g⟩
  map_one' := RestrictedProduct.ext _ _ fun v => map_one (unitaryMap K E H (finiteAdeleEval K v))
  map_mul' g h := RestrictedProduct.ext _ _ fun v => map_mul (unitaryMap K E H (finiteAdeleEval K v)) g h
theorem toRestrictedUnitary_apply (g : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) :
    toRestrictedUnitary H b g v = unitaryMap K E H (finiteAdeleEval K v) g := rfl
def restrictedCoord (p : ι × ι × κ)
    (y : Πʳ v : HeightOneSpectrum (𝓞 K),
      [unitaryPoints K E H (v.adicCompletion K), localIntegral H b v]) :
    FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.mapAlong (fun v : HeightOneSpectrum (𝓞 K) =>
      unitaryPoints K E H (v.adicCompletion K))
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) id tendsto_id
    (fun v g => unitaryCoords H (v.adicCompletion K) b g p)
    (by
      filter_upwards [eventually_isAdapted b] with v hv g hg
      exact ((mem_latticeStabilizer_iff hv g).1 hg).1 p) y
theorem restrictedCoord_apply (p : ι × ι × κ)
    (y : Πʳ v : HeightOneSpectrum (𝓞 K),
      [unitaryPoints K E H (v.adicCompletion K), localIntegral H b v])
    (v : HeightOneSpectrum (𝓞 K)) :
    restrictedCoord H b p y v = unitaryCoords H (v.adicCompletion K) b (y v) p := rfl
theorem continuous_restrictedCoord (p : ι × ι × κ) : Continuous (restrictedCoord H b p) := by
  unfold restrictedCoord
  exact RestrictedProduct.mapAlong_continuous _ _ _ _ _ _
    fun v => (continuous_apply p).comp
      (continuous_unitaryCoords H (HeightOneSpectrum.adicCompletion K v) b)
theorem toRestrictedUnitary_bijective (hH : IsUnit H.det) :
    Function.Bijective (toRestrictedUnitary H b) := by
  constructor
  · intro g g' h
    apply unitaryCoords_injective H _ b
    funext p
    refine FiniteAdeleRing.ext K fun v => ?_
    have := congrArg (fun y => unitaryCoords H (v.adicCompletion K) b (y v) p) h
    simpa only [toRestrictedUnitary_apply, unitaryCoords_finiteAdeleEval] using this
  · intro y
    let M : Matrix ι ι (FiniteAdeleRing (𝓞 K) K ⊗[K] E) :=
      (matrixCoords b (FiniteAdeleRing (𝓞 K) K)).symm fun p => restrictedCoord H b p y
    have hMv : ∀ v : HeightOneSpectrum (𝓞 K),
        M.map (tensorMap E (finiteAdeleEval K v)) = unitaryMat (y v) := by
      intro v
      apply (matrixCoords b (v.adicCompletion K)).injective
      rw [matrixCoords_map, Equiv.apply_symm_apply]
      rfl
    obtain ⟨g, hg⟩ := exists_unitaryPoints_of_forall hH (fun v => finiteAdeleEval K v)
      (fun a ha => FiniteAdeleRing.ext K ha) M fun v => ⟨y v, (hMv v).symm⟩
    refine ⟨g, RestrictedProduct.ext _ _ fun v => ?_⟩
    apply Subtype.ext; apply Units.ext
    change unitaryMat (unitaryMap K E H _ g) = unitaryMat (y v)
    rw [unitaryMat_unitaryMap, hg, hMv]
theorem isOpen_setOf_coords_mem (T : Set (HeightOneSpectrum (𝓞 K))) :
    IsOpen {g : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K) | ∀ p, ∀ v ∈ T,
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g p v ∈ v.adicCompletionIntegers K ∧
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g⁻¹ p v ∈ v.adicCompletionIntegers K} := by
  have hW : IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v, v ∈ T → a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (fun v => Valued.isOpen_valuationSubring _) (p := (· ∈ T))
  have hc : Continuous (unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b) :=
    continuous_unitaryCoords H _ b
  have h : ∀ p, IsOpen {g : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K) | ∀ v ∈ T,
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g p v ∈ v.adicCompletionIntegers K ∧
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g⁻¹ p v ∈ v.adicCompletionIntegers K} := by
    intro p
    have h₁ := hW.preimage ((continuous_apply p).comp hc)
    have h₂ := hW.preimage ((continuous_apply p).comp (hc.comp continuous_inv))
    convert h₁.inter h₂ using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
    exact ⟨fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩,
      fun h v hv => ⟨h.1 v hv, h.2 v hv⟩⟩
  convert isOpen_iInter_of_finite h using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
theorem continuous_toRestrictedUnitary : Continuous (toRestrictedUnitary H b) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  set T : Set (HeightOneSpectrum (𝓞 K)) := {v | IsAdapted b (v.adicCompletionIntegers K).toSubring ∧
    ∀ p, unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g₀ p v ∈ v.adicCompletionIntegers K ∧
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g₀⁻¹ p v ∈ v.adicCompletionIntegers K} with hTdef
  have hT : cofinite ≤ 𝓟 T := by
    rw [le_principal_iff]
    have h₁ : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ p,
        unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g₀ p v ∈ v.adicCompletionIntegers K ∧
        unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g₀⁻¹ p v ∈ v.adicCompletionIntegers K :=
      eventually_all.2 fun p =>
        (unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g₀ p).2.and
          (unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g₀⁻¹ p).2
    exact (eventually_isAdapted b).and h₁
  let N : Set (unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K)) := {g | ∀ p, ∀ v ∈ T,
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g p v ∈ v.adicCompletionIntegers K ∧
      unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b g⁻¹ p v ∈ v.adicCompletionIntegers K}
  have hNo : IsOpen N := isOpen_setOf_coords_mem H b T
  have hgN : g₀ ∈ N := fun p v hv => hv.2 p
  have hmem : ∀ g ∈ N, ∀ v ∈ T, unitaryMap K E H (finiteAdeleEval K v) g ∈ localIntegral H b v := by
    intro g hg v hv
    rw [mem_latticeStabilizer_iff hv.1]
    refine ⟨fun p => ?_, fun p => ?_⟩
    · rw [unitaryCoords_finiteAdeleEval]
      exact (hg p v hv).1
    · rw [← map_inv, unitaryCoords_finiteAdeleEval]
      exact (hg p v hv).2
  let G : N → Πʳ v : HeightOneSpectrum (𝓞 K),
      [unitaryPoints K E H (v.adicCompletion K), localIntegral H b v]_[𝓟 T] :=
    fun g => ⟨fun v => unitaryMap K E H (finiteAdeleEval K v) g.1,
      eventually_principal.2 fun v hv => hmem g.1 g.2 v hv⟩
  have hG : Continuous G := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_pi fun v =>
      (continuous_unitaryMap _ (continuous_finiteAdeleEval v)).comp continuous_subtype_val
  have hFN : ContinuousOn (toRestrictedUnitary H b) N := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (RestrictedProduct.continuous_inclusion hT).comp hG
  exact hFN.continuousAt (hNo.mem_nhds hgN)
def finiteAdeleUnitaryEquiv (hH : IsUnit H.det) :
    unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K) ≃ₜ*
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [unitaryPoints K E H (v.adicCompletion K), localIntegral H b v] where
  toMulEquiv := MulEquiv.ofBijective (toRestrictedUnitary H b) (toRestrictedUnitary_bijective H b hH)
  continuous_toFun := continuous_toRestrictedUnitary H b
  continuous_invFun := by
    rw [(isEmbedding_unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b hH).continuous_iff]
    have : ∀ y, (unitaryCoords H (FiniteAdeleRing (𝓞 K) K) b ∘ (MulEquiv.ofBijective
        (toRestrictedUnitary H b) (toRestrictedUnitary_bijective H b hH)).symm) y =
        fun p => restrictedCoord H b p y := by
      intro y
      have hy := (MulEquiv.ofBijective _ (toRestrictedUnitary_bijective H b hH)).apply_symm_apply y
      funext p
      refine FiniteAdeleRing.ext K fun v => ?_
      conv_rhs => rw [← hy]
      rw [restrictedCoord_apply]
      simp only [Function.comp_apply, MulEquiv.ofBijective_apply, toRestrictedUnitary_apply,
        unitaryCoords_finiteAdeleEval]
    exact Continuous.congr (continuous_pi fun p => continuous_restrictedCoord H b p)
      (fun y => (this y).symm)
end
end GroundTheory.Automorphic


