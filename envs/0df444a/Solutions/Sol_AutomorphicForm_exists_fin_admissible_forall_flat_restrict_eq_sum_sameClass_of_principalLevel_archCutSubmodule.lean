-- Prove2me | solution 1 for AutomorphicForm.exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/adb5bd67-e796-5261-9366-3961685da0ae

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Theorems.Thm_AutomorphicForm_exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact
import Theorems.Thm_AutomorphicForm_isOpen_principalLevel
import Theorems.Thm_AutomorphicForm_exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace EisFinDim

open Module

theorem exists_finset_forall_eq_zero_of_forall_apply_eq_zero {X : Type*} (U : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ U] :
    ∃ E : Finset X, ∀ u ∈ U, (∀ x ∈ E, u x = 0) → u = 0 := by
  classical
  set d := Module.finrank ℂ U
  let b := Module.finBasis ℂ U
  let vec : X → (Fin d → ℂ) := fun x i => ((b i : U) : X → ℂ) x
  have hfg : (Submodule.span ℂ (Set.range vec)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  have hpre : ∀ v ∈ t, ∃ x, vec x = v := fun v hv => ht hv
  choose pt hpt using hpre
  refine ⟨t.attach.image fun v => pt v.1 v.2, fun u hu hz => ?_⟩
  set c : Fin d → ℂ := fun i => b.repr ⟨u, hu⟩ i with hc
  have hu_eq : ∀ x, u x = ∑ i, c i * vec x i := by
    intro x
    have hsum := b.sum_repr ⟨u, hu⟩
    have hx := congrArg (fun w : U => ((w : U) : X → ℂ) x) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    simpa [hc, vec] using hx.symm

  have hLt : ∀ v ∈ (t : Set (Fin d → ℂ)), ∑ i, c i * v i = 0 := by
    intro v hv
    have h := hz (pt v hv) (Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_attach _ _, rfl⟩)
    rw [hu_eq, hpt v hv] at h
    exact h
  have hLspan : ∀ v ∈ Submodule.span ℂ (t : Set (Fin d → ℂ)), ∑ i, c i * v i = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hLt v hv
    | zero => simp
    | add v w _ _ hv hw => simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, hv, hw]
    | smul a v _ hv => simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm _ a, ← Finset.mul_sum, hv] <;>
        (rw [show ∑ i, c i * (a * v i) = a * ∑ i, c i * v i from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hv, mul_zero])
  funext x
  have hx : vec x ∈ Submodule.span ℂ (t : Set (Fin d → ℂ)) := by
    rw [← hspan]; exact Submodule.subset_span ⟨x, rfl⟩
  rw [hu_eq x, hLspan _ hx]
  rfl

variable {H G : Type*} [Group H] [Group G]

def matrixCoeffSubmodule {n : ℕ} (ρ : Representation ℂ H (Fin n → ℂ)) : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ (Set.range fun p : Fin n × Fin n => fun k : H => ρ k (Pi.single p.2 1) p.1)

scoped instance finiteDimensional_matrixCoeffSubmodule {n : ℕ} (ρ : Representation ℂ H (Fin n → ℂ)) :
    FiniteDimensional ℂ ↥(matrixCoeffSubmodule ρ) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem apply_rep_mem_matrixCoeffSubmodule {n : ℕ} (ρ : Representation ℂ H (Fin n → ℂ))
    (lam : (Fin n → ℂ) →ₗ[ℂ] ℂ) (v : Fin n → ℂ) :
    (fun k : H => lam (ρ k v)) ∈ matrixCoeffSubmodule ρ := by
  classical
  have hbasis : ∀ w : Fin n → ℂ, w = ∑ j, w j • (Pi.single j 1 : Fin n → ℂ) := by
    intro w; ext i; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : ∀ j, (fun k : H => lam (ρ k (Pi.single j 1))) ∈ matrixCoeffSubmodule ρ := by
    intro j
    have heq : (fun k : H => lam (ρ k (Pi.single j 1))) =
        ∑ i, lam (Pi.single i 1) • fun k : H => ρ k (Pi.single j 1) i := by
      funext k
      conv_lhs => rw [hbasis (ρ k (Pi.single j 1))]
      simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have h1 : (fun k : H => lam (ρ k v)) = ∑ j, v j • fun k : H => lam (ρ k (Pi.single j 1)) := by
    funext k
    conv_lhs => rw [hbasis v]
    simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
  rw [h1]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h2 j)

theorem comp_mul_mem_matrixCoeffSubmodule {n : ℕ} {ι : H →* G} {ρ : Representation ℂ H (Fin n → ℂ)}
    {f : G → ℂ} (hf : f ∈ AutomorphicForm.typeSubmodule ι ρ) (x : G) :
    (fun k : H => f (x * ι k)) ∈ matrixCoeffSubmodule ρ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨T, hT, v, rfl⟩ := hf
    have h : (fun k : H => T v (x * ι k)) = fun k : H => (LinearMap.proj x ∘ₗ T) (ρ k v) := by
      funext k; exact (hT k v x).symm
    rw [h]
    exact apply_rep_mem_matrixCoeffSubmodule ρ _ v
  | zero => exact (matrixCoeffSubmodule ρ).zero_mem
  | add f g _ _ hf hg => exact (matrixCoeffSubmodule ρ).add_mem hf hg
  | smul c f _ hf => exact (matrixCoeffSubmodule ρ).smul_mem c hf

theorem comp_mul_mem_iSup_matrixCoeffSubmodule {m : ℕ} {n : Fin m → ℕ} {ι : H →* G}
    (ρ : (i : Fin m) → Representation ℂ H (Fin (n i) → ℂ)) {f : G → ℂ}
    (hf : f ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i)) (x : G) :
    (fun k : H => f (x * ι k)) ∈ ⨆ i, matrixCoeffSubmodule (ρ i) := by
  induction hf using Submodule.iSup_induction' with
  | mem i f hfi => exact Submodule.mem_iSup_of_mem i (comp_mul_mem_matrixCoeffSubmodule hfi x)
  | zero => exact (⨆ i, matrixCoeffSubmodule (ρ i)).zero_mem
  | add f g _ _ hf hg => exact (⨆ i, matrixCoeffSubmodule (ρ i)).add_mem hf hg

scoped instance finiteDimensional_iSup_matrixCoeffSubmodule {m : ℕ} {n : Fin m → ℕ}
    (ρ : (i : Fin m) → Representation ℂ H (Fin (n i) → ℂ)) :
    FiniteDimensional ℂ ↥(⨆ i, matrixCoeffSubmodule (ρ i)) :=
  Submodule.finiteDimensional_iSup _

end EisFinDim
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace EisFinDim

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

theorem eq_of_forall_archComponent_eq {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (hc : ∀ w : InfinitePlace F, archComponent F w g = archComponent F w h) : g = h := by
  apply Units.ext
  ext i j
  funext w
  have := congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (hc w)
  simp only [archComponent_apply] at this
  exact this

theorem eq_of_glArch_eq_of_glFin_eq' {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (h₂ : glFin (𝓞 F) F x = glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  ext i j
  have h₁' := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem commute_adelicArchGLInclAt_of_archComponent_eq_one {a : AdelicGL2 (𝓞 F) F} {w₀ : InfinitePlace F}
    (haf : glFin (𝓞 F) F a = 1) (haw : archComponent F w₀ (glArch (𝓞 F) F a) = 1) (g : GL (Fin 2) w₀.Completion) :
    Commute a (adelicArchGLInclAt F w₀ g) := by
  change a * adelicArchGLInclAt F w₀ g = adelicArchGLInclAt F w₀ g * a
  refine eq_of_glArch_eq_of_glFin_eq' F ?_ ?_
  · rw [map_mul, map_mul]
    refine eq_of_forall_archComponent_eq F fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = w₀
    · subst hw
      rw [haw, one_mul, mul_one]
    · show archComponent F w (glArch (𝓞 F) F a) * archComponent F w (glArch (𝓞 F) F ((adelicArchGLIncl F) (archGLIncl F w₀ g))) =
        archComponent F w (glArch (𝓞 F) F ((adelicArchGLIncl F) (archGLIncl F w₀ g))) * archComponent F w (glArch (𝓞 F) F a)
      rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne F hw, mul_one, one_mul]
  · rw [map_mul, map_mul, haf, one_mul, mul_one]

theorem commute_of_glArch_eq_one_of_glFin_eq_one {u a : AdelicGL2 (𝓞 F) F}
    (hu : glArch (𝓞 F) F u = 1) (ha : glFin (𝓞 F) F a = 1) : Commute u a := by
  change u * a = a * u
  refine eq_of_glArch_eq_of_glFin_eq' F ?_ ?_
  · rw [map_mul, map_mul, hu, one_mul, mul_one]
  · rw [map_mul, map_mul, ha, one_mul, mul_one]

theorem archComponent_glArch_adelicArchGLInclAt_self (w₀ : InfinitePlace F) (g : GL (Fin 2) w₀.Completion) :
    archComponent F w₀ (glArch (𝓞 F) F (adelicArchGLInclAt F w₀ g)) = g := by
  show archComponent F w₀ (glArch (𝓞 F) F ((adelicArchGLIncl F) (archGLIncl F w₀ g))) = g
  rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_glArch_adelicArchGLInclAt_of_ne {w w₀ : InfinitePlace F} (hw : w ≠ w₀)
    (g : GL (Fin 2) w₀.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w₀ g)) = 1 := by
  show archComponent F w (glArch (𝓞 F) F ((adelicArchGLIncl F) (archGLIncl F w₀ g))) = 1
  rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne F hw]

theorem glFin_adelicArchGLInclAt (w₀ : InfinitePlace F) (g : GL (Fin 2) w₀.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w₀ g) = 1 :=
  glFin_adelicArchGLIncl F _

def ArchSupported (S : Finset (InfinitePlace F)) (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k = 1 ∧ (∀ w, w ∉ S → archComponent F w (glArch (𝓞 F) F k) = 1) ∧
    ∀ w, w ∈ S → archComponent F w (glArch (𝓞 F) F k) ∈ rowIsometrySubgroup₀ w.Completion

theorem peel (f : AdelicGL2 (𝓞 F) F → ℂ)
    (M : (w : InfinitePlace F) → Submodule ℂ (rowIsometrySubgroup₀ w.Completion → ℂ))
    (E : (w : InfinitePlace F) → Finset (rowIsometrySubgroup₀ w.Completion))
    (hE : ∀ w, ∀ u ∈ M w, (∀ e ∈ E w, u e = 0) → u = 0)
    (hf : ∀ (w : InfinitePlace F) (x : AdelicGL2 (𝓞 F) F),
      (fun k : rowIsometrySubgroup₀ w.Completion => f (x * rowIsometryInclAt₀ F w k)) ∈ M w)
    (S : Finset (InfinitePlace F)) :
    ∀ x₀ : AdelicGL2 (𝓞 F) F,
      (∀ k, ArchSupported F S k →
        (∀ w, w ∈ S → ∃ e ∈ E w, archComponent F w (glArch (𝓞 F) F k) = (e : GL (Fin 2) w.Completion)) →
        f (x₀ * k) = 0) →
      ∀ k, ArchSupported F S k → f (x₀ * k) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro x₀ h k hk
    exact h k hk (fun w hw => absurd hw (Finset.notMem_empty w))
  | insert w₀ S hw₀ ih =>
    intro x₀ h k hk
    obtain ⟨hkf, hkoff, hkon⟩ := hk

    set c : rowIsometrySubgroup₀ w₀.Completion := ⟨archComponent F w₀ (glArch (𝓞 F) F k), hkon w₀ (Finset.mem_insert_self _ _)⟩
      with hc
    set kS : AdelicGL2 (𝓞 F) F := k * (rowIsometryInclAt₀ F w₀ c)⁻¹ with hkS
    have hkS_fin : glFin (𝓞 F) F kS = 1 := by
      rw [hkS, map_mul, map_inv, hkf, rowIsometryInclAt₀_apply, glFin_adelicArchGLInclAt, inv_one, mul_one]
    have hkS_w₀ : archComponent F w₀ (glArch (𝓞 F) F kS) = 1 := by
      rw [hkS, map_mul, map_inv, map_mul, map_inv, rowIsometryInclAt₀_apply, archComponent_glArch_adelicArchGLInclAt_self]
      exact mul_inv_cancel _
    have hkS_of_ne : ∀ w, w ≠ w₀ → archComponent F w (glArch (𝓞 F) F kS) = archComponent F w (glArch (𝓞 F) F k) := by
      intro w hw
      rw [hkS, map_mul, map_inv, map_mul, map_inv, rowIsometryInclAt₀_apply,
        archComponent_glArch_adelicArchGLInclAt_of_ne F hw, inv_one, mul_one]
    have hkS_supp : ArchSupported F S kS := by
      refine ⟨hkS_fin, fun w hw => ?_, fun w hw => ?_⟩
      · by_cases hww : w = w₀
        · subst hww; exact hkS_w₀
        · rw [hkS_of_ne w hww]; exact hkoff w (by simp [hww, hw])
      · have hww : w ≠ w₀ := fun h => hw₀ (h ▸ hw)
        rw [hkS_of_ne w hww]; exact hkon w (Finset.mem_insert_of_mem hw)
    have hk_eq : k = kS * rowIsometryInclAt₀ F w₀ c := by rw [hkS, inv_mul_cancel_right]

    have hcomm : ∀ (a : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F a = 1 → archComponent F w₀ (glArch (𝓞 F) F a) = 1 →
        ∀ e : rowIsometrySubgroup₀ w₀.Completion, a * rowIsometryInclAt₀ F w₀ e = rowIsometryInclAt₀ F w₀ e * a := by
      intro a haf haw e
      rw [rowIsometryInclAt₀_apply]
      exact commute_adelicArchGLInclAt_of_archComponent_eq_one F haf haw _

    have hF : (fun k' : rowIsometrySubgroup₀ w₀.Completion => f (x₀ * kS * rowIsometryInclAt₀ F w₀ k')) = 0 := by
      refine hE w₀ _ (hf w₀ (x₀ * kS)) fun e he => ?_

      have hrew : x₀ * kS * rowIsometryInclAt₀ F w₀ e = x₀ * rowIsometryInclAt₀ F w₀ e * kS := by
        rw [mul_assoc, hcomm kS hkS_fin hkS_w₀ e, ← mul_assoc]
      show f (x₀ * kS * rowIsometryInclAt₀ F w₀ e) = 0
      rw [hrew]
      refine ih (x₀ * rowIsometryInclAt₀ F w₀ e) (fun k' hk' hk'E => ?_) kS hkS_supp

      obtain ⟨hk'f, hk'off, hk'on⟩ := hk'
      have hk'w₀ : archComponent F w₀ (glArch (𝓞 F) F k') = 1 := hk'off w₀ hw₀
      rw [mul_assoc, ← hcomm k' hk'f hk'w₀ e]
      refine h (k' * rowIsometryInclAt₀ F w₀ e) ⟨?_, fun w hw => ?_, fun w hw => ?_⟩ fun w hw => ?_
      · rw [map_mul, hk'f, rowIsometryInclAt₀_apply, glFin_adelicArchGLInclAt, mul_one]
      · have hww : w ≠ w₀ := fun h' => hw (h' ▸ Finset.mem_insert_self _ _)
        rw [map_mul, map_mul, rowIsometryInclAt₀_apply, archComponent_glArch_adelicArchGLInclAt_of_ne F hww, mul_one]
        exact hk'off w fun h' => hw (Finset.mem_insert_of_mem h')
      · rcases Finset.mem_insert.mp hw with rfl | hwS
        · rw [map_mul, map_mul, rowIsometryInclAt₀_apply, archComponent_glArch_adelicArchGLInclAt_self, hk'w₀, one_mul]
          exact e.2
        · have hww : w ≠ w₀ := fun h' => hw₀ (h' ▸ hwS)
          rw [map_mul, map_mul, rowIsometryInclAt₀_apply, archComponent_glArch_adelicArchGLInclAt_of_ne F hww, mul_one]
          exact hk'on w hwS
      · rcases Finset.mem_insert.mp hw with rfl | hwS
        · refine ⟨e, he, ?_⟩
          rw [map_mul, map_mul, rowIsometryInclAt₀_apply, archComponent_glArch_adelicArchGLInclAt_self, hk'w₀, one_mul]
        · have hww : w ≠ w₀ := fun h' => hw₀ (h' ▸ hwS)
          obtain ⟨e', he', heq⟩ := hk'E w hwS
          refine ⟨e', he', ?_⟩
          rw [map_mul, map_mul, rowIsometryInclAt₀_apply, archComponent_glArch_adelicArchGLInclAt_of_ne F hww, mul_one]
          exact heq
    have := congrFun hF c
    simp only [Pi.zero_apply] at this
    rw [hk_eq, ← mul_assoc]
    exact this

end EisFinDim
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace EisFinDim

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

section DetTrick

variable {L : Type*} [NormedField L]

theorem det_val_ne_zero (k : GL (Fin 2) L) : (k : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det k).ne_zero

def diagDetLoc (k : GL (Fin 2) L) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (k : Matrix (Fin 2) (Fin 2) L).det]
    (by rw [Matrix.det_fin_two_of]; simpa using det_val_ne_zero k)

theorem diagDetLoc_inv_val (k : GL (Fin 2) L) :
    (((diagDetLoc k)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, 0; 0, ((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹] := by
  have hd := det_val_ne_zero k
  rw [Matrix.coe_units_inv]
  have hD : ((diagDetLoc k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, 0; 0, (k : Matrix (Fin 2) (Fin 2) L).det] := rfl
  rw [hD, Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hd, Ring.inverse_eq_inv']

theorem diagDetLoc_inv_mul_mem_rowIsometrySubgroup₀ {k : GL (Fin 2) L} (hk : IsRowIsometry k) :
    (diagDetLoc k)⁻¹ * k ∈ rowIsometrySubgroup₀ L := by
  have hdet0 : (k : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det k).ne_zero
  have hnorm : ‖(k : Matrix (Fin 2) (Fin 2) L).det‖ = 1 := hk.1

  have hval : (((diagDetLoc k)⁻¹ * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![(k : Matrix (Fin 2) (Fin 2) L) 0 0, (k : Matrix (Fin 2) (Fin 2) L) 0 1;
         ((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 0,
         ((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 1] := by
    rw [Units.val_mul, diagDetLoc_inv_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [hval, Matrix.det_fin_two_of]
    rw [Matrix.det_fin_two] at hdet0 ⊢
    field_simp
  · rw [hval, Matrix.det_fin_two_of]
    have : (k : Matrix (Fin 2) (Fin 2) L) 0 0 * (((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 1) -
        (k : Matrix (Fin 2) (Fin 2) L) 0 1 * (((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 0) = 1 := by
      rw [Matrix.det_fin_two] at hdet0 ⊢
      field_simp
    rw [this, norm_one]
  · intro x y
    have h := hk.2 x (y * ((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹)
    rw [hval]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [norm_mul, norm_inv, hnorm, inv_one, mul_one] at h
    calc ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 0 + y * (((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 0)‖ ^ 2 +
          ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 1 + y * (((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 1)‖ ^ 2
        = ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 0 + y * ((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 +
          ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 1 + y * ((k : Matrix (Fin 2) (Fin 2) L).det)⁻¹ * (k : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2 := by
          simp only [mul_assoc]
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := h

end DetTrick
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

def diagDet (g : GL (Fin 2) (InfiniteAdeleRing F)) : GL (Fin 2) (InfiniteAdeleRing F) where
  val := !![1, 0; 0, ((Matrix.GeneralLinearGroup.det g : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)]
  inv := !![1, 0; 0, (((Matrix.GeneralLinearGroup.det g)⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add, Units.mul_inv]
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add, Units.inv_mul]

theorem archComponent_diagDet (g : GL (Fin 2) (InfiniteAdeleRing F)) (w : InfinitePlace F) :
    archComponent F w (diagDet F g) = diagDetLoc (archComponent F w g) := by
  apply Units.ext
  ext i j
  rw [archComponent_apply]
  have hdet : ((Matrix.GeneralLinearGroup.det g : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w =
      ((archComponent F w g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [archComponent_apply]
    rfl
  fin_cases i <;> fin_cases j <;> simp [diagDet, diagDetLoc, hdet] <;> rfl

theorem adelicArchGLIncl_diagDet_mem_adelicBorel (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    adelicArchGLIncl F (diagDet F g) ∈ adelicBorel (𝓞 F) F := by
  show ((adelicArchGLIncl F (diagDet F g) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  refine Prod.ext ?_ ?_
  · show (glArch (𝓞 F) F (adelicArchGLIncl F (diagDet F g)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0
    rw [glArch_adelicArchGLIncl]
    rfl
  · show (glFin (𝓞 F) F (adelicArchGLIncl F (diagDet F g)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0
    rw [glFin_adelicArchGLIncl]
    exact Matrix.one_apply_ne (by decide)

theorem exists_finset_cosets_principalLevel (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    ∃ R : Finset (AdelicGL2 (𝓞 F) F),
      (∀ r ∈ R, r ∈ adelicMaximalCompact F ∧ glArch (𝓞 F) F r = 1) ∧
      ∀ c : AdelicGL2 (𝓞 F) F, c ∈ adelicMaximalCompact F → glArch (𝓞 F) F c = 1 →
        ∃ r ∈ R, r⁻¹ * c ∈ principalLevel (𝓞 F) F N := by
  classical
  set C : Set (AdelicGL2 (𝓞 F) F) := {c | c ∈ adelicMaximalCompact F ∧ glArch (𝓞 F) F c = 1} with hC
  have hCc : IsCompact C := by
    refine (isCompact_adelicMaximalCompact F).inter_right ?_
    exact isClosed_singleton.preimage (continuous_glArch (𝓞 F) F)
  let U : AdelicGL2 (𝓞 F) F → Set (AdelicGL2 (𝓞 F) F) := fun c => {x | c⁻¹ * x ∈ principalLevel (𝓞 F) F N}
  have hUo : ∀ c ∈ C, IsOpen (U c) := fun c _ =>
    (AutomorphicForm.isOpen_principalLevel F N hN).preimage (continuous_const_mul _)
  have hcov : C ⊆ ⋃ c ∈ C, U c := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨x, hx, by simp [U, (principalLevel (𝓞 F) F N).one_mem]⟩
  obtain ⟨b, hbC, hbfin, hbcov⟩ := hCc.elim_finite_subcover_image hUo hcov
  refine ⟨hbfin.toFinset, fun r hr => hbC (hbfin.mem_toFinset.mp hr), fun c hcK hca => ?_⟩
  have hx : c ∈ ⋃ i ∈ b, U i := hbcov (show c ∈ C from ⟨hcK, hca⟩)
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨c', hc'b, hc'U⟩ := hx
  exact ⟨c', hbfin.mem_toFinset.mpr hc'b, hc'U⟩

end EisFinDim
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace EisFinDim

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

def rightInvariantSubmodule {G : Type*} [Group G] (U : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {φ | ∀ g : G, ∀ u ∈ U, φ (g * u) = φ g}
  add_mem' := by
    intro a b ha hb g u hu
    simp only [Pi.add_apply, ha g u hu, hb g u hu]
  zero_mem' := by intro g u hu; rfl
  smul_mem' := by
    intro c a ha g u hu
    simp only [Pi.smul_apply, ha g u hu]

theorem eq_zero_of_forall_apply_eq_zero
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (N : Ideal (𝓞 F)) (tys : ArchTypeFamily F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφI : IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    (hφU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, φ (g * u) = φ g)
    (hφT : φ ∈ archCutSubmodule F tys)
    (R : Finset (AdelicGL2 (𝓞 F) F))
    (hR1 : ∀ r ∈ R, r ∈ adelicMaximalCompact F ∧ glArch (𝓞 F) F r = 1)
    (hR2 : ∀ c : AdelicGL2 (𝓞 F) F, c ∈ adelicMaximalCompact F → glArch (𝓞 F) F c = 1 →
        ∃ r ∈ R, r⁻¹ * c ∈ principalLevel (𝓞 F) F N)
    (E : (w : InfinitePlace F) → Finset (rowIsometrySubgroup₀ w.Completion))
    (hE : ∀ w, ∀ u ∈ (⨆ i : Fin (tys.card w), matrixCoeffSubmodule (tys.rep w i).ρ), (∀ e ∈ E w, u e = 0) → u = 0)
    (hz : ∀ r ∈ R, ∀ k, ArchSupported F Finset.univ k →
        (∀ w, ∃ e ∈ E w, archComponent F w (glArch (𝓞 F) F k) = (e : GL (Fin 2) w.Completion)) → φ (r * k) = 0) :
    φ = 0 := by
  classical

  have hfM : ∀ (w : InfinitePlace F) (x : AdelicGL2 (𝓞 F) F),
      (fun k : rowIsometrySubgroup₀ w.Completion => φ (x * rowIsometryInclAt₀ F w k)) ∈
        ⨆ i : Fin (tys.card w), matrixCoeffSubmodule (tys.rep w i).ρ := by
    intro w x
    have h := (mem_archCutSubmodule_iff F tys φ).mp hφT w
    exact comp_mul_mem_iSup_matrixCoeffSubmodule (fun i => (tys.rep w i).ρ) h x

  have stepA : ∀ r ∈ R, ∀ k, ArchSupported F Finset.univ k → φ (r * k) = 0 := fun r hr =>
    peel F φ (fun w => ⨆ i : Fin (tys.card w), matrixCoeffSubmodule (tys.rep w i).ρ) E hE hfM Finset.univ r
      (fun k hk hkE => hz r hr k hk fun w => hkE w (Finset.mem_univ w))

  have stepB : ∀ κ : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F κ ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F κ))) → φ κ = 0 := by
    intro κ hκf hκa
    set a : AdelicGL2 (𝓞 F) F := adelicArchGLIncl F (glArch (𝓞 F) F κ) with ha
    set c : AdelicGL2 (𝓞 F) F := κ * a⁻¹ with hc
    have haA : glArch (𝓞 F) F a = glArch (𝓞 F) F κ := by rw [ha, glArch_adelicArchGLIncl]
    have haf : glFin (𝓞 F) F a = 1 := by rw [ha, glFin_adelicArchGLIncl]
    have hca : glArch (𝓞 F) F c = 1 := by rw [hc, map_mul, map_inv, haA, mul_inv_cancel]
    have hcf : glFin (𝓞 F) F c = glFin (𝓞 F) F κ := by rw [hc, map_mul, map_inv, haf, inv_one, mul_one]
    have hcK : c ∈ adelicMaximalCompact F := by
      rw [mem_adelicMaximalCompact_iff]
      refine ⟨by rw [hcf]; exact hκf, fun w => ?_⟩
      rw [hca, map_one]; exact isRowIsometry_one
    obtain ⟨r, hr, hu⟩ := hR2 c hcK hca
    have huA : glArch (𝓞 F) F (r⁻¹ * c) = 1 := by rw [map_mul, map_inv, (hR1 r hr).2, hca, inv_one, one_mul]
    have huU : r⁻¹ * c ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
      Subgroup.mem_inf.mpr ⟨hu, (mem_finiteAdelicGL2Subgroup_iff F _).mpr huA⟩
    have hκ : κ = r * a * (r⁻¹ * c) := by
      have h1 : κ = c * a := by rw [hc, inv_mul_cancel_right]
      have h2 : (r⁻¹ * c) * a = a * (r⁻¹ * c) := (commute_of_glArch_eq_one_of_glFin_eq_one F huA haf).eq
      calc κ = c * a := h1
        _ = r * ((r⁻¹ * c) * a) := by group
        _ = r * (a * (r⁻¹ * c)) := by rw [h2]
        _ = r * a * (r⁻¹ * c) := by rw [mul_assoc]
    rw [hκ, hφU (r * a) _ huU]

    set δ : AdelicGL2 (𝓞 F) F := adelicArchGLIncl F (diagDet F (glArch (𝓞 F) F κ)) with hδ
    have ha1 : ArchSupported F Finset.univ (δ⁻¹ * a) := by
      refine ⟨?_, fun w hw => absurd (Finset.mem_univ w) hw, fun w _ => ?_⟩
      · rw [map_mul, map_inv, hδ, glFin_adelicArchGLIncl, haf, inv_one, one_mul]
      · rw [map_mul, map_inv, map_mul, map_inv, hδ, ha, glArch_adelicArchGLIncl, glArch_adelicArchGLIncl,
          archComponent_diagDet]
        exact diagDetLoc_inv_mul_mem_rowIsometrySubgroup₀ (hκa w)
    have hrδ : r * δ = δ * r :=
      (commute_of_glArch_eq_one_of_glFin_eq_one F (hR1 r hr).2 (by rw [hδ, glFin_adelicArchGLIncl])).eq
    have hra : r * a = δ * (r * (δ⁻¹ * a)) := by
      rw [← mul_assoc, ← mul_assoc, ← hrδ, mul_assoc r δ, mul_inv_cancel, mul_one]
    rw [hra, hφI δ (adelicArchGLIncl_diagDet_mem_adelicBorel F _) (r * (δ⁻¹ * a)), stepA r hr _ ha1, mul_zero]

  exact AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact F χ₁ χ₂ φ 0 hφI (isInducedSection_zero χ₁ χ₂)
    fun k hk1 hk2 => stepB k hk1 hk2

end EisFinDim
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace Ws31
namespace VDimB

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open EisFinDim

theorem exists_finset_forall_eq_zero (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∀ (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ),
      IsInducedSection (𝓞 K) K χ₁ χ₂ φ →
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
      φ ∈ archCutSubmodule K tysK →
      (∀ t ∈ T, φ t = 0) → φ = 0 := by
  classical
  have hE : ∀ w : InfinitePlace K, ∃ E : Finset (rowIsometrySubgroup₀ w.Completion),
      ∀ u ∈ (⨆ i : Fin (tysK.card w), matrixCoeffSubmodule (tysK.rep w i).ρ), (∀ e ∈ E, u e = 0) → u = 0 := fun w =>
    exists_finset_forall_eq_zero_of_forall_apply_eq_zero _
  choose E hE using hE
  obtain ⟨R, hR1, hR2⟩ := exists_finset_cosets_principalLevel K N hN
  let Tt : Type := {k : AdelicGL2 (𝓞 K) K // ArchSupported K Finset.univ k ∧
      ∀ w, ∃ e ∈ E w, archComponent K w (glArch (𝓞 K) K k) = (e : GL (Fin 2) w.Completion)}
  have hTcomp : ∀ (t : Tt) (w : InfinitePlace K),
      (⟨archComponent K w (glArch (𝓞 K) K t.1), t.2.1.2.2 w (Finset.mem_univ w)⟩ : rowIsometrySubgroup₀ w.Completion) ∈ E w := by
    intro t w
    obtain ⟨e, he, heq⟩ := t.2.2 w
    have : (⟨archComponent K w (glArch (𝓞 K) K t.1), t.2.1.2.2 w (Finset.mem_univ w)⟩ : rowIsometrySubgroup₀ w.Completion) = e :=
      Subtype.ext heq
    rw [this]; exact he
  haveI : Finite Tt := by
    refine Finite.of_injective (fun t : Tt => fun w : InfinitePlace K =>
      (⟨⟨archComponent K w (glArch (𝓞 K) K t.1), t.2.1.2.2 w (Finset.mem_univ w)⟩, hTcomp t w⟩ : ↥(E w))) ?_
    intro t t' htt
    apply Subtype.ext
    refine eq_of_glArch_eq_of_glFin_eq' K ?_ ?_
    · refine eq_of_forall_archComponent_eq K fun w => ?_
      have := congrFun htt w
      simp only [Subtype.mk.injEq] at this
      exact this
    · rw [t.2.1.1, t'.2.1.1]
  haveI : Fintype Tt := Fintype.ofFinite Tt
  refine ⟨(Finset.univ : Finset (↥R × Tt)).image fun p => (p.1 : AdelicGL2 (𝓞 K) K) * (p.2 : AdelicGL2 (𝓞 K) K), ?_⟩
  intro χ₁ χ₂ φ hφI hφU hφT hz
  refine eq_zero_of_forall_apply_eq_zero K χ₁ χ₂ N tysK φ hφI hφU hφT R hR1 hR2 E hE ?_
  intro r hr k hk hkE
  exact hz _ (Finset.mem_image.mpr ⟨(⟨r, hr⟩, ⟨k, hk, hkE⟩), Finset.mem_univ _, rfl⟩)

theorem card_le_of_linearIndependent_restrict (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hT : ∀ (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ),
      IsInducedSection (𝓞 K) K χ₁ χ₂ φ →
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
      φ ∈ archCutSubmodule K tysK →
      (∀ t ∈ T, φ t = 0) → φ = 0)
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {m : ℕ} (φ : Fin m → AdelicGL2 (𝓞 K) K → ℂ)
    (hφI : ∀ j, IsInducedSection (𝓞 K) K χ₁ χ₂ (φ j))
    (hφU : ∀ j (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ j (g * u) = φ j g)
    (hφT : ∀ j, φ j ∈ archCutSubmodule K tysK)
    (hli : LinearIndependent ℂ (fun j => fun k : adelicMaximalCompact K => φ j (k : AdelicGL2 (𝓞 K) K))) :
    m ≤ T.card := by
  classical
  let L : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (↥T → ℂ) := LinearMap.pi fun t : ↥T => LinearMap.proj (t : AdelicGL2 (𝓞 K) K)
  have hL : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (t : ↥T), L f t = f (t : AdelicGL2 (𝓞 K) K) := fun _ _ => rfl
  have hliL : LinearIndependent ℂ (fun j : Fin m => L (φ j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set ψ : AdelicGL2 (𝓞 K) K → ℂ := ∑ j, c j • φ j with hψ
    have hψI : IsInducedSection (𝓞 K) K χ₁ χ₂ ψ := by
      have : ψ ∈ inducedSectionSubmodule χ₁ χ₂ := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφI j)
      exact this
    have hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ (g * u) = ψ g := by
      have : ψ ∈ rightInvariantSubmodule (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφU j)
      exact this
    have hψT : ψ ∈ archCutSubmodule K tysK := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφT j)
    have hψz : ∀ t ∈ T, ψ t = 0 := by
      intro t ht
      have h := congrFun hc ⟨t, ht⟩
      simp only [Finset.sum_apply, Pi.smul_apply, hL, Pi.zero_apply, smul_eq_mul] at h
      rw [hψ]
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    have hψ0 : ψ = 0 := hT χ₁ χ₂ ψ hψI hψU hψT hψz
    have hres : ∑ j, c j • (fun k : adelicMaximalCompact K => φ j (k : AdelicGL2 (𝓞 K) K)) = 0 := by
      funext k
      have := congrFun hψ0 (k : AdelicGL2 (𝓞 K) K)
      rw [hψ] at this
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    exact (Fintype.linearIndependent_iff.mp hli) c hres
  have hcard := hliL.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_coe] at hcard
  exact hcard

theorem exists_bound_forall_linearIndependent_restrict (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∃ T : ℕ, ∀ (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (m : ℕ) (φ : Fin m → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ j, IsInducedSection (𝓞 K) K χ₁ χ₂ (φ j)) → (∀ j, Continuous (φ j)) → (∀ j, IsArchKFinite K (φ j)) →
      (∀ j (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ j (g * u) = φ j g) →
      (∀ j, φ j ∈ archCutSubmodule K tysK) →
      LinearIndependent ℂ (fun j => fun k : adelicMaximalCompact K => φ j (k : AdelicGL2 (𝓞 K) K)) → m ≤ T := by
  obtain ⟨T, hT⟩ := exists_finset_forall_eq_zero K N hN tysK
  exact ⟨T.card, fun χ₁ χ₂ m φ hφI _ _ hφU hφT hli =>
    card_le_of_linearIndependent_restrict K N tysK T hT χ₁ χ₂ φ hφI hφU hφT hli⟩

end Ws31.VDimB
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace Ws31
namespace C0Asm

open IsDedekindDomain NumberField

theorem infinite_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Infinite (HeightOneSpectrum (𝓞 K)) := by
  classical
  have key : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K),
      Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal = Ideal.span {((p : ℕ) : ℤ)} := by
    intro p
    have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
      (⊥ : Ideal (𝓞 K)) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
    refine ⟨⟨Q, hQ, ?_⟩, hQc⟩
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hQc
    exact hp0 (Ideal.span_singleton_eq_bot.mp hQc.symm)
  choose f hf using key
  haveI : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOf_prime
  refine Infinite.of_injective f fun p q h => ?_
  have h1 : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, h]
  have h2 := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h1)
  exact Subtype.ext (by simpa using h2)

theorem ne_bot_of_forall_dvd_mem_finset (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK) : N ≠ ⊥ := by
  intro h
  subst h
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ SK := fun v => hN v (dvd_zero _)
  haveI := infinite_heightOneSpectrum K
  have hfin : Finite (HeightOneSpectrum (𝓞 K)) :=
    Finite.of_injective (fun v => (⟨v, hall v⟩ : SK)) (fun a b h => by simpa using h)
  exact not_finite (HeightOneSpectrum (𝓞 K))

end Ws31.C0Asm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace Ws31
namespace SectionExt

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K]

theorem norm_diag_eq_one_of_isRowIsometry {L : Type*} [NormedField L] (k : GL (Fin 2) L)
    (hk : AutomorphicForm.WindowedSiegel.IsRowIsometry k) (h10 : (k : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ‖(k : Matrix (Fin 2) (Fin 2) L) 0 0‖ = 1 ∧ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
  obtain ⟨hdet, hrow⟩ := hk
  have h11 : ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
    have := hrow 0 1
    rw [h10] at this
    simp only [zero_mul, one_mul, zero_add, mul_zero, norm_zero, norm_one] at this
    have h0 : 0 ≤ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ := norm_nonneg _
    nlinarith
  refine ⟨?_, h11⟩
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, h11, mul_one] at hdet
  exact hdet

theorem norm_eq_one_of_mul_eq_one (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K)
    (hxy : x * y = 1) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) : ‖x‖ = 1 := by
  apply le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hx)
  apply Valued.toNormedField.one_le_norm_iff.mpr
  have h := congrArg Valued.v hxy
  rw [map_mul, map_one] at h
  by_contra hlt
  push_neg at hlt
  have : Valued.v x * Valued.v y < 1 := mul_lt_one_of_lt_of_le hlt hy
  rw [h] at this
  exact lt_irrefl _ this

theorem distribHaarChar_borelDiag_eq_one (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K)
    (hβK : β ∈ adelicMaximalCompact K) :
    ((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagFst ⟨β, hβ⟩) : ℝ≥0) : ℝ) = 1 ∧
    ((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagSnd ⟨β, hβ⟩) : ℝ≥0) : ℝ) = 1 := by
  have h10 : (β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hβ

  have harch : ∀ w : InfinitePlace K,
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w‖ = 1 ∧
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w‖ = 1 := by
    intro w
    have hk := hβK.2 w
    have h := norm_diag_eq_one_of_isRowIsometry (archComponent K w (glArch (𝓞 K) K β)) hk (by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 w = 0
      rw [NumberField.AdelicLevel.glArch_apply, h10]; rfl)
    have e0 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w := by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 w = _
      rw [NumberField.AdelicLevel.glArch_apply]
    have e1 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w := by
      show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 w = _
      rw [NumberField.AdelicLevel.glArch_apply]
    rw [e0, e1] at h
    exact h

  have hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Fin 2),
      ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v‖ = 1 := by
    intro v i
    have hle := AutomorphicForm.valued_finComponent_apply_le_one hβK v i i

    have ex : ((finComponent (𝓞 K) K v (glFin (𝓞 K) K β) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
      rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
    have ey : (((finComponent (𝓞 K) K v (glFin (𝓞 K) K β))⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
      rw [← map_inv, ← map_inv, NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
    rw [ex] at hle; rw [ey] at hle

    have hprod : ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i) *
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i) = 1 := by
      fin_cases i
      · exact congrArg Units.val (mul_inv_cancel (borelDiagFst (⟨β, hβ⟩ : ↥(adelicBorel (𝓞 K) K))))
      · exact congrArg Units.val (mul_inv_cancel (borelDiagSnd (⟨β, hβ⟩ : ↥(adelicBorel (𝓞 K) K))))
    have hprodv : ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v *
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v = 1 := by
      have := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) hprod
      first
        | simpa using this
        | (have h' := this; simp at h' ⊢; exact h')
        | (have h' := this; simp at h'; exact h')
        | exact this
        | (simpa [Function.comp_def] using this)
    exact norm_eq_one_of_mul_eq_one v _ _ hprodv hle.1 hle.2
  constructor
  · rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    show (∏ w : InfinitePlace K, ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0).2 v‖ = 1
    rw [Finset.prod_eq_one fun w _ => by rw [(harch w).1, one_pow], finprod_eq_one_of_forall_eq_one fun v => hfin v 0, one_mul]
  · rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    show (∏ w : InfinitePlace K, ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v‖ = 1
    rw [Finset.prod_eq_one fun w _ => by rw [(harch w).2, one_pow], finprod_eq_one_of_forall_eq_one fun v => hfin v 1, one_mul]

end Ws31.SectionExt
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace Ws31
namespace SectionExt

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def bchar (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) : ℂ :=
  ((χ₁ (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ) * ((χ₂ (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ)

theorem bchar_mul (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (b b' : AdelicGL2 (𝓞 K) K)
    (hb : b ∈ adelicBorel (𝓞 K) K) (hb' : b' ∈ adelicBorel (𝓞 K) K) :
    bchar K χ₁ χ₂ (b * b') (mul_mem hb hb') = bchar K χ₁ χ₂ b hb * bchar K χ₁ χ₂ b' hb' := by
  unfold bchar
  have h1 : (⟨b * b', mul_mem hb hb'⟩ : ↥(adelicBorel (𝓞 K) K)) = ⟨b, hb⟩ * ⟨b', hb'⟩ := rfl
  rw [h1, map_mul, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul]; ring

theorem bchar_one (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : bchar K χ₁ χ₂ 1 (one_mem _) = 1 := by
  unfold bchar
  have h1 : (⟨1, one_mem _⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := rfl
  rw [h1, map_one, map_one, map_one, map_one, Units.val_one, mul_one]

theorem isInducedSection_iff (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (f : AdelicGL2 (𝓞 K) K → ℂ) :
    IsInducedSection (𝓞 K) K χ₁ χ₂ f ↔ ∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      f (b * g) = bchar K χ₁ χ₂ b hb * f g := Iff.rfl

noncomputable def classHom (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) →* ℂ where
  toFun β := bchar K μ ν (β : AdelicGL2 (𝓞 K) K) (Subgroup.mem_inf.mp β.2).1
  map_one' := bchar_one K μ ν
  map_mul' β β' := bchar_mul K μ ν _ _ _ _

theorem classHom_apply (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (β : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K)) :
    classHom K μ ν β = bchar K μ ν (β : AdelicGL2 (𝓞 K) K) (Subgroup.mem_inf.mp β.2).1 := rfl

end Ws31.SectionExt
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

namespace Ws31
namespace VDimGeneric

theorem eq_zero_of_sum_character_mul_eq_zero {H X : Type*} [Monoid H] {n : ℕ}
    (χ : Fin n → (H →* ℂ)) (hχ : Function.Injective χ) (g : Fin n → X → ℂ)
    (h : ∀ (t : H) (x : X), ∑ j, χ j t * g j x = 0) : ∀ j, g j = 0 := by
  classical
  have hli : LinearIndependent ℂ (fun j : Fin n => ((χ j : H →* ℂ) : H → ℂ)) :=
    (linearIndependent_monoidHom H ℂ).comp χ hχ
  intro j
  funext x
  have key := (Fintype.linearIndependent_iff.mp hli) (fun i => g i x) ?_ j
  · simpa using key
  · funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h t x]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem exists_linearIndependent_subfamily_span {A V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : A → V) (d : ℕ)
    (hd : ∀ (m : ℕ) (e : Fin m → A), LinearIndependent ℂ (fun j => R (e j)) → m ≤ d) :
    ∃ (n : ℕ) (e : Fin n → A), LinearIndependent ℂ (fun j => R (e j)) ∧
      ∀ a : A, R a ∈ Submodule.span ℂ (Set.range fun j => R (e j)) := by
  classical
  let P : ℕ → Prop := fun m => ∃ e : Fin m → A, LinearIndependent ℂ (fun j => R (e j))
  have hP0 : P 0 := ⟨Fin.elim0, linearIndependent_empty_type⟩
  set n₀ := Nat.findGreatest P d with hn₀
  have hPn : P n₀ := Nat.findGreatest_spec (P := P) (Nat.zero_le d) hP0
  obtain ⟨e, he⟩ := hPn
  refine ⟨n₀, e, he, fun a => ?_⟩
  by_contra ha

  have hcons : LinearIndependent ℂ (fun j => R ((Fin.cons a e : Fin (n₀ + 1) → A) j)) := by
    have : (fun j => R ((Fin.cons a e : Fin (n₀ + 1) → A) j)) = Fin.cons (R a) (fun j => R (e j)) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp
      · simp
    rw [this, linearIndependent_fin_cons]
    exact ⟨he, ha⟩
  have hle : n₀ + 1 ≤ d := hd (n₀ + 1) (Fin.cons a e : Fin (n₀ + 1) → A) hcons
  have hnot : ¬ P (n₀ + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle
  exact hnot ⟨(Fin.cons a e : Fin (n₀ + 1) → A), hcons⟩

theorem eq_zero_of_integral_norm_sq_sum_eq_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasure μ]
    {n : ℕ} (b : Fin n → X → ℂ) (hb : ∀ j, Continuous (b j)) (hli : LinearIndependent ℂ b)
    (a : Fin n → ℂ) (h : (∫ x, ‖∑ j, a j * b j x‖ ^ 2 ∂μ) = 0) : a = 0 := by
  classical
  set F : X → ℂ := fun x => ∑ j, a j * b j x with hF
  have hFc : Continuous F := by
    rw [hF]; exact continuous_finsetSum _ fun j _ => (continuous_const.mul (hb j))
  have hGc : Continuous fun x => ‖F x‖ ^ 2 := (hFc.norm).pow 2
  have hGi : Integrable (fun x => ‖F x‖ ^ 2) μ := by
    have := hGc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ (μ := μ)
    simpa using this
  have hG0 : (fun x => ‖F x‖ ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hGi).mp (by simpa [hF] using h)
  have hG0' : (fun x => ‖F x‖ ^ 2) = (fun _ => (0 : ℝ)) :=
    (Continuous.ae_eq_iff_eq μ hGc continuous_const).mp hG0
  have hF0 : F = 0 := by
    funext x
    have := congrFun hG0' x
    try simp only [] at this
    have : ‖F x‖ = 0 := by
      have h2 : ‖F x‖ ^ 2 = 0 := this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    simpa using this

  have hsum : ∑ j, a j • b j = 0 := by
    funext x
    have := congrFun hF0 x
    simp only [hF, Pi.zero_apply] at this
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  funext j
  exact (Fintype.linearIndependent_iff.mp hli) a hsum j

theorem integrable_mul_conj_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => f x * conj (g x)) μ := by
  have hc : Continuous fun x => f x * conj (g x) := hf.mul (Complex.continuous_conj.comp hg)
  have := hc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ (μ := μ)
  simpa using this

end Ws31.VDimGeneric
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim"

noncomputable section

namespace Ws31
namespace VDimB

variable {K : Type} [Field K] [NumberField K]

def archPart (z : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((z : AdeleRing (𝓞 K) K).1, 1)
  inv := (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1, 1)
  val_inv := Prod.ext (by
    show (z : AdeleRing (𝓞 K) K).1 * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1
    exact congrArg Prod.fst z.mul_inv) (mul_one 1)
  inv_val := Prod.ext (by
    show ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * (z : AdeleRing (𝓞 K) K).1 = 1
    exact congrArg Prod.fst z.inv_mul) (mul_one 1)

def finPart (z : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (z : AdeleRing (𝓞 K) K).2)
  inv := (1, ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2)
  val_inv := Prod.ext (mul_one 1) (by
    show (z : AdeleRing (𝓞 K) K).2 * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1
    exact congrArg Prod.snd z.mul_inv)
  inv_val := Prod.ext (mul_one 1) (by
    show ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * (z : AdeleRing (𝓞 K) K).2 = 1
    exact congrArg Prod.snd z.inv_mul)

@[scoped simp] theorem archPart_fst (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((archPart z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = (z : AdeleRing (𝓞 K) K).1 := rfl
@[scoped simp] theorem archPart_snd (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((archPart z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl
@[scoped simp] theorem finPart_fst (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((finPart z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl
@[scoped simp] theorem finPart_snd (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((finPart z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = (z : AdeleRing (𝓞 K) K).2 := rfl
@[scoped simp] theorem archPart_inv_fst (z : (AdeleRing (𝓞 K) K)ˣ) :
    (((archPart z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 := rfl
@[scoped simp] theorem finPart_inv_snd (z : (AdeleRing (𝓞 K) K)ˣ) :
    (((finPart z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := rfl

theorem archPart_mul_finPart (z : (AdeleRing (𝓞 K) K)ˣ) : archPart z * finPart z = z :=
  Units.ext (Prod.ext (mul_one _) (one_mul _))

abbrev archUnitAt (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ) : (w.Completion)ˣ :=
  NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w z

abbrev finUnitAt (v : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ) : (v.adicCompletion K)ˣ :=
  NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z

@[scoped simp] theorem archUnitAt_val (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (archUnitAt w z : w.Completion) = (z : AdeleRing (𝓞 K) K).1 w := rfl
@[scoped simp] theorem finUnitAt_val (v : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (finUnitAt v z : v.adicCompletion K) = (z : AdeleRing (𝓞 K) K).2 v := rfl
theorem archUnitAt_inv_val (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (((archUnitAt w z)⁻¹ : (w.Completion)ˣ) : w.Completion) = ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w := by
  rw [← map_inv]; rfl
theorem finUnitAt_inv_val (v : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (((finUnitAt v z)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v := by
  rw [← map_inv]; rfl

theorem finPart_eq_map_finIncl_finitePartUnits (z : (AdeleRing (𝓞 K) K)ˣ) :
    finPart z = Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)
      (NumberField.AdeleRing.finitePartUnits (𝓞 K) K z) := Units.ext rfl

theorem finitePartUnits_finPart (z : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.AdeleRing.finitePartUnits (𝓞 K) K (finPart z) = NumberField.AdeleRing.finitePartUnits (𝓞 K) K z :=
  Units.ext rfl

theorem archUnitAt_archPart (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    archUnitAt w (archPart z) = archUnitAt w z := Units.ext rfl
theorem finUnitAt_finPart (v : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ) :
    finUnitAt v (finPart z) = finUnitAt v z := Units.ext rfl

end Ws31.VDimB
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"

noncomputable section

namespace Ws31
namespace VDimB

open NumberField AutomorphicForm

variable {K : Type} [Field K] [NumberField K]

theorem norm_diag_eq_one_of_isRowIsometry_arch {L : Type*} [NormedField L] (k : GL (Fin 2) L)
    (hk : AutomorphicForm.WindowedSiegel.IsRowIsometry k) (h10 : (k : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ‖(k : Matrix (Fin 2) (Fin 2) L) 0 0‖ = 1 ∧ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
  obtain ⟨hdet, hrow⟩ := hk
  have h11 : ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
    have := hrow 0 1
    rw [h10] at this
    simp only [zero_mul, one_mul, zero_add, mul_zero, norm_zero, norm_one] at this
    have h0 : 0 ≤ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ := norm_nonneg _
    nlinarith
  refine ⟨?_, h11⟩
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, h11, mul_one] at hdet
  exact hdet

theorem archPart_eq_prod (z : (AdeleRing (𝓞 K) K)ˣ) :
    archPart z = ∏ w : InfinitePlace K, NumberField.TateGlobal.archUnitHom w (archUnitAt w z) := by
  classical
  apply Units.ext
  rw [Units.coe_prod]
  have hfst : (∏ w : InfinitePlace K,
      ((NumberField.TateGlobal.archUnitHom w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1
      = ∏ w : InfinitePlace K,
        (((NumberField.TateGlobal.archUnitHom w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 :=
    map_prod (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) _ _
  have hsnd : (∏ w : InfinitePlace K,
      ((NumberField.TateGlobal.archUnitHom w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2
      = ∏ w : InfinitePlace K,
        (((NumberField.TateGlobal.archUnitHom w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 :=
    map_prod (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) _ _
  refine Prod.ext ?_ ?_
  · refine Eq.trans ?_ hfst.symm
    funext w'
    have hev : (∏ w : InfinitePlace K,
        (((NumberField.TateGlobal.archUnitHom w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1) w'
        = ∏ w : InfinitePlace K,
          (((NumberField.TateGlobal.archUnitHom w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w' :=
      map_prod (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completion) w') _ _
    refine Eq.trans ?_ hev.symm
    rw [Finset.prod_eq_single_of_mem w' (Finset.mem_univ w') (fun w _ hw => ?_)]
    · show (z : AdeleRing (𝓞 K) K).1 w' =
        ((NumberField.AdelicVolume.archCentralUnit K w' (archUnitAt w' z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w'
      rw [NumberField.AdelicVolume.archCentralUnit_fst_self]; rfl
    · show ((NumberField.AdelicVolume.archCentralUnit K w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = 1
      exact NumberField.AdelicVolume.archCentralUnit_fst_of_ne w (archUnitAt w z) (Ne.symm hw)
  · refine Eq.trans ?_ hsnd.symm
    show (1 : FiniteAdeleRing (𝓞 K) K) = ∏ w : InfinitePlace K,
      ((NumberField.AdelicVolume.archCentralUnit K w (archUnitAt w z) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
    rw [Finset.prod_eq_one fun w _ => NumberField.AdelicVolume.archCentralUnit_snd w (archUnitAt w z)]

theorem apply_archPart_eq_prod (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((χ (archPart z) : ℂˣ) : ℂ) =
      ∏ w : InfinitePlace K, ((NumberField.TateGlobal.archLocalChar χ w (archUnitAt w z) : ℂˣ) : ℂ) := by
  rw [archPart_eq_prod, map_prod, Units.coe_prod]
  rfl

theorem norm_extensionEmbedding_archUnitAt_borelDiag_eq_one
    (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K) (hβK : β ∈ adelicMaximalCompact K) (w : InfinitePlace K) :
    ‖InfinitePlace.Completion.extensionEmbedding w (archUnitAt w (borelDiagFst ⟨β, hβ⟩) : w.Completion)‖ = 1 ∧
    ‖InfinitePlace.Completion.extensionEmbedding w (archUnitAt w (borelDiagSnd ⟨β, hβ⟩) : w.Completion)‖ = 1 := by
  have h10 : (β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hβ
  have hk := hβK.2 w
  have h := norm_diag_eq_one_of_isRowIsometry_arch (archComponent K w (glArch (𝓞 K) K β)) hk (by
    show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 w = 0
    rw [NumberField.AdelicLevel.glArch_apply, h10]; rfl)
  have e0 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 =
      (archUnitAt w (borelDiagFst ⟨β, hβ⟩) : w.Completion) := by
    show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 w = _
    rw [NumberField.AdelicLevel.glArch_apply]; rfl
  have e1 : ((archComponent K w (glArch (𝓞 K) K β) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 =
      (archUnitAt w (borelDiagSnd ⟨β, hβ⟩) : w.Completion) := by
    show ((glArch (𝓞 K) K β : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 w = _
    rw [NumberField.AdelicLevel.glArch_apply]; rfl
  rw [e0, e1] at h
  have iso : ∀ x : w.Completion, ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ := fun x =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  exact ⟨by rw [iso]; exact h.1, by rw [iso]; exact h.2⟩

end Ws31.VDimB
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"

open AutomorphicForm in
theorem Ws31.VDimB.archWeightsFinite
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ M₀ : ℕ, ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK),
      (∃ k : adelicMaximalCompact K, ψf 0 (k : AdelicGL2 (𝓞 K) K) ≠ 0) →
      ∃ (mμ mν : InfinitePlace K → ℤ),
        (∀ v : InfinitePlace K, |mμ v| ≤ (M₀ : ℤ) ∧ |mν v| ≤ (M₀ : ℤ)) ∧
        (∀ v : InfinitePlace K, v.IsReal → (mμ v = 0 ∨ mμ v = 1) ∧ (mν v = 0 ∨ mν v = 1)) ∧
        (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
          ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
            (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v)) ∧
        (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
          ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
            (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v)) := by
  intro αm
  obtain ⟨M₀, hM₀⟩ :=
    AutomorphicForm.exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule K ξK hξc hξt N tysK w hξw
  refine ⟨M₀, ?_⟩
  intro hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν ψf _hψf _hψfK _hψff _hψfjc _hψfhol _hψfKu _hψfflat _hψflev _hψfty hne
  obtain ⟨τμ, mμ, -, hmμ, hrμ⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K μ _hμ _hμc
  obtain ⟨τν, mν, -, hmν, hrν⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K ν _hν _hνc
  have hne0 : ψf 0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hne
    intro h; exact hk (by rw [h]; rfl)
  have hcont : Continuous (ψf 0) := _hψfjc.comp (continuous_const.prodMk continuous_id)
  have hKu0 : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K,
        (fun k : ↥(archRowIsometrySubgroup K w) => ψf 0 (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := fun w' => by
    obtain ⟨W, hW, h⟩ := _hψfKu w'
    exact ⟨W, hW, fun g => h 0 g⟩
  have hb := hM₀ hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν (ψf 0) (_hψf 0) (_hψfK 0) (_hψff 0) hcont hKu0
    (_hψflev 0) (_hψfty 0) hne0 mμ mν hmμ hmν (fun v hv => ⟨hrμ v hv, hrν v hv⟩)
  exact ⟨mμ, mν, hb, fun v hv => ⟨hrμ v hv, hrν v hv⟩, hmμ, hmν⟩

open AutomorphicForm Ws31.VDimB in

theorem Ws31.VDimB.archClassFinite
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ Carch : Finset (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ), ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK),
      (∃ k : adelicMaximalCompact K, ψf 0 (k : AdelicGL2 (𝓞 K) K) ≠ 0) →
      (fun β : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) =>
        ((μ (archPart (borelDiagFst ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩)) : ℂˣ) : ℂ) *
        ((ν (archPart (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩)) : ℂˣ) : ℂ)) ∈ Carch := by
  intro αm
  classical
  obtain ⟨M₀, hM⟩ := Ws31.VDimB.archWeightsFinite K SK ξK hξc hξt N hN tysK w hξw

  let Box : Type := InfinitePlace K → ↥(Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ))
  let e : ∀ w' : InfinitePlace K, (w'.Completion)ˣ → ℂ := fun w' x =>
    InfinitePlace.Completion.extensionEmbedding w' (x : w'.Completion)
  let F : Box × Box → (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ) := fun p β =>
    (∏ w' : InfinitePlace K,
        e w' (archUnitAt w' (borelDiagFst ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩)) ^ ((p.1 w' : ℤ))) *
    (∏ w' : InfinitePlace K,
        e w' (archUnitAt w' (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩)) ^ ((p.2 w' : ℤ)))
  refine ⟨(Finset.univ : Finset (Box × Box)).image F, ?_⟩
  intro hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν ψf _hψf _hψfK _hψff _hψfjc _hψfhol _hψfKu _hψfflat _hψflev _hψfty hne
  obtain ⟨mμ, mν, hbd, -, hpinμ, hpinν⟩ := hM hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν ψf _hψf _hψfK _hψff _hψfjc
    _hψfhol _hψfKu _hψfflat _hψflev _hψfty hne
  have hmemμ : ∀ w', mμ w' ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ) := fun w' =>
    Finset.mem_Icc.mpr (abs_le.mp (hbd w').1)
  have hmemν : ∀ w', mν w' ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ) := fun w' =>
    Finset.mem_Icc.mpr (abs_le.mp (hbd w').2)
  let p : Box × Box := (fun w' => ⟨mμ w', hmemμ w'⟩, fun w' => ⟨mν w', hmemν w'⟩)
  refine Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩
  funext β
  have hn := Ws31.VDimB.norm_extensionEmbedding_archUnitAt_borelDiag_eq_one (β : AdelicGL2 (𝓞 K) K)
    (Subgroup.mem_inf.mp β.2).1 (Subgroup.mem_inf.mp β.2).2
  show F p β = _
  simp only [F, p, e]
  rw [Ws31.VDimB.apply_archPart_eq_prod μ, Ws31.VDimB.apply_archPart_eq_prod ν]
  congr 1
  · exact Finset.prod_congr rfl fun w' _ => (hpinμ w' _ (hn w').1).symm
  · exact Finset.prod_congr rfl fun w' _ => (hpinν w' _ (hn w').2).symm

noncomputable section

namespace Ws31
namespace VDimB

variable {K : Type} [Field K] [NumberField K]

section SkPart

open scoped Classical
open NumberField.TateGlobal

noncomputable def skPart (S : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  ∏ v ∈ S, Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K) (localUnit (𝓞 K) K v (finUnitAt v z))

theorem skPart_fst (S : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  unfold skPart
  rw [Units.coe_prod, ← AdelicLevel.adeleArch_apply, map_prod]
  exact Finset.prod_eq_one fun v _ => rfl

theorem skPart_snd (S : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
      ∏ v ∈ S, ((localUnit (𝓞 K) K v (finUnitAt v z) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) := by
  unfold skPart
  rw [Units.coe_prod, ← AdelicLevel.adeleFin_apply, map_prod]
  exact Finset.prod_congr rfl fun v _ => rfl

theorem skPart_snd_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v =
      ∏ v' ∈ S, ((localUnit (𝓞 K) K v' (finUnitAt v' z) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v := by
  rw [skPart_snd, ← finAdeleEval_apply (𝓞 K) K v, map_prod]
  exact Finset.prod_congr rfl fun v' _ => finAdeleEval_apply (𝓞 K) K v _

theorem skPart_snd_of_mem {S : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = (z : AdeleRing (𝓞 K) K).2 v := by
  rw [skPart_snd_apply, Finset.prod_eq_single_of_mem v hv fun v' _ hv' => localUnit_apply_of_ne (𝓞 K) K v' _ (Ne.symm hv'),
    localUnit_apply_self]
  rfl

theorem skPart_snd_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
  rw [skPart_snd_apply]
  exact Finset.prod_eq_one fun v' hv' => localUnit_apply_of_ne (𝓞 K) K v' _ (fun h => hv (h ▸ hv'))

theorem apply_skPart (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ) :
    χ (skPart S z) = ∏ v ∈ S, NumberField.TateGlobal.localChar χ v (finUnitAt v z) := by
  unfold skPart
  rw [map_prod]
  exact Finset.prod_congr rfl fun v _ => (localChar_apply χ v _).symm

theorem skPart_inv_snd (S : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((skPart S z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v =
      ((((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v))⁻¹ := by
  have h : (((skPart S z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v *
      ((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
    have := congrArg (fun a : AdeleRing (𝓞 K) K => (finAdeleEval (𝓞 K) K v) (AdelicLevel.adeleFin (𝓞 K) K a))
      (Units.inv_val (skPart S z))
    simp only [map_mul, map_one] at this
    simpa [AdelicLevel.adeleFin_apply, finAdeleEval_apply] using this
  exact eq_inv_of_mul_eq_one_left h

end SkPart
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"

section FinHalf

open AutomorphicForm NumberField.TateGlobal

theorem units_inv_fst_mul (u : (AdeleRing (𝓞 K) K)ˣ) :
    ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * (u : AdeleRing (𝓞 K) K).1 = 1 := by
  show (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (u : AdeleRing (𝓞 K) K)).1 = (1 : AdeleRing (𝓞 K) K).1
  exact congrArg Prod.fst u.inv_mul

theorem units_inv_snd_mul_apply (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v * (u : AdeleRing (𝓞 K) K).2 v = 1 := by
  have h : (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (u : AdeleRing (𝓞 K) K)).2 = (1 : AdeleRing (𝓞 K) K).2 :=
    congrArg Prod.snd u.inv_mul
  exact congrArg (fun x : FiniteAdeleRing (𝓞 K) K => x v) h

theorem units_snd_mul_inv_apply (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (u : AdeleRing (𝓞 K) K).2 v * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
  have h : ((u : AdeleRing (𝓞 K) K) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 = (1 : AdeleRing (𝓞 K) K).2 :=
    congrArg Prod.snd u.mul_inv
  exact congrArg (fun x : FiniteAdeleRing (𝓞 K) K => x v) h

theorem units_inv_fst_eq_one {u : (AdeleRing (𝓞 K) K)ˣ} (h : (u : AdeleRing (𝓞 K) K).1 = 1) :
    ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  have := units_inv_fst_mul u
  rwa [h, mul_one] at this

theorem units_inv_snd_apply_eq (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = ((u : AdeleRing (𝓞 K) K).2 v)⁻¹ :=
  eq_inv_of_mul_eq_one_left (units_inv_snd_mul_apply u v)

theorem units_snd_apply_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (u : AdeleRing (𝓞 K) K).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (units_snd_mul_inv_apply u v)

theorem continuous_units_of_continuous_val (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (h : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.mpr ⟨h, ?_⟩
  have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((χ z⁻¹ : ℂˣ) : ℂ) := by
    funext z; rw [map_inv]
  rw [this]
  exact h.comp continuous_inv

theorem apply_finPart_eq_prod_localChar (S : Finset (HeightOneSpectrum (𝓞 K))) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v)
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (hz : ∀ v : HeightOneSpectrum (𝓞 K), (z : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
      ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K) :
    χ (finPart z) = ∏ v ∈ S, localChar χ v (finUnitAt v z) := by
  classical
  have hskinv : ∀ v, (((skPart S z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v =
      (((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v)⁻¹ := fun v => units_inv_snd_apply_eq _ v
  have htail : χ (finPart z * (skPart S z)⁻¹) = 1 := by
    refine NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous K χ
      (continuous_units_of_continuous_val χ hχc) S hunr _ ?_ ?_ ?_
    ·
      show ((finPart z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 *
          (((skPart S z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1
      rw [finPart_fst, units_inv_fst_eq_one (skPart_fst S z), mul_one]
    ·
      intro v hv
      show ((finPart z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v *
          (((skPart S z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1
      rw [finPart_snd, hskinv, skPart_snd_of_mem hv, mul_inv_cancel₀ (units_snd_apply_ne_zero z v)]
    ·
      rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
      refine ⟨fun v => ?_, fun v => ?_⟩
      · show ((finPart z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v *
          (((skPart S z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K
        rw [finPart_snd, hskinv]
        by_cases hv : v ∈ S
        · rw [skPart_snd_of_mem hv, mul_inv_cancel₀ (units_snd_apply_ne_zero z v)]; exact one_mem _
        · rw [skPart_snd_of_not_mem hv, inv_one, mul_one]; exact (hz v).1
      · rw [← map_inv, mul_inv_rev, inv_inv]
        show ((skPart S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v *
          (((finPart z)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K
        rw [finPart_inv_snd]
        by_cases hv : v ∈ S
        · rw [skPart_snd_of_mem hv, units_snd_mul_inv_apply]; exact one_mem _
        · rw [skPart_snd_of_not_mem hv, one_mul]; exact (hz v).2
  calc χ (finPart z) = χ (finPart z * (skPart S z)⁻¹ * skPart S z) := by rw [inv_mul_cancel_right]
    _ = χ (skPart S z) := by rw [map_mul, htail, one_mul]
    _ = _ := apply_skPart χ S z

theorem borelDiag_integral (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K)
    (hβK : β ∈ adelicMaximalCompact K) (v : HeightOneSpectrum (𝓞 K)) :
    (((borelDiagFst ⟨β, hβ⟩ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
      (((borelDiagFst ⟨β, hβ⟩)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K) ∧
    (((borelDiagSnd ⟨β, hβ⟩ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
      (((borelDiagSnd ⟨β, hβ⟩)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K) := by
  have hle := fun i : Fin 2 => AutomorphicForm.valued_finComponent_apply_le_one hβK v i i
  have ex : ∀ i : Fin 2, ((finComponent (𝓞 K) K v (glFin (𝓞 K) K β) : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i = ((β : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
    intro i; rw [NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
  have ey : ∀ i : Fin 2, (((finComponent (𝓞 K) K v (glFin (𝓞 K) K β))⁻¹ : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        (((β⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i).2 v := by
    intro i; rw [← map_inv, ← map_inv, NumberField.AdelicLevel.finComponent_apply, NumberField.AdelicLevel.glFin_apply]
  have h0 := hle 0
  have h1 := hle 1
  rw [ex 0, ey 0] at h0
  rw [ex 1, ey 1] at h1
  exact ⟨⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h0.1,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h0.2⟩,
    ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1.1,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1.2⟩⟩

end FinHalf
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"

end Ws31.VDimB
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.EisFinDim P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31 P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.Ws31.VDimB"

open AutomorphicForm NumberField.TateGlobal Ws31.VDimB in
theorem Ws31.VDimB.finClassFinite
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ C : Finset (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ),
    ∀ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK),
      (∃ k : adelicMaximalCompact K, ψf 0 (k : AdelicGL2 (𝓞 K) K) ≠ 0) →
      (fun β : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) =>
        ((μ (finPart (borelDiagFst ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩)) : ℂˣ) : ℂ) *
        ((ν (finPart (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩)) : ℂˣ) : ℂ)) ∈ C := by
  intro αm hαm
  classical
  obtain ⟨n, ρs, hFR⟩ :=
    AutomorphicForm.exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
      K SK N hN
  let dF : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → (AdeleRing (𝓞 K) K)ˣ :=
    fun β => borelDiagFst ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩
  let dS : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → (AdeleRing (𝓞 K) K)ˣ :=
    fun β => borelDiagSnd ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩
  let Φ : Fin n × Fin n → (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ) := fun rr β =>
    ((∏ v ∈ SK, ρs rr.1 v (finUnitAt v (dF β)) : ℂˣ) : ℂ) * ((∏ v ∈ SK, ρs rr.2 v (finUnitAt v (dS β)) : ℂˣ) : ℂ)
  refine ⟨(Finset.univ : Finset (Fin n × Fin n)).image Φ, ?_⟩
  intro μ ν hμ hν hμic hνic hμc hνc hμν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hne
  have hφ0 : ψf 0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hne
    intro h
    exact hk (by rw [h]; rfl)
  obtain ⟨hunr, r, r', hrr'⟩ := hFR hαm μ ν 0 (ψf 0) (hψf 0) hφ0 (hψflev 0)
  refine Finset.mem_image.mpr ⟨(r, r'), Finset.mem_univ _, ?_⟩
  funext β
  have hint := fun v => borelDiag_integral (β : AdelicGL2 (𝓞 K) K) (Subgroup.mem_inf.mp β.2).1
    (Subgroup.mem_inf.mp β.2).2 v
  have hF := apply_finPart_eq_prod_localChar SK μ hμc (fun v hv => (hunr v hv).1) (dF β) (fun v => (hint v).1)
  have hS := apply_finPart_eq_prod_localChar SK ν hνc (fun v hv => (hunr v hv).2) (dS β) (fun v => (hint v).2)
  show Φ (r, r') β = ((μ (finPart (dF β)) : ℂˣ) : ℂ) * ((ν (finPart (dS β)) : ℂˣ) : ℂ)
  rw [hF, hS]
  show ((∏ v ∈ SK, ρs r v (finUnitAt v (dF β)) : ℂˣ) : ℂ) * ((∏ v ∈ SK, ρs r' v (finUnitAt v (dS β)) : ℂˣ) : ℂ) = _
  congr 2
  · exact Finset.prod_congr rfl fun v hv => ((hrr' v hv (finUnitAt v (dF β)) (hint v).1.1
      (by rw [finUnitAt_inv_val]; exact (hint v).1.2)).1).symm
  · exact Finset.prod_congr rfl fun v hv => ((hrr' v hv (finUnitAt v (dS β)) (hint v).2.1
      (by rw [finUnitAt_inv_val]; exact (hint v).2.2)).2).symm

open AutomorphicForm Ws31.VDimB in
theorem Ws31.VDimB.classFinite
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ C : Finset (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ),
    ∀ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK),
      (∃ k : adelicMaximalCompact K, ψf 0 (k : AdelicGL2 (𝓞 K) K) ≠ 0) →
      (fun β : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) =>
        ((μ (borelDiagFst ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩) : ℂˣ) : ℂ) *
        ((ν (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩) : ℂˣ) : ℂ)) ∈ C := by
  intro αm hαm
  classical
  obtain ⟨Ca, hCa⟩ := Ws31.VDimB.archClassFinite K SK ξK hξc hξt N hN tysK w hξw
  obtain ⟨Cf, hCf⟩ := Ws31.VDimB.finClassFinite K SK ξK hξc hξt N hN tysK w hξw hαm
  refine ⟨Finset.image₂ (· * ·) Ca Cf, ?_⟩
  intro μ ν hμ hν hμic hνic hμc hνc hμν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hne
  have ha := hCa hαm μ ν hμ hν hμic hνic hμc hνc hμν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hne
  have hf := hCf μ ν hμ hν hμic hνic hμc hνc hμν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hne
  refine Finset.mem_image₂.mpr ⟨_, ha, _, hf, ?_⟩
  funext β
  simp only [Pi.mul_apply]
  conv_rhs => rw [← archPart_mul_finPart (borelDiagFst ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩),
    ← archPart_mul_finPart (borelDiagSnd ⟨(β : AdelicGL2 (𝓞 K) K), (Subgroup.mem_inf.mp β.2).1⟩),
    map_mul, map_mul, Units.val_mul, Units.val_mul]
  ring

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    let Adm : (∀ x, 0 < ((αm x : ℝˣ) : ℝ)) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        (ℂ → AdelicGL2 (𝓞 K) K → ℂ) → Prop := fun hαm μ ν ψf =>
      IsUnitaryChar (𝓞 K) K μ ∧ IsUnitaryChar (𝓞 K) K ν ∧
      IsIdeleClassChar (𝓞 K) K μ ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)) ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s)) ∧
      (∀ s, IsArchKFinite K (ψf s)) ∧
      (∀ s, IsKfSmooth K (ψf s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => ψf s g)) ∧
      (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
      (∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g) ∧
      (∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
    let SameClass : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → Prop := fun μ' ν' μ ν =>
      ∀ (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ adelicBorel (𝓞 K) K), g ∈ adelicMaximalCompact K →
        ((μ (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ) =
          ((μ' (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν' (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ)
    ∃ (n : ℕ) (μs νs : Fin n → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) (ψs : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)) (i : Fin n), Adm hαm (μs i) (νs i) (ψs i)) ∧
      (∀ i j : Fin n, Integrable (fun k : adelicMaximalCompact K =>
        ψs i 0 (k : AdelicGL2 (𝓞 K) K) * conj (ψs j 0 (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K)) ∧
      (∀ a : Fin n → ℂ,
        (∫ k, ‖∑ j, a j * ψs j 0 ((k : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) = 0 →
          a = 0) ∧
      ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ),
        Adm hαm μ ν ψf →
        ∃ a : Fin n → ℂ,
          (∀ k : adelicMaximalCompact K,
            ψf 0 (k : AdelicGL2 (𝓞 K) K) = ∑ i, a i * ψs i 0 (k : AdelicGL2 (𝓞 K) K)) ∧
          (∀ i, a i ≠ 0 → SameClass (μs i) (νs i) μ ν) := by
  intro αm Adm SameClass
  classical
  have hαm₀ : ∀ x, 0 < ((αm x : ℝˣ) : ℝ) := (AutomorphicForm.isInducedSection_adelicHeight_cpow K).1

  let A := { d : (((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) × ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) × (ℂ → AdelicGL2 (𝓞 K) K → ℂ) //
    Adm hαm₀ d.1.1 d.1.2 d.2 }
  let R : A → (adelicMaximalCompact K → ℂ) := fun d k => d.1.2 0 (k : AdelicGL2 (𝓞 K) K)

  have hbchar_eta : ∀ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (β : AdelicGL2 (𝓞 K) K) (hβ : β ∈ adelicBorel (𝓞 K) K),
      β ∈ adelicMaximalCompact K →
      Ws31.SectionExt.bchar K (etaFst μ αm hαm₀ s) (etaSnd ν αm hαm₀ s) β hβ = Ws31.SectionExt.bchar K μ ν β hβ := by
    intro μ ν s β hβ hβK
    obtain ⟨h1, h2⟩ := Ws31.SectionExt.distribHaarChar_borelDiag_eq_one β hβ hβK
    unfold Ws31.SectionExt.bchar
    rw [etaFst_apply, etaSnd_apply]
    simp only [Units.val_mul, cpowChar_apply_val]
    have e1 : (((αm (borelDiagFst ⟨β, hβ⟩) : ℝˣ) : ℝ) : ℂ) = 1 := by
      show (((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagFst ⟨β, hβ⟩) : ℝ≥0) : ℝ) : ℂ) = 1; exact_mod_cast h1
    have e2 : (((αm (borelDiagSnd ⟨β, hβ⟩) : ℝˣ) : ℝ) : ℂ) = 1 := by
      show (((distribHaarChar (AdeleRing (𝓞 K) K) (borelDiagSnd ⟨β, hβ⟩) : ℝ≥0) : ℝ) : ℂ) = 1; exact_mod_cast h2
    rw [e1, e2]; simp only [Complex.one_cpow, mul_one]

  have heqv : ∀ (dd : A) (β : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K)) (k : adelicMaximalCompact K),
      R dd ⟨(β : AdelicGL2 (𝓞 K) K) * k, mul_mem (Subgroup.mem_inf.mp β.2).2 k.2⟩ =
        Ws31.SectionExt.classHom K dd.1.1.1 dd.1.1.2 β * R dd k := by
    intro dd β k
    have hsec : IsInducedSection (𝓞 K) K (etaFst dd.1.1.1 αm hαm₀ 0) (etaSnd dd.1.1.2 αm hαm₀ 0) (dd.1.2 0) :=
      dd.2.2.2.2.2.2.2.2.1 0
    show dd.1.2 0 ((β : AdelicGL2 (𝓞 K) K) * k) = _ * dd.1.2 0 k
    rw [(Ws31.SectionExt.isInducedSection_iff K _ _ _).mp hsec _ (Subgroup.mem_inf.mp β.2).1,
      hbchar_eta _ _ 0 _ _ (Subgroup.mem_inf.mp β.2).2, Ws31.SectionExt.classHom_apply]

  have B1 : ∃ C : Finset (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ), ∀ dd : A,
      (∃ k : adelicMaximalCompact K, R dd k ≠ 0) →
      (⇑(Ws31.SectionExt.classHom K dd.1.1.1 dd.1.1.2) : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ) ∈ C := by
    obtain ⟨C, hC⟩ := Ws31.VDimB.classFinite K SK ξK hξc hξt N hN tysK w hξw hαm₀
    refine ⟨C, fun dd hdd => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := dd.2
    have := hC dd.1.1.1 dd.1.1.2 h1 h2 h3 h4 h5 h6 h7 dd.1.2 h8 h9 h10 h11 h12 h13 h14 h15 h16 hdd
    exact this

  have B2 : ∃ T : ℕ, ∀ (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (m : ℕ) (φ : Fin m → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ j, IsInducedSection (𝓞 K) K χ₁ χ₂ (φ j)) → (∀ j, Continuous (φ j)) → (∀ j, IsArchKFinite K (φ j)) →
      (∀ j (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ j (g * u) = φ j g) →
      (∀ j, φ j ∈ archCutSubmodule K tysK) →
      LinearIndependent ℂ (fun j => fun k : adelicMaximalCompact K => φ j (k : AdelicGL2 (𝓞 K) K)) → m ≤ T :=
    Ws31.VDimB.exists_bound_forall_linearIndependent_restrict K N (Ws31.C0Asm.ne_bot_of_forall_dvd_mem_finset K SK N hN) tysK
  have stepB : ∃ d : ℕ, ∀ (m : ℕ) (e : Fin m → A), LinearIndependent ℂ (fun j => R (e j)) → m ≤ d := by
    obtain ⟨C, hC⟩ := B1
    obtain ⟨T, hT⟩ := B2
    refine ⟨C.card * T, fun m e hli => ?_⟩

    have hne : ∀ j, ∃ k : adelicMaximalCompact K, R (e j) k ≠ 0 := by
      intro j
      by_contra h
      push_neg at h
      exact hli.ne_zero j (funext h)
    let cl : Fin m → ↥C := fun j => ⟨⇑(Ws31.SectionExt.classHom K (e j).1.1.1 (e j).1.1.2), hC (e j) (hne j)⟩

    have hfib : ∀ c : ↥C, (Finset.univ.filter (fun j => cl j = c)).card ≤ T := by
      intro c
      set J := Finset.univ.filter (fun j => cl j = c) with hJ
      rcases J.eq_empty_or_nonempty with hJe | ⟨j₀, hj₀⟩
      · rw [hJe, Finset.card_empty]; exact Nat.zero_le _

      let μ₀ := (e j₀).1.1.1
      let ν₀ := (e j₀).1.1.2
      obtain ⟨hμ₀, hν₀, hμ₀ic, hν₀ic, hμ₀c, hν₀c, hμ₀ν₀, -⟩ := (e j₀).2

      have hclass : ∀ j ∈ J, SameClass (e j).1.1.1 (e j).1.1.2 μ₀ ν₀ := by
        intro j hj g hg hgK
        have h1 : cl j = cl j₀ := by rw [(Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hj₀).2]
        have h2 := congrArg (fun (f : ↥C) => (f : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) → ℂ) ⟨g, Subgroup.mem_inf.mpr ⟨hg, hgK⟩⟩) h1
        simp only [cl, Ws31.SectionExt.classHom_apply, Ws31.SectionExt.bchar] at h2
        exact h2.symm

      have hext : ∀ j ∈ J, ∃ φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ, Adm hαm₀ μ₀ ν₀ φ ∧
          ∀ (s : ℂ) (k : adelicMaximalCompact K), φ s (k : AdelicGL2 (𝓞 K) K) = (e j).1.2 0 (k : AdelicGL2 (𝓞 K) K) :=
        fun j hj => AutomorphicForm.exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
          K SK ξK hξc hξt N hN tysK w hξw hαm₀ (e j).1.1.1 (e j).1.1.2 (e j).1.2 (e j).2 μ₀ ν₀ hμ₀ hν₀ hμ₀ic hν₀ic hμ₀c hν₀c hμ₀ν₀ (hclass j hj)

      let ι : Fin J.card → Fin m := fun l => (J.equivFin.symm l : ↥J)
      have hιmem : ∀ l, ι l ∈ J := fun l => (J.equivFin.symm l).2
      have hιinj : Function.Injective ι := fun l l' h => J.equivFin.symm.injective (Subtype.ext h)
      let φ : Fin J.card → AdelicGL2 (𝓞 K) K → ℂ := fun l => (hext (ι l) (hιmem l)).choose 0
      have hφadm : ∀ l, Adm hαm₀ μ₀ ν₀ (hext (ι l) (hιmem l)).choose := fun l => (hext (ι l) (hιmem l)).choose_spec.1
      have hφres : ∀ l (k : adelicMaximalCompact K), φ l (k : AdelicGL2 (𝓞 K) K) = R (e (ι l)) k :=
        fun l k => (hext (ι l) (hιmem l)).choose_spec.2 0 k
      have hliφ : LinearIndependent ℂ (fun l => fun k : adelicMaximalCompact K => φ l (k : AdelicGL2 (𝓞 K) K)) := by
        have : (fun l => fun k : adelicMaximalCompact K => φ l (k : AdelicGL2 (𝓞 K) K)) = (fun j => R (e j)) ∘ ι := by
          funext l k; exact hφres l k
        rw [this]
        exact hli.comp ι hιinj
      have hcard := hT (etaFst μ₀ αm hαm₀ 0) (etaSnd ν₀ αm hαm₀ 0) J.card φ
        (fun l => (hφadm l).2.2.2.2.2.2.2.1 0)
        (fun l => ((hφadm l).2.2.2.2.2.2.2.2.2.2.1).comp (continuous_const.prodMk continuous_id))
        (fun l => (hφadm l).2.2.2.2.2.2.2.2.1 0)
        (fun l g u hu => (hφadm l).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 g u hu)
        (fun l => (hφadm l).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0)
        hliφ
      simpa [hJ] using hcard

    calc m = (Finset.univ : Finset (Fin m)).card := by simp
      _ = ∑ c ∈ (Finset.univ : Finset ↥C), (Finset.univ.filter (fun j => cl j = c)).card :=
          (Finset.card_eq_sum_card_fiberwise (f := cl) (fun j _ => Finset.mem_univ (cl j))).trans (by rfl)
      _ ≤ ∑ c ∈ (Finset.univ : Finset ↥C), T := Finset.sum_le_sum fun c _ => hfib c
      _ = C.card * T := by simp [Finset.card_univ]
  obtain ⟨d, hd⟩ := stepB
  obtain ⟨n, e, hli, hspan⟩ := Ws31.VDimGeneric.exists_linearIndependent_subfamily_span R d hd

  have hRc : ∀ i, Continuous (R (e i)) := by
    intro i
    have hjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => (e i).1.2 p.1 p.2) := (e i).2.2.2.2.2.2.2.2.2.2.2.1
    exact (hjc.comp (continuous_const.prodMk continuous_id)).comp continuous_subtype_val
  refine ⟨n, fun i => (e i).1.1.1, fun i => (e i).1.1.2, fun i => (e i).1.2, fun hαm i => (e i).2, ?_, ?_, ?_⟩
  ·
    intro i j
    haveI : CompactSpace (adelicMaximalCompact K) := isCompact_iff_compactSpace.mp (isCompact_adelicMaximalCompact K)
    exact Ws31.VDimGeneric.integrable_mul_conj_of_continuous (maximalCompactHaar K) _ _ (hRc i) (hRc j)
  ·
    intro a ha
    haveI : CompactSpace (adelicMaximalCompact K) := isCompact_iff_compactSpace.mp (isCompact_adelicMaximalCompact K)
    exact Ws31.VDimGeneric.eq_zero_of_integral_norm_sq_sum_eq_zero (maximalCompactHaar K) (fun j => R (e j)) hRc hli a ha
  ·
    intro hαm μ ν ψf hadm
    let D : A := ⟨((μ, ν), ψf), hadm⟩
    obtain ⟨a, haD⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan D)
    refine ⟨a, fun k => ?_, fun i hi => ?_⟩
    · have := congrFun haD k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this.symm
    ·
      by_contra hne

      let χ : Fin n → (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) →* ℂ) := fun j => Ws31.SectionExt.classHom K (e j).1.1.1 (e j).1.1.2
      let χD : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) →* ℂ := Ws31.SectionExt.classHom K μ ν
      have hχi : χ i ≠ χD := by
        intro h
        apply hne
        intro g hg hgK
        have := congrArg (fun f : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) →* ℂ => f ⟨g, Subgroup.mem_inf.mpr ⟨hg, hgK⟩⟩) h
        simp only [χ, χD, Ws31.SectionExt.classHom_apply, Ws31.SectionExt.bchar] at this
        exact this.symm

      let S : Finset (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) →* ℂ) := insert χD (Finset.univ.image χ)
      have hχS : ∀ j, χ j ∈ S := fun j => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
      have hDS : χD ∈ S := Finset.mem_insert_self _ _

      let g : (↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) →* ℂ) → (adelicMaximalCompact K → ℂ) := fun c k =>
        (∑ j ∈ Finset.univ.filter (fun j => χ j = c), a j * R (e j) k) - (if c = χD then R D k else 0)
      have hsum : ∀ (t : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K)) (k : adelicMaximalCompact K), ∑ c ∈ S, c t * g c k = 0 := by
        intro t k
        have hpt := congrFun haD ⟨(t : AdelicGL2 (𝓞 K) K) * k, mul_mem (Subgroup.mem_inf.mp t.2).2 k.2⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpt

        rw [heqv D t k] at hpt
        simp only [heqv _ t k] at hpt

        have hre : ∑ c ∈ S, c t * g c k =
            (∑ j, a j * (χ j t * R (e j) k)) - χD t * R D k := by
          simp only [g, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1
          · rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := χ) (fun j _ => hχS j)]
            refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j hj => ?_
            rw [(Finset.mem_filter.mp hj).2]; ring
          · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos hDS]
        rw [hre, sub_eq_zero]
        calc ∑ j, a j * (χ j t * R (e j) k) = ∑ j, a j * (Ws31.SectionExt.classHom K (e j).1.1.1 (e j).1.1.2 t * R (e j) k) := rfl
          _ = Ws31.SectionExt.classHom K μ ν t * R D k := hpt
          _ = χD t * R D k := rfl

      have hL1 := Ws31.VDimGeneric.eq_zero_of_sum_character_mul_eq_zero
        (fun l : Fin S.card => ((S.equivFin.symm l) : ↥(adelicBorel (𝓞 K) K ⊓ adelicMaximalCompact K) →* ℂ))
        (fun l l' h => S.equivFin.symm.injective (Subtype.ext h))
        (fun l => g (S.equivFin.symm l)) (fun t k => by
          rw [← hsum t k, ← Finset.sum_coe_sort S]
          exact (Fintype.sum_equiv S.equivFin.symm _ _ fun l => rfl))
      have hgi : g (χ i) = 0 := by
        have := hL1 (S.equivFin ⟨χ i, hχS i⟩)
        simpa using this

      have hpart : ∑ j, (if χ j = χ i then a j else 0) • R (e j) = 0 := by
        funext k
        have := congrFun hgi k
        simp only [g, if_neg hχi, sub_zero, Pi.zero_apply] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have key : ∑ x, (if χ x = χ i then a x else 0) * R (e x) k =
            ∑ j ∈ Finset.univ.filter (fun j => χ j = χ i), a j * R (e j) k := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
        rw [key]; exact this
      have hzero := (Fintype.linearIndependent_iff.mp hli) (fun j => if χ j = χ i then a j else 0) hpart i
      simp only [if_pos rfl] at hzero
      exact hi hzero

end
end S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule (solution)
