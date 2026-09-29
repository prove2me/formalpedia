-- Prove2me | solution 1 for AutomorphicForm.exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c20419cb-6fdb-511b-b3c8-c6021ce24be0

import Definitions.Def_AutomorphicForm_TwistedOrbital
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
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact
import Theorems.Thm_AutomorphicForm_isOpen_principalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot

set_option autoImplicit false

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
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.EisFinDim"

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
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.EisFinDim"

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
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.EisFinDim"

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
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.EisFinDim"

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
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.EisFinDim"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm EisFinDim

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ D : ℕ, ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (n : ℕ) (φ : Fin n → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ j, IsInducedSection (𝓞 K) K (etaFst μ αm hαm 0) (etaSnd ν αm hαm 0) (φ j))
      (_hφK : ∀ j, IsArchKFinite K (φ j)) (_hφf : ∀ j, IsKfSmooth K (φ j)) (_hφc : ∀ j, Continuous (φ j))
      (_hφKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K,
          (fun k : ↥(archRowIsometrySubgroup K w) => φ j (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφlev : ∀ j (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ j (g * u) = φ j g)
      (_hφty : ∀ j, φ j ∈ archCutSubmodule K tysK)
      (_hφon : ∀ i j, ∫ k, φ i (k : AdelicGL2 (𝓞 K) K) * conj (φ j (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0),
      n ≤ D := by
  intro αm
  classical

  have hE : ∀ w : InfinitePlace K, ∃ E : Finset (rowIsometrySubgroup₀ w.Completion),
      ∀ u ∈ (⨆ i : Fin (tysK.card w), matrixCoeffSubmodule (tysK.rep w i).ρ), (∀ e ∈ E, u e = 0) → u = 0 := fun w =>
    exists_finset_forall_eq_zero_of_forall_apply_eq_zero _
  choose E hE using hE
  obtain ⟨R, hR1, hR2⟩ := exists_finset_cosets_principalLevel K N hN
  let T : Type := {k : AdelicGL2 (𝓞 K) K // ArchSupported K Finset.univ k ∧
      ∀ w, ∃ e ∈ E w, archComponent K w (glArch (𝓞 K) K k) = (e : GL (Fin 2) w.Completion)}
  have hTcomp : ∀ (t : T) (w : InfinitePlace K),
      (⟨archComponent K w (glArch (𝓞 K) K t.1), t.2.1.2.2 w (Finset.mem_univ w)⟩ : rowIsometrySubgroup₀ w.Completion) ∈ E w := by
    intro t w
    obtain ⟨e, he, heq⟩ := t.2.2 w
    have : (⟨archComponent K w (glArch (𝓞 K) K t.1), t.2.1.2.2 w (Finset.mem_univ w)⟩ : rowIsometrySubgroup₀ w.Completion) = e :=
      Subtype.ext heq
    rw [this]; exact he
  haveI : Finite T := by
    refine Finite.of_injective (fun t : T => fun w : InfinitePlace K =>
      (⟨⟨archComponent K w (glArch (𝓞 K) K t.1), t.2.1.2.2 w (Finset.mem_univ w)⟩, hTcomp t w⟩ : ↥(E w))) ?_
    intro t t' htt
    apply Subtype.ext
    refine eq_of_glArch_eq_of_glFin_eq' K ?_ ?_
    · refine eq_of_forall_archComponent_eq K fun w => ?_
      have := congrFun htt w
      simp only [Subtype.mk.injEq] at this
      exact this
    · rw [t.2.1.1, t'.2.1.1]
  haveI : Fintype T := Fintype.ofFinite T
  refine ⟨Fintype.card (↥R × T), ?_⟩
  intro hαm μ ν _ _ _ _ _ _ n φ hφI _ _ hφc _ hφlev hφty hφon

  let L : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (↥R × T → ℂ) :=
    LinearMap.pi fun p : ↥R × T => LinearMap.proj ((p.1 : AdelicGL2 (𝓞 K) K) * (p.2 : AdelicGL2 (𝓞 K) K))
  have hL : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (p : ↥R × T),
      L f p = f ((p.1 : AdelicGL2 (𝓞 K) K) * (p.2 : AdelicGL2 (𝓞 K) K)) := fun _ _ => rfl

  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hint : ∀ i j, Integrable (fun k : adelicMaximalCompact K =>
      φ j (k : AdelicGL2 (𝓞 K) K) * conj (φ i (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) := by
    intro i j
    have hc : Continuous (fun k : adelicMaximalCompact K =>
        φ j (k : AdelicGL2 (𝓞 K) K) * conj (φ i (k : AdelicGL2 (𝓞 K) K))) :=
      ((hφc j).comp continuous_subtype_val).mul
        (Complex.continuous_conj.comp ((hφc i).comp continuous_subtype_val))
    exact hc.integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (Set.subset_univ _))

  have hli : LinearIndependent ℂ (fun j : Fin n => L (φ j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    set ψ : AdelicGL2 (𝓞 K) K → ℂ := ∑ j, c j • φ j with hψ

    have hψI : IsInducedSection (𝓞 K) K (etaFst μ αm hαm 0) (etaSnd ν αm hαm 0) ψ := by
      have : ψ ∈ inducedSectionSubmodule (etaFst μ αm hαm 0) (etaSnd ν αm hαm 0) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφI j)
      exact this
    have hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        ψ (g * u) = ψ g := by
      have : ψ ∈ rightInvariantSubmodule (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφlev j)
      exact this
    have hψT : ψ ∈ archCutSubmodule K tysK :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφty j)
    have hψz : ∀ r ∈ R, ∀ k, ArchSupported K Finset.univ k →
        (∀ w, ∃ e ∈ E w, archComponent K w (glArch (𝓞 K) K k) = (e : GL (Fin 2) w.Completion)) → ψ (r * k) = 0 := by
      intro r hr k hk hkE
      have h := congrFun hc (⟨r, hr⟩, ⟨k, hk, hkE⟩)
      simp only [Finset.sum_apply, Pi.smul_apply, hL, Pi.zero_apply, smul_eq_mul] at h
      rw [hψ]
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    have hψ0 : ψ = 0 :=
      eq_zero_of_forall_apply_eq_zero K _ _ N tysK ψ hψI hψU hψT R hR1 hR2 E hE hψz

    have hpair : ∫ k, ψ (k : AdelicGL2 (𝓞 K) K) * conj (φ i (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = c i := by
      have hrew : (fun k : adelicMaximalCompact K => ψ (k : AdelicGL2 (𝓞 K) K) * conj (φ i (k : AdelicGL2 (𝓞 K) K))) =
          fun k : adelicMaximalCompact K =>
            ∑ j, c j * (φ j (k : AdelicGL2 (𝓞 K) K) * conj (φ i (k : AdelicGL2 (𝓞 K) K))) := by
        funext k
        rw [hψ]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
      rw [hrew, integral_finset_sum _ (fun j _ => (hint i j).const_mul (c j))]
      simp only [integral_const_mul, hφon]
      simp [Finset.sum_ite_eq']
    rw [hψ0] at hpair
    simpa using hpair.symm
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
  exact hcard

end
end S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot (solution)
