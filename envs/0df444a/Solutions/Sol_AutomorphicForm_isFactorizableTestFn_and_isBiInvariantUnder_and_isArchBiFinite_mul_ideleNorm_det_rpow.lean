-- Prove2me | solution 1 for AutomorphicForm.isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7823ffd3-8b1e-5851-97df-eafff22bebf9

import Mathlib
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"

set_option autoImplicit false

noncomputable section

namespace R1TestFnTwist

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm IsDedekindDomain
open scoped ComplexConjugate

section Modulus

variable (K : Type) [Field K] [NumberField K]

def dm (g : AdelicGL2 (𝓞 K) K) : ℝ :=
  NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)

theorem dm_def (g : AdelicGL2 (𝓞 K) K) :
    dm K g = NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) := rfl

theorem dm_pos (g : AdelicGL2 (𝓞 K) K) : 0 < dm K g := NumberField.TateGlobal.ideleNorm_pos _

theorem dm_mul (g h : AdelicGL2 (𝓞 K) K) : dm K (g * h) = dm K g * dm K h := by
  rw [dm, map_mul, NumberField.TateGlobal.ideleNorm_mul]; rfl

theorem dm_one : dm K 1 = 1 := by
  have h := dm_mul K 1 1
  rw [mul_one] at h
  have hp := dm_pos K 1
  have : dm K 1 * (dm K 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hp.ne'
  · linarith

theorem dm_inv (g : AdelicGL2 (𝓞 K) K) : dm K g⁻¹ = (dm K g)⁻¹ := by
  have h := dm_mul K g g⁻¹
  rw [mul_inv_cancel, dm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem continuous_dm : Continuous (dm K) := NumberField.TateGlobal.continuous_ideleNorm_det K

theorem dm_eq_one_of_glArch_eq_one {X : AdelicGL2 (𝓞 K) K} (h1 : glArch (𝓞 K) K X = 1)
    (h2 : glFin (𝓞 K) K X ∈ finiteIntegralGL2 (𝓞 K) K) : dm K X = 1 := by
  rw [dm, NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K X h2]
  refine Finset.prod_eq_one fun w _ => ?_
  have : archDetNorm w X = 1 := by
    unfold archDetNorm
    rw [h1, map_one, Units.val_one, Matrix.det_one, norm_one]
  rw [this, one_pow]

def cw (w : ℝ) (g : AdelicGL2 (𝓞 K) K) : ℂ := (((dm K g) ^ (w / 2) : ℝ) : ℂ)

theorem cw_def (w : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    cw K w g = (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) :=
  rfl

theorem cw_mul (w : ℝ) (g h : AdelicGL2 (𝓞 K) K) : cw K w (g * h) = cw K w g * cw K w h := by
  rw [cw, dm_mul, Real.mul_rpow (dm_pos K g).le (dm_pos K h).le, Complex.ofReal_mul]; rfl

theorem cw_eq_one_of_dm {w : ℝ} {g : AdelicGL2 (𝓞 K) K} (h : dm K g = 1) : cw K w g = 1 := by
  rw [cw, h, Real.one_rpow, Complex.ofReal_one]

theorem cw_one (w : ℝ) : cw K w 1 = 1 := cw_eq_one_of_dm K (dm_one K)

theorem continuous_cw (w : ℝ) : Continuous (cw K w) :=
  Complex.continuous_ofReal.comp ((continuous_dm K).rpow_const fun g => Or.inl (dm_pos K g).ne')

theorem cw_ne_zero (w : ℝ) (g : AdelicGL2 (𝓞 K) K) : cw K w g ≠ 0 := by
  rw [cw, Complex.ofReal_ne_zero]
  exact (Real.rpow_pos_of_pos (dm_pos K g) _).ne'

end Modulus

section Level

variable (K : Type) [Field K] [NumberField K]

theorem glFin_mem_finiteIntegralGL2_of_mem_levelOne {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K N) : glFin (𝓞 K) K u ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hu
  exact mem_finiteIntegralGL2_iff.mpr ⟨hu.1.integral, hu.2.integral⟩

theorem dm_eq_one_of_mem_principalLevel_inf {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : dm K u = 1 :=
  dm_eq_one_of_glArch_eq_one K ((mem_finiteAdelicGL2Subgroup_iff K u).mp hu.2)
    (glFin_mem_finiteIntegralGL2_of_mem_levelOne K (principalLevel_le_levelOne (𝓞 K) K N hu.1))

theorem isBiInvariantUnder_mul_cw {N : Ideal (𝓞 K)} (w : ℝ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f) :
    IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun g => f g * cw K w g) := by
  intro u hu g
  have h1 : cw K w u = 1 := cw_eq_one_of_dm K (dm_eq_one_of_mem_principalLevel_inf K hu)
  refine ⟨?_, ?_⟩
  · show f (u * g) * cw K w (u * g) = f g * cw K w g
    rw [(hf u hu g).1, cw_mul, h1, one_mul]
  · show f (g * u) * cw K w (g * u) = f g * cw K w g
    rw [(hf u hu g).2, cw_mul, h1, mul_one]

end Level

section ArchTypes

variable (K : Type) [Field K] [NumberField K]

theorem dm_rowIsometryInclAt₀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) :
    dm K (rowIsometryInclAt₀ K w k) = 1 := by
  have hglFin : glFin (𝓞 K) K (rowIsometryInclAt₀ K w k) = 1 := by
    rw [rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]
  have hint : glFin (𝓞 K) K (rowIsometryInclAt₀ K w k) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [hglFin]; exact Subgroup.one_mem _
  rw [dm, NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K _ hint]
  refine Finset.prod_eq_one fun w' _ => ?_
  have hdet : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff (K := w.Completion)).mp k.2).1
  have : archDetNorm w' (rowIsometryInclAt₀ K w k) = 1 := by
    unfold archDetNorm
    rw [rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]
    by_cases hw : w' = w
    · subst hw
      rw [archComponent_archGLIncl_self, hdet, norm_one]
    · rw [archComponent_archGLIncl_of_ne K hw, Units.val_one, Matrix.det_one, norm_one]
  rw [this, one_pow]

theorem cw_mul_rowIsometryInclAt₀ (wt : ℝ) (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 K) K) : cw K wt (x * rowIsometryInclAt₀ K w k) = cw K wt x := by
  rw [cw_mul, cw_eq_one_of_dm K (dm_rowIsometryInclAt₀ K w k), mul_one]

theorem cw_inv_mul_rowIsometryInclAt₀ (wt : ℝ) (w : InfinitePlace K)
    (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 K) K) :
    cw K wt (x * rowIsometryInclAt₀ K w k)⁻¹ = cw K wt x⁻¹ := by
  rw [mul_inv_rev, ← map_inv, cw_mul, cw_eq_one_of_dm K (dm_rowIsometryInclAt₀ K w k⁻¹), one_mul]

theorem mul_mem_iSup_typeSubmodule (w : InfinitePlace K) {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (ρ : ∀ j, Representation ℂ (rowIsometrySubgroup₀ w.Completion) (W j))
    {m : AdelicGL2 (𝓞 K) K → ℂ}
    (hm : ∀ (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 K) K),
      m (x * rowIsometryInclAt₀ K w k) = m x)
    {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : f ∈ ⨆ j : J, typeSubmodule (rowIsometryInclAt₀ K w) (ρ j)) :
    (fun x => f x * m x) ∈ ⨆ j : J, typeSubmodule (rowIsometryInclAt₀ K w) (ρ j) := by
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f x * m x) ∈ ⨆ j : J, typeSubmodule (rowIsometryInclAt₀ K w) (ρ j))
    hf ?_ ?_ ?_
  · intro j f hfj
    refine le_iSup (fun j => typeSubmodule (rowIsometryInclAt₀ K w) (ρ j)) j ?_
    have key := comp_mul_mem_typeSubmodule_of_hom (ι := rowIsometryInclAt₀ K w)
      (ι' := rowIsometryInclAt₀ K w) (MonoidHom.id (AdelicGL2 (𝓞 K) K)) (fun _ => rfl) hm hfj
    exact key
  · show (fun x => (0 : AdelicGL2 (𝓞 K) K → ℂ) x * m x) ∈ _
    have : (fun x => (0 : AdelicGL2 (𝓞 K) K → ℂ) x * m x) = 0 := funext fun x => zero_mul _
    rw [this]; exact Submodule.zero_mem _
  · intro u v hu hv
    show (fun x => (u + v) x * m x) ∈ _
    have : (fun x => (u + v) x * m x) = (fun x => u x * m x) + fun x => v x * m x :=
      funext fun x => add_mul _ _ _
    rw [this]; exact Submodule.add_mem _ hu hv

theorem isArchBiFinite_mul_cw (tys : ArchTypeFamily K) (wt : ℝ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsArchBiFinite K tys f) : IsArchBiFinite K tys (fun g => f g * cw K wt g) := by
  refine ⟨?_, ?_⟩
  · rw [mem_archCutSubmodule_iff]
    intro w
    have h := (mem_archCutSubmodule_iff K tys _).mp hf.1 w
    exact mul_mem_iSup_typeSubmodule K w (fun i => (tys.rep w i).ρ)
      (m := fun x => cw K wt x⁻¹) (fun k x => cw_inv_mul_rowIsometryInclAt₀ K wt w k x) h
  · rw [mem_archDualCutSubmodule_iff]
    intro w
    have h := (mem_archDualCutSubmodule_iff K tys _).mp hf.2 w
    exact mul_mem_iSup_typeSubmodule K w (fun i => (tys.rep w i).ρ.dual)
      (m := fun x => cw K wt x) (fun k x => cw_mul_rowIsometryInclAt₀ K wt w k x) h

end ArchTypes

section FinPart

variable (K : Type) [Field K] [NumberField K]

theorem cw_finEmbed_eq_one_of_mem (wt : ℝ) {k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hk : k ∈ finiteIntegralGL2 (𝓞 K) K) : cw K wt (AdelicDock.finEmbed (𝓞 K) K k) = 1 :=
  cw_eq_one_of_dm K (dm_eq_one_of_glArch_eq_one K (AdelicDock.glArch_finEmbed (𝓞 K) K k)
    (by rwa [AdelicDock.glFin_finEmbed]))

theorem isLocallyConstant_cw_finEmbed (wt : ℝ) :
    IsLocallyConstant (fun k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      cw K wt (AdelicDock.finEmbed (𝓞 K) K k)) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun k₀ => ?_
  refine ⟨{k | k₀⁻¹ * k ∈ finiteIntegralGL2 (𝓞 K) K}, ?_, ?_, ?_⟩
  · have hT : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
    exact (isOpen_finiteLevelZero (𝓞 K) K hT).preimage (continuous_const.mul continuous_id)
  · show k₀⁻¹ * k₀ ∈ finiteIntegralGL2 (𝓞 K) K
    rw [inv_mul_cancel]; exact Subgroup.one_mem _
  · intro k hk
    have hk' : k₀⁻¹ * k ∈ finiteIntegralGL2 (𝓞 K) K := hk
    have : k = k₀ * (k₀⁻¹ * k) := by rw [mul_inv_cancel_left]
    show cw K wt (AdelicDock.finEmbed (𝓞 K) K k) = cw K wt (AdelicDock.finEmbed (𝓞 K) K k₀)
    rw [this, map_mul, cw_mul, cw_finEmbed_eq_one_of_mem K wt hk', mul_one]

theorem isFinTestFactor_mul_cw (wt : ℝ) {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hff : IsFinTestFactor K ff) :
    IsFinTestFactor K (fun k => ff k * cw K wt (AdelicDock.finEmbed (𝓞 K) K k)) :=
  ⟨hff.1.mul (isLocallyConstant_cw_finEmbed K wt), hff.2.mul_right⟩

theorem cw_eq_cw_arch_mul_cw_fin (wt : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    cw K wt g = cw K wt (adelicArchGLIncl K (glArch (𝓞 K) K g)) *
      cw K wt (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g)) := by
  set h : AdelicGL2 (𝓞 K) K :=
    adelicArchGLIncl K (glArch (𝓞 K) K g) * AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g) with hh
  have hA : glArch (𝓞 K) K h = glArch (𝓞 K) K g := by
    rw [hh, map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  have hF : glFin (𝓞 K) K h = glFin (𝓞 K) K g := by
    rw [hh, map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]
  have h1 : cw K wt (h⁻¹ * g) = 1 := by
    refine cw_eq_one_of_dm K (dm_eq_one_of_glArch_eq_one K ?_ ?_)
    · rw [map_mul, map_inv, hA, inv_mul_cancel]
    · rw [map_mul, map_inv, hF, inv_mul_cancel]; exact Subgroup.one_mem _
  calc cw K wt g = cw K wt (h * (h⁻¹ * g)) := by rw [mul_inv_cancel_left]
    _ = cw K wt h := by rw [cw_mul, h1, mul_one]
    _ = _ := by rw [hh, cw_mul]

end FinPart

section ArchPart

variable (K : Type) [Field K] [NumberField K]

open scoped Classical

local notation "GA" => GL (Fin 2) (InfiniteAdeleRing K)
local notation "MS" => (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)

def nA (y : GL (Fin 2) (InfiniteAdeleRing K)) : ℝ := dm K (adelicArchGLIncl K y)

theorem nA_pos (y : GA) : 0 < nA K y := dm_pos K _

theorem nA_eq_prod (y : GA) :
    nA K y = ∏ w : InfinitePlace K,
      ‖((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ w.mult := by
  have hint : glFin (𝓞 K) K (adelicArchGLIncl K y) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [glFin_adelicArchGLIncl]; exact Subgroup.one_mem _
  rw [nA, dm, NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K _ hint]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold archDetNorm
  rw [glArch_adelicArchGLIncl]

def dR (i : {w : InfinitePlace K // w.IsReal}) (m : MS) : ℝ :=
  (m 0 0).1 i * (m 1 1).1 i - (m 0 1).1 i * (m 1 0).1 i

def dC (i : {w : InfinitePlace K // w.IsComplex}) (m : MS) : ℂ :=
  (m 0 0).2 i * (m 1 1).2 i - (m 0 1).2 i * (m 1 0).2 i

theorem contDiff_coordR (i : {w : InfinitePlace K // w.IsReal}) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => (m a b).1 i) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => m a b) := contDiff_apply_apply ℝ _ a b
  exact (contDiff_apply ℝ ℝ i).comp (contDiff_fst.comp h1)

theorem contDiff_coordC (i : {w : InfinitePlace K // w.IsComplex}) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => (m a b).2 i) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => m a b) := contDiff_apply_apply ℝ _ a b
  exact (contDiff_apply ℝ ℂ i).comp (contDiff_snd.comp h1)

theorem contDiff_dR (i : {w : InfinitePlace K // w.IsReal}) : ContDiff ℝ (⊤ : ℕ∞) (dR K i) :=
  ((contDiff_coordR K i 0 0).mul (contDiff_coordR K i 1 1)).sub
    ((contDiff_coordR K i 0 1).mul (contDiff_coordR K i 1 0))

theorem contDiff_dC (i : {w : InfinitePlace K // w.IsComplex}) : ContDiff ℝ (⊤ : ℕ∞) (dC K i) :=
  ((contDiff_coordC K i 0 0).mul (contDiff_coordC K i 1 1)).sub
    ((contDiff_coordC K i 0 1).mul (contDiff_coordC K i 1 0))

def sq (w : InfinitePlace K) (m : MS) : ℝ :=
  if hw : w.IsReal then (dR K ⟨w, hw⟩ m) ^ 2
  else ‖dC K ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ m‖ ^ 2

theorem contDiff_sq (w : InfinitePlace K) : ContDiff ℝ (⊤ : ℕ∞) (sq K w) := by
  by_cases hw : w.IsReal
  · have : sq K w = fun m => (dR K ⟨w, hw⟩ m) ^ 2 := funext fun m => dif_pos hw
    rw [this]
    exact (contDiff_dR K ⟨w, hw⟩).pow 2
  · have : sq K w = fun m => ‖dC K ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ m‖ ^ 2 :=
      funext fun m => dif_neg hw
    rw [this]
    exact (contDiff_norm_sq ℝ).comp (contDiff_dC K _)

omit [NumberField K] in
theorem det_archComponent (w : InfinitePlace K) (y : GA) :
    ((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det =
      (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 w *
          (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 w -
        (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 w *
          (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 w := by
  rw [Matrix.det_fin_two]
  rfl

omit [NumberField K] in
theorem sq_archEntries (w : InfinitePlace K) (y : GA) :
    sq K w (archEntries K y) =
      ‖((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2 := by
  by_cases hw : w.IsReal
  · rw [sq, dif_pos hw]
    have hd : dR K ⟨w, hw⟩ (archEntries K y) =
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          ((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
      rw [det_archComponent, map_sub, map_mul, map_mul]
      rfl
    rw [hd, ← sq_abs, ← Real.norm_eq_abs,
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _)]
  · rw [sq, dif_neg hw]
    have hd : dC K ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ (archEntries K y) =
        NumberField.InfinitePlace.Completion.extensionEmbedding w
          ((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
      rw [det_archComponent, map_sub, map_mul, map_mul]
      rfl
    rw [hd, (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _)]

omit [NumberField K] in
theorem sq_archEntries_pos (w : InfinitePlace K) (y : GA) : 0 < sq K w (archEntries K y) := by
  rw [sq_archEntries]
  refine pow_pos (norm_pos_iff.mpr ?_) 2
  exact (Matrix.GeneralLinearGroup.det_ne_zero _)

def hS (wt : ℝ) (m : MS) : ℝ := ∏ w : InfinitePlace K, (sq K w m) ^ ((w.mult : ℝ) * wt / 4)

theorem contDiffAt_hS (wt : ℝ) {m : MS} (hm : ∀ w, sq K w m ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (hS K wt) m :=
  contDiffAt_prod fun w _ => ((contDiff_sq K w).contDiffAt).rpow_const_of_ne (hm w)

theorem hS_archEntries (wt : ℝ) (y : GA) : hS K wt (archEntries K y) = (nA K y) ^ (wt / 2) := by
  rw [nA_eq_prod, ← Real.finsetProd_rpow _ _ (fun w _ => pow_nonneg (norm_nonneg _) _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [sq_archEntries]
  set a : ℝ := ‖((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖
  have ha : 0 ≤ a := norm_nonneg _
  rw [← Real.rpow_natCast a 2, ← Real.rpow_natCast a w.mult, ← Real.rpow_mul ha, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

def U : Set MS := {m | ∀ w, sq K w m ≠ 0}

theorem isOpen_U : IsOpen (U K) := by
  have : U K = ⋂ w : InfinitePlace K, {m | sq K w m ≠ 0} := by
    ext m; simp [U]
  rw [this]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (contDiff_sq K w).continuous continuous_const

omit [NumberField K] in
theorem archEntries_mem_U (y : GA) : archEntries K y ∈ U K := fun w => (sq_archEntries_pos K w y).ne'

omit [NumberField K] in
theorem continuous_archEntries : Continuous (archEntries K : GA → MS) :=
  continuous_pi fun i => continuous_pi fun j =>
    (AdelicBox.continuous_ringEquiv_mixedSpace (K := K)).comp (Units.continuous_val.matrix_elem i j)

theorem exists_bump {C : Set MS} (hC : IsCompact C) (hCU : C ⊆ U K) :
    ∃ b : MS → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ (∀ᶠ x in nhdsSet (U K)ᶜ, b x = 0) ∧ ∀ x ∈ C, b x = 1 := by
  have hd : Disjoint (U K)ᶜ C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    exact hx (hCU hxC)
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ MS) (n := (⊤ : ℕ∞)) (isOpen_U K).isClosed_compl hC.isClosed hd
  refine ⟨f, ?_, hf0, fun x hx => hf1.self_of_nhdsSet x hx⟩
  exact contMDiff_iff_contDiff.mp f.contMDiff

theorem isArchTestFactor_mul_nA (wt : ℝ) {fa : GA → ℂ} (hfa : IsArchTestFactor K fa) :
    IsArchTestFactor K (fun y => fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ)) := by
  obtain ⟨⟨Φ, hΦ, hrepr⟩, hsupp⟩ := hfa

  set C : Set MS := archEntries K '' tsupport fa with hC
  have hCc : IsCompact C := hsupp.image (continuous_archEntries K)
  have hCU : C ⊆ U K := by
    rintro _ ⟨y, -, rfl⟩
    exact archEntries_mem_U K y
  obtain ⟨b, hb, hb0, hb1⟩ := exists_bump K hCc hCU
  let ρ : MS → ℝ := fun m => b m * hS K wt m
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := by
    rw [contDiff_iff_contDiffAt]
    intro m
    by_cases hm : m ∈ U K
    · exact hb.contDiffAt.mul (contDiffAt_hS K wt hm)
    · have hev : ∀ᶠ x in nhds m, b x = 0 := hb0.filter_mono (nhds_le_nhdsSet hm)
      have hev' : ρ =ᶠ[nhds m] fun _ => 0 := hev.mono fun x hx => by
        show b x * hS K wt x = 0
        rw [hx, zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev'
  refine ⟨⟨fun m => Φ m * ((ρ m : ℝ) : ℂ), hΦ.mul (Complex.ofRealCLM.contDiff.comp hρ), fun y => ?_⟩,
    hsupp.mul_right⟩
  by_cases hy : y ∈ tsupport fa
  · have h1 : b (archEntries K y) = 1 := hb1 _ ⟨y, hy, rfl⟩
    show fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ) = Φ (archEntries K y) * ((ρ (archEntries K y) : ℝ) : ℂ)
    rw [← hrepr y]
    congr 2
    show nA K y ^ (wt / 2) = b (archEntries K y) * hS K wt (archEntries K y)
    rw [h1, one_mul, hS_archEntries]
  · have h0 : fa y = 0 := image_eq_zero_of_notMem_tsupport hy
    show fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ) = Φ (archEntries K y) * ((ρ (archEntries K y) : ℝ) : ℂ)
    rw [← hrepr y, h0, zero_mul, zero_mul]

theorem cw_adelicArchGLIncl (wt : ℝ) (y : GA) :
    cw K wt (adelicArchGLIncl K y) = (((nA K y) ^ (wt / 2) : ℝ) : ℂ) := rfl

end ArchPart

section Assembly

variable (K : Type) [Field K] [NumberField K]

theorem isFactorizableTestFn_mul_cw (wt : ℝ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsFactorizableTestFn K f) : IsFactorizableTestFn K (fun g => f g * cw K wt g) := by
  obtain ⟨fa, ff, hfa, hff, hrepr⟩ := hf
  refine ⟨fun y => fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ),
    fun k => ff k * cw K wt (AdelicDock.finEmbed (𝓞 K) K k),
    isArchTestFactor_mul_nA K wt hfa, isFinTestFactor_mul_cw K wt hff, fun g => ?_⟩
  show f g * cw K wt g = _
  rw [hrepr g, cw_eq_cw_arch_mul_cw_fin K wt g, cw_adelicArchGLIncl]
  ring

end Assembly

end R1TestFnTwist

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (w : ℝ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hfact : IsFactorizableTestFn K f)
    (_hbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (_harch : IsArchBiFinite K tysK f) :
    Continuous (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    HasCompactSupport (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    IsFactorizableTestFn K (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    IsArchBiFinite K tysK (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) :=
  ⟨_hf.mul (R1TestFnTwist.continuous_cw K w), _hfc.mul_right,
    R1TestFnTwist.isFactorizableTestFn_mul_cw K w _hfact,
    R1TestFnTwist.isBiInvariantUnder_mul_cw K w _hbi,
    R1TestFnTwist.isArchBiFinite_mul_cw K tysK w _harch⟩

end S_AutomorphicForm_isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
end P2MW
export P2MW.S_AutomorphicForm_isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow (solution)
