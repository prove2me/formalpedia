-- Prove2me | solution 1 for AutomorphicForm.mul_ideleNorm_det_rpow_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/392c066a-a235-5c00-b597-3e65dfc1a5af

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_ideleNorm_det_rpow_mem_archCutSubmodule

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel

namespace TwistArch
variable (K : Type) [Field K] [NumberField K]

theorem det_fst_apply (g : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w =
      ((AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det := by
  have h1 : ((AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).map
        (((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
          (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) : AdeleRing (𝓞 K) K →+* w.Completion) := by
    ext i j; rfl
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem det_snd_eq (g : AdelicGL2 (𝓞 K) K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
      ((AdelicLevel.glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)).det := by
  have h1 : ((AdelicLevel.glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).map
        (((RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
          (RingHom.id (AdeleRing (𝓞 K) K))) : AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K) := by
    ext i j; rfl
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem det_rowIsometryInclAt₀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ K w k) = 1 := by
  apply Units.ext
  apply Prod.ext
  · funext v
    rw [det_fst_apply K]
    show ((AdelicLevel.archComponent K v (AdelicLevel.glArch (𝓞 K) K
        (adelicArchGLIncl K (archGLIncl K w (k : GL (Fin 2) w.Completion)))) : GL (Fin 2) v.Completion) :
          Matrix (Fin 2) (Fin 2) v.Completion).det = 1
    rw [glArch_adelicArchGLIncl]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self]
      exact ((mem_rowIsometrySubgroup₀_iff _).mp k.2).1
    · rw [archComponent_archGLIncl_of_ne K hv, Units.val_one, Matrix.det_one]
  · rw [det_snd_eq K]
    show ((AdelicLevel.glFin (𝓞 K) K
        (adelicArchGLIncl K (archGLIncl K w (k : GL (Fin 2) w.Completion))) : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)).det = 1
    rw [glFin_adelicArchGLIncl, Units.val_one, Matrix.det_one]

noncomputable def mult (s : ℝ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun g => (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ s : ℝ) : ℂ)

theorem mult_mul_rowIsometryInclAt₀ (s : ℝ) (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 K) K) : mult K s (x * rowIsometryInclAt₀ K w k) = mult K s x := by
  simp only [mult, map_mul, det_rowIsometryInclAt₀, mul_one]

noncomputable def M (s : ℝ) : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) where
  toFun φ := fun g => φ g * mult K s g
  map_add' φ ψ := by funext g; simp only [Pi.add_apply]; ring
  map_smul' c φ := by funext g; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem M_mem_archTypeSubmoduleAt (s : ℝ) (w : InfinitePlace K) (τ : ArchRepAt K w)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : f ∈ archTypeSubmoduleAt K w τ) :
    M K s f ∈ archTypeSubmoduleAt K w τ := by
  unfold archTypeSubmoduleAt typeSubmodule at hf ⊢
  refine Submodule.span_induction (p := fun f _ => M K s f ∈ _) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant (rowIsometryInclAt₀ K w) τ.ρ (M K s ∘ₗ T) := by
      intro k' v' x
      show T (τ.ρ k' v') x * mult K s x = T v' (x * rowIsometryInclAt₀ K w k') * mult K s (x * rowIsometryInclAt₀ K w k')
      rw [hT k' v' x, mult_mul_rowIsometryInclAt₀]
    exact Submodule.subset_span ⟨M K s ∘ₗ T, hS, LinearMap.mem_range_self _ v⟩
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; simpa only [map_add] using Submodule.add_mem _ hx hy
  · intro c x _ hx; simpa only [map_smul] using Submodule.smul_mem _ c hx

end TwistArch

open AutomorphicForm TwistArch in
theorem solution
    (K : Type) [Field K] [NumberField K] (tysK : ArchTypeFamily K) (w : ℝ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : φ ∈ archCutSubmodule K tysK) :
    (fun g : AdelicGL2 (𝓞 K) K => φ g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) ∈ archCutSubmodule K tysK := by
  have hM : (fun g : AdelicGL2 (𝓞 K) K => φ g *
      (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) =
      M K (-(w / 2)) φ := rfl
  rw [hM]
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro v
  have hle : (⨆ i : Fin (tysK.card v), archTypeSubmoduleAt K v (tysK.rep v i)).map (M K (-(w / 2))) ≤
      ⨆ i : Fin (tysK.card v), archTypeSubmoduleAt K v (tysK.rep v i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => Submodule.map_le_iff_le_comap.mpr fun f hf =>
      M_mem_archTypeSubmoduleAt K (-(w / 2)) v (tysK.rep v i) f hf
  exact hle ⟨φ, hφ v, rfl⟩

end S_AutomorphicForm_mul_ideleNorm_det_rpow_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_mul_ideleNorm_det_rpow_mem_archCutSubmodule (solution)
