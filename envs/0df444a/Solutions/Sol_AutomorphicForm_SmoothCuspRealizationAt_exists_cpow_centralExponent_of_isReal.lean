-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.exists_cpow_centralExponent_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/671893b9-d8a1-5fd7-9245-d7a42d179bb1

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_ArchType
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_cpow_centralExponent_of_isReal
set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace Ws23
namespace CC

p2m_open "NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

variable {F : Type} [Field F] [NumberField F]

private theorem _root_.Ws23.CC.central_transform {pins : CarrierPins F} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Θ) (z : (AdeleRing (𝓞 F) F)ˣ) (hz : z ∈ pins.Z)
    (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (centralScalar (𝓞 F) F z * g) = ((R.centralChar ⟨z, hz⟩ : ℂˣ) : ℂ) * R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform ⟨z, hz⟩ g

p2m_export "Ws23.CC" "central_transform"

theorem adelicArchGLInclAt_val_apply (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

theorem centralScalar_val_apply (z : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem adelicArchGLInclAt_map_scalar {w : InfinitePlace F} (hw : w.IsReal) (t : ℝˣ) :
    adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) =
      centralScalar (𝓞 F) F (NumberField.AdelicVolume.archCentralUnit F w
        (Units.map ((ringEquivRealOfIsReal hw).symm.toRingHom : ℝ →* w.Completion) t)) := by
  classical
  apply Units.ext
  ext i j
  rw [adelicArchGLInclAt_val_apply, centralScalar_val_apply]
  have hM : ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
      (Matrix.GeneralLinearGroup.scalar (Fin 2) t) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j =
      if i = j then (ringEquivRealOfIsReal hw).symm (t : ℝ) else 0 := by
    show (ringEquivRealOfIsReal hw).symm.toRingHom ((Matrix.scalar (Fin 2) (t : ℝ)) i j) = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  refine Prod.ext (funext fun v => ?_) ?_
  · show archMatrixUpdate F w _ i j v = _
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hM]
      split_ifs with hij
      · show _ = Function.update (1 : InfiniteAdeleRing F) v _ v
        rw [Function.update_self]; rfl
      · rfl
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      split_ifs with hij
      · subst hij
        rw [Matrix.one_apply_eq]
        show (1 : v.Completion) = Function.update (1 : InfiniteAdeleRing F) w _ v
        rw [Function.update_of_ne hv]; rfl
      · rw [Matrix.one_apply_ne hij]; rfl
  · show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j = _
    split_ifs with hij
    · subst hij; rw [Matrix.one_apply_eq]; rfl
    · rw [Matrix.one_apply_ne hij]; rfl

theorem main (D : Set (AdelicGL2 (𝓞 F) F))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ R)
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ c₀ : ℂ, ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      R.toFun (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * R.toFun g := by
  obtain ⟨-, -, hcont⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      F D (fun v => heckeGen (𝓞 F) F v) (adelicBox F) Θ R
  obtain ⟨u, a, hua⟩ := LanglandsTunnell.Converse.exists_isArchCompAt_of_isReal F
    (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (hcont hR) w hw
  refine ⟨(w.mult : ℂ) * u, fun t ht g => ?_⟩
  rw [adelicArchGLInclAt_map_scalar hw t, central_transform R _ (Subgroup.mem_top _) g]
  congr 1
  have h1 := hua (Units.map ((ringEquivRealOfIsReal hw).symm.toRingHom : ℝ →* w.Completion) t)
  have hnorm : ‖((Units.map ((ringEquivRealOfIsReal hw).symm.toRingHom : ℝ →* w.Completion) t :
      (w.Completion)ˣ) : w.Completion)‖ = (t : ℝ) := by
    show ‖(ringEquivRealOfIsReal hw).symm (t : ℝ)‖ = _
    rw [← norm_ringEquivRealOfIsReal hw, RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_pos ht]
  have hemb : extensionEmbedding w ((Units.map ((ringEquivRealOfIsReal hw).symm.toRingHom : ℝ →* w.Completion) t :
      (w.Completion)ˣ) : w.Completion) = ((t : ℝ) : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hw]
    show ((ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm (t : ℝ)) : ℝ) : ℂ) = _
    rw [RingEquiv.apply_symm_apply]
  rw [hnorm, hemb, div_self (by exact_mod_cast ht.ne'), one_zpow, mul_one] at h1
  exact h1

end Ws23.CC

end

open _root_.NumberField _root_.NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion in

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ R)
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ c₀ : ℂ, ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      R.toFun (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * R.toFun g :=
  Ws23.CC.main D Θ R hR w hw

end S_AutomorphicForm_SmoothCuspRealizationAt_exists_cpow_centralExponent_of_isReal
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_cpow_centralExponent_of_isReal (solution)
