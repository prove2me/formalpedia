-- Prove2me | solution 1 for AutomorphicForm.exists_forall_archOccursInClassOf_and_centralExponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/38fc0ea5-33cb-5583-a0e6-72cfb7bddef5

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_ArchType
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_cpow_centralExponent_of_isReal
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_archOccursInClassOf_and_centralExponent
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section
namespace Ws23
namespace CCocc

variable {F : Type} [Field F] [NumberField F]

private theorem _root_.Ws23.CCocc.central_transform {pins : CarrierPins F} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Θ) (z : (AdeleRing (𝓞 F) F)ˣ) (hz : z ∈ pins.Z)
    (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (centralScalar (𝓞 F) F z * g) = ((R.centralChar ⟨z, hz⟩ : ℂˣ) : ℂ) * R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform ⟨z, hz⟩ g

p2m_export "Ws23.CCocc" "central_transform"

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

theorem main (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ c₀ : ℂ, ∀ P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ P →
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => P φ ∧ ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
            φ (adelicArchGLInclAt F w
                (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) := by
  classical
  by_cases hex : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True)
  · obtain ⟨Θ₀, hΘ₀, R₀, hR₀, -⟩ := hex
    obtain ⟨c₀, hc₀⟩ := AutomorphicForm.SmoothCuspRealizationAt.exists_cpow_centralExponent_of_isReal F _ Θ₀.toRawCentral
      R₀ hR₀ w hw
    refine ⟨c₀, fun P hP ↦ ?_⟩
    obtain ⟨Θ', hΘ', R', hR', hP'⟩ := hP
    refine ⟨Θ', hΘ', R', hR', hP', fun t ht g ↦ ?_⟩
    have hcc : R₀.centralChar = R'.centralChar :=
      AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite F _ Θ₀ Θ'
        (TranslateSpanOccurrence.agrees_trans hΘ₀ (TranslateSpanOccurrence.agrees_symm hΘ')) R₀ hR₀ R' hR'
    obtain ⟨g₀, hg₀⟩ := R₀.exists_ne_zero
    have hz := hc₀ t ht g₀
    rw [adelicArchGLInclAt_map_scalar hw t, central_transform R₀ _ (Subgroup.mem_top _)] at hz
    have hval := mul_right_cancel₀ hg₀ hz
    rw [adelicArchGLInclAt_map_scalar hw t, central_transform R' _ (Subgroup.mem_top _), ← hval, hcc]
  · exact ⟨0, fun P hP ↦ absurd (hP.mono fun _ _ ↦ trivial) hex⟩

end Ws23.CCocc
end

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ c₀ : ℂ, ∀ P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ P →
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => P φ ∧ ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
            φ (adelicArchGLInclAt F w
                (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) :=
  Ws23.CCocc.main c u d₁ d₂ T Θ w hw

end S_AutomorphicForm_exists_forall_archOccursInClassOf_and_centralExponent
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_archOccursInClassOf_and_centralExponent (solution)
