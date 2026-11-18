-- Prove2me | Definitions.Def_AvramDividend_Classical_BVULiftTransportPublic20261117
-- name    : AvramDividend_Classical_BVULiftTransportPublic20261117
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T17:57:40.380551+00:00
-- url     : https://prove2.me/theorems/c5a61400-bdeb-4101-aa36-cb89dee5cb02
-- title:
--   Public source-equivalent ULift transport of spectrally negative Levy path and filtration
-- statement:
--   Reusable exact measurable universe lifting of an original spectrally negative Lévy process with its filtration and pushforward probability measure; no change to triplet, paths, jump measure or law.
-- source:
--   Proof infrastructure for original Avram–Palmowski–Pistorius zero-contact universe restriction in mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical

set_option maxHeartbeats 650000
universe u
namespace AvramDividend.Classical
def bvbULiftFiltrationPublic20261117 {Omega : Type} [mOmega : MeasurableSpace Omega]
    (f : MeasureTheory.Filtration NNReal mOmega) :
    MeasureTheory.Filtration NNReal (inferInstance : MeasurableSpace (ULift.{u} Omega)) := {
  seq := fun t => MeasurableSpace.comap ULift.down (f t)
  mono' := by intro s t hst; exact MeasurableSpace.comap_mono (f.mono hst)
  le' := by intro t; exact (MeasurableSpace.comap_mono (f.le t)).trans measurable_down.comap_le
}

noncomputable def bvbULiftLevyPublic20261117 {Omega : Type} [mOmega : MeasurableSpace Omega]
    {P : Measure Omega} (f : MeasureTheory.Filtration NNReal mOmega)
    (X : SpectrallyNegativeLevy P f) :
    SpectrallyNegativeLevy (P.map ULift.up) (bvbULiftFiltrationPublic20261117.{u} f) where
  X := fun t z => X.X t z.down
  c := X.c
  σ := X.σ
  ν := X.ν
  isProbability := by
    letI := X.isProbability
    exact Measure.isProbabilityMeasure_map (MeasurableEquiv.ulift.symm.measurable.aemeasurable)
  σ_nonneg := X.σ_nonneg
  ν_Ici := X.ν_Ici
  ν_integrable := X.ν_integrable
  X_zero := fun z => X.X_zero z.down
  rightCont := fun z t => X.rightCont z.down t
  leftLim := fun z t ht => X.leftLim z.down t ht
  noPosJumps := fun z t l ht hl => X.noPosJumps z.down t l ht hl
  adapted := by
    intro t
    change Measurable[MeasurableSpace.comap ULift.down (f t)]
      (fun z : ULift.{u} Omega => X.X t z.down)
    exact (X.adapted t).comp (comap_measurable ULift.down)
  indepIncrements := by
    intro s t hst
    change Indep
      (MeasurableSpace.comap (fun z : ULift.{u} Omega => X.X t z.down - X.X s z.down)
        inferInstance)
      (MeasurableSpace.comap ULift.down (f s)) (P.map ULift.up)
    letI : IsProbabilityMeasure P := X.isProbability
    letI : IsProbabilityMeasure (P.map ULift.up) :=
      Measure.isProbabilityMeasure_map (MeasurableEquiv.ulift.symm.measurable.aemeasurable)
    have hOld := X.indepIncrements s t hst
    have hMeas1 : MeasurableSpace.comap
        (fun z : ULift.{u} Omega => X.X t z.down - X.X s z.down)
        (inferInstance : MeasurableSpace Real) =
        MeasurableSpace.comap ULift.down
          (MeasurableSpace.comap (fun z : Omega => X.X t z - X.X s z)
            (inferInstance : MeasurableSpace Real)) := by
      rw [MeasurableSpace.comap_comp]; rfl
    rw [hMeas1]; apply (indep_iff_forall_indepSet _).2
    intro A B hA hB
    change MeasurableSet[MeasurableSpace.comap ULift.down _] A at hA
    rcases hA with ⟨A0, hA0, rfl⟩; rcases hB with ⟨B0, hB0, rfl⟩
    have hI := hOld.indepSet_of_measurableSet hA0 hB0
    have hFt : Measurable (X.X t) := (X.adapted t).mono (f.le t) le_rfl
    have hFs : Measurable (X.X s) := (X.adapted s).mono (f.le s) le_rfl
    have hA0_meas : MeasurableSet A0 := ((hFt.sub hFs).comap_le A0) hA0
    have hB0_meas : MeasurableSet B0 := ((f.le s) B0) hB0
    have hMap : ∀ S : Set Omega, MeasurableSet S →
        (P.map ULift.up) (ULift.down ⁻¹' S) = P S := by
      intro S hS
      have hUp : Measurable (ULift.up : Omega → ULift.{u} Omega) :=
        MeasurableEquiv.ulift.symm.measurable
      calc
        (P.map ULift.up) (ULift.down ⁻¹' S) =
            P (ULift.up ⁻¹' (ULift.down ⁻¹' S)) :=
          Measure.map_apply hUp (hS.preimage measurable_down)
        _ = P S := by rfl
    apply (indepSet_iff_measure_inter_eq_mul
      (hA0_meas.preimage measurable_down) (hB0_meas.preimage measurable_down) _).2
    rw [← Set.preimage_inter]
    rw [hMap (A0 ∩ B0) (hA0_meas.inter hB0_meas),
      hMap A0 hA0_meas, hMap B0 hB0_meas]
    exact hI.measure_inter_eq_mul
  stationaryIncrements := by
    intro s t hst
    have hOld := X.stationaryIncrements s t hst
    have hmT : Measurable (X.X t) := (X.adapted t).mono (f.le t) le_rfl
    have hmS : Measurable (X.X s) := (X.adapted s).mono (f.le s) le_rfl
    have hmD : Measurable (X.X (t - s)) :=
      (X.adapted (t - s)).mono (f.le (t - s)) le_rfl
    have hMap (g : Omega → Real) (hg : Measurable g) :
        (P.map ULift.up).map (fun z : ULift.{u} Omega => g z.down) = P.map g := by
      have hUp : Measurable (ULift.up : Omega → ULift.{u} Omega) :=
        MeasurableEquiv.ulift.symm.measurable
      exact (Measure.map_map (hg.comp measurable_down) hUp).trans
        (by congr 1)
    refine ⟨(hmT.sub hmS).comp measurable_down |>.aemeasurable,
      hmD.comp measurable_down |>.aemeasurable, ?_⟩
    exact (hMap _ (hmT.sub hmS)).trans
      (hOld.map_eq.trans (hMap _ hmD).symm)
  laplace := by
    intro t theta htheta
    obtain ⟨hI, hMean⟩ := X.laplace t theta htheta
    constructor
    · exact (integrable_map_equiv (MeasurableEquiv.ulift.symm) _).2 hI
    · exact (integral_map_equiv (MeasurableEquiv.ulift.symm) _).trans hMean

end AvramDividend.Classical


