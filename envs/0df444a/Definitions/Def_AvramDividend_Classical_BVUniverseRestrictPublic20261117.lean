-- Prove2me | Definitions.Def_AvramDividend_Classical_BVUniverseRestrictPublic20261117
-- name    : AvramDividend_Classical_BVUniverseRestrictPublic20261117
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T18:01:53.615313+00:00
-- url     : https://prove2.me/theorems/dfaf1128-119c-4f68-8e85-0027f1bc4ce0
-- title:
--   Public source-equivalent BV zero-contact universal law transport through ULift
-- statement:
--   Kernel-check the exact implication from the original arbitrary-universe BV zero-contact hypothesis to the Type-0 claim, via measurable ULift transport of all original jump, dividend, cap, ruin, grid and compensation data.
-- source:
--   Original finite-cap BV zero-contact condition and disproof route in the Avram classical mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaim
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaimType0
import Definitions.Def_AvramDividend_Classical_BVULiftTransportPublic20261117
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
universe u
namespace AvramDividend.Classical

/-- The almost-everywhere filter transports through the measurable ULift equivalence. -/
private theorem bvbULiftAE {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) (p : Omega → Prop) :
    (∀ᵐ z ∂P, p z) ↔ (∀ᵐ z ∂(P.map (ULift.up : Omega → ULift.{u} Omega)), p z.down) := by
  simp only [ae_iff]
  have hu : MeasurableEmbedding (ULift.up : Omega → ULift.{u} Omega) :=
    MeasurableEquiv.ulift.symm.measurableEmbedding
  have hmap : (P.map (ULift.up : Omega → ULift.{u} Omega)) {z : ULift.{u} Omega | ¬p z.down} =
      P {z : Omega | ¬p z} := by
    exact hu.map_apply P _
  exact ⟨fun hp => hmap.trans hp, fun hq => hmap.symm.trans hq⟩

noncomputable def bvbUniverseRestrictPublic20261117
    (h : BVZeroContactUniversalClaim.{u}) :
    BVZeroContactUniversalClaimType0 := by
  unfold BVZeroContactUniversalClaimType0
  intro Omega mOmega P f X hX hBV q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
    grid hgrid hmono huniform B hB hAllB hPre hFinite hActivity
  letI : IsProbabilityMeasure P := X.isProbability
  let Q : Measure (ULift.{u} Omega) := P.map ULift.up
  let G := bvbULiftFiltrationPublic20261117.{u} f
  let Y := bvbULiftLevyPublic20261117.{u} f X
  let D' : NNReal → ULift.{u} Omega → Real := fun t z => D t z.down
  let B' : Nat → ULift.{u} Omega → Real := fun n z => B n z.down
  have hBV' : Y.BoundedVariation := by
    simpa [Y, bvbULiftLevyPublic20261117, SpectrallyNegativeLevy.BoundedVariation] using hBV
  have hX' : Y.Standing := by
    rcases hX with ⟨hNoMono, hInt, h33⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hmonoY
      apply hNoMono
      refine ⟨hBV, ?_⟩
      have hdrift : Y.drift = X.drift := by rfl
      have hnu : Y.ν = X.ν := by rfl
      simpa only [hdrift, hnu] using hmonoY.2
    · exact (integrable_map_equiv (MeasurableEquiv.ulift.symm) _).2 hInt
    · simpa [Y, bvbULiftLevyPublic20261117, SpectrallyNegativeLevy.Condition33] using h33
  have hD' : IsAdmissibleLe Y x C D' := by
    rcases hD with ⟨⟨⟨h0, hMon, hLeft, hAdapt⟩, hPay⟩, hCap⟩
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact fun z => h0 z.down
    · exact fun z => hMon z.down
    · exact fun z t => hLeft z.down t
    · intro t
      change Measurable[MeasurableSpace.comap ULift.down (f t)]
        (fun z : ULift.{u} Omega => D t z.down)
      exact (hAdapt t).comp (comap_measurable ULift.down)
    · intro z t ht
      simpa [Y, D', bvbULiftLevyPublic20261117, ruinTime, riskProcess, rightLimit]
        using hPay z.down t ht
    · intro z t ht
      simpa [Y, D', bvbULiftLevyPublic20261117, riskProcess] using hCap z.down t ht
  have hGen' : ∀ y : Real, 0 < y → ENNReal.ofReal y < C →
      Y.GeneratorIntegrable w y ∧ Y.generator w y - q * w y ≤ 0 := by
    intro y hy hcy
    simpa [Y, bvbULiftLevyPublic20261117, SpectrallyNegativeLevy.GeneratorIntegrable,
      SpectrallyNegativeLevy.generator] using hw_gen y hy hcy
  have hNonneg' : ∀ z : ULift.{u} Omega, ∀ t : NNReal,
      0 < t → (t : ENNReal) < ruinTime Y x D' z →
      0 ≤ w (riskProcess Y x D' t z) := by
    intro z t ht hr
    have hr0 : (t : ENNReal) < ruinTime X x D z.down := by
      simpa [Y, D', bvbULiftLevyPublic20261117, ruinTime, riskProcess] using hr
    simpa [Y, D', bvbULiftLevyPublic20261117, riskProcess] using hw_nonneg z.down t ht hr0
  have hJump' : ∀ z : ULift.{u} Omega, ∀ t : NNReal,
      (t = 0 ∨ (t : ENNReal) < ruinTime Y x D' z) →
      rightLimit D' t z - D' t z ≤
        w (riskProcess Y x D' t z) -
          w (riskProcess Y x D' t z - (rightLimit D' t z - D' t z)) := by
    intro z t ht
    have ht0 : t = 0 ∨ (t : ENNReal) < ruinTime X x D z.down := by
      simpa [Y, D', bvbULiftLevyPublic20261117, ruinTime, riskProcess] using ht
    simpa [Y, D', bvbULiftLevyPublic20261117, riskProcess, rightLimit]
      using hjump z.down t ht0
  have hAllB' : ∀ᵐ z ∂Q, ∀ n : Nat, B' n z ≤ 0 := by
    simpa [Q, B'] using
      ((bvbULiftAE.{u} P (fun z => ∀ n : Nat, B n z ≤ 0)).mp hAllB)
  have hPre' : ∀ᵐ z ∂Q, ∀ n i,
      Function.leftLim
        (fun t : NNReal => x + Y.X t z - rightLimit D' t z)
        (grid n (i + 1)) = riskProcess Y x D' (grid n (i + 1)) z := by
    have hr := (bvbULiftAE.{u} P (fun z => ∀ n i,
      Function.leftLim (fun t : NNReal => x + X.X t z - rightLimit D t z)
        (grid n (i + 1)) = riskProcess X x D (grid n (i + 1)) z)).mp hPre
    simpa [Q, Y, D', bvbULiftLevyPublic20261117, riskProcess, rightLimit] using hr
  have H := h Y hX' hBV' q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hGen' hw_grad x hx hxc D' hD' hNonneg' hJump' T hT
    grid hgrid hmono huniform B'
    (by intro n z; exact hB n z.down)
    hAllB' hPre' hFinite
    (by simpa [Y, bvbULiftLevyPublic20261117] using hActivity)
  have hUp : AEMeasurable (ULift.up : Omega → ULift.{u} Omega) P :=
    MeasurableEquiv.ulift.symm.measurable.aemeasurable
  have H0 := ae_of_ae_map hUp H
  refine H0.mono ?_
  intro z hz
  exact hz

end AvramDividend.Classical


