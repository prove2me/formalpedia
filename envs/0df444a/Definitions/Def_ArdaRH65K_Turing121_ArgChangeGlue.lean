-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_ArgChangeGlue
-- name    : ArdaRH65K_Turing121_ArgChangeGlue
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:09:41.000374+00:00
-- url     : https://prove2.me/theorems/35e0bd67-ae11-4cdb-a02e-506222266253
-- title:
--   ArgChangeGlue certificate definitions
-- statement:
--   This bundle defines the side-argument bounds combined by the zero-count argument. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArgChangeGlue.K6Side.hL5},\;\mathtt{ArgChangeGlue.K6Side},\;\mathtt{ArgChangeGlue.K6Side.hT0},\;\mathtt{ArgChangeGlue.K6Side.hH1}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ArgChangeGlue.lean

import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_BandGlue
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
/-  ArgChangeGlue.lean -- bricks K6a + K6b + K6c consumed by the K0/K1 band glue
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3; `BandGlue.lean`,
    `EdgeClearGlue.lean`).

    `BandGlue.BandData.EnclHyp` is the five-enclosure tail of the `hArbT` binder of every emitted
    Turing band.  After this file:
      * conjunct 5 (`hAV2`, σ = 2 vertical of ζ) is discharged for EVERY band by K6a
        (`ArgZetaTwo.hAV2_of_le`), given the rational side condition `[L1, H1] ⊇ [-249/250, 249/250]`;
      * conjuncts 8, 9 (`hAG1`, `hAG2`, Γℝ verticals) are discharged for every band with
        `0 ≤ T0`, `0 ≤ T1` by K6b (`ArgGammaR.hAG1_of_bounds`, `hAG2_of_bounds`), given rational
        side conditions comparing `L4 H4 L5 H5` with the closed-form brackets `Sm1`, `S2`;
      * conjuncts 6, 7 (`hAHt`, `hAHb`, the horizontal edges) remain as `HorizHyp`, which K6c
        (`ArgHoriz.hAH_of_octCert_boxes`) reduces to an octant certificate plus two point
        enclosures per edge (`HorizHyp.of_octCerts`).
    Combined with K1 (`EdgeClearGlue`), the per-band input becomes `K6Inputs`: the on-line zeros,
    two zero-free edge slabs and the two horizontal enclosures.  `BoxCert.of_K6`,
    `segBandHyp_of_K6` and `ladder_of_K6` feed it into the K0 composition unchanged.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height. -/






open Complex

namespace ArgChangeGlue

open BandGlue BandGlue.BandData

/-- The rational side conditions under which K6a and K6b discharge conjuncts 5, 8 and 9 of a
    band's `hArbT` binder. -/
structure K6Side (d : BandData) : Prop where
  hT0 : 0 ≤ d.T0
  hT1 : 0 ≤ d.T1
  hL1 : d.L1 ≤ -(249 / 250)
  hH1 : 249 / 250 ≤ d.H1
  hL4 : d.L4 ≤ ArgGammaR.Sm1 d.T1 - ArgGammaR.Sm1 d.T0 - ArgGammaR.em1 d.T1
  hH4 : ArgGammaR.Sm1 d.T1 - ArgGammaR.Sm1 d.T0 + ArgGammaR.em1 d.T0 ≤ d.H4
  hL5 : d.L5 ≤ ArgGammaR.S2 d.T1 - ArgGammaR.S2 d.T0 - ArgGammaR.e2 d.T1
  hH5 : ArgGammaR.S2 d.T1 - ArgGammaR.S2 d.T0 + ArgGammaR.e2 d.T0 ≤ d.H5

/-- The two horizontal conjuncts of `EnclHyp` (6 and 7), the only enclosures K6a/K6b leave. -/
def HorizHyp (d : BandData) : Prop :=
  DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc d.L2 d.H2 ∧
    DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc d.L3 d.H3

















/-! ## Band-table helpers (for emitted K6 segments) -/





/-! ## K6a feeding K6c: the `x = 2` endpoint of every horizontal edge -/





end ArgChangeGlue


def ArdaRH65K_Turing121_ArgChangeGlue : Nat := 0


