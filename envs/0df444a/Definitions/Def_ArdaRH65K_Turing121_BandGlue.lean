-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_BandGlue
-- name    : ArdaRH65K_Turing121_BandGlue
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:08:57.584926+00:00
-- url     : https://prove2.me/theorems/5678c081-cc2f-4f0f-9ac0-dbfa2c1b0a75
-- title:
--   BandGlue certificate definitions
-- statement:
--   This bundle defines the data and geometric conditions for an argument-principle band certificate. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{BandGlue.BandData.H1},\;\mathtt{BandGlue.BandData.T1},\;\mathtt{BandGlue.BandData.L4},\;\mathtt{BandGlue.BandData.L1}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/BandGlue.lean

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
/-  BandGlue.lean -- brick K0 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `segBandHyp_of_bands`).

    THE GAP IT CLOSES.  The h280000 capstone
    `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000` takes
    `hbands : ∀ k, k < 280 → SegBandHyp k`, and each `SegBandHyp k` is a list of BOX CLAIMS
    ("every zero of ζ in `[1/4000000, 3999999/4000000] x [segLo k i, segHi k i]` is on the line").
    Every box claim is the conclusion of one emitted band theorem `RHInBoxT_*.rh_in_box_*`, but the
    capstone ASSUMES the claims: nothing composes them.  This file makes the composition a theorem,
    parametric in the per-band Arb inputs, so a future evaluator only has to supply those inputs.

    CONTENTS.
      * `BandData`: the parameters of one Turing band, i.e. the arguments of the canonical
        `TuringBand.BandStatement` other than the strip.  `Stmt`, `LineHyp`, `ArbHyp`, `EnclHyp`,
        `Box`, `Inputs`.  `stmt_iff` checks, by `Iff.rfl`, that `LineHyp`/`ArbHyp` are EXACTLY the
        two binders of `BandStatement` (so `Inputs` is what `hLine`/`hArbT` ask for, verbatim).
      * `stmt_of_valid`: the band statement from its decidable side conditions (pins, ball
        geometry), via `TuringBand.turing_band_on_line`; the generic proof of every `rh_in_box_*`.
      * K0 generic: `segBandHyp_of_bands` (indexed band table: the `SegBandHyp` shape),
        `segBandHyp_of_bandList` (a `List` of bands), `ladder_of_bands` (a ladder of segments: the
        `∀ k, k < K → SegBandHyp k` shape the capstone consumes).  Bands may COVER their boxes
        (`T0 ≤ lo`, `hi ≤ T1`); the emitted ladder has equality.
      * K0 + K1: `ReducedInputs` (on-line zeros, two one-sided edge-clearance slabs, five
        enclosures) and `CapGeom` (decidable ball-cap geometry); `inputs_of_reduced`,
        `segBandHyp_of_reduced`, `ladder_of_reduced` (per-band slab heights).  With K1 the `hnzl`
        binder disappears and `hnzb`/`hnzt`/`hins` reduce to two zero-free slabs per band.
      * Certificate form: `BoxCert σ0 σ1 lo hi` (some band covering the box, with its statement
        and its inputs), constructors `of_stmt` / `of_valid` / `of_reduced`, and
        `segBandHyp_of_certs`, `ladder_of_certs`.  A future evaluator may pick its own band
        parameters here (for instance enclosures much wider than the 1e-12 Arb ones, as long as
        the pins hold), which the fixed-table form does not allow.

    The real-segment instantiation (segment 0 of the ladder, 25 bands, the real `rh_in_box_*`
    theorems) is `BandGlue_h1000.lean`.

    Trust: every theorem here is proved outright from its stated hypotheses; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height; nothing
    here says anything about the Riemann Hypothesis. -/





open Complex

namespace BandGlue

/-- The parameters of one Turing band certificate: exactly the arguments of
    `TuringBand.BandStatement` other than the strip `σ0, σ1`. -/
structure BandData where
  T0 : ℝ
  T1 : ℝ
  n : ℕ
  L1 : ℝ
  H1 : ℝ
  L2 : ℝ
  H2 : ℝ
  L3 : ℝ
  H3 : ℝ
  L4 : ℝ
  H4 : ℝ
  L5 : ℝ
  H5 : ℝ
  c : ℂ
  R : ℝ
  hs1 : (1 : ℂ) ∉ Metric.ball c R

/-- A default band (empty ball), so that band tables can have a catch-all arm. -/
instance : Inhabited BandData :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by simp⟩⟩

namespace BandData

variable (σ0 σ1 : ℝ) (d : BandData)

/-- The band's canonical statement: the Prop every emitted `rh_in_box_*` theorem proves (its
    `statement_match` gate). -/
def Stmt : Prop :=
  TuringBand.BandStatement σ0 σ1 d.T0 d.T1 d.n d.L1 d.H1 d.L2 d.H2 d.L3 d.H3 d.L4 d.H4 d.L5 d.H5
    d.c d.R d.hs1

/-- The `hLine` binder: `n` increasing on-line zeros of `completedRiemannZeta` in `[T0, T1]`. -/
def LineHyp : Prop :=
  ∃ xs : List ℝ, xs.length = d.n ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, d.T0 ≤ t ∧ t ≤ d.T1) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)

/-- Conjuncts 5 to 9 of the `hArbT` binder: the five RvM edge argument-change enclosures. -/
def EnclHyp : Prop :=
  DiffractionCore.argChangeVert riemannZeta 2 d.T0 d.T1 ∈ Set.Icc d.L1 d.H1 ∧
  DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc d.L2 d.H2 ∧
  DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc d.L3 d.H3 ∧
  DiffractionCore.argChangeVert Gammaℝ (-1) d.T0 d.T1 ∈ Set.Icc d.L4 d.H4 ∧
  DiffractionCore.argChangeVert Gammaℝ 2 d.T0 d.T1 ∈ Set.Icc d.L5 d.H5

/-- The `hArbT` binder: edge non-vanishing (`hnzb`, `hnzt`, `hnzl`), ball confinement (`hins`)
    and the five enclosures. -/
def ArbHyp : Prop :=
  (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (d.T0 : ℂ) * I) ≠ 0) ∧
  (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (d.T1 : ℂ) * I) ≠ 0) ∧
  (∀ y ∈ Set.uIcc d.T0 d.T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
  (∀ ρ ∈ RHInBoxAnalytic.zeroFinset d.c d.R d.hs1,
    (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ d.T0 < ρ.im ∧ ρ.im < d.T1) ∧
  d.EnclHyp

/-- The per-band Arb inputs: `hLine` and `hArbT`. -/
def Inputs : Prop := d.LineHyp ∧ d.ArbHyp





variable {σ0 σ1 d}







/-! ## K1 inside the band: the reduced per-band input -/

/-- The per-band input after brick K1: the on-line zeros, the two edge-clearance slabs (zero-free
    `(0, 1) x [T0 - δ0, T0]` below the bottom edge and `(0, 1) x [T1, T1 + δ1]` above the top
    edge) and the five enclosures.  (`hnzl` is gone; `hnzb`, `hnzt`, `hins` come from the slabs.) -/
def ReducedInputs (δ0 δ1 : ℝ) (d : BandData) : Prop :=
  d.LineHyp ∧ EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0 ∧ EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1) ∧
    d.EnclHyp

/-- The decidable ball-cap geometry K1 needs: the edges avoid the real axis, the ball sits above
    it, and its bottom/top caps stay inside the clearance slabs (`δ0`, `δ1` at least the caps). -/
structure CapGeom (δ0 δ1 : ℝ) (d : BandData) : Prop where
  hT0 : d.T0 ≠ 0
  hT1 : d.T1 ≠ 0
  hδ0 : 0 ≤ δ0
  hδ1 : 0 ≤ δ1
  hpos : 0 ≤ d.c.im - d.R
  hlo : d.T0 - δ0 ≤ d.c.im - d.R
  hhi : d.c.im + d.R ≤ d.T1 + δ1







end BandData

open BandData

/-! ## Band certificates for a box -/

/-- **A band certificate for the box `[σ0, σ1] x [lo, hi]`**: a Turing band covering the box
    whose statement holds and whose Arb inputs hold.  The statement can come from an emitted
    `rh_in_box_*` theorem (`BoxCert.of_stmt`) or from the band's decidable side conditions
    (`BoxCert.of_valid`); the inputs can be the raw `hLine`/`hArbT` or the K1-reduced ones
    (`BoxCert.of_reduced`).  This is the interface a future evaluator fills: it may choose its own
    band parameters (for instance enclosures wider than the 1e-12 Arb ones, as long as the pins
    hold). -/
def BoxCert (σ0 σ1 lo hi : ℝ) : Prop :=
  ∃ d : BandData, d.T0 ≤ lo ∧ hi ≤ d.T1 ∧ d.Stmt σ0 σ1 ∧ d.Inputs









/-! ## K0: segments and ladders -/















end BandGlue


def ArdaRH65K_Turing121_BandGlue : Nat := 0


