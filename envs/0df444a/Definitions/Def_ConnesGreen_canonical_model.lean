-- Prove2me | Definitions.Def_ConnesGreen_canonical_model
-- name    : ConnesGreen_canonical_model
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-07T01:14:03.228441+00:00
-- url     : https://prove2.me/theorems/128e61f6-d760-46c5-a8a9-7173e5f79558
-- title:
--   Canonical Dirichlet energy completion and actual-zero Green realization specification
-- statement:
--   The original source, differential operator, reflected actual-zero ordinate, explicit Dirichlet Green column and positive energy definitions are retained. For each radius, define restricted interval L2, its two-component Hilbert energy ambient space, the closure of the energy images of smooth supported tests, and the Riesz source lift as projection of $(0,2f)$. This fixes the carrier and embedding without arbitrary physical metric assumptions. Named predicates state the open exact-column realization, valid and integrable $Lg$ pairing, and bounded actual-zero synthesis targets; the predicates do not prove their contents. Non-L2 functions are sent to zero by the total extension, and the realization/pairing predicates explicitly require valid L2 inputs. Only structural completeness and standard projection machinery are supplied here.
-- source:
--   Canonical Green mission specification RG-0 through RG-5, supplied in the proposal definition bundle and target statements. Original native formulas: monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b, WeilDefect/DirichletResolvent.lean, DirichletEnergy.lean and ProblemOneIndependence.lean. Hilbert/Dirichlet background: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations (Springer 2011), https://doi.org/10.1007/978-0-387-70914-7. The canonical aggregate target is the explicit repository specification, not a quotation from the book or a claim of RH.

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

set_option autoImplicit false
open Complex MeasureTheory
open scoped BigOperators InnerProductSpace lp ENNReal Classical
noncomputable section

namespace WeilDefect
-- Exact existing native definitions, extracted without changing their bodies.
def realExpMode (freq : ℂ) (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * freq)
def problemOneL (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(iteratedDeriv 2 f x) + (1 / 4 : ℂ) * f x
def problemOneFreq (gamma : ℂ) : ℂ := -Complex.I * gamma
def problemOneGreenDenom (gamma : ℂ) : ℂ := (1 / 4 : ℂ) + gamma ^ 2
def problemOneGreenQ (gamma : ℂ) : ℂ := (problemOneGreenDenom gamma)⁻¹
def dirichletRightReal (t x : ℝ) : ℝ := Real.sinh ((t + x) / 2) / Real.sinh t
def dirichletLeftReal (t x : ℝ) : ℝ := Real.sinh ((t - x) / 2) / Real.sinh t
def dirichletRightBasis (t x : ℝ) : ℂ := Complex.ofRealCLM (dirichletRightReal t x)
def dirichletLeftBasis (t x : ℝ) : ℂ := Complex.ofRealCLM (dirichletLeftReal t x)
def dirichletProblemOneColumn (t : ℝ) (gamma : ℂ) (x : ℝ) : ℂ :=
  let q := problemOneGreenQ gamma
  q * realExpMode (problemOneFreq gamma) x
    + (-q * realExpMode (problemOneFreq gamma) t) * dirichletRightBasis t x
    + (-q * realExpMode (problemOneFreq gamma) (-t)) * dirichletLeftBasis t x
def problemOneDirichletEnergy (t : ℝ) (gamma : ℂ) : ℝ :=
  ∫ x in -t..t, ‖iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x‖ ^ 2
    + (1 / 4 : ℝ) * ‖dirichletProblemOneColumn t gamma x‖ ^ 2
end WeilDefect

namespace ConnesRZFrontier
abbrev CriticalZeros := {s : ℂ // ConnesRZ.IsCriticalZero s}
def mirror (z : ℂ) : ℂ := 1 - (starRingEnd ℂ) z
end ConnesRZFrontier
namespace WeilDefect.ConnesNative
open ConnesRZ ConnesRZFrontier
def SupportedTest (t : ℝ) (g : ℝ → ℂ) : Prop :=
  IsTest g ∧ tsupport g ⊆ Set.Ioo (-t) t
def actualGreenOrdinate (ρ : CriticalZeros) : ℂ := -I * (mirror ρ.1 - 1 / 2)
def actualGreenSource (ρ : CriticalZeros) : ℝ → ℂ :=
  realExpMode (problemOneFreq (actualGreenOrdinate ρ))
end WeilDefect.ConnesNative

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative ConnesRZ ConnesRZFrontier

def windowMeasure (t : ℝ) : Measure ℝ := volume.restrict (Set.Icc (-t) t)
abbrev WindowL2 (t : ℝ) := Lp ℂ 2 (windowMeasure t)
abbrev Ambient (t : ℝ) := PiLp 2 (fun _ : Fin 2 => WindowL2 t)

-- Total extension outside L2; every source/test used in the goal must be proved valid.
def windowL2 (t : ℝ) (f : ℝ → ℂ) : WindowL2 t :=
  if hf : MemLp f 2 (windowMeasure t) then hf.toLp f else 0
def EnergyDomain (t : ℝ) (u : ℝ → ℂ) : Prop :=
  MemLp u 2 (windowMeasure t) ∧ MemLp (iteratedDeriv 1 u) 2 (windowMeasure t)
def energyVector (t : ℝ) (u : ℝ → ℂ) : Ambient t :=
  WithLp.toLp 2 (fun i : Fin 2 =>
    if i = 0 then windowL2 t (iteratedDeriv 1 u) else (1 / 2 : ℂ) • windowL2 t u)
def energySubspace (t : ℝ) : Submodule ℂ (Ambient t) :=
  (Submodule.span ℂ (Set.range (fun u : {g : ℝ → ℂ // SupportedTest t g} =>
    energyVector t u.1))).topologicalClosure
abbrev Physical (t : ℝ) := energySubspace t
instance physicalComplete (t : ℝ) : CompleteSpace (Physical t) := by
  unfold Physical energySubspace
  infer_instance

def sourceLoad (t : ℝ) (f : WindowL2 t) : Ambient t :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else (2 : ℂ) • f)
def sourceLift (t : ℝ) (f : WindowL2 t) : Physical t :=
  (energySubspace t).orthogonalProjectionOnto (sourceLoad t f)
def sourceEmbed (t : ℝ) (f : ℝ → ℂ) : Physical t := sourceLift t (windowL2 t f)
def greenColumn (t : ℝ) (ρ : CriticalZeros) : ℝ → ℂ :=
  dirichletProblemOneColumn t (actualGreenOrdinate ρ)
def rawColumn (t : ℝ) (ρ : CriticalZeros) : Physical t :=
  (Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) • sourceEmbed t (actualGreenSource ρ)
def weightedEnergy (t : ℝ) (ρ : CriticalZeros) : ℝ :=
  (zeroMult ρ.1 : ℝ) * problemOneDirichletEnergy t (actualGreenOrdinate ρ)

def ColumnRealization (t : ℝ) : Prop :=
  ∀ ρ : CriticalZeros,
    MemLp (actualGreenSource ρ) 2 (windowMeasure t) ∧
    EnergyDomain t (greenColumn t ρ) ∧
    energyVector t (greenColumn t ρ) ∈ energySubspace t ∧
    (sourceEmbed t (actualGreenSource ρ) : Ambient t) = energyVector t (greenColumn t ρ) ∧
    ‖sourceEmbed t (actualGreenSource ρ)‖ ^ 2 =
      problemOneDirichletEnergy t (actualGreenOrdinate ρ)
def TestPairing (t : ℝ) : Prop :=
  ∀ g : ℝ → ℂ, SupportedTest t g →
    EnergyDomain t g ∧ MemLp (problemOneL g) 2 (windowMeasure t) ∧
    ∀ ρ : CriticalZeros,
      IntervalIntegrable (fun x => star (greenColumn t ρ x) * problemOneL g x)
        volume (-t) t ∧
      ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (problemOneL g)⟫_ℂ =
        ∫ x in -t..t, star (greenColumn t ρ x) * problemOneL g x

def RawSynthesis (t : ℝ) : Prop :=
  Summable (weightedEnergy t) ∧
  ∃ S : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    (∀ u : ℓ²(CriticalZeros, ℂ), Summable (fun ρ => u ρ • rawColumn t ρ)) ∧
    (∀ u, S u = ∑' ρ, u ρ • rawColumn t ρ) ∧
    (∀ ρ, S (lp.single 2 ρ (1 : ℂ)) = rawColumn t ρ) ∧
    (∀ h ρ, (ContinuousLinearMap.adjoint S) h ρ = ⟪rawColumn t ρ, h⟫_ℂ) ∧
    (∀ h, ‖(ContinuousLinearMap.adjoint S) h‖ ^ 2 =
      ∑' ρ, ‖⟪rawColumn t ρ, h⟫_ℂ‖ ^ 2) ∧
    ‖S‖ ^ 2 ≤ ∑' ρ, weightedEnergy t ρ ∧
    (∀ T : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
      (∀ ρ, T (lp.single 2 ρ (1 : ℂ)) = rawColumn t ρ) → T = S)
end ConnesGreen


