-- Prove2me | Definitions.Def_OAIQ13Tt000
-- name    : OAIQ13Tt000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T12:01:19.251428+00:00
-- url     : https://prove2.me/theorems/4ec84ae3-dd60-434f-bb68-21afc36947af
-- title:
--   Definitions bundle OAIQ13Tt000 of the split of OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 361 declarations of OpenAI's Lean: 265 definitions, 19 inductive types or structures, 10 instances and 67 theorems. The definitions and types are `OAI.ThreeTorus.ActualColoredBlock`, `OAI.ThreeTorus.ActualColoredBlocks`, `OAI.ThreeTorus.ActualQuantileFamily`, `OAI.ThreeTorus.CircleBounded`, `OAI.ThreeTorus.ColoredAnchor`, `OAI.ThreeTorus.ColoredAnchor.chart`, `OAI.ThreeTorus.ColoredAnchor.nextFrame`, `OAI.ThreeTorus.ColoredAnchor.output`, `OAI.ThreeTorus.ColoredPair`, `OAI.ThreeTorus.ColoredPair.Tracks`, `OAI.ThreeTorus.ColoredPair.chart`, `OAI.ThreeTorus.ColoredPair.nextFrame`, `OAI.ThreeTorus.ColoredPair.output`, `OAI.ThreeTorus.ColoredPath`, `OAI.ThreeTorus.ColoredSignalControlledRealizes`, `OAI.ThreeTorus.ColoredState`, `OAI.ThreeTorus.ColoredState.InBand`, `OAI.ThreeTorus.ColoredState.Matches`, `OAI.ThreeTorus.ColoredState.Reflection`, `OAI.ThreeTorus.ColoredState.density`, `OAI.ThreeTorus.ColoredState.laurent`, `OAI.ThreeTorus.ColoredState.measurablePackets`, `OAI.ThreeTorus.ColoredState.totalVector`, `OAI.ThreeTorus.ColoredState.vector`, `OAI.ThreeTorus.ColoredState.weightedVector`, `OAI.ThreeTorus.CylinderSmooth`, `OAI.ThreeTorus.LawCutoffs`, `OAI.ThreeTorus.MeasurablePackets`, `OAI.ThreeTorus.MeasurablePackets.Reflection`, `OAI.ThreeTorus.MeasurablePackets.Supported`, `OAI.ThreeTorus.MeasurablePackets.spectrum`, `OAI.ThreeTorus.MeasurablePackets.vector`, `OAI.ThreeTorus.NeutralStep`, `OAI.ThreeTorus.NeutralStep.chart`, `OAI.ThreeTorus.NeutralStep.nextFrame`, `OAI.ThreeTorus.NeutralStep.reindex`, `OAI.ThreeTorus.PassageGeometryFamily`, `OAI.ThreeTorus.PassageGeometryFamily.correctedFamily`, `OAI.ThreeTorus.PassageGeometryFamily.primitive`, `OAI.ThreeTorus.PassageGeometryFamily.scale` and 244 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/ThreeTorus, in whole or in part: `ThreeTorus_Averaging`, `ThreeTorus_BlockMoments`, `ThreeTorus_ColorBlocks`, `ThreeTorus_ControlledBlocks`, `ThreeTorus_Cutoffs`, `ThreeTorus_CyclicPrediction`, `ThreeTorus_DynamicsLimit`, `ThreeTorus_FiniteBlocks`, `ThreeTorus_FlatPackets`, `ThreeTorus_Geometry`, `ThreeTorus_Jitter`, `ThreeTorus_NeutralSupport`, `ThreeTorus_PacketAlgebra`, `ThreeTorus_PacketCalculus`, `ThreeTorus_PacketStates`, `ThreeTorus_PassageDensity`, `ThreeTorus_PassageFamilies`, `ThreeTorus_PassageMass`, `ThreeTorus_PhysicalBasis`, `ThreeTorus_PhysicalJets`, `ThreeTorus_PositiveLaws`, `ThreeTorus_Prediction`, `ThreeTorus_PredictionModels`, `ThreeTorus_Preparation`, `ThreeTorus_RetainedPackets`, `ThreeTorus_SmoothLimits`, `ThreeTorus_SpectralTransport`, `ThreeTorus_Stages`, `ThreeTorus_StationaryPhase`, `ThreeTorus_SymmetricPackets`, `ThreeTorus_TensorPackets`, `ThreeTorus_TrackedPackets`, `ThreeTorus_Transmission`, `ThreeTorus_Twists`, `ThreeTorus_Whitening`.
--
--   **Imports.** It imports the published bundle `Def_ThreeTorus`.
--
--   **Imported by** (directly, in this split): the statements `OAI.ThreeTorus.StageState.exists_step`, `OAI.ThreeTorus.actual_controlled_density_prediction`, `OAI.ThreeTorus.eventually_colored_controlled_anchor`, `OAI.ThreeTorus.exact_neutral_circle_spectral_estimate`, `OAI.ThreeTorus.exact_neutral_passage`, `OAI.ThreeTorus.exact_passage_circle_spectral_limit`, `OAI.ThreeTorus.exact_quantile_circle_spectral_estimate`, `OAI.ThreeTorus.exact_quantile_passage`, `OAI.ThreeTorus.exists_colored_separation_small`, `OAI.ThreeTorus.exists_concrete_colored_controlled_signal`, `OAI.ThreeTorus.exists_physical_basis`, `OAI.ThreeTorus.exists_predicted_whitening`, `OAI_ThreeTorus_exists_prediction_ready`, `OAI_ThreeTorus_exists_prepared_pair`, `OAI.ThreeTorus.exists_signal_reflected_geometry_state` and `OAI.ThreeTorus.exists_two_slow_insertions`; the proofs of `OAI.ThreeTorus.StageState.exists_step`, `OAI.ThreeTorus.actual_controlled_density_prediction`, `OAI.ThreeTorus.eventually_colored_controlled_anchor`, `OAI.ThreeTorus.exact_neutral_circle_spectral_estimate`, `OAI.ThreeTorus.exact_neutral_passage`, `OAI.ThreeTorus.exact_passage_circle_spectral_limit`, `OAI.ThreeTorus.exact_quantile_circle_spectral_estimate`, `OAI.ThreeTorus.exact_quantile_passage`, `OAI.ThreeTorus.exists_colored_separation_small`, `OAI.ThreeTorus.exists_concrete_colored_controlled_signal`, `OAI.ThreeTorus.exists_physical_basis`, `OAI.ThreeTorus.exists_predicted_whitening`, `OAI_ThreeTorus_exists_prediction_ready`, `OAI_ThreeTorus_exists_prepared_pair`, `OAI.ThreeTorus.exists_signal_reflected_geometry_state`, `OAI.ThreeTorus.exists_two_slow_insertions` and `OAI.ThreeTorus.simple_lebesgue_spectrum`.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/ThreeTorus at commit adc7f12

import Mathlib
import Definitions.Def_ThreeTorus

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-frequency fast averaging on the compact slow circle. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace ThreeTorus

abbrev fastHaar : Measure UnitAddCircle := AddCircle.haarAddCircle
abbrev fastProduct : Measure (UnitAddTorus (Fin 2)) :=
  Measure.pi (fun _ => fastHaar)

def fastOrbit (n : ℕ) (beta : UnitAddCircle) (z : UnitAddCircle) : UnitAddTorus (Fin 2) :=
  ![z,(n:ℤ) • z+beta]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Filter Set Function
open scoped Topology BigOperators

/-- Rescale a compactly supported real frequency variable to one fundamental
interval. Its endpoints vanish, so the quotient is genuinely continuous. -/
def compactRealTorus (H : ℝ × UnitAddCircle → ℂ) (hH : Continuous H) (M : ℕ) :
    UnitAddCircle → C(UnitAddCircle,ℂ) :=
  AddCircle.liftIoc 1 0 (fun x : ℝ =>
    (ContinuousMap.curry ⟨H,hH⟩) ((2*(M:ℝ))*x-M))

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_BlockMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-color moment laws, binomial estimates, and phase expansion. -/

section
noncomputable section
open scoped BigOperators
noncomputable section
open MeasureTheory Complex Set Filter
open scoped Topology ComplexConjugate
namespace ThreeTorus

abbrev phaseHaar : Measure UnitAddCircle := AddCircle.haarAddCircle
abbrev phaseProduct (n : ℕ) : Measure (Fin n → UnitAddCircle) :=
  Measure.pi (fun _ => phaseHaar)

def blockFactor (ell : ℝ) (a : ℂ) (z : UnitAddCircle) : ℝ :=
  1+2*ell*(a*conj (fourier 1 z)).re

def blockFactorC (ell : ℝ) (a : ℂ) (z : UnitAddCircle) : ℂ :=
  1+(ell:ℂ)*a*fourier (-1) z+(ell:ℂ)*conj a*fourier 1 z

def blockProduct (n : ℕ) (ell : ℝ) (a : ℂ) (z : Fin n → UnitAddCircle) : ℝ :=
  ∏ i, blockFactor ell a (z i)

def blockMixture {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ)
    (z : Fin n → UnitAddCircle) : ℝ := ∑ r, t r * blockProduct n ell (a r) z

end ThreeTorus
noncomputable section
open MeasureTheory Complex
open scoped BigOperators ComplexConjugate

noncomputable section
open MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
variable {X : Type*} [MeasurableSpace X] {mu : Measure X} [SigmaFinite mu]

/-- Tensor density on an n-fold product probability space. -/
def weightedProduct (h : X → ℝ) (n : ℕ) (z : Fin n → X) : ℝ := ∏ i, h (z i)

end ThreeTorus

noncomputable section
open MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockEstimatorNoise (n : ℕ) (ell : ℝ) (a : ℂ) (z : Fin n → UnitAddCircle) : ℂ :=
  ((n:ℂ)*(ell:ℂ))⁻¹ * ∑ i, (fourier 1 (z i)-(ell:ℂ)*a)

end ThreeTorus

/-! Finite phase tests.  These are integral tests,
not a claim that a one-dimensional diagonal has product distribution. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology RealInnerProductSpace FourierTransform
namespace ThreeTorus

local instance instMeasureSpaceUnitAddCircle_solutions : MeasureSpace UnitAddCircle := ⟨phaseHaar⟩

/-- A finite Laurent expression, with coefficients depending measurably on
its original circle variable. -/
def phaseTest {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ)
    (z : UnitAddCircle) (y : UnitAddTorus (Fin n)) : ℂ :=
  ∑ i, c i z * UnitAddTorus.mFourier (ν i) y

/-- The recursive choices allow any finite lower bound depending on the
already selected frequencies. -/
def phaseFrequencies (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) : ℕ → ℤ :=
  Nat.strongRec fun j prev =>
    max 0 (max (B j (fun i => prev i i.isLt))
      (R + D * ∑ i : Fin j, prev i i.isLt)) + 1

end ThreeTorus
end
end
end
end
end
end
end

section

/-! The two tests are actual finite Laurent expressions. Their expansions
do not assume phase independence. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- A bounded measurable coefficient on the temporal circle. -/
def CircleBounded (f : UnitAddCircle → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C

/-- An actual finite expansion; every coefficient is proved measurable and
bounded. The finite coefficient type can vary with the expression. -/
def PhaseLaurent {n : ℕ} (F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ) : Prop :=
  ∃ (ι : Type) (fi : Fintype ι), letI := fi
    ∃ (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ),
      (∀ i, CircleBounded (c i)) ∧ ∀ z y, F z y = phaseTest c ν z y

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PositiveLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Fourier laws, compact integral differentiation, affine densities, and prime-sieve signal laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

/-! The positive Fourier law. The sinc and averaged
baseline below are exactly those of the manuscript, including the scale and
normalization. -/
open scoped FourierTransform Convolution

def signalSinc (α R : ℝ) : ℝ := α * Real.sinc (Real.pi*α*R)^2

def signalAverageRadius (α : ℝ) : ℝ := (2*α)⁻¹

def signalBaseline (α R : ℝ) : ℝ :=
  (2*signalAverageRadius α)⁻¹ *
    ∫ t in -signalAverageRadius α..signalAverageRadius α, signalSinc α (R-t)

/-! Exact Fourier support, without assuming an interval inversion formula. -/
def signalBox (α : ℝ) (x : ℝ) : ℂ := (Icc (-α/2) (α/2)).indicator (fun _ => 1) x

def signalTriangle (α v : ℝ) : ℂ := ((max (α-|v|) 0 / α : ℝ) : ℂ)

open scoped ComplexConjugate

def signalInverse (d : ℝ → ℂ) (R : ℝ) : ℝ := (𝓕 d R).re

/-- The exact Ramanujan coefficient in the joint law of Section 3. -/
def signalRamanujanC (P : ℕ) [NeZero P] (h : ZMod P) : ℂ :=
  ∑ u : (ZMod P)ˣ, ZMod.stdAddChar (-(u.val*h))

def signalRamanujan (P : ℕ) [NeZero P] (h : ZMod P) : ℝ :=
  (signalRamanujanC P h).re

/-- Joint law; its marginal over the residue coordinate has total mass one. -/
def signalJoint (α γ : ℝ) (d : ℝ → ℂ) (P : ℕ) [NeZero P] (h : ZMod P) (R : ℝ) : ℝ :=
  (signalBaseline α R+γ*signalRamanujan P h*signalInverse d R)/P

/-- The manuscript's finite sieve modulus, unchanged (not a factorial proxy). -/
def signalPrimeProduct (L : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (L+1)).filter Nat.Prime, p

lemma signalPrimeProduct_pos (L : ℕ) : 0 < signalPrimeProduct L := by
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.pos

instance instNeZeroNatSignalPrimeProduct (L : ℕ) : NeZero (signalPrimeProduct L) := ⟨(signalPrimeProduct_pos L).ne'⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace ThreeTorus

def affineDensity (q : ℝ → ℝ) (a b y : ℝ) : ℝ := a*q (a*y+b)

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace ThreeTorus

/-- Density of J_*=(R/B+h/P)/c; the finite representatives are h.val. -/
def signalJitter (α γ : ℝ) (d : ℝ → ℂ) (P : ℕ) [NeZero P]
    (B c y : ℝ) : ℝ :=
  c*B*∑ h : ZMod P, signalJoint α γ d P h (B*(c*y-h.val/P))

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace ThreeTorus

/-- Density under multiplication by a nonzero real scale, including negative scales. -/
def scaledDensity (q : ℝ → ℝ) (s y : ℝ) : ℝ := |s|⁻¹*q (y/s)

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus
abbrev TripleTorus := UnitAddCircle × UnitAddCircle × UnitAddCircle
abbrev slowVolume : Measure (UnitAddCircle × UnitAddCircle) :=
  AddCircle.haarAddCircle.prod AddCircle.haarAddCircle
abbrev tripleVolume : Measure TripleTorus := AddCircle.haarAddCircle.prod slowVolume

/-- The actual angular packet, in the volume preserving coordinates of section 2. -/
def packet (m : ℤ) (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) : ℂ :=
  A x.2 * fourier m x.1

/-- All integer powers of an intermediate twist in its coordinates. -/
def twistIter (φ : UnitAddCircle → UnitAddCircle) (n : ℤ) (x : TripleTorus) : TripleTorus :=
  (x.1+n • φ x.2.1,x.2)

/-- Packet spectral measure is the precise pushforward stated in (2.3). -/
def packetSpectralMeasure (φ : UnitAddCircle → UnitAddCircle) (m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) : Measure UnitAddCircle :=
  Measure.map (fun ua : UnitAddCircle × UnitAddCircle => m • φ ua.1)
    (slowVolume.withDensity (fun ua => ENNReal.ofReal (‖A ua‖^2)))

end ThreeTorus

namespace ThreeTorus
def circleCycle : TripleTorus ≃ TripleTorus where
  toFun x := (x.2.1,x.2.2,x.1)
  invFun x := (x.2.2,x.1,x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def circleThetaShear (H : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus where
  toFun x := (x.1+H x.2.1,x.2)
  invFun x := (x.1-H x.2.1,x.2)
  left_inv x := by simp
  right_inv x := by simp

def passageChart (H : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus :=
  (circleThetaShear (fun u => -H u)).trans circleCycle

def passageTwist (σ : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus :=
  circleThetaShear σ

def passageMap (H σ : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus where
  toFun x := (x.1+H (x.2.1+σ x.2.2)-H x.2.1, x.2.1+σ x.2.2, x.2.2)
  invFun x := (x.1-H x.2.1+H (x.2.1-σ x.2.2), x.2.1-σ x.2.2, x.2.2)
  left_inv x := by
    simp only [add_sub_cancel_right]
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  right_inv x := by
    simp only [sub_add_cancel]
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Torus coordinate equivalence, smooth passage geometry, and all-jet passage convergence. -/

section

/-! Torus coordinate equivalence and retained passage geometry. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

def torusTriple : Torus ≃ᵐ TripleTorus :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitAddCircle) 0).trans
    ((MeasurableEquiv.refl UnitAddCircle).prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)))

lemma measurePreserving_torusTriple : MeasurePreserving torusTriple μ tripleVolume := by
  exact ((MeasurePreserving.id AddCircle.haarAddCircle).prod
    (measurePreserving_piFinTwo (fun _ : Fin 2 => AddCircle.haarAddCircle))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => AddCircle.haarAddCircle) 0)

def torusPassage (h s : UnitAddCircle → UnitAddCircle) : Equiv.Perm Torus :=
  (torusTriple.toEquiv.trans (passageMap h s)).trans torusTriple.symm.toEquiv

def passageLift (h s : ℝ → ℝ) (x : Cover) : Cover :=
  ![x 0+h (x 1+s (x 2))-h (x 1),x 1+s (x 2),x 2]

def passageInverseLift (h s : ℝ → ℝ) (x : Cover) : Cover :=
  ![x 0-h (x 1)+h (x 1-s (x 2)),x 1-s (x 2),x 2]

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology
namespace ThreeTorus

lemma contDiff_real_primitive {v : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in 0..x, v t) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous hv.continuous,?_⟩
  have hd : deriv (fun x => ∫ t in 0..x, v t) = v := by
    funext x
    exact (intervalIntegral.integral_hasDerivAt_right (hv.continuous.intervalIntegrable 0 x)
      hv.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuous.continuousAt).deriv
  rw [hd]
  exact hv

lemma primitive_translate_one {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) (x : ℝ) :
    (∫ t in 0..x+1, v t) = (∫ t in 0..x, v t)+(∫ t in 0..1, v t) := by
  simpa only [zero_add] using hv.intervalIntegral_add_eq_add 0 x (fun a b => hc.intervalIntegrable a b)

lemma periodic_primitive_mod {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    Function.Periodic (fun x => (↑(∫ t in 0..x, v t):UnitAddCircle)) 1 := by
  intro x
  dsimp only
  rw [primitive_translate_one hv hc,hk,AddCircle.coe_add]
  have hk0 : ((k:ℝ):UnitAddCircle) = 0 := by
    rw [show (k:ℝ) = k • (1:ℝ) by simp,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]
  rw [hk0,add_zero]

/-- The precise globally defined circle-valued primitive used by a passage. -/
def circlePrimitive {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) : UnitAddCircle → UnitAddCircle :=
  (periodic_primitive_mod hv hc hk).lift

def circleSpeed {s : ℝ → ℝ} (hs : Function.Periodic s 1) : UnitAddCircle → UnitAddCircle :=
  fun z => (hs.lift z : UnitAddCircle)

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

/-- A nonsingular two-parameter form of the exact passage lift (both signs). -/
def passageFamily (v J : ℝ → ℝ) (r : ℝ) (p : ℝ × ℝ) (x : Cover) : Cover :=
  let s := r*p.1*(1+p.1*J (x 2))
  ![x 0+r*(1+p.1*J (x 2))*(∫ t in (0:ℝ)..1, v (x 1+t*s)+p.2),
    x 1+s,x 2]

end ThreeTorus
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Cutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth cylinder cutoffs, circle periodization, and regularity of covering lifts. -/

section

/-! Smooth compact supported cutoffs on the actual real-frequency/slow-circle
cylinder, used for the disjoint stationary images in the passage lemma. -/
noncomputable section
open Set Function Filter Topology
open scoped Topology Manifold
namespace ThreeTorus

/-- Periodization only in the circle coordinate. -/
def cylinderPeriodize (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ᶠ k : ℤ, f (p.1,p.2+k)

lemma cylinderPeriodize_periodic (f : ℝ × ℝ → ℝ) (s : ℝ) :
    Periodic (fun a => cylinderPeriodize f (s,a)) 1 := by
  intro a
  have hh := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => f (s,a+k))
  simpa [cylinderPeriodize,add_comm,add_left_comm,add_assoc] using hh

/-- The covering map for the real-frequency/slow-circle cylinder. -/
def cylinderProjection (p : ℝ × ℝ) : ℝ × UnitAddCircle := (p.1,(p.2 : UnitAddCircle))

lemma continuous_cylinderProjection : Continuous cylinderProjection :=
  continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp continuous_snd)

lemma cylinderProjection_surjective : Surjective cylinderProjection := by
  rintro ⟨s,a⟩
  obtain ⟨b,hb⟩ := QuotientAddGroup.mk_surjective a
  exact ⟨(s,b),Prod.ext rfl hb⟩

lemma isOpenMap_cylinderProjection : IsOpenMap cylinderProjection := by
  exact IsOpenMap.id.prodMap QuotientAddGroup.isOpenMap_coe

lemma isQuotientMap_cylinderProjection : IsQuotientMap cylinderProjection :=
  isOpenMap_cylinderProjection.isQuotientMap continuous_cylinderProjection cylinderProjection_surjective

/-- Smoothness on this cylinder is smoothness of the periodic covering lift. -/
def CylinderSmooth (f : ℝ × UnitAddCircle → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ cylinderProjection)

lemma CylinderSmooth.continuous {f : ℝ × UnitAddCircle → ℝ} (hf : CylinderSmooth f) :
    Continuous f := isQuotientMap_cylinderProjection.continuous_iff.mpr (ContDiff.continuous hf)

/-- Periodization with a smooth saturation gives a [0,1]-valued cylinder function. -/
def cylinderCutoff (f : ℝ × ℝ → ℝ) (p : ℝ × UnitAddCircle) : ℝ :=
  Real.smoothTransition ((cylinderPeriodize_periodic f p.1).lift p.2)

@[simp] lemma cylinderCutoff_coe (f : ℝ × ℝ → ℝ) (s a : ℝ) :
    cylinderCutoff f (s,(a : UnitAddCircle)) =
      Real.smoothTransition (cylinderPeriodize f (s,a)) := rfl

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter Topology
open scoped Topology BigOperators
namespace ThreeTorus

/-- Periodization in the REAL coordinate of a compact cylinder cutoff. -/
def cylinderFirstPeriodize (χ : ℝ × UnitAddCircle → ℝ) (p : ℝ × UnitAddCircle) : ℝ :=
  ∑ᶠ k : ℤ, χ (p.1+k,p.2)

lemma cylinderFirstPeriodize_periodic (χ : ℝ × UnitAddCircle → ℝ) (a : UnitAddCircle) :
    Periodic (fun u => cylinderFirstPeriodize χ (u,a)) 1 := by
  intro u
  have hh := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => χ (u+k,a))
  simpa [cylinderFirstPeriodize,add_comm,add_left_comm,add_assoc] using hh

lemma cylinderFirstPeriodize_local_support {χ : ℝ × UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ) (p : ℝ × ℝ) :
    ∃ S : Finset ℤ, ∀ᶠ q in 𝓝 p,
      support (fun k : ℤ => χ (q.1+k,(q.2:UnitAddCircle))) ⊆ (S : Set ℤ) := by
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|p.1|+1)
  refine ⟨Finset.Icc (-(N:ℤ)) N,?_⟩
  filter_upwards [continuous_fst.tendsto p (Metric.ball_mem_nhds p.1 (by norm_num : (0:ℝ)<1))] with q hq
  intro k hk
  have hq' : |q.1| < |p.1|+1 := by
    have hh := abs_add_le (q.1-p.1) p.1
    have hi : |q.1-p.1| < 1 := hq
    simpa only [sub_add_cancel] using hh.trans_lt (by linarith : |q.1-p.1|+|p.1| < |p.1|+1)
  have hk' : |q.1+(k:ℝ)| ≤ R := hR _ (mem_image_of_mem _ (subset_tsupport χ hk))
  have hz : |(k:ℝ)| < (N:ℝ) := calc
    |(k:ℝ)| = |(q.1+k)-q.1| := by congr 1; ring
    _ ≤ |q.1+k|+|q.1| := abs_sub _ _
    _ < (N:ℝ) := by linarith
  rw [Finset.mem_coe,Finset.mem_Icc]
  exact_mod_cast (abs_le.mp hz.le)

lemma cylinderFirstPeriodize_smooth {χ : ℝ × UnitAddCircle → ℝ}
    (hχ : CylinderSmooth χ) (hc : HasCompactSupport χ) :
    CylinderSmooth (cylinderFirstPeriodize χ) := by
  classical
  rw [CylinderSmooth, contDiff_iff_contDiffAt]
  intro p
  obtain ⟨S,hS⟩ := cylinderFirstPeriodize_local_support hc p
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ∑ k ∈ S, χ (q.1+k,(q.2:UnitAddCircle))) :=
    ContDiff.sum (fun _ _ => hχ.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd))
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hS] with q hq
  exact finsum_eq_sum_of_support_subset _ hq

/-- The cutoff on the actual two-torus, not a chart-only surrogate. -/
def cylinderTorusCutoff (χ : ℝ × UnitAddCircle → ℝ) (p : UnitAddCircle × UnitAddCircle) : ℝ :=
  (cylinderFirstPeriodize_periodic χ p.2).lift p.1

@[simp] lemma cylinderTorusCutoff_coe (χ : ℝ × UnitAddCircle → ℝ) (u : ℝ) (a : UnitAddCircle) :
    cylinderTorusCutoff χ ((u:UnitAddCircle),a) = cylinderFirstPeriodize χ (u,a) := rfl

lemma cylinderTorusCutoff_smooth {χ : ℝ × UnitAddCircle → ℝ}
    (hχ : CylinderSmooth χ) (hc : HasCompactSupport χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => cylinderTorusCutoff χ ((p.1:UnitAddCircle),(p.2:UnitAddCircle))) :=
  cylinderFirstPeriodize_smooth hχ hc

lemma cylinderTorusCutoff_continuous {χ : ℝ × UnitAddCircle → ℝ}
    (hχ : CylinderSmooth χ) (hc : HasCompactSupport χ) :
    Continuous (cylinderTorusCutoff χ) := by
  have hq : IsQuotientMap (fun p : ℝ × UnitAddCircle => ((p.1:UnitAddCircle),p.2)) :=
    (QuotientAddGroup.isOpenMap_coe.prodMap IsOpenMap.id).isQuotientMap
      (QuotientAddGroup.continuous_mk.prodMap continuous_id)
      (QuotientAddGroup.mk_surjective.prodMap surjective_id)
  apply hq.continuous_iff.mpr
  exact (cylinderFirstPeriodize_smooth hχ hc).continuous

lemma cylinderFirstPeriodize_eq {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) {u : ℝ} (hu : u ∈ Ioc o (o+1))
    (a : UnitAddCircle) : cylinderFirstPeriodize χ (u,a) = χ (u,a) := by
  classical
  unfold cylinderFirstPeriodize
  have hz : ∀ k : ℤ, k ≠ 0 → χ (u+k,a) = 0 := by
    intro k hk
    apply notMem_support.mp
    intro hh
    have h := (hs hh).1
    rcases lt_or_gt_of_ne hk with hk' | hk'
    · have hk'' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      linarith [h.1,hu.2]
    · have hk'' : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      linarith [h.2,hu.1]
  rw [finsum_eq_single _ 0 (fun k hk => hz k hk)]
  simp

lemma cylinderTorusCutoff_eq {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) {u : ℝ} (hu : u ∈ Ioc o (o+1))
    (a : UnitAddCircle) : cylinderTorusCutoff χ ((u:UnitAddCircle),a) = χ (u,a) :=
  cylinderFirstPeriodize_eq hs hu a

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter Topology
open scoped Topology
namespace ThreeTorus

/-- Cover smoothness supplies the parameter-continuous first derivatives
needed by stationary phase on a cylinder; it is not an additional regularity
assumption on the clipped packets. -/
lemma cylinder_smooth_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × UnitAddCircle → E}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ cylinderProjection)) :
    (∀ a, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (x,a))) ∧
    Continuous f ∧ Continuous (fun p : ℝ × UnitAddCircle => deriv (fun x => f (x,p.2)) p.1) := by
  have ht a : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (x,a)) := by
    obtain ⟨b,rfl⟩ := QuotientAddGroup.mk_surjective a
    exact hf.comp (contDiff_id.prodMk contDiff_const)
  refine ⟨ht,isQuotientMap_cylinderProjection.continuous_iff.mpr hf.continuous,?_⟩
  apply isQuotientMap_cylinderProjection.continuous_iff.mpr
  have he (p : ℝ × ℝ) : deriv (fun x : ℝ => f (x,(p.2:UnitAddCircle))) p.1 =
      fderiv ℝ (f ∘ cylinderProjection) p (1,0) := by
    have hd : HasFDerivAt (f ∘ cylinderProjection) (fderiv ℝ (f ∘ cylinderProjection) p) p :=
      (hf.differentiable (by simp) p).hasFDerivAt
    have hh := hd.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    simpa only [Function.comp_def,cylinderProjection,id_eq] using hh.deriv
  change Continuous (fun p : ℝ × ℝ => deriv (fun x : ℝ => f (x,(p.2:UnitAddCircle))) p.1)
  simp_rw [he]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

/-- The manuscript's distribution function, without a normalization convention
for non-probability inputs. -/
def cumulative (ρ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ x in Iic y, ρ x

/-- The inverse is only used on (0,1); its arbitrary values elsewhere are killed
by a smooth compactly supported cutoff. -/
def quantile (ρ : ℝ → ℝ) : ℝ → ℝ := invFun (cumulative ρ)

/-- Periodize by a locally finite sum. Unlike a raw `fract` expression this
also makes smoothness at the identified endpoints explicit. -/
def periodize (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑ᶠ k : ℤ, f (x + k)

lemma periodize_periodic (f : ℝ → ℝ) : Periodic (periodize f) 1 := by
  intro x
  have hh := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => f (x + k))
  simpa [periodize, add_comm, add_left_comm, add_assoc] using hh

/-- The two actual smooth cutoffs used by the manuscript's quantile construction. -/
structure LawCutoffs (δ : ℝ) where
  ξ : ℝ → ℝ
  ψ : ℝ → ℝ
  ξ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ
  ψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ
  ξ_compact : HasCompactSupport ξ
  ψ_compact : HasCompactSupport ψ
  ξ_support : tsupport ξ ⊆ Ioo (0 : ℝ) 1
  ψ_support : tsupport ψ ⊆ Ioo δ (1-δ)
  ξ_one : ∀ a ∈ Icc δ (1-δ), ξ a = 1
  ψ_one : ∀ a ∈ Icc (2*δ) (1-2*δ), ψ a = 1
  ψ_nonneg : ∀ a, 0 ≤ ψ a
  ψ_le_one : ∀ a, ψ a ≤ 1

def lawCutoffs (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1/8) : LawCutoffs δ := by
  let ξ : ContDiffBump (1/2 : ℝ) :=
    ⟨1/2-δ, 1/2-3*δ/4, by linarith, by linarith⟩
  let ψ : ContDiffBump (1/2 : ℝ) :=
    ⟨1/2-2*δ, 1/2-3*δ/2, by linarith, by linarith⟩
  refine ⟨ξ, ψ, ξ.contDiff, ψ.contDiff, ξ.hasCompactSupport, ψ.hasCompactSupport,
    ?_, ?_, ?_, ?_, fun _ => ψ.nonneg, fun _ => ψ.le_one⟩
  · intro a ha
    rw [ξ.tsupport_eq] at ha
    change |a-1/2| ≤ 1/2-3*δ/4 at ha
    have hh := abs_le.mp ha
    constructor <;> linarith
  · intro a ha
    rw [ψ.tsupport_eq] at ha
    change |a-1/2| ≤ 1/2-3*δ/2 at ha
    have hh := abs_le.mp ha
    constructor <;> linarith
  · intro a ha
    apply ξ.one_of_mem_closedBall
    change |a-1/2| ≤ 1/2-δ
    rw [abs_le]
    constructor <;> linarith [ha.1,ha.2]
  · intro a ha
    apply ψ.one_of_mem_closedBall
    change |a-1/2| ≤ 1/2-2*δ
    rw [abs_le]
    constructor <;> linarith [ha.1,ha.2]

def lawJitter (ρ : ℝ → ℝ) {δ : ℝ} (c : LawCutoffs δ) : ℝ → ℝ :=
  periodize (fun a => c.ξ a * quantile ρ a)

def lawPsi {δ : ℝ} (c : LawCutoffs δ) : ℝ → ℝ := periodize c.ψ

def lawDensity (ρ : ℝ → ℝ) {δ : ℝ} (c : LawCutoffs δ) (y : ℝ) : ℝ :=
  ρ y * c.ψ (cumulative ρ y) ^ 2

end ThreeTorus

namespace ThreeTorus
open Set Function MeasureTheory
open scoped Topology

/-- A bounded smooth periodic jitter that is exactly affine on the fixed
large good arc. The cutoff and good arc do not depend on the slope. -/
def neutralJitterReal {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) : ℝ → ℝ :=
  periodize (fun a => c.ξ a*(L*a+β))

lemma neutralJitterReal_periodic {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    Periodic (neutralJitterReal c L β) 1 := periodize_periodic _

def neutralJitter {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) : UnitAddCircle → ℝ :=
  (neutralJitterReal_periodic c L β).lift

def neutralCircleCutoff {δ : ℝ} (c : LawCutoffs δ) : UnitAddCircle → ℝ :=
  (periodize_periodic c.ψ).lift

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_StationaryPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform signed stationary phase, oscillatory integral estimates, and summed coefficient-mass control. -/

noncomputable section

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
namespace ThreeTorus

/-- Actual stationary leading term: zero outside the derivative branch. -/
def stationaryLeading (Φ : ℝ → ℝ) (A : ℝ → ℂ) (l u s t : ℝ) : ℂ :=
  if s ∈ Icc (deriv Φ l) (deriv Φ u) then
    let v := Function.invFunOn (deriv Φ) (Icc l u) s
    Complex.exp (I * (t*(Φ v-s*v) : ℝ)) *
      ((Real.sqrt (iteratedDeriv 2 Φ v/(2*Real.pi)) : ℂ)⁻¹ *
        (A v * Complex.exp ((Real.pi : ℂ)/4*I)))
  else 0

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology

namespace ThreeTorus

/-- Rounding is in the slow Fourier slope, not a translation of the fast variable. -/
def passageSlope (κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) : ℝ := κ*(j:ℝ)/(n:ℝ)-α n

def passageCoefficient {Ω : Type*} (Φ : ℝ → ℝ) (A : Ω → ℝ → ℂ)
    (κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) (z : Ω) : ℂ :=
  ∫ x, A z x * Complex.exp (I * ((n:ℝ)*(Φ x-passageSlope κ α n j*x) : ℝ))

def passageLeading {Ω : Type*} (Φ : ℝ → ℝ) (A : Ω → ℝ → ℂ)
    (a b R κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) (z : Ω) : ℂ :=
  stationaryLeading Φ (A z) (a-R) (b+R) (passageSlope κ α n j) n

end ThreeTorus

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

/-- The precise old-amplitude Fourier coefficients in the passage chart. -/
def passageFourierInput (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (a θ : UnitAddCircle) : ℂ :=
  A (θ,a)*fourier m (H θ)

def exactPassageCoeff (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) : ℂ :=
  fourierCoeff (passageFourierInput m H A a) j

def retainedPassage (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ)
    (χ : ℤ → UnitAddCircle → ℝ) (ψ : UnitAddCircle → ℝ) (x : TripleTorus) : ℂ :=
  ∑ j ∈ S, (ψ x.2.1:ℂ)*(χ j x.2.1:ℂ)*exactPassageCoeff m H A j x.2.1*
    fourier m x.2.2*fourier j x.1

end ThreeTorus

namespace ThreeTorus

open Function
/-- Zero-extended Jacobian density on a single injective good arc. -/
def branchDensity (I : Set ℝ) (J g D q : ℝ → ℝ) (y : ℝ) : ℝ :=
  (J '' I).indicator (fun y => q (g y)/|D (g y)|) y

/-- The normalized physical-frequency mass used in (W-definition). -/
def stationaryWeight (I : Set ℝ) (J : ℝ → ℝ) (A : ℝ → ℂ) : ℝ → ℝ :=
  branchDensity I J (invFunOn J I) (deriv J) (fun u => ‖A u‖^2)

/-- The branch Jacobian with an arbitrary compact slow parameter space. -/
def branchFamily {Ω : Type*} (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × Ω → ℝ)
    (p : ℝ × Ω) : ℝ := by
  classical
  exact if p.1 ∈ J '' I then F (invFunOn J I p.1,p.2)/|deriv J (invFunOn J I p.1)| else 0

open scoped NNReal
def roundingMass (W : ℝ → UnitAddCircle → ℝ) (n : ℕ) (e : ℝ) : ℝ :=
  (n:ℝ)⁻¹ * ∑' j : ℤ, ∫ a : UnitAddCircle,
    |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

/-- The usual interval representative of a circle weight, with zero extension. -/
def circleDensityLift (o : ℝ) (q : UnitAddCircle → ℝ) : ℝ → ℝ :=
  (Ioc o (o+1)).indicator (fun x => q (x : UnitAddCircle))

/-- The manuscript kernel K(s,y), including both signs of s. -/
def scaledBranchKernel (I : Set ℝ) (J g D q : ℝ → ℝ) (s y : ℝ) : ℝ :=
  |s|⁻¹*branchDensity I J g D q (y/s)

/-- The actual unfolded spectral density of a retained angular mode, of mass q da.
The argument q₀ is its zero-extended representative in the jitter good arc. -/
def unfoldedModeDensity (I : Set ℝ) (J g D q₀ : ℝ → ℝ) (n j t : ℝ) : ℝ :=
  scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j)

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
namespace ThreeTorus

/-- Parametrized old-frequency Jacobian density, extended by zero off its branch. -/
def branchKernel (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if p.1 ∈ J '' I then F (invFunOn J I p.1,p.2) / |deriv J (invFunOn J I p.1)| else 0

/-- The exact Jacobian kernel for the affine-on-the-good-arc neutral jitter. -/
def affineKernel (F : ℝ × ℝ → ℝ) (L β s y : ℝ) : ℝ :=
  (|s| * L)⁻¹ * F (s,(y/s-β)/L)

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace ThreeTorus

def samplingWindow (x : ℝ) (M : ℕ) : Finset ℤ :=
  Finset.Icc (⌊x⌋-(M:ℤ)-1) (⌊x⌋+(M:ℤ)+1)

end ThreeTorus

namespace ThreeTorus

/-- Exact progression j=h+kP; no divisibility restriction on the passage integer. -/
def sampledResidueKernel (K : ℝ → ℝ → ℝ) (P : ℕ) (h : ℤ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℤ, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P)

def fineResidueKernel (K : ℝ → ℝ → ℝ) (P : ℕ) (h : ℤ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℤ, K t ((n:ℝ)*t-h-k*P)

end ThreeTorus

namespace ThreeTorus

/-- General smooth jitter kernel. The source's old-frequency variable is the
second coordinate of F; the first is the new slow-coordinate good arc. -/
def passageBranchKernel (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) : ℝ → ℝ → ℝ :=
  affineKernel (fun p => branchKernel I J F (p.2,p.1)) 1 0

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- The exact circle weights of one retained passage mode. -/
noncomputable def retainedCircleWeight (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (c : ℕ → ℤ → UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a : UnitAddCircle) : ℝ :=
  ψ a^2*χ ((j:ℝ)/n) a^2*‖c n j a‖^2

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- The actual cutoff old-frequency Jacobian in real coordinates. The first
coordinate is the new slow coordinate; the second is the old frequency. -/
noncomputable def stationaryCutoffLift (C : Set ℝ) (J : ℝ → ℝ)
    (A : ℝ × ℝ → ℂ) (ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ψ p.1^2*stationaryWeight C J (fun x => A (x,p.1)) p.2

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

/-- The actual period-one lattice sum used to fold an unfolded temporal density. -/
def periodizedReal (q : ℝ → ℝ) (x : ℝ) : ℝ := ∑' k : ℤ, q (x+k)

def foldCircleDensity (q : ℝ → ℝ) : UnitAddCircle → ℝ :=
  AddCircle.liftIoc 1 0 (periodizedReal q)

def intUnitEquiv : ℤ ≃ AddSubgroup.zmultiples (1:ℝ) :=
  Equiv.ofInjective (fun n : ℤ => n • (1:ℝ)) (zsmul_left_strictMono (by norm_num : 0 < (1:ℝ))).injective

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Transmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Law averaging and weighted errors, folded packet transmission, and concrete signal-circle comparison. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

def quantileCircleJitter {δ : ℝ} (ρ : ℝ → ℝ) (c : LawCutoffs δ) : UnitAddCircle → ℝ :=
  (periodize_periodic (fun a => c.ξ a*quantile ρ a)).lift

/-- The finite retained spectral density of one actual signed Fourier packet. -/
def exactRetainedPacketDensity (I : Set ℝ) (J₀ : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) : UnitAddCircle → ℝ :=
  foldCircleDensity (fun t => ∑ j ∈ S,
    unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
      (circleDensityLift 0 (retainedCircleWeight ψ χ
        (fun n j => exactPassageCoeff m (H n) A j) n j)) n j t)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

/-- The exact three-mode index signal, in the source's positive-moment convention. -/
noncomputable def signalCircleModel (P : ℕ) (γ B : ℝ) (d : ℝ → ℂ) (m : ℤ) (z : UnitAddCircle) : ℝ := by
  classical
  exact 1+2*((if IsUnit (m : ZMod P) then (γ:ℂ)*d ((m:ℝ)/B) else 0)*fourier (-1) z).re

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_NeutralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neutral lattice sampling, retained support, and stationary image separation. -/

section

/-! The two exact support separations in the passage and stage construction.
No spectral or asymptotic separation is substituted for actual disjoint sets. -/
noncomputable section
open Set Function
open scoped Topology
namespace ThreeTorus

/-- A stationary image of an amplitude support. The pair records frequency
and the unchanged slow coordinate. -/
def stationaryImage (m : ℤ) (V : ℝ → ℝ) (K : Set (ℝ × UnitAddCircle)) :
    Set (ℝ × UnitAddCircle) :=
  (fun p : ℝ × UnitAddCircle => ((m:ℝ)*V p.1,p.2)) '' K

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section
open Set Function Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- The literal new amplitude at a retained angular mode. -/
def retainedAmplitude (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (p : UnitAddCircle × UnitAddCircle) : ℂ :=
  (ψ p.1:ℂ)*(χ ((j:ℝ)/n) p.1:ℂ)*exactPassageCoeff m (H n) A j p.1*fourier m p.2

end ThreeTorus
end
end
end
end
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

/-- The literal real lift of a retained coefficient weight. The smooth cutoff
is taken before the final passage integer, as in the source. -/
def realRetainedWeight (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (x : ℝ) : ℝ :=
  ψ₀ x^2*χ ((j:ℝ)/n) x^2*‖exactPassageCoeff m (H n) A j x‖^2

lemma continuous_of_continuous_lift {Y : Type*} [TopologicalSpace Y]
    {f : UnitAddCircle → Y} (hf : Continuous (fun x : ℝ => f (x:UnitAddCircle))) :
    Continuous f :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr hf

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded common primitives, neutral and quantile families, exact indices, signal passages, and support tracking. -/

section

/-! Closure of the literal output coefficient class under a passage.
The next passage uses these very coefficients, rather than new placeholders. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

def retainedRealCore (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (u : ℝ) : ℂ :=
  (ψ₀ u:ℂ)*(χ s (u:UnitAddCircle):ℂ)*exactPassageCoeff m H A j (u:UnitAddCircle)

def retainedRealAmplitude (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ)
    (b : UnitAddCircle) (u : ℝ) : ℂ :=
  retainedRealCore ψ₀ χ m H A s j u*fourier m b

end ThreeTorus

end
end

section

/-! The second exact support separation, applied to the literal coefficients
of the first passage. No abstract output-support or disjoint-index oracle is
assumed. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

abbrev PassageOutputIndex {ι : Type*} (S : ι → Finset ℤ) := Σ i, {j // j ∈ S i}

def passageOutputCore {ι : Type*} (S : ι → Finset ℤ) (ψ₀ : ℝ → ℝ)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (m : ι → ℤ)
    (H : UnitAddCircle → UnitAddCircle) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (n : ℕ) (i : PassageOutputIndex S) : ℝ → ℂ :=
  retainedRealCore ψ₀ (χ i.1) (m i.1) H (A i.1) ((i.2.val:ℝ)/n) i.2.val

end ThreeTorus
end
end

section

/-! A concrete closed class for finite passage iteration.  The constructor
below uses the literal retained amplitudes; it does not postulate a next
packet state or any of its analytic regularity. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- All input data used by the proved simultaneous passage theorems.  No
asymptotic estimate, transport, density, or conclusion is a field. -/
structure PassagePackets (ι : Type*) where
  m : ι → ℤ
  nonzero : ∀ i, m i ≠ 0
  A : ι → UnitAddCircle × UnitAddCircle → ℂ
  A₀ : ι → UnitAddCircle → ℝ → ℂ
  o : ℝ
  l : ℝ
  u : ℝ
  R : ℝ
  lo : o ≤ l
  uo : u ≤ o+1
  lu : l ≤ u
  Rpos : 0 < R
  lift_matches : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x:UnitAddCircle),a) = A₀ i a x
  two : ∀ i a, ContDiff ℝ 2 (A₀ i a)
  continuous_lift : ∀ i, Continuous (A₀ i).uncurry
  continuous_deriv : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2)
  smooth_lift : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : ℝ × ℝ => A₀ i (p.2:UnitAddCircle) p.1)
  support_lift : ∀ i a, support (A₀ i a) ⊆ Ioc l u
  continuous_amplitude : ∀ i, Continuous (A i)
  smooth_amplitude : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : ℝ × ℝ => A i (p.1,p.2))
  V : ℝ → ℝ
  periodic : Periodic V 1
  smooth_speed : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V
  positive_deriv : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x

def PassagePackets.SpareIndependent {ι : Type*} (F : PassagePackets ι) : Prop :=
  (∀ i a x, ‖F.A₀ i a x‖ = ‖F.A₀ i 0 x‖) ∧
    ∀ i u a, ‖F.A i (u,a)‖ = ‖F.A i (u,0)‖

end ThreeTorus
end
end

section

/-! A genuine signal passage, not an abstract transmission oracle. The signal
prime modulus and strength bound precede all packet scales; one sufficiently
large integral carrier fixes the explicit positive law, and the SAME literal
retained coefficients satisfy geometry, physical and spectral conclusions. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

universe u

/-- The full conclusion of the actual quantile passage. This abbreviation
contains geometry, exact Fourier coefficients, all moments, and both errors;
its constructor below assumes no one of these output conclusions. -/
def ActualQuantileFamily {ι : Type*}
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (A₀ : ι → UnitAddCircle → ℝ → ℂ) (V : ℝ → ℝ) (m : ι → ℤ)
    (l u R : ℝ) (ρ : ℝ → ℝ) {δ : ℝ} (c : LawCutoffs δ)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (g : ι → UnitAddCircle → ℝ) (ε : ℝ) : Prop :=
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
    (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      let ψ := neutralCircleCutoff c
      let J := quantileCircleJitter ρ c
      let J₀ := lawJitter ρ c
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
        Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily V J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily V J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → ∀ i j, j ∈ S n i → j ≠ 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n) a = 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          0 < n ∧ ∀ i,
          let f := retainedPassage (m i) (H n) (A i) (S n i) (fun j => χ i ((j:ℝ)/n)) ψ
          let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i) (S n i) n
          let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x) (A₀ i 0)
          (∫ x : TripleTorus, ‖packet (m i) (A i) x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
            8*δ*(∫ u, ‖A i (u,0)‖^2 ∂AddCircle.haarAddCircle)+η ∧
          (∫ z, |p z-foldCircleDensity w z*g i ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
            (∫ s, w s)*(4*δ+ε)+η ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
          (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
            ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
          (∀ j u a, ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,a)‖ =
            ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed finite packet states, canonical densities, residue reindexing, anchors, reflection, clipping, and state tracking. -/

section

/-! Concrete finite-packet input data and the support bookkeeping used by
iteration. Field regularity is inherited from literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

def core (i : ι) : Set ℝ := tsupport (F.A₀ i 0)

/-- Adding an integral carrier changes no temporal eigenfrequency modulo one. -/
def carrier (c : ℤ) : PassagePackets ι := { F with
  V := fun x => (c:ℝ)+F.V x
  periodic := fun x => by dsimp; rw [F.periodic x]
  smooth_speed := contDiff_const.add F.smooth_speed
  positive_deriv := fun x hx => by
    simpa only [deriv_const_add] using F.positive_deriv x hx }

end PassagePackets
end ThreeTorus
end
end

section

/-! Canonical smooth density of a literal passage-state packet.  These are
computed from the actual amplitude and speed; no spectral property is a field. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

def weight (i : ι) : ℝ → ℝ :=
  stationaryWeight (Icc (F.l-F.R) (F.u+F.R)) (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i 0)

def density (i : ι) : UnitAddCircle → ℝ := foldCircleDensity (F.weight i)

end PassagePackets
end ThreeTorus
end
end

section

/-! Actual conjugation data, invariant cutoff choices, and canonical spectral
reflection. No symmetry of an approximate model is substituted for reality of
the packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

/-- The entire increasing good arc, including its relation to the lifted
support interval. The excluded length is exactly `2*δ`. -/
def GoodArc (δ : ℝ) : Prop :=
  F.o = 0 ∧ δ < F.l ∧ F.u < 1-δ ∧
    ∀ x ∈ Ioo δ (1-δ), 0 < deriv F.V x

structure Reflection (τ : ι → ι) : Prop where
  index : ∀ i, F.m (τ i) = -F.m i
  amplitude : ∀ i p, F.A (τ i) p = conj (F.A i p)
  lift : ∀ i a x, F.A₀ (τ i) a x = conj (F.A₀ i a x)

end PassagePackets

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι κ : Type*} (F : PassagePackets ι)

def cylinderCore (i : ι) : Set (ℝ × UnitAddCircle) :=
  tsupport (fun p : ℝ × UnitAddCircle => F.A₀ i p.2 p.1)

/-- Multiply the literal torus amplitudes by smooth disjoint cylinder
cutoffs and retain their actual lifts. All passage regularity is derived. -/
def clipped (q : κ → ι) (χ : κ → ℝ × UnitAddCircle → ℝ)
    (hχ : ∀ k, CylinderSmooth (χ k)) (hc : ∀ k, HasCompactSupport (χ k))
    (hs : ∀ k, support (χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) : PassagePackets κ where
  m := fun k => F.m (q k)
  nonzero := fun k => F.nonzero (q k)
  A := fun k p => (cylinderTorusCutoff (χ k) p:ℂ)*F.A (q k) p
  A₀ := fun k a x => (χ k (x,a):ℂ)*F.A₀ (q k) a x
  o := F.o
  l := F.l
  u := F.u
  R := F.R
  lo := F.lo
  uo := F.uo
  lu := F.lu
  Rpos := F.Rpos
  lift_matches := by
    intro k a x hx
    rw [cylinderTorusCutoff_eq (hs k) hx,F.lift_matches (q k) a x hx]
  two := by
    intro k a
    have hh := (cylinder_smooth_regular (hχ k)).1 a
    exact ((Complex.ofRealCLM.contDiff.comp hh).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤))).mul (F.two (q k) a)
  continuous_lift := by
    intro k
    exact (Complex.continuous_ofReal.comp ((hχ k).continuous.comp continuous_swap)).mul
      (F.continuous_lift (q k))
  continuous_deriv := by
    intro k
    have he (p : UnitAddCircle × ℝ) :
        deriv (fun x => (χ k (x,p.1):ℂ)*F.A₀ (q k) p.1 x) p.2 =
          Complex.ofReal (deriv (fun x => χ k (x,p.1)) p.2)*F.A₀ (q k) p.1 p.2 +
          (χ k (p.2,p.1):ℂ)*deriv (F.A₀ (q k) p.1) p.2 := by
      have hχd := ((cylinder_smooth_regular (hχ k)).1 p.1).differentiable (by simp) p.2
      have hFd := (F.two (q k) p.1).differentiable (by norm_num) p.2
      have hx : HasDerivAt (fun x => (χ k (x,p.1):ℂ))
          (Complex.ofReal (deriv (fun x => χ k (x,p.1)) p.2)) p.2 :=
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ hχd.hasDerivAt
      exact (hx.mul hFd.hasDerivAt).deriv
    simp_rw [he]
    exact ((Complex.continuous_ofReal.comp ((cylinder_smooth_regular (hχ k)).2.2.comp continuous_swap)).mul
      (F.continuous_lift (q k))).add
      ((Complex.continuous_ofReal.comp ((hχ k).continuous.comp continuous_swap)).mul (F.continuous_deriv (q k)))
  smooth_lift := fun k => (Complex.ofRealCLM.contDiff.comp (hχ k)).mul (F.smooth_lift (q k))
  support_lift := by
    intro k a x hx
    apply F.support_lift (q k) a
    intro hz
    exact hx (by simp [hz])
  continuous_amplitude := fun k => (Complex.continuous_ofReal.comp
    (cylinderTorusCutoff_continuous (hχ k) (hc k))).mul (F.continuous_amplitude (q k))
  smooth_amplitude := fun k => (Complex.ofRealCLM.contDiff.comp
    (cylinderTorusCutoff_smooth (hχ k) (hc k))).mul (F.smooth_amplitude (q k))
  V := F.V
  periodic := F.periodic
  smooth_speed := F.smooth_speed
  positive_deriv := F.positive_deriv

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

def marginalWeight (i : ι) (s : ℝ) : ℝ :=
  ∫ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s ∂AddCircle.haarAddCircle

def marginalDensity (i : ι) : UnitAddCircle → ℝ := foldCircleDensity (F.marginalWeight i)

end PassagePackets
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite passage geometry families, physical charts, and all-jet bounds. -/

section

/-! Bookkeeping for an ACTUAL geometric passage family. All fields are produced
by the unconditional neutral/signal theorems, not assumed as a main theorem
interface. This keeps the geometric data attached during finite iteration. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure PassageGeometryFamily (V : ℝ → ℝ) where
  c : ℕ
  c_pos : 0 < c
  Δ : ℕ → ℝ
  H : ℕ → UnitAddCircle → UnitAddCircle
  J : UnitAddCircle → ℝ
  J₀ : ℝ → ℝ
  Jmatch : ∀ x : ℝ, J (x:UnitAddCircle) = J₀ x
  Jcontinuous : Continuous J
  delta_bound : ∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹
  delta_tendsto : Tendsto Δ atTop (𝓝 0)
  Hcontinuous : ∀ n, Continuous (H n)
  Hformula : ∀ n (x : ℝ), H n (x:UnitAddCircle) =
    ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+V t)+Δ n*x):UnitAddCircle)
  geometry : ∀ n : ℕ, let σ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
    Smooth (torusPassage (H n) σ) ∧ Smooth (torusPassage (H n) σ).symm ∧
      MeasurePreserving (torusPassage (H n) σ) μ μ
  graph : ∀ n, 0 < n → ∀ x : Cover,
    torusPassage (H n) (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) (project x) =
      project (passageFamily (fun t => (c:ℝ)+V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
    (torusPassage (H n) (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle))).symm (project x) =
      project (passageFamily (fun t => (c:ℝ)+V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)
  convergence : ∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
    TendstoUniformlyOn
      (fun (n : ℕ) x => iteratedFDeriv ℝ d
        (passageFamily (fun t => (c:ℝ)+V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
      (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*((c:ℝ)+V (y 1)),y 1,y 2]) x)
      atTop K

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)
def scale (B : ℝ) (n : ℕ) : ℝ := (n:ℝ)*g.c*B
lemma scale_pos {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) : 0 < g.scale B n := by
  unfold scale
  exact mul_pos (mul_pos (by exact_mod_cast hn) (by exact_mod_cast g.c_pos)) hB
end PassageGeometryFamily

/-- The linked support displacement of an actual next state. The old support
point is shared by the index and every temporal comparison. -/
def StateTracks {ι κ : Type*} (F : PassagePackets ι) (G : PassagePackets κ)
    (parent : κ → ι) (B B' η : ℝ) : Prop :=
  ∀ i, ∃ x ∈ F.core (parent i),
    |(G.m i:ℝ)/B'-(F.m (parent i):ℝ)/B| < η ∧
    ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
      ((F.m (parent i):ℝ)*F.V x:UnitAddCircle) < η

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)

/-- The integer carrier contributes only a deck translation. Removing it
makes the limit the literal old twist lift, including at derivative order 0. -/
def correctedFamily (r : ℝ) (p : ℝ × ℝ) (x : Cover) : Cover :=
  passageFamily (fun t => (g.c:ℝ)+V t) g.J₀ r p x - ![r*(g.c:ℝ),0,0]

end PassageGeometryFamily
end ThreeTorus
end
end

section

/-! Global smooth cover charts with independently chosen deck representatives
for the two signs. This makes the corrected physical passage lift compatible
with further coordinate changes, rather than losing the integer carrier. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def tripleProject (x : Cover) : TripleTorus := torusTriple (project x)

def coverTwist (V : ℝ → ℝ) (r : ℝ) (x : Cover) : Cover :=
  ![x 0+r*V (x 1),x 1,x 2]

def coverChart (h : ℝ → ℝ) (x : Cover) : Cover := ![x 1,x 2,x 0-h (x 1)]
def coverChartInv (h : ℝ → ℝ) (x : Cover) : Cover := ![x 2+h (x 0),x 0,x 1]

def coverDeck (k : ℤ) (x : Cover) : Cover := ![x 0+(k:ℝ),x 1,x 2]

lemma smooth_coverChart {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coverChart h) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverChart] <;> fun_prop

lemma smooth_coverChartInv {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coverChartInv h) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverChartInv] <;> fun_prop

lemma smooth_coverDeck (k : ℤ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coverDeck k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverDeck] <;> fun_prop

lemma tripleProject_coverDeck (k : ℤ) (x : Cover) : tripleProject (coverDeck k x) = tripleProject x := by
  change (((x 0+(k:ℝ):ℝ):UnitAddCircle),(x 1:UnitAddCircle),(x 2:UnitAddCircle)) = _
  rw [AddCircle.coe_add]
  have hz : ((k:ℝ):UnitAddCircle) = 0 := by
    rw [← mul_one (k:ℝ),← zsmul_eq_mul,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]
  rw [hz,add_zero]
  rfl

lemma coverChart_graph {h : ℝ → ℝ} {H : UnitAddCircle → UnitAddCircle}
    (hH : ∀ x : ℝ, H (x:UnitAddCircle) = (h x:UnitAddCircle)) (x : Cover) :
    tripleProject (coverChart h x) = passageChart H (tripleProject x) := by
  change ((x 1:UnitAddCircle),(x 2:UnitAddCircle),((x 0-h (x 1):ℝ):UnitAddCircle)) =
    ((x 1:UnitAddCircle),(x 2:UnitAddCircle),(x 0:UnitAddCircle)+(-H (x 1:UnitAddCircle)))
  rw [AddCircle.coe_sub,hH,sub_eq_add_neg]

lemma coverChartInv_graph {h : ℝ → ℝ} {H : UnitAddCircle → UnitAddCircle}
    (hH : ∀ x : ℝ, H (x:UnitAddCircle) = (h x:UnitAddCircle)) (x : Cover) :
    tripleProject (coverChartInv h x) = (passageChart H).symm (tripleProject x) := by
  change (((x 2+h (x 0):ℝ):UnitAddCircle),(x 0:UnitAddCircle),(x 1:UnitAddCircle)) =
    ((x 2:UnitAddCircle)-(-H (x 0:UnitAddCircle)),(x 0:UnitAddCircle),(x 1:UnitAddCircle))
  rw [AddCircle.coe_add,hH,sub_neg_eq_add]

structure PhysicalFrame where
  chart : Equiv.Perm TripleTorus
  forward : Cover → Cover
  backward : ℤ → Cover → Cover
  forward_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) forward
  backward_smooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (backward k)
  forward_graph : ∀ x, tripleProject (forward x) = chart (tripleProject x)
  backward_graph : ∀ k x, tripleProject (backward k x) = chart.symm (tripleProject x)

namespace PhysicalFrame

def ident : PhysicalFrame where
  chart := Equiv.refl _
  forward := id
  backward := fun _ => id
  forward_smooth := contDiff_id
  backward_smooth := fun _ => contDiff_id
  forward_graph := fun _ => rfl
  backward_graph := fun _ _ => rfl

def mapLift (F : PhysicalFrame) (V : ℝ → ℝ) (k : ℤ) : Cover → Cover :=
  F.backward k ∘ coverTwist V (k:ℝ) ∘ F.forward

end PhysicalFrame

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)

def primitive (n : ℕ) (x : ℝ) : ℝ := ∫ t in 0..x, (n:ℝ)*((g.c:ℝ)+V t+g.Δ n)

lemma primitive_smooth (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g.primitive n) :=
  contDiff_real_primitive (contDiff_const.mul ((contDiff_const.add hV).add contDiff_const))

lemma primitive_matches (hV : Continuous V) (n : ℕ) (x : ℝ) :
    g.H n (x:UnitAddCircle) = (g.primitive n x:UnitAddCircle) := by
  rw [g.Hformula,primitive,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (f := fun t => (g.c:ℝ)+V t) (g := fun _ => g.Δ n) ((continuous_const.add hV : Continuous (fun t => (g.c:ℝ)+V t)).intervalIntegrable 0 x)
      (continuous_const.intervalIntegrable 0 x)]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm (g.Δ n) x]

end PassageGeometryFamily

namespace PhysicalFrame

def next (F : PhysicalFrame) {V : ℝ → ℝ} (g : PassageGeometryFamily V)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (n : ℕ) : PhysicalFrame where
  chart := F.chart.trans (passageChart (g.H n))
  forward := coverChart (g.primitive n) ∘ F.forward
  backward := fun k => F.backward k ∘ coverDeck (-k*(g.c:ℤ)) ∘ coverChartInv (g.primitive n)
  forward_smooth := (smooth_coverChart (g.primitive_smooth hV n)).comp F.forward_smooth
  backward_smooth := fun k => (F.backward_smooth k).comp ((smooth_coverDeck _).comp
    (smooth_coverChartInv (g.primitive_smooth hV n)))
  forward_graph := by
    intro x
    dsimp only [Function.comp_apply,Equiv.trans_apply]
    rw [coverChart_graph (g.primitive_matches hV.continuous n),F.forward_graph]
  backward_graph := by
    intro k x
    dsimp only [Function.comp_apply,Equiv.symm_trans_apply]
    rw [F.backward_graph,tripleProject_coverDeck,coverChartInv_graph (g.primitive_matches hV.continuous n)]

end PhysicalFrame
end ThreeTorus
end
end

section

/-! Finite summation and composition estimates in the original physical L².
These let the literal per-packet passages be assembled without replacing their
vectors by independent spectral models. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def physicalError (f g : TripleTorus → ℂ) : ℝ :=
  ∫ x, ‖f x-g x‖^2 ∂tripleVolume

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PredictionModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block tests, diagonal predictions, centering, and stability of finite-color models. -/

section

/-! Actual Laurent tests for source 04, using the fixed pre-block densities,
centering function and previous estimator. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockTotal {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (z : UnitAddCircle) : ℝ :=
  ∑ r, p r z

def blockWeights {m : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (r : Fin m) (z : UnitAddCircle) : ℝ := p r z / blockTotal p z

def blockTagMean {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (z : UnitAddCircle) : ℂ := ∑ r, (blockWeights p r z : ℂ)*b r

/-- The exact polynomial lower bound, not the non-polynomial square root. -/
def blockSqrtTest {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q : UnitAddCircle → ℂ) (n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℝ :=
  let R := blockMixture (fun r => blockWeights p r z) (fun r => b r-q z) n ell y
  Real.sqrt (blockTotal p z) * (1+(R-1)/2-(R-1)^2)

def blockPhaseEstimator (q : UnitAddCircle → ℂ) (n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℂ :=
  q z+((n:ℂ)*(ell:ℂ))⁻¹*∑ i, fourier 1 (y i)

def blockErrorTest {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q A : UnitAddCircle → ℂ) (k n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℝ :=
  ∑ r, p r z * blockProduct n ell (b r-q z) y *
    ‖A z+blockPhaseEstimator q n ell z y-((k:ℂ)+1)*b r‖^2

end ThreeTorus
end
end

section

/-! Transfer of the two actual block tests to a common temporal diagonal. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockPreviousError {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (A : UnitAddCircle → ℂ) (k : ℕ) (z : UnitAddCircle) : ℝ :=
  ∑ r, p r z*‖A z-(k:ℂ)*b r‖^2

end ThreeTorus
end
end

section

/-! Exact finite-frequency model step for source 04.  Both phase tests are
selected simultaneously from the actual pre-block data; no probability law
for the whole diagonal is assumed. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockModelDensity {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q : UnitAddCircle → ℂ) (n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℝ :=
  ∑ r, p r z*blockProduct n ell (b r-q z) y

end ThreeTorus
end
end

section

/-! Explicit smooth centering of the actual pre-block tag field.  Positive
regularization avoids any regularity assumption on the quotient at its zero set. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockNumerator {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (z : UnitAddCircle) : ℂ := ∑ r, (p r z:ℂ)*b r

def blockCenter {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (epsilon : ℝ) (z : UnitAddCircle) : ℂ :=
  blockNumerator p b z / (blockTotal p z+epsilon:ℝ)

end ThreeTorus
end
end

section

/-! Quantitative passage from the fixed pre-block model to actual color
 densities, source 04:239--286 and 409--437. No geometric approximation oracle
 is introduced: these are deterministic L1 stability estimates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def colorL1Distance {m : ℕ} (p g : Fin m → UnitAddCircle → ℝ) : ℝ :=
  ∑ r, ∫ z, |p r z-g r z| ∂phaseHaar

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TrackedPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refresh and residue estimates, physical aggregates, tracked producers, pair/color aggregates, and colored states. -/

section

/-! Deterministic refresh--transmit estimate (03-signals, equation
`signal-refresh-error`).  Residues are the residues of the ACTUAL refreshed
indices, and the coefficient comparison is only required on their support.
No independence of the phase variable is used. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Summed residue discrepancy, for one color. -/
def refreshResidueError {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) (p : ι → UnitAddCircle → ℝ) (q : UnitAddCircle → ℝ) (z : UnitAddCircle) : ℝ :=
  ∑ h, |(∑ i, if r i = h then p i z else 0)-q z/Fintype.card κ|

def refreshSignalAggregate {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (r : ι → κ) (H : Finset κ) (p : ι → UnitAddCircle → ℝ) (c : ι → ℂ)
    (γ : ℝ) (e : UnitAddCircle → ℂ) (z : UnitAddCircle) : ℝ :=
  (∑ i, p i z)+2*γ*(e z*(∑ i, if r i ∈ H then (p i z:ℂ)*c i else 0)).re

end ThreeTorus
end
end

section

/-! Exact arithmetic conversion of refreshed integer residues to the unit
fraction used in the signal. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

 def signalResidue (P : ℕ) [NeZero P] (j : ℤ) : Fin P :=
  ⟨(j:ZMod P).val,ZMod.val_lt _⟩

def signalUnitResidues (P : ℕ) [NeZero P] : Finset (Fin P) := by
  classical
  exact Finset.univ.filter (fun h => IsUnit (h.val:ZMod P))

/-- The source's exact positive strength after residue refresh. -/
def refreshedStrength (P : ℕ) [NeZero P] (γ : ℝ) : ℝ :=
  γ*((signalUnitResidues P).card:ℝ)/P

end ThreeTorus
end
end

section

/-! Physical vectors and spectral densities grouped by their actual source
packet. No spectral data is chosen independently of the literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

 def outputVector {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) (x : TripleTorus) : ℂ :=
  ∑ j : ↥(S i), packet (G.m ⟨i,j⟩) (G.A ⟨i,j⟩) x

 def outputDensity {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) (z : UnitAddCircle) : ℝ :=
  ∑ j : ↥(S i), G.density ⟨i,j⟩ z

end ThreeTorus
end
end

section

/-! Actual two-passage sums, still expressed in their literal final packet state. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

 def pairOutputVector {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (i : ι) (x : TripleTorus) : ℂ :=
  ∑ j : ↥(S i), outputVector K ⟨i,j⟩ x

 def pairOutputDensity {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (i : ι) (z : UnitAddCircle) : ℝ :=
  ∑ j : ↥(S i), outputDensity K ⟨i,j⟩ z

end ThreeTorus
end
end

section

/-! Literal color sums in the concrete packet state. Colors are labels, not
new independent spectral data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

variable {ι R : Type*} [Fintype ι] [DecidableEq R]

def colorVector (F : PassagePackets ι) (c : ι → R) (r : R) (x : TripleTorus) : ℂ :=
  ∑ i, if c i = r then packet (F.m i) (F.A i) x else 0

def colorDensity (F : PassagePackets ι) (c : ι → R) (r : R) (z : UnitAddCircle) : ℝ :=
  ∑ i, if c i = r then F.density i z else 0

end ThreeTorus
end
end

section

/-! A finite colored state and a pair record containing the two ACTUAL
smooth volume-preserving passage families. The existence theorem is derived
from the concrete neutral/signal producers, not supplied as an oracle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure ColoredState (R : Type) where
  Index : Type
  finite : Fintype Index
  packets : PassagePackets Index
  injective : Injective packets.m
  spare : packets.SpareIndependent
  color : Index → R
  scale : ℝ
  scale_pos : 0 < scale

attribute [instance] ColoredState.finite

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)
def density (r : R) : UnitAddCircle → ℝ := colorDensity C.packets C.color r
def vector (r : R) : TripleTorus → ℂ := colorVector C.packets C.color r

def InBand (b D margin : ℝ) : Prop :=
  ∀ i, b+margin ≤ |(C.packets.m i:ℝ)/C.scale| ∧
    |(C.packets.m i:ℝ)/C.scale| ≤ D-margin

def Matches (d : ℝ → ℂ) (a : R → UnitAddCircle → ℂ) (ω : ℝ) : Prop :=
  ∀ i x, x ∈ C.packets.core i →
    ‖d ((C.packets.m i:ℝ)/C.scale)-a (C.color i)
      ((C.packets.m i:ℝ)*C.packets.V x:UnitAddCircle)‖ ≤ ω
end ColoredState

/-- A pair retaining real passage geometry, not merely a density transition. -/
structure ColoredPair {R : Type} (C : ColoredState R) (N : ℕ) where
  refresh : PassageGeometryFamily C.packets.V
  indices : C.Index → Finset ℤ
  n : ℕ
  n_pos : 0 < n
  middle : PassagePackets (PassageOutputIndex indices)
  middle_injective : Injective middle.m
  middle_spare : middle.SpareIndependent
  middle_speed : middle.V = fun x => (1+refresh.J₀ x/n)/n
  middle_index : ∀ i, middle.m i = i.2.val
  transmit : PassageGeometryFamily middle.V
  indices' : PassageOutputIndex indices → Finset ℤ
  N_pos : 0 < N
  final : PassagePackets (PassageOutputIndex indices')
  final_injective : Injective final.m
  final_spare : final.SpareIndependent
  final_speed : final.V = fun x => (1+transmit.J₀ x/N)/N
  final_index : ∀ i, final.m i = i.2.val

namespace ColoredPair
variable {R : Type} {C : ColoredState R} {N : ℕ} (s : ColoredPair C N)
def output : ColoredState R where
  Index := PassageOutputIndex s.indices'
  finite := inferInstance
  packets := s.final
  injective := s.final_injective
  spare := s.final_spare
  color := C.color ∘ Sigma.fst ∘ Sigma.fst
  scale := s.transmit.scale (s.refresh.scale C.scale s.n) N
  scale_pos := s.transmit.scale_pos (s.refresh.scale_pos C.scale_pos s.n_pos) s.N_pos

def chart : Equiv.Perm TripleTorus :=
  (passageChart (s.refresh.H s.n)).trans (passageChart (s.transmit.H N))

def Tracks (η : ℝ) : Prop :=
  StateTracks C.packets s.final (Sigma.fst ∘ Sigma.fst) C.scale s.output.scale η
end ColoredPair

def colorFactor {R : Type} (a : R → UnitAddCircle → ℂ) (ell : ℝ) (N : ℤ)
    (r : R) (z : UnitAddCircle) : ℝ :=
  1+2*ell*(fourier (-1) (N • z)*a r z).re

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ColorBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block transfer, cofinal frequency trees, color-density products, finite iteration, and actual anchored blocks. -/

section

/-! Uniform-in-frequency estimator bounds and the correct parameter order for
transferring both block tests to actual densities. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockModelColors {m n : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q : UnitAddCircle → ℂ) (ell : ℝ) (L : Fin n → ℤ) : Fin m → UnitAddCircle → ℝ :=
  fun r z => p r z*blockProduct n ell (b r-q z) (fun i => L i • z)

def blockDiagonalEstimator {n : ℕ} (q : UnitAddCircle → ℂ) (ell : ℝ)
    (L : Fin n → ℤ) (z : UnitAddCircle) : ℂ :=
  blockPhaseEstimator q n ell z (fun i => L i • z)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def colorMass {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) : ℝ :=
  ∑ r, ∫ z, p r z ∂phaseHaar

def colorModel {m k : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (a : Fin m → UnitAddCircle → ℂ) (ell : ℝ) (L : Fin k → ℤ)
    (r : Fin m) (z : UnitAddCircle) : ℝ :=
  p r z*∏ j, colorFactor a ell (L j) r z

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- A finite trace contains actual neutral--signal pairs, including their
smooth geometry and exact intermediate speeds. -/
inductive ColoredPath {R : Type} (C : ColoredState R) :
    {k : ℕ} → (Fin k → ℤ) → ColoredState R → Equiv.Perm TripleTorus → Prop
  | nil : ColoredPath C (fun i => Fin.elim0 i) C (Equiv.refl TripleTorus)
  | snoc {k : ℕ} {L : Fin k → ℤ} {D : ColoredState R} {α : Equiv.Perm TripleTorus}
      (h : ColoredPath C L D α) {N : ℕ} (s : ColoredPair D N) :
      ColoredPath C (Fin.snoc L (N:ℤ)) s.output (α.trans s.chart)

end ThreeTorus
end
end

section
noncomputable section
open scoped BigOperators
namespace ThreeTorus

def iterationError (t : ℝ) (k : ℕ) : ℝ := ((k:ℝ)+1)*2^k*t

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure ColoredAnchor {R : Type} (C : ColoredState R) (n : ℕ) where
  geometry : PassageGeometryFamily C.packets.V
  indices : C.Index → Finset ℤ
  n_pos : 0 < n
  final : PassagePackets (PassageOutputIndex indices)
  final_injective : Injective final.m
  final_spare : final.SpareIndependent
  final_speed : final.V = fun x => (1+geometry.J₀ x/n)/n
  final_index : ∀ i, final.m i = i.2.val

namespace ColoredAnchor
variable {R : Type} {C : ColoredState R} {n : ℕ} (s : ColoredAnchor C n)
def output : ColoredState R where
  Index := PassageOutputIndex s.indices
  finite := inferInstance
  packets := s.final
  injective := s.final_injective
  spare := s.final_spare
  color := C.color ∘ Sigma.fst
  scale := n
  scale_pos := by exact_mod_cast s.n_pos

def chart : Equiv.Perm TripleTorus := passageChart (s.geometry.H n)
end ColoredAnchor

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet algebra and physical L2 metric estimates. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets

variable {ι κ : Type*}

def reindex (F : PassagePackets ι) (r : κ → ι) : PassagePackets κ where
  m := F.m ∘ r
  nonzero := fun i => F.nonzero (r i)
  A := F.A ∘ r
  A₀ := F.A₀ ∘ r
  o := F.o
  l := F.l
  u := F.u
  R := F.R
  lo := F.lo
  uo := F.uo
  lu := F.lu
  Rpos := F.Rpos
  lift_matches := fun i => F.lift_matches (r i)
  two := fun i => F.two (r i)
  continuous_lift := fun i => F.continuous_lift (r i)
  continuous_deriv := fun i => F.continuous_deriv (r i)
  smooth_lift := fun i => F.smooth_lift (r i)
  support_lift := fun i => F.support_lift (r i)
  continuous_amplitude := fun i => F.continuous_amplitude (r i)
  smooth_amplitude := fun i => F.smooth_amplitude (r i)
  V := F.V
  periodic := F.periodic
  smooth_speed := F.smooth_speed
  positive_deriv := F.positive_deriv

lemma reindex_good (F : PassagePackets ι) (r : κ → ι) {δ : ℝ} (h : F.GoodArc δ) :
    (F.reindex r).GoodArc δ := h

/-- Two arbitrary smooth packet lists in the SAME good arc and speed may be
merged. The coefficient supports are not required to be disjoint. -/
def append (F : PassagePackets ι) (G : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : F.GoodArc δ) (hG : G.GoodArc δ) (_hV : G.V=F.V) :
    PassagePackets (ι ⊕ κ) := by
  let l := min F.l G.l
  let u := max F.u G.u
  let R := min (l-δ) (1-δ-u)/4
  have hl : δ < l := lt_min hF.2.1 hG.2.1
  have hu : u < 1-δ := max_lt hF.2.2.1 hG.2.2.1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRl : 2*R < l-δ := by
    have ha : min (l-δ) (1-δ-u) ≤ l-δ := min_le_left _ _
    dsimp only [R]; linarith
  have hRu : 2*R < 1-δ-u := by
    have ha : min (l-δ) (1-δ-u) ≤ 1-δ-u := min_le_right _ _
    dsimp only [R]; linarith
  refine {
    m := Sum.elim F.m G.m
    nonzero := ?_
    A := Sum.elim F.A G.A
    A₀ := Sum.elim F.A₀ G.A₀
    o := 0
    l := l
    u := u
    R := R
    lo := hδ.trans hl.le
    uo := by linarith
    lu := (min_le_left _ _).trans (F.lu.trans (le_max_left _ _))
    Rpos := hR
    lift_matches := ?_
    two := ?_
    continuous_lift := ?_
    continuous_deriv := ?_
    smooth_lift := ?_
    support_lift := ?_
    continuous_amplitude := ?_
    smooth_amplitude := ?_
    V := F.V
    periodic := F.periodic
    smooth_speed := F.smooth_speed
    positive_deriv := ?_ }
  · intro i; cases i with
    | inl i => exact F.nonzero i
    | inr i => exact G.nonzero i
  · intro i a x hx; cases i with
    | inl i => exact F.lift_matches i a x (by rwa [hF.1])
    | inr i => exact G.lift_matches i a x (by rwa [hG.1])
  · intro i; cases i with
    | inl i => exact F.two i
    | inr i => exact G.two i
  · intro i; cases i with
    | inl i => exact F.continuous_lift i
    | inr i => exact G.continuous_lift i
  · intro i; cases i with
    | inl i => exact F.continuous_deriv i
    | inr i => exact G.continuous_deriv i
  · intro i; cases i with
    | inl i => exact F.smooth_lift i
    | inr i => exact G.smooth_lift i
  · intro i a x hx; cases i with
    | inl i => exact ⟨(min_le_left _ _).trans_lt (F.support_lift i a hx).1,
        (F.support_lift i a hx).2.trans (le_max_left _ _)⟩
    | inr i => exact ⟨(min_le_right _ _).trans_lt (G.support_lift i a hx).1,
        (G.support_lift i a hx).2.trans (le_max_right _ _)⟩
  · intro i; cases i with
    | inl i => exact F.continuous_amplitude i
    | inr i => exact G.continuous_amplitude i
  · intro i; cases i with
    | inl i => exact F.smooth_amplitude i
    | inr i => exact G.smooth_amplitude i
  · intro x hx
    exact hF.2.2.2 x ⟨by linarith [hx.1],by linarith [hx.2]⟩

lemma append_reflection (F : PassagePackets ι) (G : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : F.GoodArc δ) (hG : G.GoodArc δ) (hV : G.V=F.V)
    {τ : ι → ι} {σ : κ → κ} (hrF : F.Reflection τ) (hrG : G.Reflection σ) :
    (F.append G hδ hF hG hV).Reflection (Sum.map τ σ) := by
  constructor
  · intro i; cases i with
    | inl i => exact hrF.index i
    | inr i => exact hrG.index i
  · intro i p; cases i with
    | inl i => exact hrF.amplitude i p
    | inr i => exact hrG.amplitude i p
  · intro i a x; cases i with
    | inl i => exact hrF.lift i a x
    | inr i => exact hrG.lift i a x

/-- Finite regrouping of amplitudes. Used only for equal-mode terms; this
constructor does not assert an orthogonality or spectral identity. -/
def regroup [Fintype ι] (F : PassagePackets ι) (s : κ → Finset ι)
    (m : κ → ℤ) (hm : ∀ i, m i ≠ 0) (c : κ → ι → ℂ) : PassagePackets κ where
  m := m
  nonzero := hm
  A := fun i p => ∑ j ∈ s i, c i j * F.A j p
  A₀ := fun i a x => ∑ j ∈ s i, c i j * F.A₀ j a x
  o := F.o
  l := F.l
  u := F.u
  R := F.R
  lo := F.lo
  uo := F.uo
  lu := F.lu
  Rpos := F.Rpos
  lift_matches := fun i a x hx => Finset.sum_congr rfl (fun j _ => by rw [F.lift_matches j a x hx])
  two := fun i a => ContDiff.sum (fun j _ => contDiff_const.mul (F.two j a))
  continuous_lift := fun i => continuous_finsetSum _ (fun j _ => continuous_const.mul (F.continuous_lift j))
  continuous_deriv := by
    intro i
    have hd (a : UnitAddCircle) (j : ι) : Differentiable ℝ (F.A₀ j a) :=
      (F.two j a).differentiable (by norm_num)
    have he : (fun p : UnitAddCircle × ℝ => deriv (fun x => ∑ j ∈ s i, c i j * F.A₀ j p.1 x) p.2) =
        fun p => ∑ j ∈ s i, c i j * deriv (F.A₀ j p.1) p.2 := by
      funext p
      rw [deriv_fun_sum (fun j _ => (hd p.1 j).differentiableAt.const_mul _)]
      exact Finset.sum_congr rfl (fun j _ => deriv_const_mul _ (hd p.1 j).differentiableAt)
    rw [he]
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul (F.continuous_deriv j))
  smooth_lift := fun i => ContDiff.sum (fun j _ => contDiff_const.mul (F.smooth_lift j))
  support_lift := by
    intro i a x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    have hz : F.A₀ j a x = 0 := by by_contra hz; exact hn (F.support_lift j a hz)
    rw [hz,mul_zero]
  continuous_amplitude := fun i => continuous_finsetSum _ (fun j _ => continuous_const.mul (F.continuous_amplitude j))
  smooth_amplitude := fun i => ContDiff.sum (fun j _ => contDiff_const.mul (F.smooth_amplitude j))
  V := F.V
  periodic := F.periodic
  smooth_speed := F.smooth_speed
  positive_deriv := F.positive_deriv

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def physicalDist (f g : TripleTorus → ℂ) : ℝ := Real.sqrt (physicalError f g)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SymmetricPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflected neutral and signal producers, symmetric colors, physical control, and grouped cutoffs. -/

section

/-! The actual retained family, including its real compactly supported lifts,
preserves conjugation, with the literal inherited parent on its finite indices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def reflectedOutputIndex {ι : Type*} (τ : ι → ι) (S : ι → Finset ℤ)
    (hs : ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i) : PassageOutputIndex S → PassageOutputIndex S :=
  fun i => ⟨τ i.1,⟨-i.2.val,(hs i.1 (-i.2.val)).mpr (by simpa only [neg_neg] using i.2.property)⟩⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)

def Reflection (τR : R → R) : Prop :=
  ∃ τ : C.Index → C.Index, C.packets.Reflection τ ∧
    ∀ i, C.color (τ i) = τR (C.color i)

end ColoredState

end ThreeTorus
end
end

section

/-! Finite physical C-infinity restrictions, on both the map and inverse,
threaded through the actual refresh and transmission integer choices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure PhysicalJetData where
  size : ℕ
  sign : Fin size → ℤ
  domain : Fin size → Set Cover
  compact : ∀ i, IsCompact (domain i)
  order : Fin size → ℕ

namespace PhysicalJetData

def Close (Q : PhysicalJetData) (ε : ℝ) (F : PhysicalFrame) (V : ℝ → ℝ)
    (G : PhysicalFrame) (W : ℝ → ℝ) : Prop :=
  ∀ i x, x ∈ Q.domain i → dist
    (iteratedFDeriv ℝ (Q.order i) (G.mapLift W (Q.sign i)) x)
    (iteratedFDeriv ℝ (Q.order i) (F.mapLift V (Q.sign i)) x) ≤ ε

end PhysicalJetData

namespace ColoredPair
variable {R : Type} {C : ColoredState R} {N : ℕ} (s : ColoredPair C N)

def nextFrame (F : PhysicalFrame) : PhysicalFrame :=
  (F.next s.refresh C.packets.smooth_speed s.n).next s.transmit s.middle.smooth_speed N

end ColoredPair

end ThreeTorus
end
end

section

/-! Actual general neutral steps with arbitrary repeated indices, carrying the
literal coefficient formulas, physical charts and controlled cover jets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure NeutralStep {ι : Type*} (F : PassagePackets ι) where
  δ : ℝ
  cut : LawCutoffs δ
  L : ℝ
  δpos : 0 < δ
  δsmall : δ < 1/8
  Lpos : 0 < L
  geometry : PassageGeometryFamily F.V
  jitter : geometry.J₀ = neutralJitterReal cut L 0
  n : ℕ
  positive : 0 < n
  χ : ι → ℝ → UnitAddCircle → ℝ
  S : ι → Finset ℤ
  indices : ∀ i j, j ∈ S i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0
  final : PassagePackets (PassageOutputIndex S)
  spare : final.SpareIndependent
  speed : final.V = (fun x => (1+geometry.J₀ x/n)/n)
  mode : ∀ i, final.m i = i.2.val
  amplitude : ∀ i, final.A i = retainedAmplitude (neutralCircleCutoff cut) (χ i.1)
    (F.m i.1) geometry.H (F.A i.1) n i.2.val
  lift : ∀ i, final.A₀ i = retainedRealAmplitude cut.ψ (χ i.1) (F.m i.1) (geometry.H n)
    (F.A i.1) ((i.2.val:ℝ)/n) i.2.val
  good : final.GoodArc δ

namespace NeutralStep
variable {ι : Type*} {F : PassagePackets ι} (s : NeutralStep F)

def chart : Equiv.Perm TripleTorus := passageChart (s.geometry.H s.n)
def nextFrame (frame : PhysicalFrame) : PhysicalFrame :=
  frame.next s.geometry F.smooth_speed s.n

end NeutralStep

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Whitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coefficient-space spectral whitening, including the zero-density set. -/

section

/-!
Exact coefficient-space whitening, including the zero
set of the spectral density. The frequency map is arbitrary; for torus packets
it is `(m,u,a) ↦ m φ(u) mod 1`. No nonvanishing of the density is imposed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical
namespace ThreeTorus

/-- Squared modulus as a nonnegative measure density. -/
def energyWeight {X : Type*} (F : X → ℂ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (‖F x‖ ^ 2)

/-- The exact whitening coefficient, filling the density's zero set with a flat vector. -/
def whitenCoefficient {X Y : Type*} (ζ : X → Y) (p : Y → ℝ)
    (F V : X → ℂ) (x : X) : ℂ :=
  if p (ζ x) = 0 then V x else F x / (Real.sqrt (p (ζ x)) : ℂ)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FlatPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat support, finite packet L2 estimates, neutral selection, density invariance, and finite spectral whitening. -/

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology ENNReal NNReal
namespace ThreeTorus

/-- Packets of arbitrary L² coefficients have the same norm as their coefficients. -/
lemma memLp_packet {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (m : ℤ) : MemLp (packet m A) 2 tripleVolume := by
  have hbase : MemLp (fun x : TripleTorus => A x.2) 2 tripleVolume :=
    hA.comp_measurePreserving measurePreserving_snd
  apply hbase.congr_norm
  · exact hbase.aestronglyMeasurable.mul
      (((fourier m).continuous.comp continuous_fst).aestronglyMeasurable)
  · filter_upwards [] with x
    simp only [packet, norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- The representative in the old good-arc coordinate chart. -/
def circleRep (o : ℝ) (z : UnitAddCircle) : ℝ :=
  ((AddCircle.measurableEquivIoc 1 o) z).1

/-- The manuscript's endpoint-discontinuous coefficient. -/
def flatAmplitude (o l u : ℝ) (D : ℝ → ℝ) (z : UnitAddCircle) : ℂ :=
  ((Icc l u).indicator (fun x => Real.sqrt (|D x|/2)) (circleRep o z) : ℝ)

end ThreeTorus
end
end

section

/-! Finite measurable packet coefficient families, needed for whitening the
actual output of reflected prediction. The physical vectors remain literal
finite packet sums, not arbitrary Hilbert-space replacements. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

abbrev coefficientVolume : Measure (ι × (UnitAddCircle × UnitAddCircle)) :=
  Measure.count.prod slowVolume

def finitePacketVector (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (x : TripleTorus) : ℂ := ∑ i, packet (m i) (A i) x

def coefficientFrequency (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (x : ι × (UnitAddCircle × UnitAddCircle)) : UnitAddCircle := m x.1 • φ x.2.1

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma memLp_finitePacketVector {m : ι → ℤ} {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) : MemLp (finitePacketVector m A) 2 tripleVolume := by
  exact memLp_finsetSum _ (fun i _ => memLp_packet (hA i) (m i))

lemma integrable_coefficient_normsq {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    Integrable (fun x : ι × (UnitAddCircle × UnitAddCircle) => ‖A x.1 x.2‖^2) coefficientVolume := by
  refine (integrable_prod_iff ?_).2 ⟨?_,?_⟩
  · exact ((measurable_from_prod_countable_right hAm).norm.pow_const 2).aestronglyMeasurable
  · exact Eventually.of_forall (fun i => (hA i).integrable_norm_pow (by norm_num))
  · exact Integrable.of_finite

lemma coefficient_memLp {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    MemLp (fun x : ι × (UnitAddCircle × UnitAddCircle) => A x.1 x.2) 2 coefficientVolume := by
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_from_prod_countable_right hAm).aestronglyMeasurable).2
      (integrable_coefficient_normsq hAm hA)

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace NeutralStep
variable {ι κ : Type*} {F : PassagePackets ι} (s : NeutralStep F)

/-- Restrict a simultaneously transported finite family to a chosen root
list. This is the SAME physical passage, not another existence choice. -/
def reindex (r : κ → ι) : NeutralStep (F.reindex r) where
  δ := s.δ
  cut := s.cut
  L := s.L
  δpos := s.δpos
  δsmall := s.δsmall
  Lpos := s.Lpos
  geometry := s.geometry
  jitter := s.jitter
  n := s.n
  positive := s.positive
  χ := fun k => s.χ (r k)
  S := fun k => s.S (r k)
  indices := fun k => s.indices (r k)
  final := s.final.reindex (fun p => ⟨r p.1,p.2⟩)
  spare := ⟨fun _k => s.spare.1 _,fun _k => s.spare.2 _⟩
  speed := s.speed
  mode := fun _k => s.mode _
  amplitude := fun _k => s.amplitude _
  lift := fun _k => s.lift _
  good := s.final.reindex_good _ s.good

end NeutralStep
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} [Fintype ι] (F : PassagePackets ι)

abbrev ModeIndex := ↥(Finset.univ.image F.m)

def modeNeg {τ : ι → ι} (hr : F.Reflection τ) : F.ModeIndex → F.ModeIndex :=
  fun k => ⟨-k.val, by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp k.property
    exact Finset.mem_image.mpr ⟨τ i,Finset.mem_univ _,by rw [hr.index,hi]⟩⟩

/-- Regroup a literal weighted family by its actual nonzero angular mode.
Only algebra is used: no cross-family orthogonality is asserted. -/
def modeSum (b : ι → ℂ) : PassagePackets F.ModeIndex :=
  F.regroup (fun _ => Finset.univ) Subtype.val
    (fun k => by obtain ⟨i,_,hi⟩ := Finset.mem_image.mp k.property; rw [← hi]; exact F.nonzero i)
    (fun k i => if F.m i=k.val then b i else 0)

end PassagePackets
end ThreeTorus
end
end

section

/-! Exact measurable spectral calculus for the literal finite packets.
This is the bridge from the energy-map whitening to the
actual physical packet family. It does not assume a spectral constructor. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The spectral measure is the pushforward of the coefficients' actual energy. -/
def finitePacketSpectralMeasure (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) : Measure UnitAddCircle :=
  (coefficientVolume.withDensity (energyWeight (fun x => A x.1 x.2))).map
    (coefficientFrequency φ m)

end FinitePacket
end ThreeTorus
end
end

section

/-! Whitening in the literal finite angular-packet family. All operations act on
its actual coefficient functions; angular collisions with the flat filler are
allowed, provided both are indexed by the same injective angular list. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def whitenPackets (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (p : UnitAddCircle → ℝ) (A V : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (i : ι) (ua : UnitAddCircle × UnitAddCircle) : ℂ :=
  whitenCoefficient (coefficientFrequency φ m) p (fun x => A x.1 x.2)
    (fun x => V x.1 x.2) (i,ua)

end FinitePacket
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trigonometric approximation, spectral calculus, density distances, and reflected clipping. -/

section

/-! Literal measurable finite-packet spectral calculus and Laurent approximation.
No abstract unitary is substituted for the actual twist. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Actual spectral multiplication of every retained angular coefficient. -/
def multiplyPackets (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (a : UnitAddCircle → ℂ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (i : ι) (ua : UnitAddCircle × UnitAddCircle) : ℂ := a (m i • φ ua.1)*A i ua

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Function
open scoped BigOperators
namespace ThreeTorus

/-- Nonzero reflected mode lists are exactly their positive half and its
negative copy. This equivalence is used BEFORE the ratio cutoff choices. -/
def reflectedIndexEquiv {ι : Type*} (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (τ : ι → ι) (hτ : Involutive τ) (hr : ∀ i, m (τ i) = -m i) :
    ({i : ι // 0 < m i} ⊕ {i : ι // 0 < m i}) ≃ ι where
  toFun := Sum.elim Subtype.val (fun i => τ i.val)
  invFun := fun i => if h : 0 < m i then Sum.inl ⟨i,h⟩ else
    Sum.inr ⟨τ i,by rw [hr]; have hn := hm i; omega⟩
  left_inv := by
    intro i
    rcases i with i|i
    · dsimp only [Sum.elim_inl]
      rw [dite_eq_left i.property]
    · have hn : ¬ 0 < m (τ i.val) := by rw [hr]; have hp := i.property; omega
      dsimp only [Sum.elim_inr]
      rw [dite_eq_right hn]
      exact congrArg Sum.inr (Subtype.ext (hτ i.val))
  right_inv := by
    intro i
    dsimp only
    split_ifs
    · rfl
    · exact hτ i

end ThreeTorus
end
end

section

noncomputable section
open Function Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus
variable {ι : Type*} [Fintype ι]

abbrev PositiveIndex (m : ι → ℤ) := {i : ι // 0 < m i}

def reflectedVector (m : ι → ℤ) (τ : ι → ι)
    (A : PositiveIndex m → UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) : ℂ :=
  (∑ i, packet (m i.val) (A i) x)+(∑ i, packet (m (τ i.val)) (fun p => conj (A i p)) x)

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

variable {ι : Type} [Fintype ι] (F : PassagePackets ι)
variable (J : PositiveIndex F.m → Type)

abbrev RatioPositive := Σ i : PositiveIndex F.m, J i
abbrev RatioIndex := RatioPositive F J ⊕ RatioPositive F J

def ratioRoot (τ : ι → ι) : RatioIndex F J → ι :=
  Sum.elim (fun p => p.1.val) (fun p => τ p.1.val)

def ratioCut (χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ) :
    RatioIndex F J → ℝ × UnitAddCircle → ℝ :=
  Sum.elim (fun p => χ p.1 p.2) (fun p => χ p.1 p.2)

def ratioTag (b : ∀ i, J i → ℂ) : RatioIndex F J → ℂ :=
  Sum.elim (fun p => b p.1 p.2) (fun p => conj (b p.1 p.2))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real perturbation, smooth cylinder approximation, tensor preparation, real packet families, and two neutral separations. -/

section

/-!
Concrete preparation with null zero sets for the packet ratios.
The perturbation parameter is REAL and works simultaneously for all packets.
No stage, spectral conclusion, or transport theorem is assumed here.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ThreeTorus

/-- The weighted coefficient measure in the constant-ratio preparation. -/
def coefficientMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℂ) : Measure X :=
  μ.withDensity (fun x => (‖F x‖₊ ^ 2 : ℝ≥0∞))

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
namespace ThreeTorus

/-- Fundamental cylinder with the exact normalized slow-coordinate measure. -/
def cylinderVolume (o : ℝ) : Measure (ℝ × UnitAddCircle) :=
  (volume.restrict (Ioc o (o+1))).prod phaseHaar

def cylinderToSlow (p : ℝ × UnitAddCircle) : UnitAddCircle × UnitAddCircle := (p.1,p.2)

def slowToCylinder (o : ℝ) (p : UnitAddCircle × UnitAddCircle) : ℝ × UnitAddCircle :=
  (circleRep o p.1,p.2)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

local instance instMeasureSpaceUnitAddCircle_solutions_2 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : Type*} [Fintype d]

def multiTrigPolynomial (c : (d → ℤ) →₀ ℂ) : C(UnitAddTorus d,ℂ) :=
  c.sum (fun k a => a • UnitAddTorus.mFourier k)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

local instance instMeasureSpaceUnitAddCircle_solutions_3 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def slowPair : UnitAddTorus (Fin 2) ≃ᵐ (UnitAddCircle × UnitAddCircle) :=
  MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- A finite literal real smooth packet list. Repeated frequencies are permitted;
no orthogonality is part of this bookkeeping structure. -/
structure RealPacketFamily where
  Index : Type
  finite : Fintype Index
  data : PassagePackets Index
  neg : Index → Index
  invol : Involutive neg
  reflected : data.Reflection neg
attribute [instance] RealPacketFamily.finite
namespace RealPacketFamily
variable (F : RealPacketFamily)
def vector : TripleTorus → ℂ := finitePacketVector F.data.m F.data.A
def density : UnitAddCircle → ℝ := fun z => ∑ i, F.data.marginalDensity i z

def append (G : RealPacketFamily) {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : F.data.GoodArc δ) (hG : G.data.GoodArc δ) (hV : G.data.V=F.data.V) : RealPacketFamily where
  Index := F.Index ⊕ G.Index
  finite := inferInstance
  data := F.data.append G.data hδ hF hG hV
  neg := Sum.map F.neg G.neg
  invol := by intro i; cases i with
    | inl i => exact congrArg Sum.inl (F.invol i)
    | inr i => exact congrArg Sum.inr (G.invol i)
  reflected := F.data.append_reflection G.data hδ hF hG hV F.reflected G.reflected

end RealPacketFamily
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

local instance instMeasureSpaceUnitAddCircle_solutions_4 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : Type*} [Fintype d]

def conjugateCoefficients (c : (d → ℤ) →₀ ℂ) : (d → ℤ) →₀ ℂ :=
  Finsupp.mapDomain (fun k => -k) (Finsupp.mapRange conj (map_zero _) c)

end ThreeTorus
end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus
/-- The coordinate convention used by the analytic packet calculations. -/
def toTriple : Torus ≃ᵐ TripleTorus :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitAddCircle) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl UnitAddCircle)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)))

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

local instance instMeasureSpaceUnitAddCircle_solutions_5 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev TensorIndex := Fin 3 → ℤ

def tensorCharacter (k : TensorIndex) (x : TripleTorus) : ℂ :=
  fourier (k 0) x.1 * fourier (k 1) x.2.1 * fourier (k 2) x.2.2

def tensorPolynomial (c : TensorIndex →₀ ℂ) (x : TripleTorus) : ℂ :=
  c.sum (fun k a => a*tensorCharacter k x)

/-- Angular split, first slow split, and the final centered slow average. -/
def tensorAngular (c : TensorIndex →₀ ℂ) : TensorIndex →₀ ℂ :=
  c.filter (fun k => k 0 ≠ 0)
def tensorMiddle (c : TensorIndex →₀ ℂ) : TensorIndex →₀ ℂ :=
  c.filter (fun k => k 0 = 0 ∧ k 1 ≠ 0)
def tensorLast (c : TensorIndex →₀ ℂ) : TensorIndex →₀ ℂ :=
  c.filter (fun k => k 0 = 0 ∧ k 1 = 0)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Build literal smooth passage input coefficients from compact smooth
cylinder cutoffs and smooth periodic two-torus coefficients. -/
def cutoffPackets {ι : Type*} (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (C : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hCc : ∀ i, Continuous (C i))
    (hCs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C i (p.1,p.2)))
    (χ : ι → ℝ × UnitAddCircle → ℝ) (hχs : ∀ i, CylinderSmooth (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i))
    (o l u R : ℝ) (hχo : ∀ i, support (χ i) ⊆ Ioo o (o+1) ×ˢ univ)
    (hχI : ∀ i, support (χ i) ⊆ Ioc l u ×ˢ univ)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) : PassagePackets ι where
  m := m
  nonzero := hm
  A := fun i p => (cylinderTorusCutoff (χ i) p:ℂ)*C i p
  A₀ := fun i a x => (χ i (x,a):ℂ)*C i ((x:UnitAddCircle),a)
  o := o
  l := l
  u := u
  R := R
  lo := hlo
  uo := huo
  lu := hlu
  Rpos := hR
  lift_matches := fun i a x hx => by rw [cylinderTorusCutoff_eq (hχo i) hx]
  two := by
    intro i a
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun p : ℝ × UnitAddCircle => (χ i p:ℂ)*C i (p.1,p.2)) ∘ cylinderProjection) :=
      (Complex.ofRealCLM.contDiff.comp (hχs i)).mul (hCs i)
    exact ((cylinder_smooth_regular hs).1 a).of_le (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤))
  continuous_lift := by
    intro i
    exact ((Complex.continuous_ofReal.comp (hχs i).continuous).mul
      ((hCc i).comp (QuotientAddGroup.continuous_mk.prodMap continuous_id))).comp continuous_swap
  continuous_deriv := by
    intro i
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun p : ℝ × UnitAddCircle => (χ i p:ℂ)*C i (p.1,p.2)) ∘ cylinderProjection) :=
      (Complex.ofRealCLM.contDiff.comp (hχs i)).mul (hCs i)
    exact (cylinder_smooth_regular hs).2.2.comp continuous_swap
  smooth_lift := fun i => (Complex.ofRealCLM.contDiff.comp (hχs i)).mul (hCs i)
  support_lift := by
    intro i a x hx
    exact (hχI i (show χ i (x,a) ≠ 0 from fun hz => hx (by simp [hz]))).1
  continuous_amplitude := fun i => (Complex.continuous_ofReal.comp
    (cylinderTorusCutoff_continuous (hχs i) (hχc i))).mul (hCc i)
  smooth_amplitude := fun i => (Complex.ofRealCLM.contDiff.comp
    (cylinderTorusCutoff_smooth (hχs i) (hχc i))).mul (hCs i)
  V := V
  periodic := hVp
  smooth_speed := hVs
  positive_deriv := hVd

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TensorPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-arc cutoffs, scalar and tensor packet constructors, fiber insertion, and initial dense tests. -/

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

def tensorSupportNeg {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ↥c.support → ↥c.support := fun k => ⟨-k.val,by
      rw [Finsupp.mem_support_iff,hc]
      exact (map_ne_zero (starRingEnd ℂ)).mpr (Finsupp.mem_support_iff.mp k.property)⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def rotatedTensor (c : TensorIndex →₀ ℂ) (a b d : Fin 3) (x : TripleTorus) : ℂ :=
  ∑ k ∈ c.support, c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2)
def tensorBudget (c : TensorIndex →₀ ℂ) : ℝ := ∑ k ∈ c.support, ‖c k‖
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma continuous_triple_memLp {f : TripleTorus → ℂ} (hf : Continuous f) : MemLp f 2 tripleVolume :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Prediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laurent prediction, flat packet filling, color energies, measurable packets, reflected smoothing, and prepared pairs. -/

section

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A literal finite Laurent polynomial in the Koopman orbit of a measurable packet vector. -/
def finitePacketLaurent (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (c : ℤ →₀ ℂ) (x : TripleTorus) : ℂ :=
  ∑ k ∈ c.support, c k*finitePacketVector m A (twistIter φ k x)

end FinitePacket
end ThreeTorus
end
end

section

/-! The literal flat coefficient, with its two pushforward measures
retained and with an arbitrarily large angular index. This permits adjoining
it to any given finite packet list without changing that list's vector. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators ComplexConjugate
namespace ThreeTorus

section Padding
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def paddedAngular (m : ι → ℤ) (k : ℤ) : ι ⊕ Bool → ℤ :=
  Sum.elim m (fun b => if b then k else -k)

def paddedOld (A : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    ι ⊕ Bool → UnitAddCircle × UnitAddCircle → ℂ := Sum.elim A (fun _ _ => 0)

def paddedFlat (V : UnitAddCircle × UnitAddCircle → ℂ) :
    ι ⊕ Bool → UnitAddCircle × UnitAddCircle → ℂ := Sum.elim (fun _ _ => 0) (fun _ => V)

end Padding
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

def totalVector (x : TripleTorus) : ℂ := ∑ r, C.vector r x

end ColoredState
end ThreeTorus
end
end

section

/-! Literal finite measurable packet states. The spectral measure is defined
from coefficient energy, not carried as an unspecified abstract spectrum. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

structure MeasurablePackets where
  Index : Type
  finite : Fintype Index
  m : Index → ℤ
  injective : Injective m
  nonzero : ∀ i, m i ≠ 0
  A : Index → UnitAddCircle × UnitAddCircle → ℂ
  measurable : ∀ i, Measurable (A i)
  memLp : ∀ i, MemLp (A i) 2 slowVolume

attribute [instance] MeasurablePackets.finite
namespace MeasurablePackets
variable (F : MeasurablePackets)
def vector := finitePacketVector F.m F.A
def spectrum (φ : UnitAddCircle → UnitAddCircle) : Measure UnitAddCircle :=
  ∑ i, packetSpectralMeasure φ (F.m i) (F.A i)

def Reflection (τ : F.Index → F.Index) : Prop :=
  Involutive τ ∧ (∀ i, F.m (τ i) = -F.m i) ∧ ∀ i ua, F.A (τ i) ua = conj (F.A i ua)

def Supported (l u : ℝ) : Prop :=
  ∀ i, support (F.A i) ⊆ ((fun x : ℝ => (x : UnitAddCircle)) '' Icc l u) ×ˢ univ

lemma vector_memLp : MemLp F.vector 2 tripleVolume := memLp_finitePacketVector F.memLp
end MeasurablePackets

namespace ColoredState
variable {n : ℕ} (C : ColoredState (Fin n))
def measurablePackets : MeasurablePackets where
  Index := C.Index
  finite := C.finite
  m := C.packets.m
  injective := C.injective
  nonzero := C.packets.nonzero
  A := C.packets.A
  measurable := fun i => (C.packets.continuous_amplitude i).measurable
  memLp := fun i => (C.packets.continuous_amplitude i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end ColoredState
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FiniteBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric anchored blocks, unconditional block production, physical mass, and estimator regularity. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- An actual finite block, centered using its ACTUAL input packet densities.
The finite chain contains the anchor and every signal/refresh pair. -/
structure ActualColoredBlock {m : ℕ} (C E : ColoredState (Fin m))
    (β : Equiv.Perm TripleTorus) (D : UnitAddCircle → ℂ) : Prop where
  witness : ∃ n : ℕ, ∃ ell : ℝ, 0 < n ∧ 0 < ell ∧
    ∃ q : UnitAddCircle → ℂ, Continuous q ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)) ∧
      (∀ z, q (-z) = conj (q z)) ∧
      ∃ N : ℕ, ∃ s : ColoredAnchor C N, ∃ L : Fin n → ℤ,
      ∃ α : Equiv.Perm TripleTorus, ColoredPath s.output L E α ∧
        β = s.chart.trans α ∧ D = blockDiagonalEstimator q ell L

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def physicalEnergy (f : TripleTorus → ℂ) : ℝ := ∫ x, ‖f x‖^2 ∂tripleVolume

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_CyclicPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated blocks, prediction budgets, physical Laurent polynomials, and actual cyclic approximation. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- A finite trace of actual centered blocks. `A` is exactly the sum of their
estimators. This data retains each anchor and each physical passage. -/
inductive ActualColoredBlocks {m : ℕ} (C : ColoredState (Fin m)) :
    ColoredState (Fin m) → ℕ → Equiv.Perm TripleTorus → (UnitAddCircle → ℂ) → Prop
  | nil : ActualColoredBlocks C C 0 (Equiv.refl _) (fun _ => 0)
  | snoc {E F : ColoredState (Fin m)} {k : ℕ} {α β : Equiv.Perm TripleTorus}
      {A D : UnitAddCircle → ℂ} (h : ActualColoredBlocks C E k α A)
      (hb : ActualColoredBlock E F β D) :
      ActualColoredBlocks C F (k+1) (α.trans β) (fun z => A z+D z)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

/-- Literal packet spectral calculus, evaluated in the current coordinates. -/
def weightedVector (a : C.Index → UnitAddCircle → ℂ) (x : TripleTorus) : ℂ :=
  ∑ i, packet (C.packets.m i)
    (fun u => a i (C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle))*C.packets.A i u) x

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

/-- A finite Laurent polynomial in the actual twist Koopman operator. -/
def laurent (c : ℤ →₀ ℂ) (x : TripleTorus) : ℂ :=
  ∑ k ∈ c.support, c k*C.totalVector
    (twistIter (fun u => (C.packets.periodic.lift u:UnitAddCircle)) k x)

end ColoredState
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ControlledBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical signal and derivative control through actual repeated blocks, cyclic prediction, and tag selection. -/

section

/-! Concrete finite colored iteration. The cofinal-frequency tree is built
from actual neutral--signal pairs. The error budget is fixed before the
initial anchor state and before any future packet index type is known. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def ColoredSignalControlledRealizes (b D : ℝ) (d : ℝ → ℂ) (γ ell : ℝ) : Prop :=
  ∀ (R : Type) [DecidableEq R], ∀ (C : ColoredState R),
    ∀ τR : R → R, C.Reflection τR →
    ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
    ∀ (a : R → UnitAddCircle → ℂ), (∀ r, Continuous (a r)) →
    ∀ ω : ℝ, 0 ≤ ω → C.Matches d a ω →
    ∀ (Q : PhysicalJetData) (F : PhysicalFrame) (ζ : ℝ), 0 < ζ →
    ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
    ∀ᶠ N : ℕ in atTop, ∃ s : ColoredPair C N, s.Tracks η ∧
      s.output.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ s.final.GoodArc δ) ∧ Q.Close ζ F C.packets.V (s.nextFrame F) s.final.V ∧ ∀ r,
      physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε ∧
      (∫ z, |s.output.density r z-C.density r z*colorFactor a ell (N:ℤ) r z| ∂phaseHaar) <
        2*γ*ω*(∫ z, C.density r z ∂phaseHaar)+ε

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace ColoredAnchor
variable {R : Type} {C : ColoredState R} {n : ℕ} (s : ColoredAnchor C n)

def nextFrame (F : PhysicalFrame) : PhysicalFrame :=
  F.next s.geometry C.packets.smooth_speed n

end ColoredAnchor

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Stages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-arc flattening, exact predicted whitening, unconditional one-stage construction, and stage states and successors. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma measurePreserving_shear {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {f : X → UnitAddCircle} (hf : Measurable f) :
    MeasurePreserving (fun x : UnitAddCircle × X => (x.1+f x.2,x.2))
      (AddCircle.haarAddCircle.prod ν) (AddCircle.haarAddCircle.prod ν) := by
  have hh := (MeasurePreserving.id ν).skew_product (g := fun (x : X) (θ : UnitAddCircle) => θ+f x)
    (measurable_snd.add (hf.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => map_add_right_eq_self AddCircle.haarAddCircle (f x)))
  exact Measure.measurePreserving_swap.comp (hh.comp Measure.measurePreserving_swap)

/-- Literal admissible states in physical coordinates. No successor or basis is
part of the data; successors are produced by the unconditional stage theorem. -/
structure StageState where
  frame : PhysicalFrame
  chart_cont : Continuous frame.chart
  chart_mp : MeasurePreserving frame.chart tripleVolume tripleVolume
  packets : MeasurablePackets
  reflected : ∃ τ, packets.Reflection τ
  V : ℝ → ℝ
  periodic : Periodic V 1
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V
  δ : ℝ
  l : ℝ
  u : ℝ
  δ_pos : 0 < δ
  δ_half : δ < 1/2
  δ_l : δ < l
  l_u : l < u
  u_δ : u < 1-δ
  increasing : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x
  supported : packets.Supported l u
  flat : packets.spectrum (fun z => (periodic.lift z : UnitAddCircle)) = phaseHaar

namespace StageState
variable (s : StageState)
def speed (z : UnitAddCircle) : UnitAddCircle := (s.periodic.lift z : UnitAddCircle)
lemma speed_cont : Continuous s.speed :=
  (AddCircle.continuous_mk' 1).comp (continuous_of_continuous_lift
    (by simpa only [Periodic.lift_coe] using s.smooth.continuous))
def chartHomeo : TripleTorus ≃ₜ TripleTorus := s.chart_cont.homeoOfEquivCompactToT2
lemma chart_symm_cont : Continuous s.frame.chart.symm := s.chartHomeo.symm.continuous
lemma chart_symm_mp : MeasurePreserving s.frame.chart.symm tripleVolume tripleVolume :=
  MeasurePreserving.symm s.chartHomeo.toMeasurableEquiv s.chart_mp

def twistEquiv (φ : UnitAddCircle → UnitAddCircle) : Equiv.Perm TripleTorus where
  toFun x := (x.1+φ x.2.1,x.2)
  invFun x := (x.1-φ x.2.1,x.2)
  left_inv x := by simp
  right_inv x := by simp

def mapPow (k : ℤ) : Equiv.Perm TripleTorus :=
  s.frame.chart.trans ((twistEquiv (fun z => k • s.speed z)).trans s.frame.chart.symm)

def vector : TripleTorus → ℂ := s.packets.vector ∘ s.frame.chart
lemma vector_memLp : MemLp s.vector 2 tripleVolume :=
  s.packets.vector_memLp.comp_measurePreserving s.chart_mp
abbrev L2 := Lp ℂ 2 tripleVolume
def vec : L2 := s.vector_memLp.toLp s.vector

lemma mapPow_cont (k : ℤ) : Continuous (s.mapPow k) := by
  change Continuous (fun x => s.frame.chart.symm
    ((s.frame.chart x).1 + k • s.speed (s.frame.chart x).2.1,
      (s.frame.chart x).2))
  exact s.chart_symm_cont.comp ((s.chart_cont.fst.add
    ((s.speed_cont.comp s.chart_cont.snd.fst).const_smul k)).prodMk s.chart_cont.snd)
lemma mapPow_mp (k : ℤ) : MeasurePreserving (s.mapPow k) tripleVolume tripleVolume :=
  s.chart_symm_mp.comp ((measurePreserving_shear ((s.speed_cont.measurable.const_smul k).comp measurable_fst)).comp s.chart_mp)

def orbit (k : ℤ) : L2 := Lp.compMeasurePreserving (s.mapPow k) (s.mapPow_mp k) s.vec

def laurent (c : ℤ →₀ ℂ) : L2 := c.sum (fun k a => a • s.orbit k)

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- A real bounded physical test. The dense test family will be constructed
explicitly; this structure only records the hypotheses of the one-stage lemma. -/
structure PhysicalTest where
  fn : C(TripleTorus,ℂ)
  real : ∀ x, conj (fn x)=fn x
  centered : ∫ x, fn x ∂tripleVolume=0
  bound : ∀ x, ‖fn x‖ ≤ 1
namespace PhysicalTest
variable (h : PhysicalTest)
lemma memLp : MemLp h.fn 2 tripleVolume := continuous_triple_memLp h.fn.continuous
def vec : StageState.L2 := h.memLp.toLp h.fn
end PhysicalTest

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SmoothLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-order local smooth jet limits, positive and negative iterate diagonal, cover descent, and volume preservation. -/

section

noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace ThreeTorus

/-- A canonical local limit; no pointwise convergence or smooth limit is assumed. -/
def incrementLimit {X F : Type*} [NormedAddCommGroup F] (f : ℕ → X → F) (x : X) : F :=
  f 0 x + ∑' n, (f (n+1) x-f n x)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace ThreeTorus

def tripleSection (z : TripleTorus) : Cover :=
  ![circleRep 0 z.1,circleRep 0 z.2.1,circleRep 0 z.2.2]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def jetIndices (N : ℕ) : Finset (ℤ × ℕ) :=
  (Finset.Icc (-(N:ℤ)) N).product (Finset.range (N+1))

def jetExhaustion (N : ℕ) : PhysicalJetData where
  size := Fintype.card ↥(jetIndices N)
  sign i := ((Fintype.equivFin ↥(jetIndices N)).symm i).val.1
  order i := ((Fintype.equivFin ↥(jetIndices N)).symm i).val.2
  domain _ := Metric.closedBall (0:Cover) (N+1)
  compact _ := isCompact_closedBall _ _

namespace StageState

def mapCont (s : StageState) (k : ℤ) : C(TripleTorus,TripleTorus) :=
  ⟨s.mapPow k,s.mapPow_cont k⟩

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace ThreeTorus

instance tripleVolume_regular : tripleVolume.Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure tripleVolume

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_DynamicsLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stage topology, genuine smooth limiting dynamics, initial stage, unconditional diagonal, and limiting moments. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace StageState

def coordinate (s : StageState) : L2 × (ℤ → C(TripleTorus,TripleTorus)) :=
  (s.vec,s.mapCont)
instance instTopologicalSpace : TopologicalSpace StageState := TopologicalSpace.induced coordinate inferInstance

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace ThreeTorus

/-- An actual smooth, volume preserving integer action on the physical torus.
This is limit DATA constructed below, not an assumption on a stage. -/
structure SmoothDynamics where
  map : ℤ → C(TripleTorus,TripleTorus)
  zero : ∀ x, map 0 x=x
  add : ∀ k j x, map (k+j) x=map k (map j x)
  mp : ∀ k, MeasurePreserving (map k) tripleVolume tripleVolume
  lift : ℤ → Cover → Cover
  smooth : ∀ k, ContDiff ℝ ∞ (lift k)
  graph : ∀ k x, tripleProject (lift k x)=map k (tripleProject x)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- The finite history is kept at every successor; no density or limit is
part of this bookkeeping data. -/
structure StageHistory (test : ℕ → PhysicalTest) (e : ℕ → ℝ) (n : ℕ) where
  stage : StageState
  coeff : ℕ → (ℤ →₀ ℂ)
  small : stage.δ < (e n)^2/8
  retained : ∀ i < n, dist (test i).vec (stage.laurent (coeff i)) < e i

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Hilbert space, L2 limiting real orbit, full test density, and complete physical basis. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace ThreeTorus

abbrev PhysicalL2 := StageState.L2

def physicalIntegral : PhysicalL2 →L[ℂ] ℂ := innerSL ℂ (Lp.const 2 tripleVolume (1:ℂ))
lemma physicalIntegral_apply (f : PhysicalL2) : physicalIntegral f=∫ x, f x ∂tripleVolume := by
  change inner ℂ (Lp.const 2 tripleVolume (1:ℂ)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 tripleVolume (1:ℂ)] with x hx
  simp only [hx,Function.const_apply,RCLike.inner_apply,map_one,mul_one]

def physicalMeanZero : Submodule ℂ PhysicalL2 := physicalIntegral.ker
lemma mem_physicalMeanZero (f : PhysicalL2) : f ∈ physicalMeanZero ↔ ∫ x, f x ∂tripleVolume=0 := by
  change physicalIntegral f=0 ↔ _
  rw [physicalIntegral_apply]

def physicalCenter (f : PhysicalL2) : PhysicalL2 :=
  f - physicalIntegral f • Lp.const 2 tripleVolume (1:ℂ)

def continuousCenter (g : C(TripleTorus,ℂ)) : C(TripleTorus,ℂ) :=
  g - ContinuousMap.const _ (∫ x, g x ∂tripleVolume)

namespace PhysicalTest
instance instTopologicalSpace : TopologicalSpace PhysicalTest := TopologicalSpace.induced PhysicalTest.fn ContinuousMap.compactOpen
instance instSecondCountableTopology : SecondCountableTopology PhysicalTest :=
  (Topology.IsInducing.induced PhysicalTest.fn).secondCountableTopology
instance instNonempty : Nonempty PhysicalTest := ⟨{
  fn := 0, real := by simp, centered := by simp, bound := by simp }⟩
end PhysicalTest

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace SmoothDynamics
variable (D : SmoothDynamics)

def homeo (k : ℤ) : TripleTorus ≃ₜ TripleTorus where
  toFun := D.map k
  invFun := D.map (-k)
  left_inv := by intro x; rw [← D.add,neg_add_cancel,D.zero]
  right_inv := by intro x; rw [← D.add,add_neg_cancel,D.zero]
  continuous_toFun := (D.map k).continuous
  continuous_invFun := (D.map (-k)).continuous

def orbit (f : PhysicalL2) (k : ℤ) : PhysicalL2 :=
  Lp.compMeasurePreserving (D.map k) (D.mp k) f

def laurent (f : PhysicalL2) (c : ℤ →₀ ℂ) : PhysicalL2 := c.sum (fun k a => a • D.orbit f k)
end SmoothDynamics

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SpectralTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measure-preserving torus transport, full mean-zero L2 isometry, ergodicity, and full circle spectral representation. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace SmoothDynamics
variable (D : SmoothDynamics)

/-- The produced physical action in the fixed torus coordinate convention. -/
def torusMap (k : ℤ) : Equiv.Perm Torus :=
  (torusTriple.toEquiv.trans (D.homeo k).toEquiv).trans torusTriple.symm.toEquiv
lemma torusMap_apply (k : ℤ) (x : Torus) : D.torusMap k x=
    torusTriple.symm (D.map k (torusTriple x)) := rfl
lemma torusMap_zero : D.torusMap 0=1 := by
  ext x
  simp only [torusMap_apply,D.zero,torusTriple.symm_apply_apply,Equiv.Perm.one_apply]
lemma torusMap_add (k j : ℤ) : D.torusMap (k+j)=D.torusMap k*D.torusMap j := by
  ext x
  simp only [torusMap_apply,Equiv.Perm.mul_apply,torusTriple.apply_symm_apply,D.add]

def torusAction : Multiplicative ℤ →* Equiv.Perm Torus where
  toFun k := D.torusMap k.toAdd
  map_one' := D.torusMap_zero
  map_mul' k j := D.torusMap_add k.toAdd j.toAdd

end SmoothDynamics
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- The coordinate change is a genuine isometry on the full L2 spaces. -/
def physicalToTorus : PhysicalL2 →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ torusTriple measurePreserving_torusTriple
def torusToPhysical : H →ₗᵢ[ℂ] PhysicalL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ torusTriple.symm
    (MeasurePreserving.symm torusTriple measurePreserving_torusTriple)
lemma physicalToTorus_ae (f : PhysicalL2) : physicalToTorus f =ᵐ[μ]
    fun x => f (torusTriple x) := Lp.coeFn_compMeasurePreserving f measurePreserving_torusTriple
lemma torusToPhysical_ae (g : H) : torusToPhysical g =ᵐ[tripleVolume]
    fun x => g (torusTriple.symm x) := Lp.coeFn_compMeasurePreserving g
      (MeasurePreserving.symm torusTriple measurePreserving_torusTriple)
lemma physicalToTorus_torusToPhysical (g : H) : physicalToTorus (torusToPhysical g)=g := by
  apply Lp.ext
  filter_upwards [physicalToTorus_ae (torusToPhysical g),
    measurePreserving_torusTriple.quasiMeasurePreserving.ae (torusToPhysical_ae g)] with x hx hy
  simpa only [torusTriple.symm_apply_apply] using hx.trans hy

lemma physicalToTorus_centered_iff (f : PhysicalL2) : physicalToTorus f ∈ meanZero ↔ f ∈ physicalMeanZero := by
  change (∫ x, physicalToTorus f x ∂μ)=0 ↔ _
  rw [mem_physicalMeanZero,integral_congr_ae (physicalToTorus_ae f),
    measurePreserving_torusTriple.integral_comp' ]
lemma torusToPhysical_centered_iff (g : H) : torusToPhysical g ∈ physicalMeanZero ↔ g ∈ meanZero := by
  rw [← physicalToTorus_centered_iff,physicalToTorus_torusToPhysical]

def physicalZeroToTorus : physicalMeanZero →ₗᵢ[ℂ] H₀ where
  toFun f := ⟨physicalToTorus f,(physicalToTorus_centered_iff f).mpr f.property⟩
  map_add' f g := Subtype.ext (map_add physicalToTorus (f:PhysicalL2) (g:PhysicalL2))
  map_smul' a f := Subtype.ext (map_smul physicalToTorus a (f:PhysicalL2))
  norm_map' f := physicalToTorus.norm_map f
lemma physicalZeroToTorus_surjective : Surjective physicalZeroToTorus := by
  intro g
  refine ⟨⟨torusToPhysical g,(torusToPhysical_centered_iff g).mpr g.property⟩,?_⟩
  exact Subtype.ext (physicalToTorus_torusToPhysical g)
def physicalZeroEquiv : physicalMeanZero ≃ₗᵢ[ℂ] H₀ :=
  LinearIsometryEquiv.ofSurjective physicalZeroToTorus physicalZeroToTorus_surjective

end ThreeTorus
end
end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma integral_comp_preserving {T : Torus → Torus} (hT : MeasurePreserving T μ μ) (g : H) :
    (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hm : AEStronglyMeasurable g (Measure.map T μ) := by
    rw [hT.map_eq]
    exact (Lp.memLp g).aestronglyMeasurable
  rw [← integral_map hT.measurable.aemeasurable hm, hT.map_eq]

/-- The actual Koopman operator, restricted to the full centered subspace. -/
def koopman {T : Torus → Torus} (hT : MeasurePreserving T μ μ) : H₀ →ₗᵢ[ℂ] H₀ where
  toFun f := ⟨Lp.compMeasurePreserving T hT f.1, by
    change ∫ x, Lp.compMeasurePreserving T hT f.1 x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_compMeasurePreserving f.1 hT)]
    exact (integral_comp_preserving hT f.1).trans f.2⟩
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact (Lp.compMeasurePreservingₗ ℂ T hT).map_smul c f.1
  norm_map' f := Lp.norm_compMeasurePreserving f.1 hT

/-- Circle coordinate multiplication, constructed on L² representatives. -/
def circleMul (n : ℤ) (f : CircleH) : CircleH :=
  ((Lp.memLp f).congr_norm
    ((fourier n).continuous.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z => by
      change ‖f z‖ = ‖fourier n z * f z‖
      rw [norm_mul, show ‖fourier n z‖ = 1 from Circle.norm_coe _, one_mul]))).toLp (fun z => fourier n z * f z)

lemma circleMul_ae (n : ℤ) (f : CircleH) :
    circleMul n f =ᵐ[AddCircle.haarAddCircle] fun z => fourier n z * f z :=
  MemLp.coeFn_toLp _

def circleMulLI (n : ℤ) : CircleH →ₗᵢ[ℂ] CircleH where
  toFun := circleMul n
  map_add' f g := by
    apply Lp.ext
    filter_upwards [circleMul_ae n (f+g), circleMul_ae n f, circleMul_ae n g,
      Lp.coeFn_add f g, Lp.coeFn_add (circleMul n f) (circleMul n g)] with z h₀ h₁ h₂ h₃ h₄
    simp only [Pi.add_apply] at h₃ h₄
    rw [h₀,h₄,h₁,h₂,h₃,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [circleMul_ae n (c • f), circleMul_ae n f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (circleMul n f)] with z h₀ h₁ h₂ h₃
    change circleMul n (c • f) z = (c • circleMul n f) z
    simp only [Pi.smul_apply, smul_eq_mul] at h₂ h₃
    rw [h₀,h₃,h₁,h₂]
    ring
  norm_map' f := by
    simp only [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [circleMul_ae n f] with z hz
    change ‖circleMul n f z‖ = ‖f z‖
    rw [hz, norm_mul, show ‖fourier n z‖ = 1 from Circle.norm_coe _, one_mul]

end ThreeTorus
end
end

end OAI
end


