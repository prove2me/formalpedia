-- Prove2me | Definitions.Def_YM_ChallengeSpec
-- name    : YM_ChallengeSpec
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T11:37:30.415215+00:00
-- url     : https://prove2.me/theorems/15befe48-97a4-4fb3-bf99-7e69f1ef47ba
-- title:
--   The joint Yang-Mills existence specification
-- statement:
--   States the target. Wilson regularity requires a positive asymptotic-freedom slope for $\beta/\log(1/a)$ and continuous gauge-invariant insertions with a fixed finite stencil. A **hierarchy** bundles a Wightman theory, finite-dimensional graded field spaces, a compact character space with a probability measure, correlation functions, an analytic continuation, OPE coefficients and a centered grade-four stress trace. Its properties combine: (i) Wilson convergence to the character-averaged correlations; (ii) reconstruction of a Wightman theory with faithfulness, permutation symmetry, smoothness off diagonals, character continuity, the mixture identity, and analytic continuation recovering the selected phase at ordered imaginary times; (iii) an all-orders separated operator product expansion with uniform remainder bounds; (iv) a trace test: the centered stress trace has short-distance two-point coefficient $3\dim\mathfrak g/\pi^4$ after multiplication by $r^8\log^2(1/r)$ and is not a finite sum of mass-shell Wick profiles. `JointExistence` asserts that every simple gauge group admits such a family and, for every volume sequence, a refinement carrying one hierarchy with all four properties.
-- source:
--   https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/ChallengeSpec.lean

import Definitions.Def_YM_PublicWilson

/-! The joint target. All correlation terms, including every spectator in the OPE,
are evaluations of one hierarchy. Finite lattice insertions precede every limit. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open Function Filter Set MeasureTheory TopologicalSpace
open scoped Topology BigOperators InnerProductSpace Distributions Classical NNReal ContDiff

/-- A fixed finite lattice stencil for each insertion works at every spacing and volume. -/
structure WilsonRegularity {g : GaugeGroup} (C : WilsonFamily g) : Prop where
  running : ∃ slope : ℝ, 0 < slope ∧ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ p, |C.beta N p / Real.log (C.mesh N)⁻¹ - slope| < ε
  continuous (N p v x) : Continuous (C.insertion N p v x)
  invariant (N p v x) (t : Site (C.period p * C.denominator N) → g.image) (U) :
    C.insertion N p v x (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) =
      C.insertion N p v x U
  localSupport (v : C.Token) : ∃ stencil : Finset (Axis → ℤ), ∀ N p (x : Site (C.period p * C.denominator N)),
    let sites := stencil.image fun z => (fun i => (z i : ZMod (C.period p * C.denominator N).val)) + x
    ∀ U V, (∀ e, e.1 ∈ sites → e.1 + Pi.single e.2 1 ∈ sites → U e = V e) →
      C.insertion N p v x U = C.insertion N p v x V

structure Hierarchy {g : GaugeGroup} (C : WilsonFamily g) where
  H : HilbertSpace
  labels : FieldLabels
  theory : WightmanTheory H labels
  Field : ℕ → Type
  [fieldAdd (d : ℕ) : NormedAddCommGroup (Field d)]
  [fieldSpace (d : ℕ) : NormedSpace ℂ (Field d)]
  [fieldFinite (d : ℕ) : FiniteDimensional ℂ (Field d)]
  toLabel (d : ℕ) : Field d →ₗ[ℂ] labels.carrier
  project : C.Token → (Σ d, Field d)
  Character : Type
  [characterMetric : MetricSpace Character]
  [characterSets : MeasurableSpace Character]
  [characterBorel : BorelSpace Character]
  [characterCompact : CompactSpace Character]
  phaseMeasure : Measure Character
  selected : Character
  correlation {n : ℕ} : Option Character → (Fin n → Σ d, Field d) → Points n → ℂ
  continuation {n : ℕ} : (Fin n → Σ d, Field d) → (Fin n → ℂ) → (Fin n → Space) → ℂ
  Channel : ℕ → Type
  [finiteChannels (d : ℕ) : Fintype (Channel d)]
  actor (d : ℕ) : Channel d → Field d
  coefficient {I : Type} [Fintype I] (a : I → Σ d, Field d) (j : ℕ) :
    Channel j → (I → Spacetime) → Spacetime → ℂ
  centeredTrace : Field 4
attribute [instance] Hierarchy.fieldAdd Hierarchy.fieldSpace Hierarchy.fieldFinite
  Hierarchy.finiteChannels Hierarchy.characterMetric Hierarchy.characterSets
  Hierarchy.characterBorel Hierarchy.characterCompact

namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
abbrev Tag := Σ d, T.Field d

/-- Enumerate the union of the insertion and spectator slots once, then read the hierarchy. -/
def grouped {I J : Type} [Fintype I] [Fintype J] (s : Option T.Character)
    (a : I → T.Tag) (x : I → Spacetime) (b : J → T.Tag) (y : J → Spacetime) : ℂ :=
  let slots := (Fintype.equivFin (I ⊕ J)).symm
  T.correlation s ((Sum.elim a b) ∘ slots) (WithLp.toLp 2 ((Sum.elim x y) ∘ slots))

def weight {I : Type} [Fintype I] (a : I → T.Tag) : ℝ := ∑ i, ((a i).1 : ℝ)

def Within {I : Type} (r M η : ℝ) (x : I → Spacetime) (o : Spacetime) : Prop :=
  (∀ i, ‖x i - o‖ ≤ M*r) ∧ (∀ i j, i ≠ j → η*r ≤ ‖x i - x j‖)
def Clear {J : Type} (o : Spacetime) (y : J → Spacetime) (c : ℝ) : Prop :=
  (∀ i, c ≤ ‖o - y i‖) ∧ (∀ i j, i ≠ j → c ≤ ‖y i - y j‖)

structure OperatorProductExpansion : Prop where
  coefficients {I : Type} [Fintype I] (a : I → T.Tag) (M η ε : ℝ) :
    0 ≤ M → 0 < η → 0 < ε → ∀ j (i : T.Channel j), ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ x o, Within r M η x o → ‖T.coefficient a j i x o‖ ≤ r ^ ((j:ℝ) - T.weight a - ε)
  remainder {I J : Type} [Fintype I] [Fintype J] (a : I → T.Tag) (b : J → T.Tag)
      (M η c ε : ℝ) : 0 ≤ M → 0 < η → 0 < c → 0 < ε → ∀ D : ℕ,
      ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x o y, Within r M η x o → Clear o y c → ∀ s,
      ‖T.grouped s a x b y -
        ∑ j : Fin (D+1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
          T.grouped s (fun _ : Unit => ⟨j.val,T.actor j.val i⟩) (fun _ => o) b y‖
        ≤ r ^ ((D:ℝ) + 1 - T.weight a - ε)

/-- Four-dimensional Euclidean spacetime used by the OPE estimates. -/
abbrev OPEPoint := EuclideanSpace ℝ (Fin 4)

/-- Ordered configurations of `n` insertion points. -/
abbrev OPEPoints (n : ℕ) := PiLp 2 (fun _ : Fin n => OPEPoint)

/-- Complex time coordinates of an analytically continued correlation. -/
abbrev OPEComplexTimes (n : ℕ) := Fin n → ℂ

/-- Spatial coordinates of an analytically continued correlation. -/
abbrev OPESpacePoints (n : ℕ) := Fin n → YangMills.Space

/-- The tube of complex times with strictly ordered imaginary parts. -/
def orderedTube (n : ℕ) : Set (OPEComplexTimes n) :=
  {z | StrictMono fun i ↦ (z i).im}

/-- Continue a real configuration into ordered imaginary-time directions. -/
def complexShift {n : ℕ} (r : ℝ) (height : Fin n → ℝ)
    (x : OPEPoints n) : OPEComplexTimes n :=
  fun i ↦ (YangMills.time (x.ofLp i) : ℂ) +
    ((r * height i : ℝ) : ℂ) * Complex.I

/-- The purely imaginary times associated with a Euclidean configuration. -/
def imaginaryTimes {n : ℕ} (x : OPEPoints n) : OPEComplexTimes n :=
  fun i ↦ (YangMills.time (x.ofLp i) : ℂ) * Complex.I

/-- Spatial coordinates of a Euclidean configuration. -/
def spatialPoints {n : ℕ} (x : OPEPoints n) : OPESpacePoints n :=
  fun i ↦ YangMills.spatial (x.ofLp i)

/-- The product test used to smear an `n`-point correlation. -/
def tensorTest {n : ℕ} (tests : Fin n → YangMills.TestFunction)
    (x : OPEPoints n) : ℂ :=
  ∏ i, tests i (x.ofLp i)

structure Reconstructed : Prop where
  axioms : T.theory.Axioms
  faithful : T.theory.fields.Faithful
  injective (d : ℕ) : Injective (T.toLabel d)
  acts : ∃ (a : T.Tag) (f : YangMills.TestFunction), T.theory.fields.field (T.toLabel a.1 a.2) f ≠ 0
  covers : Surjective (fun a : T.Tag => T.toLabel a.1 a.2)
  represents : Surjective T.project
  normalized : IsProbabilityMeasure T.phaseMeasure
  fullSupport : T.phaseMeasure.IsOpenPosMeasure
  permutation (s : Option T.Character) {n : ℕ} (a : Fin n → T.Tag)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) (π : Equiv.Perm (Fin n)) :
    T.correlation s (a ∘ π) (WithLp.toLp 2 (x.ofLp ∘ π)) = T.correlation s a x
  smooth (s : Option T.Character) {n : ℕ} (a : Fin n → T.Tag) :
    ContDiffOn ℝ ∞ (T.correlation s a) (WilsonFamily.separated n)
  characterContinuity {n : ℕ} (a : Fin n → T.Tag) (x : Points n)
      (h : x ∈ WilsonFamily.separated n) : Continuous (fun i => T.correlation (some i) a x)
  mixture {n : ℕ} (a : Fin n → T.Tag) (x : Points n) (h : x ∈ WilsonFamily.separated n) :
    (∫ i, T.correlation (some i) a x ∂T.phaseMeasure) = T.correlation none a x
  analytic {n : ℕ} (v : Fin n → T.Tag) (space : OPESpacePoints n) :
    DifferentiableOn ℂ (fun z => T.continuation v z space) (orderedTube n)
  root {n : ℕ} (v : Fin n → T.Tag) (x : Points n) (h : StrictMono fun i => time (x i)) :
    T.continuation v (imaginaryTimes x) (spatialPoints x) = T.correlation (some T.selected) v x
  boundary {n : ℕ} (v : Fin n → T.Tag) (height : Fin n → ℝ) (h : StrictMono height)
      (tests : Fin n → YangMills.TestFunction) :
    Tendsto (fun r => ∫ x : Points n, T.continuation v (complexShift r height x) (spatialPoints x) *
      tensorTest tests x) (𝓝[>] 0)
      (𝓝 (T.theory.fields.vacuumExpectation (fun i => T.toLabel (v i).1 (v i).2) tests))

/-- Two insertions on the time axis at -r/2 and r/2. -/
def timePair (r : ℝ) : Points 2 :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 (Fin.snoc (fun _ : Fin 3 => (0:ℝ))
    (Fin.append (fun _ : Fin 1 => -(r/2)) (fun _ : Fin 1 => r/2) i))
def traceTwo (r : ℝ) := T.correlation (some T.selected) (fun _ : Fin 2 => ⟨4,T.centeredTrace⟩) (timePair r)

/-- Elementary mass-shell kernels, including finite differential orders. -/
structure Mode where
  mass : ℝ≥0
  spatialOrder : ℕ
  timeOrder : ℕ
  numerator : Space → ℝ
  continuous : Continuous numerator
  homogeneous (p : Space) (r : ℝ) : 0 < r → numerator (r • p) = r^spatialOrder * numerator p
def Mode.kernel (m : Mode) (r : ℝ) (p : Space) : ℝ :=
  let E := Real.sqrt ((m.mass:ℝ)^2 + ‖p‖^2)
  1 / (2*E) * E^m.timeOrder * m.numerator p * Real.exp (-r*E)
structure Track where
  n : ℕ
  modes : Fin n → Mode
def wickProfile (terms : List (ℂ × Track)) (r : ℝ) : ℂ :=
  (terms.map fun (c,t) => c * ((∏ i, ∫ p : Space, (t.modes i).kernel r p : ℝ) : ℂ)).sum

structure TraceTest : Prop where
  centered (f : YangMills.TestFunction) :
    inner ℂ T.theory.fields.vacuum.1
      (T.theory.fields.field (T.toLabel 4 T.centeredTrace) f T.theory.fields.vacuum).1 = 0
  amplitudePositive : 0 < 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4
  shortDistance : Tendsto (fun r : ℝ => (r^8 * (Real.log r⁻¹)^2) • T.traceTwo r)
    (𝓝[>] 0) (𝓝 ((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4 : ℝ) : ℂ))
  excludes (terms : List (ℂ × Track)) : ¬ T.traceTwo =ᶠ[𝓝[>] 0] wickProfile terms

structure Properties (order : ℕ → ℕ) : Prop where
  wilson : C.Converges order (fun v => T.correlation none (T.project ∘ v))
  reconstruction : T.Reconstructed
  ope : T.OperatorProductExpansion
  nonfree : T.TraceTest
end Hierarchy

/-- One Wilson family per gauge group, followed by a refinement for every requested
volume sequence. All four conclusions concern a single hierarchy on that refinement. -/
def JointExistence : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q)

end YangMills


