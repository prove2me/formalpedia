-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16
-- name    : QAlgorithms_Papers_Independent_Support50_P16
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T19:54:52.056375+00:00
-- url     : https://prove2.me/theorems/bb4e09f0-d1a9-47c8-adff-e9b12456fc42
-- title:
--   Definitions for Relative entropy and squashed entanglement
-- statement:
--   The objects the formalized statements of *Relative entropy and squashed entanglement* (arXiv:1210.3181) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `povmOutcomeLaw`: PDF p.2: the actual probability vector of a POVM.
--   - `finiteKLBits`: PDF pp.2,10: classical relative entropy in bits, infinite on support violation. The zero summands use 0 log 0 = 0. Only probability laws are used in results.
--   - `restrictedEntropy`: PDF p.3, Eq.(5): infimum over reference states, THEN supremum over measurements. The nonnegative extended lattice gives supremum 0 for an empty measurement class and infimum infinity for an empty reference set. If G is nonempty and M is empty, the optimized value is 0.
--   - `measurementDistance`: PDF pp.3,5: full classical l1 distinguishability, with no factor 1/2. For fixed finite input operators this supremum is bounded; on states it is <= 2. An empty measurement class has value 0.
--   - `trivialMeasurement`: PDF p.2: the unique one-outcome measurement.
--   - `continuityModulus`: PDF pp.5,10: continuous zero-error extension of the printed modulus.
--   - `MeasurementKind`: PDF pp.2--3: the five distinct operational measurement classes.
--   - `IsLO`: PDF pp.2--3: local product measurements followed by classical coarse graining. There is no shared entanglement or communication in the product POVM.
--   - `IsAliceToBobPOVM`: PDF pp.3,6: Alice measures first, sends her outcome to Bob, who measures conditionally. Coarse graining permits the binary hypothesis tests as well.
--   - `IsLOCCMeasurement`: PDF pp.2--3: arbitrary finite adaptive LOCC followed by a local classical readout. The accepted tree includes rectangular local maps, disposal, randomness and both communication directions. Optimization permits arbitrary round counts.
--   - `measurementClass`: PDF pp.2--3: SEP/PPT constrain EACH effect, with POVM normalization retained.
--   - `separable`: PDF pp.2--3: exact finite convex mixtures of normalized product states.
--   - `ExtendedEntanglementFunctional`: PDF p.3: a family on every positive finite bipartite dimension.
--   - `measuredEntanglement`: PDF p.3, Eq.(5): restricted relative entropy with G=SEP.
--   - `copyDimension`: PDF pp.2--3: dimension of n local copies; at n=0 it is one.
--   - `regularizationSequence`: PDF pp.2--3: normalized positive-copy sequence with copies grouped by owner.
--   - `regularized`: PDF pp.2--3: liminf adapter; theorems with regularized quantities also assert convergence where needed, so this is never substituted for a nonexistent limit.
--   - `Regularizes`: PDF pp.2--3: the actual regularization limit exists and equals the adapter.
--   - `updated`: PDF p.13: E_r,rightArrow optimizes over LOCC OPERATIONS with unrestricted positive finite quantum output dimensions, then applies one-way measured REE.
--   - `classicalSquashed`: PDF p.13: classical squashed entanglement is HALF the mixed convex roof of MI. The accepted ensembles allow arbitrary finite lengths and mixed components.
--   - `conditionalEntanglement`: PDF p.13: E_I is half the infimum of I(AA';BB')-I(A';B') over every normalized extension, without a dimension cap or assumed minimizer.
--   - `key`: PDF pp.13,15--16: operational key rate, with arbitrary finite private shields.
--   - `StrictSeparation`: PDF pp.15--16: separate existential strict witnesses, with dimensions allowed to vary. This predicate imposes no joint-witness requirement.
--   - `cutBAE`: PDF p.4: same state expressed on the bipartition B:AE.
--   - `OneWayRetainedInstrument`: PDF pp.6--7: one-way AB->XB instrument. Alice's POVM result is sent to Bob; Bob applies a complete conditional Kraus instrument with classical binary output. Alice is discarded and Bob's quantum register is retained. No E input is present.
--   - `aliceCondition`: PDF p.7, Eq.(19): unnormalized Bob block after Alice's effect. This equals tracing out Alice after sqrt(R) on both sides; the transposed indices on R are essential for coherent inputs.
--   - `retainedBranch`: PDF p.7, Eq.(19): the actual CP branch map with a retained B output.
--   - `retainedCQOutput`: PDF p.7, Eq.(19): classical-quantum output of the rectangular instrument.
--   - `retainedClassical`: PDF p.6: T^c traces out B; it is a binary probability law on states.
--   - `retainedQuantum`: PDF p.6: T^q forgets the classical result and retains the full B matrix.
--   - `extensionCopies`: PDF pp.6--8: grouped copies of the ACTUAL tripartite input, including all E off-diagonal blocks. Each laboratory uses the accepted fixed local copy basis.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, https://arxiv.org/abs/1210.3181v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

/-!
Li--Winter, arXiv:1210.3181v2. Finite, positive-dimensional registers;
normalized density matrices; all entropies and rates in bits; full trace norm.
Only the pinned accepted library is imported. Compilation awaits batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Support50.P16

noncomputable section

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "tau" => QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed
local notation "RE" => QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement
local notation "RER" => QAlgorithms.Papers.Independent.Information100.P54.regularizedEntanglement
local notation "SQ" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed
local notation "CMI" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual
local notation "MI" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
local notation "LOCC" => QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC
local notation "power" => QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower
local notation "index" => QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex

-- Accepted matrix coordinates (not P50.Bipartite, which is a vector space).
local notation "Bipartite" => QAlgorithms.Papers.Independent.Dependency50.P50.BipartiteMat

-- Positive outcome counts follow already from a POVM on a nonzero register.
local notation "FiniteMeasurement" => QAlgorithms.Papers.Independent.Information100.P04.Measurement

/-- PDF p.2: the actual probability vector of a POVM. -/
def povmOutcomeLaw {I : Type} [Fintype I] [DecidableEq I]
    (M : FiniteMeasurement I) (rho : Matrix I I ℂ) : Fin M.outcomes → ℝ :=
  fun x => effectProb (M.effect x) rho

/-- PDF pp.2,10: classical relative entropy in bits, infinite on support violation.
The zero summands use 0 log 0 = 0. Only probability laws are used in results. -/
def finiteKLBits {m : ℕ} (p q : Fin m → ℝ) : ℝ≥0∞ :=
  if ∀ x, 0 < p x → 0 < q x then
    ENNReal.ofReal (∑ x, p x * (Real.logb 2 (p x) - Real.logb 2 (q x)))
  else ⊤

/-- PDF p.3, Eq.(5): infimum over reference states, THEN supremum over measurements.
The nonnegative extended lattice gives supremum 0 for an empty measurement class
and infimum infinity for an empty reference set. If G is nonempty and M is empty,
the optimized value is 0. -/
def restrictedEntropy {I : Type} [Fintype I] [DecidableEq I]
    (G : Set (Matrix I I ℂ)) (M : Set (FiniteMeasurement I)) (rho : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨅ sigma : G, ⨆ test : M,
    finiteKLBits (povmOutcomeLaw test.val rho) (povmOutcomeLaw test.val sigma.val)

/-- PDF pp.3,5: full classical l1 distinguishability, with no factor 1/2.
For fixed finite input operators this supremum is bounded; on states it is <= 2.
An empty measurement class has value 0. -/
def measurementDistance {I : Type} [Fintype I] [DecidableEq I]
    (M : Set (FiniteMeasurement I)) (rho sigma : Matrix I I ℂ) : ℝ :=
  (⨆ test : M, ENNReal.ofReal
    (∑ x, |povmOutcomeLaw test.val rho x - povmOutcomeLaw test.val sigma x|)).toReal

/-- PDF p.2: the unique one-outcome measurement. -/
def trivialMeasurement (I : Type) [Fintype I] [DecidableEq I] : FiniteMeasurement I :=
  ⟨1, by decide, fun _ => 1, ⟨fun _ => Matrix.PosSemidef.one, by simp⟩⟩

/-- PDF pp.5,10: continuous zero-error extension of the printed modulus. -/
def continuityModulus (k : ℕ) (epsilon : ℝ) : ℝ :=
  if epsilon = 0 then 0 else 2 * epsilon * Real.logb 2 (6 * (k : ℝ) / epsilon)

/-- PDF pp.2--3: the five distinct operational measurement classes. -/
inductive MeasurementKind where
  | LO | oneWay | LOCC | SEP | PPT
  deriving DecidableEq

/-- PDF pp.2--3: local product measurements followed by classical coarse graining.
There is no shared entanglement or communication in the product POVM. -/
def IsLO {a b : ℕ+} (M : FiniteMeasurement (Fin (a : ℕ) × Fin (b : ℕ))) : Prop :=
  ∃ r s : ℕ, ∃ A : Fin r → Matrix (Fin (a : ℕ)) (Fin (a : ℕ)) ℂ,
    ∃ B : Fin s → Matrix (Fin (b : ℕ)) (Fin (b : ℕ)) ℂ,
    IsPOVM A ∧ IsPOVM B ∧ ∃ f : Fin r × Fin s → Fin M.outcomes,
    ∀ x, M.effect x = ∑ i, ∑ j,
      if f (i,j) = x then Matrix.kronecker (A i) (B j) else 0

/-- PDF pp.3,6: Alice measures first, sends her outcome to Bob, who measures
conditionally. Coarse graining permits the binary hypothesis tests as well. -/
def IsAliceToBobPOVM {a b : ℕ+} (M : FiniteMeasurement (Fin (a : ℕ) × Fin (b : ℕ))) : Prop :=
  ∃ r s : ℕ, ∃ A : Fin r → Matrix (Fin (a : ℕ)) (Fin (a : ℕ)) ℂ,
    ∃ B : Fin r → Fin s → Matrix (Fin (b : ℕ)) (Fin (b : ℕ)) ℂ,
    IsPOVM A ∧ (∀ i, IsPOVM (B i)) ∧ ∃ f : Fin r × Fin s → Fin M.outcomes,
    ∀ x, M.effect x = ∑ i, ∑ j,
      if f (i,j) = x then Matrix.kronecker (A i) (B i j) else 0

/-- PDF pp.2--3: arbitrary finite adaptive LOCC followed by a local classical readout.
The accepted tree includes rectangular local maps, disposal, randomness and both
communication directions. Optimization permits arbitrary round counts. -/
def IsLOCCMeasurement {a b : ℕ+}
    (M : FiniteMeasurement (Fin (a : ℕ) × Fin (b : ℕ))) : Prop :=
  ∃ L : Superop (Fin (a : ℕ) × Fin (b : ℕ)) (Fin 1 × Fin M.outcomes), LOCC L ∧
    ∀ X x, (L X) (0,x) (0,x) = ((M.effect x) * X).trace

/-- PDF pp.2--3: SEP/PPT constrain EACH effect, with POVM normalization retained. -/
def measurementClass (c : MeasurementKind) (a b : ℕ+) :
    Set (FiniteMeasurement (Fin (a : ℕ) × Fin (b : ℕ))) :=
  match c with
  | .LO => {M | IsLO M}
  | .oneWay => {M | IsAliceToBobPOVM M}
  | .LOCC => {M | IsLOCCMeasurement M}
  | .SEP => {M | ∀ x, QAlgorithms.Entanglement.IsSeparablePositive (M.effect x)}
  | .PPT => {M | ∀ x, (QAlgorithms.Entanglement.partialTransposeFirst (M.effect x)).PosSemidef}

/-- PDF pp.2--3: exact finite convex mixtures of normalized product states. -/
def separable (a b : ℕ+) : Set (Bipartite a b) :=
  {rho | QAlgorithms.Entanglement.IsSeparableDensity rho}

/-- PDF p.3: a family on every positive finite bipartite dimension. -/
abbrev ExtendedEntanglementFunctional := (a b : ℕ+) → Bipartite a b → ℝ≥0∞

/-- PDF p.3, Eq.(5): restricted relative entropy with G=SEP. -/
def measuredEntanglement (c : MeasurementKind) : ExtendedEntanglementFunctional :=
  fun a b rho => restrictedEntropy (separable a b) (measurementClass c a b) rho

-- Reuse the accepted operational/variational quantity through a typed notation.
local notation "relative" =>
  ((fun _ _ rho => RE rho) : ExtendedEntanglementFunctional)

-- Reuse the accepted operational/variational quantity through a typed notation.
local notation "squashed" =>
  ((fun _ _ rho => ENNReal.ofReal (SQ rho)) : ExtendedEntanglementFunctional)

/-- PDF pp.2--3: dimension of n local copies; at n=0 it is one. -/
abbrev copyDimension (a : ℕ+) (n : ℕ) : ℕ+ := ⟨(a : ℕ)^n, pow_pos a.pos n⟩

/-- PDF pp.2--3: normalized positive-copy sequence with copies grouped by owner. -/
def regularizationSequence (F : ExtendedEntanglementFunctional) {a b : ℕ+}
    (rho : Bipartite a b) (r : ℕ) : ℝ≥0∞ :=
  F (copyDimension a (r+1)) (copyDimension b (r+1)) (power rho (r+1)) / (r+1 : ℝ≥0∞)

/-- PDF pp.2--3: liminf adapter; theorems with regularized quantities also assert
convergence where needed, so this is never substituted for a nonexistent limit. -/
def regularized (F : ExtendedEntanglementFunctional) {a b : ℕ+} (rho : Bipartite a b) : ℝ≥0∞ :=
  Filter.liminf (regularizationSequence F rho) atTop

/-- PDF pp.2--3: the actual regularization limit exists and equals the adapter. -/
def Regularizes (F : ExtendedEntanglementFunctional) {a b : ℕ+} (rho : Bipartite a b) : Prop :=
  Tendsto (regularizationSequence F rho) atTop (nhds (regularized F rho))

/-- PDF p.13: E_r,rightArrow optimizes over LOCC OPERATIONS with unrestricted
positive finite quantum output dimensions, then applies one-way measured REE. -/
def updated : ExtendedEntanglementFunctional :=
  fun a b rho => ⨆ c : ℕ+, ⨆ d : ℕ+,
    ⨆ L : {L : Superop (Fin (a : ℕ) × Fin (b : ℕ))
      (Fin (c : ℕ) × Fin (d : ℕ)) // LOCC L}, measuredEntanglement .oneWay c d (L.val rho)

/-- PDF p.13: classical squashed entanglement is HALF the mixed convex roof of MI.
The accepted ensembles allow arbitrary finite lengths and mixed components. -/
def classicalSquashed : ExtendedEntanglementFunctional := fun _ _ rho => ENNReal.ofReal
  (QAlgorithms.Papers.Independent.Information100.P08.mixedRoof MI rho / 2)

-- Exact accepted partial trace of the same AA'BB' extension.
local notation "originalMarginal" => QAlgorithms.Papers.Independent.Information100.P04.principalMarginal

-- Exact accepted partial trace of the same AA'BB' extension.
local notation "ancillaryMarginal" => QAlgorithms.Papers.Independent.Information100.P04.ancillaryMarginal

/-- PDF p.13: E_I is half the infimum of I(AA';BB')-I(A';B') over every
normalized extension, without a dimension cap or assumed minimizer. -/
def conditionalEntanglement : ExtendedEntanglementFunctional := fun a b rho =>
  ⨅ e : ℕ+, ⨅ f : ℕ+, ⨅ omega : {omega :
    Matrix ((Fin (a : ℕ) × Fin (e : ℕ)) × (Fin (b : ℕ) × Fin (f : ℕ)))
      ((Fin (a : ℕ) × Fin (e : ℕ)) × (Fin (b : ℕ) × Fin (f : ℕ))) ℂ //
      IsDensityMatrix omega ∧ originalMarginal omega = rho},
    ENNReal.ofReal ((MI omega.val - MI (ancillaryMarginal omega.val)) / 2)

-- Reuse the accepted operational/variational quantity through a typed notation.
local notation "distillable" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Gap48.P32.twoWayDistillable rho)) : ExtendedEntanglementFunctional)

/-- PDF pp.13,15--16: operational key rate, with arbitrary finite private shields. -/
def key : ExtendedEntanglementFunctional := fun _ _ rho =>
  QAlgorithms.Papers.Independent.Gap48.P42.distillableKey rho

-- Reuse the accepted operational/variational quantity through a typed notation.
local notation "cost" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Dependency50.P42.alternativeCost
    (fun _ _ X Y => traceNorm (X-Y)) rho)) : ExtendedEntanglementFunctional)

/-- PDF pp.15--16: separate existential strict witnesses, with dimensions allowed
to vary. This predicate imposes no joint-witness requirement. -/
def StrictSeparation (F G : ExtendedEntanglementFunctional) : Prop :=
  ∃ a b : ℕ+, ∃ rho : Bipartite a b, IsDensityMatrix rho ∧
    Regularizes relative rho ∧ Regularizes classicalSquashed rho ∧
    Regularizes updated rho ∧ Regularizes (measuredEntanglement .LOCC) rho ∧
    G a b rho < F a b rho

/-- PDF p.4: same state expressed on the bipartition B:AE. -/
def cutBAE {A B E : Type} (rho : Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    Matrix (B × (A × E)) (B × (A × E)) ℂ :=
  fun i j => rho ((i.2.1,i.1),i.2.2) ((j.2.1,j.1),j.2.2)

/-- PDF pp.6--7: one-way AB->XB instrument. Alice's POVM result is sent to Bob;
Bob applies a complete conditional Kraus instrument with classical binary output.
Alice is discarded and Bob's quantum register is retained. No E input is present. -/
structure OneWayRetainedInstrument (a b : ℕ+) where
  messages : ℕ
  alice : Fin messages → Matrix (Fin (a : ℕ)) (Fin (a : ℕ)) ℂ
  aliceComplete : IsPOVM alice
  krausCount : ℕ
  bob : Fin messages → Fin 2 → Fin krausCount → Matrix (Fin (b : ℕ)) (Fin (b : ℕ)) ℂ
  bobComplete : ∀ i, ∑ x, ∑ j, (bob i x j)ᴴ * bob i x j = 1

/-- PDF p.7, Eq.(19): unnormalized Bob block after Alice's effect.
This equals tracing out Alice after sqrt(R) on both sides; the transposed
indices on R are essential for coherent inputs. -/
def aliceCondition {a b : ℕ+} (R : Matrix (Fin (a : ℕ)) (Fin (a : ℕ)) ℂ)
    (rho : Bipartite a b) : Matrix (Fin (b : ℕ)) (Fin (b : ℕ)) ℂ :=
  fun u v => ∑ i, ∑ j, R j i * rho (i,u) (j,v)

/-- PDF p.7, Eq.(19): the actual CP branch map with a retained B output. -/
def retainedBranch {a b : ℕ+} (T : OneWayRetainedInstrument a b) (x : Fin 2) :
    Superop (Fin (a : ℕ) × Fin (b : ℕ)) (Fin (b : ℕ)) :=
  fun rho => ∑ i, ∑ j, T.bob i x j * aliceCondition (T.alice i) rho * (T.bob i x j)ᴴ

/-- PDF p.7, Eq.(19): classical-quantum output of the rectangular instrument. -/
def retainedCQOutput {a b : ℕ+} (T : OneWayRetainedInstrument a b) (rho : Bipartite a b) :
    Matrix (Fin 2 × Fin (b : ℕ)) (Fin 2 × Fin (b : ℕ)) ℂ :=
  fun i j => if i.1 = j.1 then retainedBranch T i.1 rho i.2 j.2 else 0

/-- PDF p.6: T^c traces out B; it is a binary probability law on states. -/
def retainedClassical {a b : ℕ+} (T : OneWayRetainedInstrument a b) (rho : Bipartite a b) :
    Fin 2 → ℝ := fun x => (retainedBranch T x rho).trace.re

/-- PDF p.6: T^q forgets the classical result and retains the full B matrix. -/
def retainedQuantum {a b : ℕ+} (T : OneWayRetainedInstrument a b) :
    Superop (Fin (a : ℕ) × Fin (b : ℕ)) (Fin (b : ℕ)) :=
  fun rho => ∑ x, retainedBranch T x rho

/-- PDF pp.6--8: grouped copies of the ACTUAL tripartite input, including all
E off-diagonal blocks. Each laboratory uses the accepted fixed local copy basis. -/
def extensionCopies {a b e : ℕ+}
    (rho : Matrix ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ))
      ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ)) ℂ) (n : ℕ) :
    Matrix ((Fin ((a : ℕ)^n) × Fin ((b : ℕ)^n)) × Fin ((e : ℕ)^n))
      ((Fin ((a : ℕ)^n) × Fin ((b : ℕ)^n)) × Fin ((e : ℕ)^n)) ℂ :=
  fun i j => ∏ t, rho (((index a n).symm i.1.1 t,(index b n).symm i.1.2 t),
    (index e n).symm i.2 t) (((index a n).symm j.1.1 t,(index b n).symm j.1.2 t),
    (index e n).symm j.2 t)

example : continuityModulus 3 0 = 0 := by simp [continuityModulus]

example {m : ℕ} (p : Fin m → ℝ) : finiteKLBits p p = 0 := by
  simp [finiteKLBits]

example {I : Type} [Fintype I] [DecidableEq I] (G : Set (Matrix I I ℂ))
    (hG : G.Nonempty) (rho : Matrix I I ℂ) : restrictedEntropy G ∅ rho = 0 := by
  obtain ⟨sigma, hsigma⟩ := hG
  letI : Nonempty G := ⟨⟨sigma, hsigma⟩⟩
  simp [restrictedEntropy]

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    measurementDistance ∅ rho sigma = 0 := by simp [measurementDistance]

example : tau 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed]

example (a : ℕ+) : (copyDimension a 0 : ℕ) = 1 := by simp [copyDimension]

example {a b : ℕ+} (T : OneWayRetainedInstrument a b) (rho : Bipartite a b)
    (u v : Fin (b : ℕ)) : retainedCQOutput T rho (0,u) (1,v) = 0 := by
  simp [retainedCQOutput]

example {a b : ℕ+} (rho : Bipartite a b) :
    aliceCondition (1 : Matrix (Fin (a : ℕ)) (Fin (a : ℕ)) ℂ) rho = traceLeft rho := by
  ext u v
  simp [aliceCondition, Matrix.one_apply, traceLeft]

example {a b e : ℕ+}
    (rho : Matrix ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ))
      ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ)) ℂ)
    (i j : (Fin ((a : ℕ)^0) × Fin ((b : ℕ)^0)) × Fin ((e : ℕ)^0)) :
    extensionCopies rho 0 i j = 1 := by simp [extensionCopies]

example {A B E : Type} (rho : Matrix ((A × B) × E) ((A × B) × E) ℂ)
    (a a2 : A) (b b2 : B) (e e2 : E) :
    cutBAE rho (b,(a,e)) (b2,(a2,e2)) = rho ((a,b),e) ((a2,b2),e2) := rfl

end

end QAlgorithms.Papers.Independent.Support50.P16


