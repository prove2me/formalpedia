-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P36
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:19:15.953267+00:00
-- url     : https://prove2.me/theorems/08e8fff5-b7dc-40a5-91ed-14ffe7b1c61f
-- title:
--   Definitions for The resource theory of steering
-- statement:
--   The objects the formalized statements of *The resource theory of steering* (arXiv:1409.5804) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AssemblageBlocks`: PDF p.2, (2): subnormalized density blocks indexed by output and input.
--   - `bobTotal`: PDF p.2, (4): the reduced matrix. Averaging over inputs avoids an arbitrary chosen input. On a positive-size no-signaling assemblage this is each input's sum.
--   - `assemblageMass`: PDF p.2, (5): common trace of an assemblage.
--   - `IsAssemblage`: PDF p.2, (1)–(5): positive finite dimensions, positive blocks, no signaling, and a common trace in [0,1]. Empty physical systems and alphabets are excluded.
--   - `IsNormalized`: PDF p.2, (5): physical input assemblages have trace one.
--   - `HasFiniteLHSModel`: PDF p.2, (6): a normalized LHS model multiplied by the assemblage's assemblageMass. Finite hidden alphabets suffice: responses can be expanded into deterministic strings of outputs and hidden positive matrices grouped by those strings. In particular this definition includes the zero assemblage at positive d,r,s.
--   - `SteeringProtocol`: PDF pp.3–4, (7),(10), Appendix A: Bob's subinstrument followed by his classical message and Alice's two normalized conditional wirings.
--   - `SteeringProtocol.Complete`: PDF p.4, (12): completeness means Bob never aborts.
--   - `bobStep`: PDF p.9, Step 1: Bob acts before Alice chooses her input.
--   - `protocolBranch`: PDF p.9, Steps 2–3: sample x using (w,xf), query Alice's device, then sample af using (w,a,x,xf), retaining Bob's branch w.
--   - `protocolAction`: PDF p.3, (9): the operational map with the outcome forgotten.
--   - `oneWayFormula`: PDF p.10, (A6), equivalently (9)–(10), written as a closed block formula.
--   - `steeringBranchProbability`: PDF p.3, (8): Bob's branch success probability, independent of Alice's input.
--   - `normalizeAssemblage`: PDF p.4: conditional normalization. All physical uses require positive assemblageMass; at zero this raw array is zero and is never called a normalized assemblage.
--   - `SteeringConverts`: PDF p.7 and Appendices E–F: exact single-copy conversion with strictly positive input-independent success. All allowed wirings are quantified.
--   - `assemblageMixture`: PDF p.5, (14): a binary affine combination, also used with nu>1 in (21).
--   - `assemblageFamilyMixture`: PDF p.11, (C2): a finite weighted assemblageMixture with the same index set throughout.
--   - `SteeringMeasure`: PDF p.5, Definition 2: a measure for every finite dimension and alphabet.
--   - `measureBranch`: PDF p.5, (13): zero-probability outcomes contribute zero, without assigning a physical conditional assemblage to an impossible event.
--   - `StrongMonotonicity`: PDF p.5, Definition 2(ii): average monotonicity for complete instruments, with the outcome available to Alice before the average is taken.
--   - `MeasureConvexity`: PDF p.5, Definition 2(iii): convexity, including both endpoints.
--   - `IsConvexSteeringMonotone`: PDF p.5, Definition 2: nonnegative, vanishes on LHS, average monotone, and convex. There is no converse assertion in the vanishing clause.
--   - `assemblageCQMatrix`: PDF p.2, (3): Alice's classical outcome flag, with Bob's actual block.
--   - `densityD`: PDF p.5, (15): the pinned Umegaki divergence, with natural logarithms and +infinity on support failure. The non-density branch is a totalization outside the physical domain; it is never a finite substitute for divergence.
--   - `steeringClassicalDivergence`: PDF p.5, (16): KL divergence of two normalized finite laws, computed as the Umegaki divergence of their diagonal density matrices. This retains negative individual log-ratio contributions before forming the nonnegative total.
--   - `EntropyStrategy`: PDF p.6, (18)–(19): arbitrary finite-outcome complete Bob instrument and an input law chosen after its outcome. The number of outcomes is unrestricted.
--   - `strategyProbability`: PDF p.6, (19): the two input assemblages give separately computed laws.
--   - `filteredCQ`: PDF p.6, numerator in (18): Bob's filtered flagged state at fixed input.
--   - `conditionalD`: PDF p.6, (18): p D(A/p || B/q), zero when p=0 and infinite when p>0=q. This homogeneous convention avoids a fictitious zero-over-zero density matrix.
--   - `entropyScore`: PDF p.6, (18): both the classical outcome KL term and the conditional quantum term weighted by P(x|g) P_g, with separate denominators P_g and P'_g.
--   - `assemblageEntropy`: PDF p.6, Definition 3: complete-order optimization, allowing +infinity. The source's maximum attainment is asserted in relativeEntropy_convexMonotone; it is not assumed or hidden by replacing the range with a bounded real set.
--   - `EntropyMaximum`: PDF p.6, (18): the explicit maximum-attainment obligation.
--   - `steeringEntropy`: PDF p.6, (20): optimize over normalized LHS assemblages on the same space and alphabets. Minimum attainment and finiteness are conclusions below.
--   - `relativeEntropyMeasure`: PDF p.6, Theorem 2: real-valued relative entropy of steering. Its finiteness on every normalized finite assemblage is an explicit theorem obligation.
--   - `entropyBranch`: PDF p.11, (C1): first-input probability weights, with each output separately normalized. If the second branch is impossible and the first is not, the term is infinite; no support-inclusion hypothesis has been added.
--   - `WeightCandidate`: PDF p.6, Definition 4: all raw nu>=0 candidates are retained, including nu>1. Feasible noise and free assemblages are normalized and no-signaling.
--   - `steerableWeight`: PDF p.6, Definition 4: the real infimum; the theorem explicitly asserts that it is an attained minimum, which rules out junk empty/unbounded values.
--   - `RobustnessCandidate`: PDF p.6, Definition 5: arbitrary assemblage noise, not necessarily LHS.
--   - `steeringRobustness`: PDF p.6, Definition 5: the attained minimum is asserted in Theorem 3.
--   - `conditionalKetProjector`: PDF p.6, (23): pure states with no chosen global phase.
--   - `IsPureAssemblage`: PDF p.6, (23): every conditional state has a unit-vector representative, including zero-probability events; purity does not require a pure Bob marginal.
--   - `IsPureOrthogonal`: PDF p.6, following (23): an orthonormal family at each input.
--   - `angleKet`: PDF p.15, (F5): the two qubit bases used for the infinite-class witnesses.
--   - `angleAssemblage`: PDF p.15, (F5): each rank-one block has probability one half.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, https://arxiv.org/abs/1409.5804v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
# The resource theory of steering (arXiv:1409.5804v3)

All locators are PDF pages. Steering-specific definitions below are local to this
paper; IsLaw is imported from the pinned accepted Information100.P56 module. The
finite positive dimensions are unrestricted. Raw block arrays let the same
operation act on normalized and subnormalized assemblages, including zero.
Theorem 4 and the qualitative security motivation are deferred in HARD.md.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

/-- PDF p.2, (2): subnormalized density blocks indexed by output and input. -/
abbrev AssemblageBlocks (d r s : ℕ) := Fin r → Fin s → Matrix (Fin d) (Fin d) ℂ

variable {d r s df rf sf m : ℕ}

/-- PDF p.2, (4): the reduced matrix. Averaging over inputs avoids an arbitrary
chosen input. On a positive-size no-signaling assemblage this is each input's sum. -/
def bobTotal (rho : AssemblageBlocks d r s) : Matrix (Fin d) (Fin d) ℂ :=
  ((s : ℂ)⁻¹) • ∑ x, ∑ a, rho a x

/-- PDF p.2, (5): common trace of an assemblage. -/
def assemblageMass (rho : AssemblageBlocks d r s) : ℝ := (bobTotal rho).trace.re

/-- PDF p.2, (1)–(5): positive finite dimensions, positive blocks, no signaling,
and a common trace in [0,1]. Empty physical systems and alphabets are excluded. -/
def IsAssemblage (rho : AssemblageBlocks d r s) : Prop :=
  0 < d ∧ 0 < r ∧ 0 < s ∧
  (∀ a x, (rho a x).PosSemidef) ∧
  (∀ x y, ∑ a, rho a x = ∑ a, rho a y) ∧ 0 ≤ assemblageMass rho ∧ assemblageMass rho ≤ 1

/-- PDF p.2, (5): physical input assemblages have trace one. -/
def IsNormalized (rho : AssemblageBlocks d r s) : Prop := IsAssemblage rho ∧ assemblageMass rho = 1

/-- PDF p.2, (6): a normalized LHS model multiplied by the assemblage's assemblageMass.
Finite hidden alphabets suffice: responses can be expanded into deterministic
strings of outputs and hidden positive matrices grouped by those strings.
In particular this definition includes the zero assemblage at positive d,r,s. -/
def HasFiniteLHSModel (rho : AssemblageBlocks d r s) : Prop :=
  IsAssemblage rho ∧ ∃ (n : ℕ) (p : Fin n → ℝ)
    (xi : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (response : Fin n → Fin s → Fin r → ℝ),
    IsLaw p ∧ (∀ l, QAlgorithms.IsDensityMatrix (xi l)) ∧
    (∀ l x, IsLaw (response l x)) ∧
    ∀ a x, rho a x = ∑ l, ((assemblageMass rho * p l * response l x a : ℝ) : ℂ) • xi l

/-- PDF pp.3–4, (7),(10), Appendix A: Bob's subinstrument followed by
his classical message and Alice's two normalized conditional wirings. -/
structure SteeringProtocol (d r s df rf sf m : ℕ) where
  dimensions : 0 < d ∧ 0 < r ∧ 0 < s ∧ 0 < df ∧ 0 < rf ∧ 0 < sf
  kraus : Fin m → Matrix (Fin df) (Fin d) ℂ
  trace_decreasing : (1 - ∑ w, (kraus w).conjTranspose * kraus w).PosSemidef
  input : Fin m → Fin sf → Fin s → ℝ
  output : Fin m → Fin rf → Fin r → Fin s → Fin sf → ℝ
  input_law : ∀ w xf, IsLaw (input w xf)
  output_law : ∀ w a x xf, IsLaw (fun af => output w af a x xf)

/-- PDF p.4, (12): completeness means Bob never aborts. -/
def SteeringProtocol.Complete (P : SteeringProtocol d r s df rf sf m) : Prop :=
  ∑ w, (P.kraus w).conjTranspose * P.kraus w = 1

/-- PDF p.9, Step 1: Bob acts before Alice chooses her input. -/
def bobStep (P : SteeringProtocol d r s df rf sf m) (rho : AssemblageBlocks d r s)
    (w : Fin m) : AssemblageBlocks df r s :=
  fun a x => P.kraus w * rho a x * (P.kraus w).conjTranspose

/-- PDF p.9, Steps 2–3: sample x using (w,xf), query Alice's device,
then sample af using (w,a,x,xf), retaining Bob's branch w. -/
def protocolBranch (P : SteeringProtocol d r s df rf sf m) (rho : AssemblageBlocks d r s)
    (w : Fin m) : AssemblageBlocks df rf sf :=
  fun af xf => ∑ x, ∑ a,
    (P.output w af a x xf : ℂ) • ((P.input w xf x : ℂ) • bobStep P rho w a x)

/-- PDF p.3, (9): the operational map with the outcome forgotten. -/
def protocolAction (P : SteeringProtocol d r s df rf sf m) (rho : AssemblageBlocks d r s) :
    AssemblageBlocks df rf sf := fun af xf => ∑ w, protocolBranch P rho w af xf

/-- PDF p.10, (A6), equivalently (9)–(10), written as a closed block formula. -/
def oneWayFormula (P : SteeringProtocol d r s df rf sf m) (rho : AssemblageBlocks d r s) :
    AssemblageBlocks df rf sf :=
  fun af xf => ∑ w, ∑ a, ∑ x,
    ((P.input w xf x * P.output w af a x xf : ℝ) : ℂ) •
      (P.kraus w * rho a x * (P.kraus w).conjTranspose)

/-- PDF p.3, (8): Bob's branch success probability, independent of Alice's input. -/
def steeringBranchProbability (P : SteeringProtocol d r s df rf sf m) (rho : AssemblageBlocks d r s)
    (w : Fin m) : ℝ :=
  (P.kraus w * bobTotal rho * (P.kraus w).conjTranspose).trace.re

/-- PDF p.4: conditional normalization. All physical uses require positive assemblageMass;
at zero this raw array is zero and is never called a normalized assemblage. -/
def normalizeAssemblage (rho : AssemblageBlocks d r s) : AssemblageBlocks d r s :=
  fun a x => ((assemblageMass rho : ℂ)⁻¹) • rho a x

/-- PDF p.7 and Appendices E–F: exact single-copy conversion with strictly
positive input-independent success. All allowed wirings are quantified. -/
def SteeringConverts (rho : AssemblageBlocks d r s) (sigma : AssemblageBlocks df rf sf) : Prop :=
  IsNormalized rho ∧ IsNormalized sigma ∧
  ∃ (m : ℕ) (P : SteeringProtocol d r s df rf sf m) (p : ℝ),
    0 < p ∧ p ≤ 1 ∧ ∀ af xf, protocolAction P rho af xf = (p : ℂ) • sigma af xf

/-- PDF p.5, (14): a binary affine combination, also used with nu>1 in (21). -/
def assemblageMixture (rho sigma : AssemblageBlocks d r s) (t : ℝ) : AssemblageBlocks d r s :=
  fun a x => (t : ℂ) • rho a x + ((1 - t : ℝ) : ℂ) • sigma a x

/-- PDF p.11, (C2): a finite weighted assemblageMixture with the same index set throughout. -/
def assemblageFamilyMixture {n : ℕ} (p : Fin n → ℝ) (rho : Fin n → AssemblageBlocks d r s) :
    AssemblageBlocks d r s := fun a x => ∑ j, (p j : ℂ) • rho j a x

/-- PDF p.5, Definition 2: a measure for every finite dimension and alphabet. -/
abbrev SteeringMeasure := (d r s : ℕ) → AssemblageBlocks d r s → ℝ

/-- PDF p.5, (13): zero-probability outcomes contribute zero, without assigning
a physical conditional assemblage to an impossible event. -/
def measureBranch (S : SteeringMeasure) (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (w : Fin m) : ℝ :=
  let p := steeringBranchProbability P rho w
  if 0 < p then p * S df rf sf (normalizeAssemblage (protocolBranch P rho w)) else 0

/-- PDF p.5, Definition 2(ii): average monotonicity for complete instruments,
with the outcome available to Alice before the average is taken. -/
def StrongMonotonicity (S : SteeringMeasure) : Prop :=
  ∀ (d r s df rf sf m : ℕ) (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s), IsNormalized rho → P.Complete →
    ∑ w, measureBranch S P rho w ≤ S d r s rho

/-- PDF p.5, Definition 2(iii): convexity, including both endpoints. -/
def MeasureConvexity (S : SteeringMeasure) : Prop :=
  ∀ (d r s : ℕ) (rho sigma : AssemblageBlocks d r s) (t : ℝ),
    IsNormalized rho → IsNormalized sigma → 0 ≤ t → t ≤ 1 →
    S d r s (assemblageMixture rho sigma t) ≤ t * S d r s rho + (1 - t) * S d r s sigma

/-- PDF p.5, Definition 2: nonnegative, vanishes on LHS, average monotone,
and convex. There is no converse assertion in the vanishing clause. -/
def IsConvexSteeringMonotone (S : SteeringMeasure) : Prop :=
  (∀ d r s (rho : AssemblageBlocks d r s), IsNormalized rho → 0 ≤ S d r s rho) ∧
  (∀ d r s (rho : AssemblageBlocks d r s), IsNormalized rho → HasFiniteLHSModel rho → S d r s rho = 0) ∧
  StrongMonotonicity S ∧ MeasureConvexity S

/-- PDF p.2, (3): Alice's classical outcome flag, with Bob's actual block. -/
def assemblageCQMatrix (rho : AssemblageBlocks d r s) (x : Fin s) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ :=
  fun i j => if i.1 = j.1 then rho i.1 x i.2 j.2 else 0

/-- PDF p.5, (15): the pinned Umegaki divergence, with natural logarithms
and +infinity on support failure. The non-density branch is a totalization
outside the physical domain; it is never a finite substitute for divergence. -/
def densityD {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ≥0∞ :=
  if h : QAlgorithms.IsDensityMatrix rho ∧ QAlgorithms.IsDensityMatrix sigma then
    QAlgorithms.QuantumLoss.umegakiEntropy rho sigma h.1 h.2
  else ⊤

/-- PDF p.5, (16): KL divergence of two normalized finite laws, computed as
the Umegaki divergence of their diagonal density matrices. This retains negative
individual log-ratio contributions before forming the nonnegative total. -/
def steeringClassicalDivergence {n : ℕ} (p q : Fin n → ℝ) : ℝ≥0∞ :=
  densityD (Matrix.diagonal (fun i => (p i : ℂ)))
    (Matrix.diagonal (fun i => (q i : ℂ)))

/-- PDF p.6, (18)–(19): arbitrary finite-outcome complete Bob instrument and
an input law chosen after its outcome. The number of outcomes is unrestricted. -/
structure EntropyStrategy (d s : ℕ) where
  outcomes : ℕ
  kraus : Fin outcomes → Matrix (Fin d) (Fin d) ℂ
  complete : ∑ g, (kraus g).conjTranspose * kraus g = 1
  input : Fin outcomes → Fin s → ℝ
  input_law : ∀ g, IsLaw (input g)

/-- PDF p.6, (19): the two input assemblages give separately computed laws. -/
def strategyProbability (T : EntropyStrategy d s) (rho : AssemblageBlocks d r s)
    (g : Fin T.outcomes) : ℝ :=
  (T.kraus g * bobTotal rho * (T.kraus g).conjTranspose).trace.re

/-- PDF p.6, numerator in (18): Bob's filtered flagged state at fixed input. -/
def filteredCQ (T : EntropyStrategy d s) (rho : AssemblageBlocks d r s)
    (g : Fin T.outcomes) (x : Fin s) : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ :=
  assemblageCQMatrix (fun a y => T.kraus g * rho a y * (T.kraus g).conjTranspose) x

/-- PDF p.6, (18): p D(A/p || B/q), zero when p=0 and infinite when p>0=q.
This homogeneous convention avoids a fictitious zero-over-zero density matrix. -/
def conditionalD {I : Type*} [Fintype I] [DecidableEq I]
    (p q : ℝ) (A B : Matrix I I ℂ) : ℝ≥0∞ :=
  if 0 < p then
    if 0 < q then ENNReal.ofReal p * densityD (((p : ℂ)⁻¹) • A) (((q : ℂ)⁻¹) • B)
    else ⊤
  else 0

/-- PDF p.6, (18): both the classical outcome KL term and the conditional
quantum term weighted by P(x|g) P_g, with separate denominators P_g and P'_g. -/
def entropyScore (T : EntropyStrategy d s) (rho sigma : AssemblageBlocks d r s) : ℝ≥0∞ :=
  steeringClassicalDivergence (strategyProbability T rho) (strategyProbability T sigma) +
    ∑ g, ∑ x, ENNReal.ofReal (T.input g x) *
      conditionalD (strategyProbability T rho g) (strategyProbability T sigma g)
        (filteredCQ T rho g x) (filteredCQ T sigma g x)

/-- PDF p.6, Definition 3: complete-order optimization, allowing +infinity.
The source's maximum attainment is asserted in relativeEntropy_convexMonotone;
it is not assumed or hidden by replacing the range with a bounded real set. -/
def assemblageEntropy (rho sigma : AssemblageBlocks d r s) : ℝ≥0∞ :=
  sSup {v | ∃ T : EntropyStrategy d s, entropyScore T rho sigma = v}

/-- PDF p.6, (18): the explicit maximum-attainment obligation. -/
def EntropyMaximum (rho sigma : AssemblageBlocks d r s) : Prop :=
  ∃ T : EntropyStrategy d s, entropyScore T rho sigma = assemblageEntropy rho sigma

/-- PDF p.6, (20): optimize over normalized LHS assemblages on the same space
and alphabets. Minimum attainment and finiteness are conclusions below. -/
def steeringEntropy (rho : AssemblageBlocks d r s) : ℝ≥0∞ :=
  sInf {v | ∃ sigma : AssemblageBlocks d r s,
    IsNormalized sigma ∧ HasFiniteLHSModel sigma ∧ assemblageEntropy rho sigma = v}

/-- PDF p.6, Theorem 2: real-valued relative entropy of steering. Its finiteness
on every normalized finite assemblage is an explicit theorem obligation. -/
def relativeEntropyMeasure : SteeringMeasure :=
  fun _ _ _ rho => (steeringEntropy rho).toReal

/-- PDF p.11, (C1): first-input probability weights, with each output separately
normalized. If the second branch is impossible and the first is not, the term
is infinite; no support-inclusion hypothesis has been added. -/
def entropyBranch (P : SteeringProtocol d r s df rf sf m) (rho sigma : AssemblageBlocks d r s)
    (w : Fin m) : ℝ≥0∞ :=
  let p := steeringBranchProbability P rho w
  let q := steeringBranchProbability P sigma w
  if 0 < p then
    if 0 < q then ENNReal.ofReal p *
      assemblageEntropy (normalizeAssemblage (protocolBranch P rho w))
        (normalizeAssemblage (protocolBranch P sigma w))
    else ⊤
  else 0

/-- PDF p.6, Definition 4: all raw nu>=0 candidates are retained, including
nu>1. Feasible noise and free assemblages are normalized and no-signaling. -/
def WeightCandidate (rho : AssemblageBlocks d r s) (nu : ℝ) : Prop :=
  0 ≤ nu ∧ ∃ noise sigma : AssemblageBlocks d r s,
    IsNormalized noise ∧ IsNormalized sigma ∧ HasFiniteLHSModel sigma ∧ rho = assemblageMixture noise sigma nu

/-- PDF p.6, Definition 4: the real infimum; the theorem explicitly asserts
that it is an attained minimum, which rules out junk empty/unbounded values. -/
def steerableWeight (rho : AssemblageBlocks d r s) : ℝ := sInf {nu | WeightCandidate rho nu}

/-- PDF p.6, Definition 5: arbitrary assemblage noise, not necessarily LHS. -/
def RobustnessCandidate (rho : AssemblageBlocks d r s) (nu : ℝ) : Prop :=
  0 ≤ nu ∧ ∃ noise : AssemblageBlocks d r s, IsNormalized noise ∧
    HasFiniteLHSModel (fun a x => (((1 + nu : ℝ) : ℂ)⁻¹) • rho a x +
      ((nu / (1 + nu) : ℝ) : ℂ) • noise a x)

/-- PDF p.6, Definition 5: the attained minimum is asserted in Theorem 3. -/
def steeringRobustness (rho : AssemblageBlocks d r s) : ℝ :=
  sInf {nu | RobustnessCandidate rho nu}

/-- PDF p.6, (23): pure states with no chosen global phase. -/
def conditionalKetProjector {d : ℕ} (v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => v i * star (v j)

/-- PDF p.6, (23): every conditional state has a unit-vector representative,
including zero-probability events; purity does not require a pure Bob marginal. -/
def IsPureAssemblage (rho : AssemblageBlocks d r s) : Prop :=
  ∃ (p : Fin s → Fin r → ℝ) (v : Fin r → Fin s → Fin d → ℂ),
    (∀ x, IsLaw (p x)) ∧ (∀ a x, ∑ i, Complex.normSq (v a x i) = 1) ∧
    ∀ a x, rho a x = (p x a : ℂ) • conditionalKetProjector (v a x)

/-- PDF p.6, following (23): an orthonormal family at each input. -/
def IsPureOrthogonal (rho : AssemblageBlocks d r s) : Prop :=
  ∃ (p : Fin s → Fin r → ℝ) (v : Fin r → Fin s → Fin d → ℂ),
    (∀ x, IsLaw (p x)) ∧
    (∀ a b x, ∑ i, star (v a x i) * v b x i = if a = b then 1 else 0) ∧
    ∀ a x, rho a x = (p x a : ℂ) • conditionalKetProjector (v a x)

/-- PDF p.15, (F5): the two qubit bases used for the infinite-class witnesses. -/
def angleKet (theta : ℝ) (a x : Fin 2) : Fin 2 → ℂ :=
  if x = 0 then (fun i => if i = a then 1 else 0)
  else if a = 0 then (fun i => if i = 0 then (Real.cos theta : ℂ) else (Real.sin theta : ℂ))
  else (fun i => if i = 0 then -(Real.sin theta : ℂ) else (Real.cos theta : ℂ))

/-- PDF p.15, (F5): each rank-one block has probability one half. -/
def angleAssemblage (theta : ℝ) : AssemblageBlocks 2 2 2 :=
  fun a x => (1 / 2 : ℂ) • conditionalKetProjector (angleKet theta a x)

/-! Sanity checks for the new local interfaces. These are definition checks,
not proofs of the paper's theorems. -/

example : IsLaw (fun _ : Fin 1 => (1 : ℝ)) := by
  simp [IsLaw]

example (rho sigma : AssemblageBlocks d r s) : assemblageMixture rho sigma 0 = sigma := by
  funext a x
  simp [assemblageMixture]

example (rho sigma : AssemblageBlocks d r s) : assemblageMixture rho sigma 1 = rho := by
  funext a x
  simp [assemblageMixture]

example {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (q : ℝ) : conditionalD 0 q A B = 0 := by
  simp [conditionalD]

example (P : SteeringProtocol d r s df rf sf 0) (rho : AssemblageBlocks d r s) :
    protocolAction P rho = 0 := by
  funext a x
  simp [protocolAction]

example (theta : ℝ) : angleKet theta 0 0 0 = 1 := by
  simp [angleKet]

example (theta : ℝ) : angleKet theta 0 0 1 = 0 := by
  simp [angleKet]

end QAlgorithms.Papers.Independent.Intakethird100.P36


