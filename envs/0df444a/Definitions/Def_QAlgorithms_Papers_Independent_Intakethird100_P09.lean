-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P09
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P09
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:32:53.694507+00:00
-- url     : https://prove2.me/theorems/a77cc96d-25f4-4c15-a7fa-8bc705c18763
-- title:
--   Definitions for Bounds on quantum nonlocality via partial transposition
-- statement:
--   The objects the formalized statements of *Bounds on quantum nonlocality via partial transposition* (arXiv:1407.6999) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BellScenario`: PDF p.2: finite nonempty input and output alphabets, without a bound on their sizes.
--   - `BellCoefficients`: PDF p.2: the real coefficient table of one fixed Bell expression.
--   - `Measurements`: PDF p.2: one complete local POVM for every local setting.
--   - `measuredBox`: PDF p.2: Born probabilities using the same two local POVMs.
--   - `bellValue`: PDF p.2: signed Bell value; no absolute value or input-law weight is implicit.
--   - `bellOperator`: PDF p.2, Eq.(1): Bell operator for the fixed measurement family.
--   - `bellOperatorNorm`
--   - `deterministicBox`: PDF p.2: deterministic local strategies. Their convex hull is the local polytope.
--   - `classicalBound`: PDF p.2: C(S) is the maximum signed local value. This finite nonempty set attains its supremum.
--   - `stateValue`: PDF p.2, Eq.(3): supremum over all complete POVMs on this fixed state.
--   - `quantumBound`: PDF p.2: Q(S) optimizes the signed value over all positive finite local dimensions.
--   - `sepDistance`: PDF p.2, Eq.(4): distance to same-dimensional normalized separable states.
--   - `sepDistanceUntransposed`: PDF p.2, following Eq.(4): equivalent distance without transposing the SEP witness.
--   - `nearSep`: PDF p.2, Eq.(5): an actual separable witness at distance at most epsilon is required.
--   - `HasFiniteLocalModel`: PDF pp.4,8: finite local boxes; shared randomness is independent of both inputs. Finite deterministic mixtures describe the entire finite local polytope.
--   - `classicalKLBits`: PDF p.4, Eq.(12): KL divergence in bits. The sum is formed BEFORE taking ofReal; individual summands may be negative. A positive mass over zero has infinite divergence.
--   - `boxD`: PDF pp.4,8: average conditional divergence, with the input law outside each KL divergence.
--   - `inputOptimization`: PDF p.8: uniform modifies every input-law optimization consistently; false means optimized.
--   - `boxNonlocality`: PDF p.4, Eq.(12): supremum over joint input laws, THEN infimum over all local boxes.
--   - `asFin`: Paper-local basis adapter to the accepted dimension-changing FiniteLOCC endpoints. It preserves each owner's basis and both matrix indices.
--   - `IsOperationalLOCC`: PDF pp.3--4,8: operational LOCC includes finite adaptive protocols and their limits. Pointwise topology on finite-dimensional linear maps equals every channel-norm topology; closure here is taken in the ambient function space, whose linear subspace is closed. No separable-operation relaxation or uniform bound on rounds is imposed.
--   - `BellExperiment`: PDF pp.3--4,8: one LOCC preprocessing channel followed by one finite Bell scenario.
--   - `rBlock`: PDF p.4, Eq.(13): finite-block optimized nonlocality, before division by blocklength.
--   - `tBlock`: PDF pp.4,8, Eqs.(14),(A.1): the infimum is INSIDE every supremum, and the same channel and measurement compare rho^n with sigma^n for a ONE-copy separable sigma.
--   - `asymptoticR`: PDF pp.4,8: asymptotic nonlocality uses limsup and positive copy numbers n+1.
--   - `asymptoticT`: PDF pp.4,8: restricted regularized relative entropy, with the source's iid reference.
--   - `LocalFilter`: PDF pp.4,9: a selected product Kraus leaf of a complete locally realizable filter. The two complete instruments are performed locally and both outcomes are flagged. Every product contraction can be rescaled between its factors to fit this form, so arbitrary single-product successful leaves are included, without nonlocal filters.
--   - `successfulFilterBranch`: PDF pp.4,9: subnormalized successful branch, applied AFTER LOCC.
--   - `hiddenBlock`: PDF pp.4,9: success probability OUTSIDE nonlocality of the normalized branch. A zero-probability branch has score zero directly, with no conditional state evaluated.
--   - `asymptoticRH`: PDF p.4, Eq.(18), and p.9: success-weighted hidden nonlocality per input copy.
--   - `chshScenario`: PDF p.3, Eq.(8): correlator CHSH, classical bound 2 and quantum bound 2 sqrt(2).
--   - `chshCoefficients`: PDF p.3, Eq.(8): plus correlations except at (1,1); outcomes use signs (-1)^a.
--   - `flatX`: PDF p.3, Eq.(9): flat-unitary shield operator, with the printed X prefactor retained.
--   - `flatY`: PDF p.3, Eq.(9): Y = sqrt(d) X^Gamma, with Gamma only on Bob's shield.
--   - `flatProbability`: PDF p.3, Eq.(9): mixing probability, with denominator sqrt(d)+1.
--   - `pptPrivate`: PDF p.3, Eq.(9): constructed approximate private bit on the physical AA':BB' cut. The source prints flat modulus 1/d. Changed to 1/sqrt(d) in theorem hypotheses: unitarity, the named QFT example and traceNorm X=1 force this correction.
--   - `hidingResource`: PDF p.7, Eq.(A.8): exact computed family, q=1/3, d=m^2, k=m. Normalizer has BOTH exponents m; no density, proximity or key premise is substituted.
--   - `paired`: PDF pp.3,7: tensor product with both owners' registers grouped together.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, https://arxiv.org/abs/1407.6999v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

/-!
Horodecki--Murta, arXiv:1407.6999v3. Citations are PDF pages.
All new objects are local to this paper. Entropies are in bits, with extended
nonnegative values and infinity on support failure. Gamma always transposes Bob.
The unrestricted signed corollaries and one-sided separable gauge are deferred.
The positive-coefficient corrections below require independent moderation.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter
open QAlgorithms.Entanglement (IsSeparableDensity)
open QAlgorithms.Papers.Independent.Dependency50.P24
  (transposeSecond partyCut xForm swapPrivate hidingOne hidingTwo)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower)
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Advance50.P47 (Box)
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntanglement)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.2: finite nonempty input and output alphabets, without a bound on their sizes. -/
structure BellScenario where
  nx : ℕ+
  ny : ℕ+
  na : ℕ+
  nb : ℕ+

/-- PDF p.2: the real coefficient table of one fixed Bell expression. -/
abbrev BellCoefficients (S : BellScenario) := Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb)

/-- PDF p.2: one complete local POVM for every local setting. -/
structure Measurements (S : BellScenario) (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] where
  alice : Fin S.nx → Fin S.na → Op I
  bob : Fin S.ny → Fin S.nb → Op J
  alice_complete : ∀ x, IsPOVM (alice x)
  bob_complete : ∀ y, IsPOVM (bob y)

/-- PDF p.2: Born probabilities using the same two local POVMs. -/
def measuredBox {S : BellScenario} {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Measurements S I J) (rho : Op (I × J)) : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb) :=
  fun x y a b => effectProb (Matrix.kronecker (M.alice x a) (M.bob y b)) rho

/-- PDF p.2: signed Bell value; no absolute value or input-law weight is implicit. -/
def bellValue {S : BellScenario} (s : BellCoefficients S) (P : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb)) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, s x y a b * P x y a b

/-- PDF p.2, Eq.(1): Bell operator for the fixed measurement family. -/
def bellOperator {S : BellScenario} {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (s : BellCoefficients S) (M : Measurements S I J) :
    Op (I × J) :=
  ∑ x, ∑ y, ∑ a, ∑ b, (s x y a b : ℂ) • Matrix.kronecker (M.alice x a) (M.bob y b)

open scoped Matrix.Norms.L2Operator in
/-- PDF p.2: the spectral/operator norm, explicitly selecting Mathlib's Euclidean operator norm. -/
def bellOperatorNorm {I : Type} [Fintype I] [DecidableEq I] (X : Op I) : ℝ :=
  ‖X‖

/-- PDF p.2: deterministic local strategies. Their convex hull is the local polytope. -/
def deterministicBox {S : BellScenario} (f : Fin S.nx → Fin S.na)
    (g : Fin S.ny → Fin S.nb) : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb) :=
  fun x y a b => if f x = a ∧ g y = b then 1 else 0

/-- PDF p.2: C(S) is the maximum signed local value. This finite nonempty set attains its supremum. -/
def classicalBound {S : BellScenario} (s : BellCoefficients S) : ℝ :=
  sSup {v | ∃ f : Fin S.nx → Fin S.na, ∃ g : Fin S.ny → Fin S.nb,
    v = bellValue s (deterministicBox f g)}

/-- PDF p.2, Eq.(3): supremum over all complete POVMs on this fixed state. -/
def stateValue {S : BellScenario} {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (s : BellCoefficients S) (rho : Op (I × J)) : ℝ :=
  sSup {v | ∃ M : Measurements S I J, v = bellValue s (measuredBox M rho)}

/-- PDF p.2: Q(S) optimizes the signed value over all positive finite local dimensions. -/
def quantumBound {S : BellScenario} (s : BellCoefficients S) : ℝ :=
  sSup {v | ∃ a b : ℕ+, ∃ rho : Op (Fin a × Fin b), IsDensityMatrix rho ∧
    ∃ M : Measurements S (Fin a) (Fin b), v = bellValue s (measuredBox M rho)}

/-- PDF p.2, Eq.(4): distance to same-dimensional normalized separable states. -/
def sepDistance {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] (rho : Op (I × J)) : ℝ :=
  sInf {r | ∃ sigma : Op (I × J), IsSeparableDensity sigma ∧
    r = traceNorm (transposeSecond rho - transposeSecond sigma)}

/-- PDF p.2, following Eq.(4): equivalent distance without transposing the SEP witness. -/
def sepDistanceUntransposed {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] (rho : Op (I × J)) : ℝ :=
  sInf {r | ∃ sigma : Op (I × J), IsSeparableDensity sigma ∧
    r = traceNorm (transposeSecond rho - sigma)}

/-- PDF p.2, Eq.(5): an actual separable witness at distance at most epsilon is required. -/
def nearSep {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] (epsilon : ℝ) : Set (Op (I × J)) :=
  {rho | IsDensityMatrix rho ∧ ∃ sigma : Op (I × J), IsSeparableDensity sigma ∧
    traceNorm (transposeSecond rho - transposeSecond sigma) ≤ epsilon}

/-- PDF pp.4,8: finite local boxes; shared randomness is independent of both inputs.
Finite deterministic mixtures describe the entire finite local polytope. -/
def HasFiniteLocalModel {S : BellScenario} (P : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb)) : Prop :=
  ∃ k : ℕ, ∃ w : Fin k → ℝ, IsLaw w ∧
    ∃ f : Fin k → Fin S.nx → Fin S.na, ∃ g : Fin k → Fin S.ny → Fin S.nb,
      ∀ x y a b, P x y a b = ∑ i, w i * deterministicBox (f i) (g i) x y a b

/-- PDF p.4, Eq.(12): KL divergence in bits. The sum is formed BEFORE taking ofReal;
individual summands may be negative. A positive mass over zero has infinite divergence. -/
def classicalKLBits {I : Type} [Fintype I] (p q : I → ℝ) : ℝ≥0∞ :=
  if ∃ i, 0 < p i ∧ q i = 0 then ⊤ else
    ENNReal.ofReal (∑ i, if p i = 0 then 0 else p i * (Real.log (p i / q i) / Real.log 2))

/-- PDF pp.4,8: average conditional divergence, with the input law outside each KL divergence. -/
def boxD {S : BellScenario} (p : Fin S.nx × Fin S.ny → ℝ) (P Q : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb)) : ℝ≥0∞ :=
  ∑ z, ENNReal.ofReal (p z) * classicalKLBits
    (fun ab : Fin S.na × Fin S.nb => P z.1 z.2 ab.1 ab.2)
    (fun ab : Fin S.na × Fin S.nb => Q z.1 z.2 ab.1 ab.2)

/-- PDF p.8: uniform modifies every input-law optimization consistently; false means optimized. -/
def inputOptimization (uniform : Bool) (S : BellScenario)
    (f : (Fin S.nx × Fin S.ny → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  if uniform then f (fun _ => ((S.nx : ℝ) * (S.ny : ℝ))⁻¹)
  else sSup {v | ∃ p, IsLaw p ∧ v = f p}

/-- PDF p.4, Eq.(12): supremum over joint input laws, THEN infimum over all local boxes. -/
def boxNonlocality {S : BellScenario} (uniform : Bool) (P : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb)) : ℝ≥0∞ :=
  inputOptimization uniform S (fun p => sInf {v | ∃ Q : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb), HasFiniteLocalModel Q ∧ v = boxD p P Q})

/-- Paper-local basis adapter to the accepted dimension-changing FiniteLOCC endpoints.
It preserves each owner's basis and both matrix indices. -/
def asFin {I J : Type} [Fintype I] [Fintype J] (rho : Op (I × J)) :
    Op (Fin (Fintype.card I) × Fin (Fintype.card J)) :=
  fun a b => rho ((Fintype.equivFin I).symm a.1, (Fintype.equivFin J).symm a.2)
    ((Fintype.equivFin I).symm b.1, (Fintype.equivFin J).symm b.2)

/-- PDF pp.3--4,8: operational LOCC includes finite adaptive protocols and their limits.
Pointwise topology on finite-dimensional linear maps equals every channel-norm topology;
closure here is taken in the ambient function space, whose linear subspace is closed.
No separable-operation relaxation or uniform bound on rounds is imposed. -/
def IsOperationalLOCC {a b c d : ℕ}
    (L : Superop (Fin a × Fin b) (Fin c × Fin d)) : Prop :=
  L ∈ closure {K | FiniteLOCC K}

/-- PDF pp.3--4,8: one LOCC preprocessing channel followed by one finite Bell scenario. -/
structure BellExperiment (a b : ℕ) where
  outA : ℕ+
  outB : ℕ+
  scenario : BellScenario
  channel : Superop (Fin a × Fin b) (Fin outA × Fin outB)
  local_channel : IsOperationalLOCC channel
  measurement : Measurements scenario (Fin outA) (Fin outB)

/-- PDF p.4, Eq.(13): finite-block optimized nonlocality, before division by blocklength. -/
def rBlock {a b : ℕ} (uniform : Bool) (rho : Op (Fin a × Fin b)) : ℝ≥0∞ :=
  sSup {v | ∃ E : BellExperiment a b,
    v = boxNonlocality uniform (measuredBox E.measurement (E.channel rho))}

/-- PDF pp.4,8, Eqs.(14),(A.1): the infimum is INSIDE every supremum, and the same
channel and measurement compare rho^n with sigma^n for a ONE-copy separable sigma. -/
def tBlock {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (uniform : Bool) (rho : Op (Fin a × Fin b)) (n : ℕ) : ℝ≥0∞ :=
  sSup {v | ∃ E : BellExperiment (a ^ n) (b ^ n),
    v = inputOptimization uniform E.scenario (fun p =>
      sInf {w | ∃ sigma : Op (Fin a × Fin b), IsSeparableDensity sigma ∧
        w = boxD p
          (measuredBox E.measurement (E.channel (dimensionedPower rho n)))
          (measuredBox E.measurement (E.channel (dimensionedPower sigma n)))})}

/-- PDF pp.4,8: asymptotic nonlocality uses limsup and positive copy numbers n+1. -/
def asymptoticR {a b : ℕ} (uniform : Bool) (rho : Op (Fin a × Fin b)) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ => rBlock uniform (dimensionedPower rho (n+1)) /
    (n+1 : ℝ≥0∞)) Filter.atTop

/-- PDF pp.4,8: restricted regularized relative entropy, with the source's iid reference. -/
def asymptoticT {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (uniform : Bool) (rho : Op (Fin a × Fin b)) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ => tBlock uniform rho (n+1) / (n+1 : ℝ≥0∞)) Filter.atTop

/-- PDF pp.4,9: a selected product Kraus leaf of a complete locally realizable filter.
The two complete instruments are performed locally and both outcomes are flagged.
Every product contraction can be rescaled between its factors to fit this form,
so arbitrary single-product successful leaves are included, without nonlocal filters. -/
structure LocalFilter (a b : ℕ) where
  countA : ℕ+
  countB : ℕ+
  alice : Fin countA → Op (Fin a)
  bob : Fin countB → Op (Fin b)
  completeA : IsKrausFamily alice
  completeB : IsKrausFamily bob
  selectedA : Fin countA
  selectedB : Fin countB

/-- PDF pp.4,9: subnormalized successful branch, applied AFTER LOCC. -/
def successfulFilterBranch {a b : ℕ} (F : LocalFilter a b) (rho : Op (Fin a × Fin b)) :
    Op (Fin a × Fin b) :=
  let K := Matrix.kronecker (F.alice F.selectedA) (F.bob F.selectedB)
  K * rho * Kᴴ

/-- PDF pp.4,9: success probability OUTSIDE nonlocality of the normalized branch.
A zero-probability branch has score zero directly, with no conditional state evaluated. -/
def hiddenBlock {a b : ℕ} (uniform : Bool) (rho : Op (Fin a × Fin b)) : ℝ≥0∞ :=
  sSup {v | ∃ E : BellExperiment a b, ∃ F : LocalFilter E.outA E.outB,
    let branch := successfulFilterBranch F (E.channel rho)
    let p := branch.trace.re
    v = if p = 0 then 0 else ENNReal.ofReal p *
      boxNonlocality uniform (measuredBox E.measurement ((p : ℂ)⁻¹ • branch))}

/-- PDF p.4, Eq.(18), and p.9: success-weighted hidden nonlocality per input copy. -/
def asymptoticRH {a b : ℕ} (uniform : Bool) (rho : Op (Fin a × Fin b)) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ => hiddenBlock uniform (dimensionedPower rho (n+1)) /
    (n+1 : ℝ≥0∞)) Filter.atTop

/-- PDF p.3, Eq.(8): correlator CHSH, classical bound 2 and quantum bound 2 sqrt(2). -/
def chshScenario : BellScenario := ⟨2, 2, 2, 2⟩

/-- PDF p.3, Eq.(8): plus correlations except at (1,1); outcomes use signs (-1)^a. -/
def chshCoefficients : BellCoefficients chshScenario :=
  fun x y a b => (if x = 1 ∧ y = 1 then -1 else 1) *
    (if a = b then 1 else -1)

/-- PDF p.3, Eq.(9): flat-unitary shield operator, with the printed X prefactor retained. -/
def flatX (d : ℕ+) (U : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin d × Fin d) :=
  fun a b => if b = (a.2, a.1) then
    (((d : ℝ) * Real.sqrt d)⁻¹ : ℂ) * (U : Op (Fin d)) a.1 a.2 else 0

/-- PDF p.3, Eq.(9): Y = sqrt(d) X^Gamma, with Gamma only on Bob's shield. -/
def flatY (d : ℕ+) (U : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin d × Fin d) :=
  (Real.sqrt d : ℂ) • transposeSecond (flatX d U)

/-- PDF p.3, Eq.(9): mixing probability, with denominator sqrt(d)+1. -/
def flatProbability (d : ℕ+) : ℝ := (Real.sqrt d + 1)⁻¹

/-- PDF p.3, Eq.(9): constructed approximate private bit on the physical AA':BB' cut.
The source prints flat modulus 1/d. Changed to 1/sqrt(d) in theorem hypotheses:
unitarity, the named QFT example and traceNorm X=1 force this correction. -/
def pptPrivate (d : ℕ+) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Op ((Fin 2 × Fin d) × (Fin 2 × Fin d)) :=
  let X := flatX d U
  let Y := flatY d U
  let p := flatProbability d
  let noise : Op ((Fin 2 × Fin 2) × (Fin d × Fin d)) :=
    fun a b => (p/2 : ℂ) *
      (if a.1 = (0,1) ∧ b.1 = (0,1) then (cfc Real.sqrt (Y * Yᴴ)) a.2 b.2
      else if a.1 = (1,0) ∧ b.1 = (1,0) then (cfc Real.sqrt (Yᴴ * Y)) a.2 b.2 else 0)
  partyCut ((1-p : ℂ) • xForm X + noise)

/-- PDF p.7, Eq.(A.8): exact computed family, q=1/3, d=m^2, k=m.
Normalizer has BOTH exponents m; no density, proximity or key premise is substituted. -/
def hidingResource (m : ℕ) :
    Op ((Fin 2 × (Fin m → Fin m → Fin (m^2))) ×
      (Fin 2 × (Fin m → Fin m → Fin (m^2)))) :=
  let tau1 := hidingOne (m^2) m
  let tau2 := hidingTwo (m^2) m
  let diag := (1/6 : ℂ) • (tau1 + tau2)
  let off := (1/6 : ℂ) • (tau1 - tau2)
  let odd := (1/6 : ℂ) • tau2
  let tensor := fun X : Op ((Fin m → Fin (m^2)) × (Fin m → Fin (m^2))) =>
    fun a b : (Fin m → Fin m → Fin (m^2)) × (Fin m → Fin m → Fin (m^2)) =>
      ∏ t, X (a.1 t, a.2 t) (b.1 t, b.2 t)
  partyCut (fun a b => ((2*(1/3 : ℂ)^m + 2*(1/6 : ℂ)^m)⁻¹) *
    (if (a.1 = (0,0) ∧ b.1 = (0,0)) ∨ (a.1 = (1,1) ∧ b.1 = (1,1)) then
      tensor diag a.2 b.2
    else if (a.1 = (0,0) ∧ b.1 = (1,1)) ∨ (a.1 = (1,1) ∧ b.1 = (0,0)) then
      tensor off a.2 b.2
    else if (a.1 = (0,1) ∧ b.1 = (0,1)) ∨ (a.1 = (1,0) ∧ b.1 = (1,0)) then
      tensor odd a.2 b.2 else 0))

/-- PDF pp.3,7: tensor product with both owners' registers grouped together. -/
def paired {I J K L : Type} (rho : Op (I × J)) (sigma : Op (K × L)) :
    Op ((I × K) × (J × L)) :=
  fun a b => rho (a.1.1,a.2.1) (b.1.1,b.2.1) * sigma (a.1.2,a.2.2) (b.1.2,b.2.2)

-- Sanity checks pin the concrete definitions; no target theorem is proved here.
example {I J : Type} (X : Op (I × J)) : transposeSecond (transposeSecond X) = X := rfl

example {S : BellScenario} (P : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb)) : bellValue (fun _ _ _ _ => 0) P = 0 := by
  simp [bellValue]

example : chshCoefficients 1 1 0 0 = -1 := by
  norm_num [chshCoefficients, chshScenario] <;> rfl

example : chshCoefficients 0 1 0 0 = 1 := by
  norm_num [chshCoefficients, chshScenario] <;> rfl

example {I : Type} [Fintype I] (p : I → ℝ) : classicalKLBits p p = 0 := by
  have h : ¬ ∃ i, 0 < p i ∧ p i = 0 := by
    rintro ⟨i, hi, he⟩
    exact (ne_of_gt hi) he
  simp only [classicalKLBits, if_neg h]
  have hsum : (∑ i, if p i = 0 then 0 else p i * (Real.log (p i / p i) / Real.log 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hz : p i = 0
    · simp [hz]
    · simp [hz]
  rw [hsum]
  exact ENNReal.ofReal_zero

example {a b : ℕ} : IsOperationalLOCC (fun X : Op (Fin a × Fin b) => X) :=
  subset_closure (FiniteLOCC.identity a b)

example {I J : Type} [Fintype I] [Fintype J] (rho : Op (I × J)) (a b) :
    dimensionedPower (asFin rho) 0 a b = 1 := by
  simp [dimensionedPower, QAlgorithms.Papers.Independent.Information100.P80.groupedPower]

example {I J K L : Type} (rho : Op (I × J)) (sigma : Op (K × L)) (a b) :
    paired rho sigma a b = rho (a.1.1,a.2.1) (b.1.1,b.2.1) *
      sigma (a.1.2,a.2.2) (b.1.2,b.2.2) := rfl

example : flatProbability 1 = 1/2 := by
  norm_num [flatProbability]

example (d : ℕ+) (U : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) :
    flatX d U (i,j) (j,i) =
      (((d : ℝ) * Real.sqrt d)⁻¹ : ℂ) * (U : Op (Fin d)) i j := by
  simp [flatX]

example (S : BellScenario) (f : (Fin S.nx × Fin S.ny → ℝ) → ℝ≥0∞) :
    inputOptimization true S f = f (fun _ => ((S.nx : ℝ) * (S.ny : ℝ))⁻¹) := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P09


