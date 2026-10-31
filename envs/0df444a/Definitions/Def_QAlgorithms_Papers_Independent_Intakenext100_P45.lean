-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P45
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:54:53.927343+00:00
-- url     : https://prove2.me/theorems/858e1a60-5d30-4fa7-80ed-c869d1fb0e0c
-- title:
--   Definitions for Asymptotic Error Rates in Quantum Hypothesis Testing
-- statement:
--   The objects the formalized statements of *Asymptotic Error Rates in Quantum Hypothesis Testing* (arXiv:0708.4282) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `chernoffOverlap`: PDF p.9 (11): oriented trace overlap.
--   - `chernoffInfimum`: PDF p.16 (26): infimum, with no assertion of attainment.
--   - `chernoffDistance`: PDF p.9 (11): extended Chernoff distance, with -log(0)=+infinity.
--   - `rateTerm`: PDF p.8: positive-copy rate term; k represents n=k+1, avoiding 0 times infinity.
--   - `HasRate`: PDF p.8: an actual extended limit, rather than a chosen default value of a limit.
--   - `typeIError`: PDF pp.6,8: alpha accepts the alternative.
--   - `typeIIError`: PDF pp.6,8: beta is acceptance of the null under the alternative.
--   - `bayesError`: PDF pp.6,10 (18): arbitrary positive weights need not sum to one.
--   - `helstromError`: PDF pp.8--9 (10): the Helstrom expression with the single outer factor 1/2.
--   - `traceDist`: PDF p.17: unsquared trace distance.
--   - `SpectralPair`: PDF p.9 (12): chosen unitary eigenbases, retained even in degenerate eigenspaces.
--   - `basisWeight`: PDF p.9 (12): eigenbasis overlap weight.
--   - `spectralP`: PDF p.9 (12): p distribution, before normalization is asserted.
--   - `spectralQ`: PDF p.9 (12): q distribution.
--   - `kl`: PDF p.10 (16): classical relative entropy in nats, including support failure.
--   - `classicalOverlap`: PDF pp.19,21: scalar trace overlap, with 0^0=1 and inverse powers zero on the kernel.
--   - `classicalCoefficient`: PDF p.19: classical Chernoff coefficient.
--   - `classicalDistance`: PDF p.19: classical Chernoff distance in nats.
--   - `exponentOf`: PDF p.21 (42): the genuine extended supremum; the divisor is positive on Ico 0 1.
--   - `classicalExponent`: PDF p.21 (42): classical Hoeffding exponent.
--   - `quantumExponent`: PDF p.25 (44): quantum Hoeffding exponent.
--   - `Common`: PDF p.22: common support; coordinates with zero basis overlap are excluded too.
--   - `overlapMass`: PDF p.22: mass p(B).
--   - `overlapConditionalLaw`: PDF p.22: conditional law, used only when mass p q is positive.
--   - `otherConditional`: PDF p.22: the other conditional law on the SAME common-support type.
--   - `conditionalExponent`: PDF p.23: conditional exponent.
--   - `SamePositiveSupport`: PDF p.21: equivalence of finite laws, without positivity of ambient zero coordinates.
--   - `iidLaw`: PDF p.21: IID product of a finite law.
--   - `RandomizedTest`: PDF pp.20--21: randomized test, accepting H1 with the indicated probability.
--   - `classicalAlpha`: PDF p.21: classical type-I error.
--   - `classicalBeta`: PDF p.21: classical type-II error.
--   - `classicalError`: PDF p.10 (17): weighted classical error.
--   - `ClassicalTestSequence`: PDF p.21: every block length is positive.
--   - `alphaSeq`: PDF p.21: alpha sequence for the original IID laws.
--   - `betaSeq`: PDF p.21: beta sequence for the original IID laws.
--   - `ClassicalHBCL`: PDF p.21, Theorem 3: the two clauses of the HBCL tradeoff, with strict converse.
--   - `ObservableWords`: PDF p.22: actual observable word space, with doubly impossible words removed.
--   - `NullAdmissible`: PDF p.22: nonrandomized tests are explicitly Bool-valued.
--   - `observableOfCommon`: PDF p.23: restriction to B^n. Its word is observable since each p coordinate is positive.
--   - `restrictTest`: PDF p.23: restriction of a nonrandomized test.
--   - `observableAlpha`: PDF p.23: actual original alpha of a nonrandomized observable-space test.
--   - `observableBeta`: PDF p.23: actual original beta.
--   - `restrictedAlpha`: PDF p.23: conditional alpha on B^n.
--   - `restrictedBeta`: PDF p.23: conditional beta on B^n.
--   - `quantumArc`: PDF pp.19--20: normalized product arc, generally not self-adjoint.
--   - `quantumArcLog`: PDF p.20: logarithm of the arc by similarity to its positive definite sandwich. Used with invertible rho,sigma. No self-adjoint cfc is applied to the arc itself.
--   - `arcRelative`: PDF p.20 (39): finite trace relative entropy of the arc.
--   - `DiagonalizesNonnegative`: PDF p.26: positive-spectrum diagonalization data; inverses are explicit, not a default inverse.
--   - `nonnegativeSpectrumLog`: PDF p.26: spectral log for diagonalizable nonnegative-spectrum products. The zero eigenvalue has log value zero. The fallback is unused on the products in the theorem; no diagonalization premise is imposed on the theorem's data.
--   - `generalizedRelative`: PDF p.26: finite trace extension, with Y positive but possibly unnormalized/singular.
--   - `supportConditionalEntropy`: PDF pp.25--26: conditional entropy-type expression, retaining multiplication order.
--   - `hellingerArc`: PDF p.19: classical Hellinger arc, including harmless zero ambient coordinates.
--   - `logDerivative`: PDF p.19: logarithmic derivative, used where common support guarantees analyticity.
--   - `Profile`: PDF pp.24--25: full finite-tail shape, retaining strict convexity only for distinct conditionals.
--   - `constrainedTypeII`: PDF p.30 (53): optimum over ALL effects, including joint effects on tensor copies.
--   - `QuantumTests`: PDF pp.8,27: arbitrary sequence of joint effects, independent of which hypothesis holds.
--   - `quantumAlpha`: PDF pp.8,27: the alpha error sequence for actual tensor copies.
--   - `quantumBeta`: PDF pp.8,27: the beta error sequence.
--   - `densityIdempotence`: PDF p.17: pure density, with normalization supplied by IsDensityMatrix at every use.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, https://arxiv.org/abs/0708.4282v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

/-! Audenaert--Nussbaum--Szkoła--Verstraete, arXiv:0708.4282v1.
Natural logarithms. Copy index k means the positive number k+1.
The zero spectral power is the identity, as in Section 4.4; infima need not
be attained. Accepted-library imports use the independent-paper override.
Compilation and independent moderation are pending the batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology
open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)
open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.9 (11): oriented trace overlap. -/
def chernoffOverlap (rho sigma : Mat I) (s : ℝ) : ℝ :=
  (positiveMatrixRpow rho (1-s) * positiveMatrixRpow sigma s).trace.re

/-- PDF p.16 (26): infimum, with no assertion of attainment. -/
def chernoffInfimum (rho sigma : Mat I) : ℝ := sInf (chernoffOverlap rho sigma '' Set.Icc 0 1)

/-- PDF p.9 (11): extended Chernoff distance, with -log(0)=+infinity. -/
def chernoffDistance (rho sigma : Mat I) : EReal := -logNonnegativeExtended (chernoffInfimum rho sigma)

/-- PDF p.8: positive-copy rate term; k represents n=k+1, avoiding 0 times infinity. -/
def rateTerm (a : ℝ) (k : ℕ) : EReal :=
  ((1 / ((k+1 : ℕ) : ℝ) : ℝ) : EReal) * (-logNonnegativeExtended a)

/-- PDF p.8: an actual extended limit, rather than a chosen default value of a limit. -/
def HasRate (a : ℕ → ℝ) (r : EReal) : Prop :=
  Tendsto (fun k => rateTerm (a k) k) atTop (nhds r)

/-- PDF pp.6,8: alpha accepts the alternative. -/
def typeIError (rho : Mat I) (P : Mat I) : ℝ := (P * rho).trace.re

/-- PDF pp.6,8: beta is acceptance of the null under the alternative. -/
def typeIIError (sigma : Mat I) (P : Mat I) : ℝ := ((1-P) * sigma).trace.re

/-- PDF pp.6,10 (18): arbitrary positive weights need not sum to one. -/
def bayesError (rho sigma P : Mat I) (a b : ℝ) : ℝ :=
  a * typeIError rho P + b * typeIIError sigma P

/-- PDF pp.8--9 (10): the Helstrom expression with the single outer factor 1/2. -/
def helstromError (rho sigma : Mat I) (a b : ℝ) : ℝ :=
  (1-traceNorm ((b : ℂ) • sigma - (a : ℂ) • rho))/2

/-- PDF p.17: unsquared trace distance. -/
def traceDist (rho sigma : Mat I) : ℝ := traceNorm (rho-sigma)/2

/-- PDF p.9 (12): chosen unitary eigenbases, retained even in degenerate eigenspaces. -/
structure SpectralPair (rho sigma : Mat I) where
  leftBasis : Matrix.unitaryGroup I ℂ
  rightBasis : Matrix.unitaryGroup I ℂ
  leftValues : I → ℝ
  rightValues : I → ℝ
  left_nonneg : ∀ i, 0 ≤ leftValues i
  right_nonneg : ∀ i, 0 ≤ rightValues i
  left_spectral : rho = (leftBasis : Mat I) *
    Matrix.diagonal (fun i => (leftValues i : ℂ)) * (leftBasis : Mat I)ᴴ
  right_spectral : sigma = (rightBasis : Mat I) *
    Matrix.diagonal (fun i => (rightValues i : ℂ)) * (rightBasis : Mat I)ᴴ

/-- PDF p.9 (12): eigenbasis overlap weight. -/
def basisWeight (U V : Mat I) (i j : I) : ℝ := Complex.normSq ((Uᴴ * V) i j)

/-- PDF p.9 (12): p distribution, before normalization is asserted. -/
def spectralP {rho sigma : Mat I} (D : SpectralPair rho sigma) : I × I → ℝ :=
  fun ij => D.leftValues ij.1 * basisWeight D.leftBasis D.rightBasis ij.1 ij.2

/-- PDF p.9 (12): q distribution. -/
def spectralQ {rho sigma : Mat I} (D : SpectralPair rho sigma) : I × I → ℝ :=
  fun ij => D.rightValues ij.2 * basisWeight D.leftBasis D.rightBasis ij.1 ij.2

/-- PDF p.10 (16): classical relative entropy in nats, including support failure. -/
def kl (p q : I → ℝ) : EReal :=
  QAlgorithms.Papers.Independent.Dependency50.P28.classicalD (.finite 1 (by norm_num)) p q

/-- PDF pp.19,21: scalar trace overlap, with 0^0=1 and inverse powers zero on the kernel. -/
def classicalOverlap (p q : I → ℝ) (s : ℝ) : ℝ := ∑ i, (p i) ^ (1-s) * (q i) ^ s

/-- PDF p.19: classical Chernoff coefficient. -/
def classicalCoefficient (p q : I → ℝ) : ℝ :=
  sInf (classicalOverlap p q '' Set.Icc 0 1)

/-- PDF p.19: classical Chernoff distance in nats. -/
def classicalDistance (p q : I → ℝ) : EReal :=
  -logNonnegativeExtended (classicalCoefficient p q)

/-- PDF p.21 (42): the genuine extended supremum; the divisor is positive on Ico 0 1. -/
def exponentOf (Q : ℝ → ℝ) (r : ℝ) : EReal :=
  sSup {v | ∃ s ∈ Set.Ico (0 : ℝ) 1,
    v = (((1-s)⁻¹ : ℝ) : EReal) *
      (((-r*s : ℝ) : EReal) - logNonnegativeExtended (Q s))}

/-- PDF p.21 (42): classical Hoeffding exponent. -/
def classicalExponent (p q : I → ℝ) (r : ℝ) : EReal :=
  exponentOf (classicalOverlap p q) r

/-- PDF p.25 (44): quantum Hoeffding exponent. -/
def quantumExponent (rho sigma : Mat I) (r : ℝ) : EReal :=
  exponentOf (chernoffOverlap rho sigma) r

/-- PDF p.22: common support; coordinates with zero basis overlap are excluded too. -/
abbrev Common (p q : I → ℝ) := {i : I // 0 < p i ∧ 0 < q i}

/-- PDF p.22: mass p(B). -/
def overlapMass (p q : I → ℝ) : ℝ := ∑ i : Common p q, p i.1

/-- PDF p.22: conditional law, used only when mass p q is positive. -/
def overlapConditionalLaw (p q : I → ℝ) : Common p q → ℝ := fun i => p i.1 / overlapMass p q

/-- PDF p.22: the other conditional law on the SAME common-support type. -/
def otherConditional (p q : I → ℝ) : Common p q → ℝ := fun i => q i.1 / overlapMass q p

/-- PDF p.23: conditional exponent. -/
def conditionalExponent (p q : I → ℝ) (r : ℝ) : EReal :=
  classicalExponent (overlapConditionalLaw p q) (otherConditional p q) r

/-- PDF p.21: equivalence of finite laws, without positivity of ambient zero coordinates. -/
def SamePositiveSupport (p q : I → ℝ) : Prop := ∀ i, (0 < p i ↔ 0 < q i)

/-- PDF p.21: IID product of a finite law. -/
def iidLaw (p : I → ℝ) (n : ℕ) (x : Fin n → I) : ℝ := ∏ j, p (x j)

/-- PDF pp.20--21: randomized test, accepting H1 with the indicated probability. -/
abbrev RandomizedTest (I : Type) := I → Set.Icc (0 : ℝ) 1

/-- PDF p.21: classical type-I error. -/
def classicalAlpha (p : I → ℝ) (f : RandomizedTest I) : ℝ := ∑ i, p i * (f i).1

/-- PDF p.21: classical type-II error. -/
def classicalBeta (q : I → ℝ) (f : RandomizedTest I) : ℝ := ∑ i, q i * (1-(f i).1)

/-- PDF p.10 (17): weighted classical error. -/
def classicalError (p q : I → ℝ) (a b : ℝ) (f : RandomizedTest I) : ℝ :=
  a * classicalAlpha p f + b * classicalBeta q f

/-- PDF p.21: every block length is positive. -/
abbrev ClassicalTestSequence (I : Type) := (k : ℕ) → RandomizedTest (Fin (k+1) → I)

/-- PDF p.21: alpha sequence for the original IID laws. -/
def alphaSeq (p : I → ℝ) (f : ClassicalTestSequence I) (k : ℕ) : ℝ :=
  classicalAlpha (iidLaw p (k+1)) (f k)

/-- PDF p.21: beta sequence for the original IID laws. -/
def betaSeq (q : I → ℝ) (f : ClassicalTestSequence I) (k : ℕ) : ℝ :=
  classicalBeta (iidLaw q (k+1)) (f k)

/-- PDF p.21, Theorem 3: the two clauses of the HBCL tradeoff, with strict converse. -/
def ClassicalHBCL (p q : I → ℝ) : Prop :=
  (∀ r : ℝ, 0 < r → ∃ f : ClassicalTestSequence I, ∃ b : EReal,
    HasRate (alphaSeq p f) (classicalExponent p q r) ∧
    HasRate (betaSeq q f) b ∧ (r : EReal) ≤ b) ∧
  (∀ (f : ClassicalTestSequence I) (a b : EReal) (r : ℝ), 0 < r →
    HasRate (alphaSeq p f) a → HasRate (betaSeq q f) b →
    (r : EReal) < b → a ≤ classicalExponent p q r)

/-- PDF p.22: actual observable word space, with doubly impossible words removed. -/
abbrev ObservableWords (p q : I → ℝ) (n : ℕ) :=
  {x : Fin n → I // 0 < iidLaw p n x ∨ 0 < iidLaw q n x}

/-- PDF p.22: nonrandomized tests are explicitly Bool-valued. -/
def NullAdmissible (p q : I → ℝ) {n : ℕ} (f : ObservableWords p q n → Bool) : Prop :=
  ∀ x, (iidLaw q n x.1 = 0 → f x = false) ∧
    (iidLaw p n x.1 = 0 → f x = true)

/-- PDF p.23: restriction to B^n. Its word is observable since each p coordinate is positive. -/
def observableOfCommon (p q : I → ℝ) {n : ℕ} (x : Fin n → Common p q) : ObservableWords p q n :=
  ⟨fun j => (x j).1, Or.inl (Finset.prod_pos (fun j _ => (x j).2.1))⟩

/-- PDF p.23: restriction of a nonrandomized test. -/
def restrictTest (p q : I → ℝ) {n : ℕ} (f : ObservableWords p q n → Bool) :
    (Fin n → Common p q) → Bool := fun x => f (observableOfCommon p q x)

/-- PDF p.23: actual original alpha of a nonrandomized observable-space test. -/
def observableAlpha (p q : I → ℝ) {n : ℕ} (f : ObservableWords p q n → Bool) : ℝ :=
  ∑ x, if f x then iidLaw p n x.1 else 0

/-- PDF p.23: actual original beta. -/
def observableBeta (p q : I → ℝ) {n : ℕ} (f : ObservableWords p q n → Bool) : ℝ :=
  ∑ x, if f x then 0 else iidLaw q n x.1

/-- PDF p.23: conditional alpha on B^n. -/
def restrictedAlpha (p q : I → ℝ) {n : ℕ} (f : ObservableWords p q n → Bool) : ℝ :=
  ∑ x : Fin n → Common p q,
    if restrictTest p q f x then iidLaw (overlapConditionalLaw p q) n x else 0

/-- PDF p.23: conditional beta on B^n. -/
def restrictedBeta (p q : I → ℝ) {n : ℕ} (f : ObservableWords p q n → Bool) : ℝ :=
  ∑ x : Fin n → Common p q,
    if restrictTest p q f x then 0 else iidLaw (otherConditional p q) n x

/-- PDF pp.19--20: normalized product arc, generally not self-adjoint. -/
def quantumArc (rho sigma : Mat I) (s : ℝ) : Mat I :=
  ((chernoffOverlap rho sigma s)⁻¹ : ℂ) • (positiveMatrixRpow rho (1-s) * positiveMatrixRpow sigma s)

/-- PDF p.20: logarithm of the arc by similarity to its positive definite sandwich.
Used with invertible rho,sigma. No self-adjoint cfc is applied to the arc itself. -/
def quantumArcLog (rho sigma : Mat I) (s : ℝ) : Mat I :=
  let R := positiveMatrixRpow rho ((1-s)/2)
  let Ri := positiveMatrixRpow rho (-((1-s)/2))
  R * cfc Real.log (((chernoffOverlap rho sigma s)⁻¹ : ℂ) •
    (R * positiveMatrixRpow sigma s * R)) * Ri

/-- PDF p.20 (39): finite trace relative entropy of the arc. -/
def arcRelative (rho sigma Y : Mat I) (s : ℝ) : ℝ :=
  (quantumArc rho sigma s * (quantumArcLog rho sigma s - cfc Real.log Y)).trace.re

/-- PDF p.26: positive-spectrum diagonalization data; inverses are explicit, not a default inverse. -/
def DiagonalizesNonnegative (X : Mat I) (d : (I → ℝ) × Mat I × Mat I) : Prop :=
  (∀ i, 0 ≤ d.1 i) ∧ d.2.1 * d.2.2 = 1 ∧ d.2.2 * d.2.1 = 1 ∧
    X = d.2.1 * Matrix.diagonal (fun i => (d.1 i : ℂ)) * d.2.2

/-- PDF p.26: spectral log for diagonalizable nonnegative-spectrum products.
The zero eigenvalue has log value zero. The fallback is unused on the products in the theorem;
no diagonalization premise is imposed on the theorem's data. -/
def nonnegativeSpectrumLog (X : Mat I) : Mat I :=
  if h : ∃ d, DiagonalizesNonnegative X d then
    let d := h.choose
    d.2.1 * Matrix.diagonal (fun i => (Real.log (d.1 i) : ℂ)) * d.2.2
  else 0

/-- PDF p.26: finite trace extension, with Y positive but possibly unnormalized/singular. -/
def generalizedRelative (X Y : Mat I) : ℝ :=
  (X * (nonnegativeSpectrumLog X - cfc Real.log Y)).trace.re

/-- PDF pp.25--26: conditional entropy-type expression, retaining multiplication order. -/
def supportConditionalEntropy (rho sigma : Mat I) : ℝ :=
  let psi := (rho * support sigma).trace.re
  let R := ((psi⁻¹ : ℝ) : ℂ) • rho
  (R * (cfc Real.log R - cfc Real.log sigma) * support sigma).trace.re

/-- PDF p.19: classical Hellinger arc, including harmless zero ambient coordinates. -/
def hellingerArc (p q : I → ℝ) (s : ℝ) : I → ℝ :=
  fun i => (p i) ^ (1-s) * (q i) ^ s / classicalOverlap p q s

/-- PDF p.19: logarithmic derivative, used where common support guarantees analyticity. -/
def logDerivative (p q : I → ℝ) (s : ℝ) : ℝ :=
  deriv (fun t : ℝ => Real.log (classicalOverlap p q t)) s

/-- PDF pp.24--25: full finite-tail shape, retaining strict convexity only for distinct conditionals. -/
def Profile (p q : I → ℝ) (e : ℝ → EReal) : Prop :=
  let a := -Real.log (overlapMass q p)
  let b := -Real.log (overlapMass p q)
  let h := kl (overlapConditionalLaw p q) (otherConditional p q)
  let hrev := kl (otherConditional p q) (overlapConditionalLaw p q)
  (∀ r : ℝ, 0 ≤ r → r < a → e r = ⊤) ∧
  e a = (b : EReal) + hrev ∧
  (b : EReal) + hrev = kl (fun i => if 0 < p i ∧ 0 < q i then q i / overlapMass q p else 0) p ∧
  (a : EReal) + h = kl (fun i => if hi : 0 < p i ∧ 0 < q i then p i / overlapMass p q else 0) q ∧
  (∀ r : ℝ, a ≤ r → e r ≠ ⊤ ∧ e r ≠ ⊥) ∧
  AntitoneOn e (Set.Ici a) ∧
  ConvexOn ℝ (Set.Ici a) (fun r => (e r).toReal) ∧
  (∀ r : ℝ, a + h.toReal ≤ r → e r = (b : EReal)) ∧
  (overlapConditionalLaw p q ≠ otherConditional p q →
    StrictConvexOn ℝ (Set.Icc a (a+h.toReal)) (fun r => (e r).toReal) ∧
    StrictAntiOn e (Set.Icc a (a+h.toReal))) ∧
  (overlapConditionalLaw p q = otherConditional p q →
    ∀ r : ℝ, a ≤ r → e r = (b : EReal))

/-- PDF p.30 (53): optimum over ALL effects, including joint effects on tensor copies. -/
def constrainedTypeII (rho sigma : Mat I) (eps : ℝ) (k : ℕ) : ℝ :=
  sInf {v | ∃ P : Mat (Fin (k+1) → I), IsEffect P ∧
    typeIError (copies (k+1) rho) P ≤ eps ∧ v = typeIIError (copies (k+1) sigma) P}

/-- PDF pp.8,27: arbitrary sequence of joint effects, independent of which hypothesis holds. -/
abbrev QuantumTests (I : Type) := (k : ℕ) → Mat (Fin (k+1) → I)

/-- PDF pp.8,27: the alpha error sequence for actual tensor copies. -/
def quantumAlpha (rho : Mat I) (P : QuantumTests I) (k : ℕ) : ℝ :=
  typeIError (copies (k+1) rho) (P k)

/-- PDF pp.8,27: the beta error sequence. -/
def quantumBeta (sigma : Mat I) (P : QuantumTests I) (k : ℕ) : ℝ :=
  typeIIError (copies (k+1) sigma) (P k)

/-- PDF p.17: pure density, with normalization supplied by IsDensityMatrix at every use. -/
def densityIdempotence (rho : Mat I) : Prop := rho * rho = rho

/-! Small-case sanity tests for the locally constructed interfaces. -/

example : -logNonnegativeExtended 0 = ⊤ := by
  simp [logNonnegativeExtended]

example (k : ℕ) : rateTerm 1 k = 0 := by
  simp [rateTerm, logNonnegativeExtended]

example (p : I → ℝ) : iidLaw p 0 (fun i => Fin.elim0 i) = 1 := by
  simp [iidLaw]

example (rho : Mat I) : typeIError rho 0 = 0 := by simp [typeIError]

example (sigma : Mat I) : typeIIError sigma 1 = 0 := by simp [typeIIError]

example (A : Mat I) : quantumExponent A A 0 = exponentOf (chernoffOverlap A A) 0 := rfl

example (X Y : Mat I) : generalizedRelative X Y =
    (X * (nonnegativeSpectrumLog X - cfc Real.log Y)).trace.re := rfl

example : positiveMatrixRpow (0 : Mat (Fin 1)) 1 = 0 := by
  simp [positiveMatrixRpow]

open scoped Matrix.Norms.L2Operator in
example (A : Mat I) (hA : A.IsHermitian) : positiveMatrixRpow A 0 = 1 := by
  simp only [positiveMatrixRpow, Real.rpow_zero]
  exact cfc_const_one ℝ A hA.isSelfAdjoint

example (X : Mat I) : generalizedRelative X X =
    (X * (nonnegativeSpectrumLog X - cfc Real.log X)).trace.re := rfl

section HilbertAppendix

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass operatorTrace traceNormValue)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end HilbertAppendix

end QAlgorithms.Papers.Independent.Intakenext100.P45


