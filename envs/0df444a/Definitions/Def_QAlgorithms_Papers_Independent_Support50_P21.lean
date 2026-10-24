-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21
-- name    : QAlgorithms_Papers_Independent_Support50_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T20:37:22.219454+00:00
-- url     : https://prove2.me/theorems/349758de-e457-4621-934e-3b8f8cef6dc4
-- title:
--   Definitions for Min- and Max- Relative Entropies and a New Entanglement Monotone
-- statement:
--   The objects the formalized statements of *Min- and Max- Relative Entropies and a New Entanglement Monotone* (arXiv:0803.2770) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Le`: PDF pp.2–3: Loewner order, expressed by positivity of the difference.
--   - `dMin`: PDF p.3, (9): support overlap, including +infinity at zero overlap.
--   - `unnormalizedPetz`: PDF p.3, (11): unnormalized Petz expression. No division by Tr rho. Only orders in (0,1) are used; zero overlap gives +infinity.
--   - `weakPositive`: PDF pp.2–3: weak positive spectral projector includes the zero eigenspace.
--   - `strictPositive`: PDF pp.2,7: strict positive spectral projector excludes the zero eigenspace.
--   - `largestEigenvalue`: PDF p.3, (7): largest eigenvalue. Uses occur on nonempty finite spectra.
--   - `thresholdSet`: PDF p.3, (8): the positive scalar parameters with vanishing positive-part trace.
--   - `unnormalizedRelativeBits`: PDF p.5, (27): Umegaki entropy in bits, with its support guard. The spectral log on the kernel is harmless only in the guarded trace.
--   - `traceSmoothingBall`: PDF p.7, Definition 4: full trace-norm ball with the source trace cap.
--   - `traceSmoothMax`: PDF p.7, Definition 4: infimum smoothing in the FIRST argument only.
--   - `traceSmoothMin`: PDF p.7, Definition 4: supremum smoothing in the FIRST argument only.
--   - `hMin`: PDF p.3, (12): unconditional min entropy.
--   - `hMax`: PDF p.3, (13): the paper's rank-based max entropy.
--   - `conditionalMin`: PDF p.3, (14): reference-state conditional min entropy. Printed first line uses rho_B; corrected to sigma_B using the preceding substitution and the second line of (14). Independent moderation required.
--   - `conditionalMax`: PDF p.3, (15): reference-state conditional rank-based max entropy.
--   - `mutualMin`: PDF p.3, Definition 3: min mutual information with fixed original marginals.
--   - `mutualMax`: PDF p.3, Definition 3: max mutual information.
--   - `smoothHMin`: PDF pp.4,7: smooth unconditional min entropy with the paper's trace-norm ball.
--   - `smoothHMax`: PDF pp.4,7: smooth unconditional rank-based max entropy.
--   - `smoothConditionalMin`: PDF pp.4,7: smooth reference-state conditional min entropy.
--   - `smoothConditionalMax`: PDF pp.4,7: smooth reference-state conditional rank-based max entropy.
--   - `smoothMutualMin`: PDF pp.4,7: smoothing holds the ORIGINAL product of marginals fixed.
--   - `smoothMutualMax`: PDF pp.4,7: smooth max mutual information, with fixed comparison operator.
--   - `chernoffCoefficient`: PDF p.6: support-limit endpoint convention in the Chernoff coefficient. At s=0 the zero spectral power is the support projector, likewise at s=1.
--   - `chernoff`: PDF p.6: Chernoff distance; the theorem also asserts attainment.
--   - `PositiveTensorBasis`: PDF p.7, Definition 5: tensor register at positive length k+1.
--   - `spectralMass`: PDF p.7, (40)–(41): positive-part trace of the difference operator. Every length is k+1, and the threshold is 2^((k+1)*gamma).
--   - `spectralSup`: PDF p.7, (40): extended infimum of the limsup-zero thresholds.
--   - `spectralInf`: PDF p.7, (41): extended supremum of the liminf-one thresholds.
--   - `maxAsymptotic`: PDF p.8, (53): inner asymptotic limsup, taken before eps tends to zero.
--   - `minAsymptotic`: PDF p.9, (67): inner asymptotic liminf, taken before eps tends to zero.
--   - `eMax`: PDF p.6, (35): optimization over every separable density matrix.
--   - `eRelative`: PDF p.7, Lemma 13: relative entropy of entanglement.
--   - `bundledMatrix`: PDF p.6, (35): convert the accepted dependent two-party basis to a product basis.
--   - `bundledEMax`: PDF pp.6,12: Emax on accepted bundled states. Theorem 1 asserts finiteness on every density, so toReal here is never an infinity fallback in the LOCC claim.
-- source:
--   Min-and Max-Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, https://arxiv.org/abs/0803.2770v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-! Datta, arXiv:0803.2770v3. All logarithms are in bits. New definitions
are paper-local; accepted support projections, powers, channels, separability,
and adaptive finite LOCC are imported without modification.
Compilation is pending the separate mechanical handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.
open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF pp.2–3: Loewner order, expressed by positivity of the difference. -/
def Le (A B : Mat I) : Prop := (B - A).PosSemidef

/-- PDF p.3, (9): support overlap, including +infinity at zero overlap. -/
def dMin (rho sigma : Mat I) : EReal := -elog (tr (support rho * sigma))

/-- PDF p.3, (11): unnormalized Petz expression. No division by Tr rho.
Only orders in (0,1) are used; zero overlap gives +infinity. -/
def unnormalizedPetz (alpha : ℝ) (rho sigma : Mat I) : EReal :=
  (((alpha - 1)⁻¹ : ℝ) : EReal) *
    elog (tr (supportPower rho alpha * supportPower sigma (1 - alpha)))

/-- PDF pp.2–3: weak positive spectral projector includes the zero eigenspace. -/
def weakPositive (A : Mat I) : Mat I :=
  cfc (fun x : ℝ => if 0 ≤ x then 1 else 0) A

/-- PDF pp.2,7: strict positive spectral projector excludes the zero eigenspace. -/
def strictPositive (A : Mat I) : Mat I :=
  cfc (fun x : ℝ => if 0 < x then 1 else 0) A

/-- PDF p.3, (7): largest eigenvalue. Uses occur on nonempty finite spectra. -/
def largestEigenvalue (A : Mat I) : ℝ := sSup (Set.range (ascEigenvalues A))

/-- PDF p.3, (8): the positive scalar parameters with vanishing positive-part trace. -/
def thresholdSet (rho sigma : Mat I) : Set ℝ :=
  {t | 0 < t ∧ tr (weakPositive (rho - (t : ℂ) • sigma) *
    (rho - (t : ℂ) • sigma)) = 0}

/-- PDF p.5, (27): Umegaki entropy in bits, with its support guard.
The spectral log on the kernel is harmless only in the guarded trace. -/
def unnormalizedRelativeBits (rho sigma : Mat I) : EReal :=
  if SupportIncluded rho sigma then
    (tr (rho * (cfc (fun x : ℝ => Real.logb 2 x) rho -
      cfc (fun x : ℝ => Real.logb 2 x) sigma)) : EReal)
  else ⊤

/-- PDF p.7, Definition 4: full trace-norm ball with the source trace cap. -/
def traceSmoothingBall (eps : ℝ) (rho : Mat I) : Set (Mat I) :=
  {r | r.PosSemidef ∧ traceNorm (r - rho) ≤ eps ∧ tr r ≤ tr rho}

/-- PDF p.7, Definition 4: infimum smoothing in the FIRST argument only. -/
def traceSmoothMax (eps : ℝ) (rho sigma : Mat I) : EReal :=
  sInf {v | ∃ r ∈ traceSmoothingBall eps rho, v = maxRelative r sigma}

/-- PDF p.7, Definition 4: supremum smoothing in the FIRST argument only. -/
def traceSmoothMin (eps : ℝ) (rho sigma : Mat I) : EReal :=
  sSup {v | ∃ r ∈ traceSmoothingBall eps rho, v = dMin r sigma}

/-- PDF p.3, (12): unconditional min entropy. -/
def hMin (rho : Mat I) : EReal := -maxRelative rho 1

/-- PDF p.3, (13): the paper's rank-based max entropy. -/
def hMax (rho : Mat I) : EReal := -dMin rho 1

/-- PDF p.3, (14): reference-state conditional min entropy.
Printed first line uses rho_B; corrected to sigma_B using the preceding
substitution and the second line of (14). Independent moderation required. -/
def conditionalMin (rho : Mat (I × J)) (sigmaB : Mat J) : EReal :=
  -maxRelative rho (Matrix.kronecker (1 : Mat I) sigmaB)

/-- PDF p.3, (15): reference-state conditional rank-based max entropy. -/
def conditionalMax (rho : Mat (I × J)) (sigmaB : Mat J) : EReal :=
  -dMin rho (Matrix.kronecker (1 : Mat I) sigmaB)

/-- PDF p.3, Definition 3: min mutual information with fixed original marginals. -/
def mutualMin (rho : Mat (I × J)) : EReal :=
  dMin rho (Matrix.kronecker (traceRight rho) (traceLeft rho))

/-- PDF p.3, Definition 3: max mutual information. -/
def mutualMax (rho : Mat (I × J)) : EReal :=
  maxRelative rho (Matrix.kronecker (traceRight rho) (traceLeft rho))

/-- PDF pp.4,7: smooth unconditional min entropy with the paper's trace-norm ball. -/
def smoothHMin (eps : ℝ) (rho : Mat I) : EReal := -traceSmoothMax eps rho 1

/-- PDF pp.4,7: smooth unconditional rank-based max entropy. -/
def smoothHMax (eps : ℝ) (rho : Mat I) : EReal := -traceSmoothMin eps rho 1

/-- PDF pp.4,7: smooth reference-state conditional min entropy. -/
def smoothConditionalMin (eps : ℝ) (rho : Mat (I × J)) (sigmaB : Mat J) : EReal :=
  -traceSmoothMax eps rho (Matrix.kronecker (1 : Mat I) sigmaB)

/-- PDF pp.4,7: smooth reference-state conditional rank-based max entropy. -/
def smoothConditionalMax (eps : ℝ) (rho : Mat (I × J)) (sigmaB : Mat J) : EReal :=
  -traceSmoothMin eps rho (Matrix.kronecker (1 : Mat I) sigmaB)

/-- PDF pp.4,7: smoothing holds the ORIGINAL product of marginals fixed. -/
def smoothMutualMin (eps : ℝ) (rho : Mat (I × J)) : EReal :=
  traceSmoothMin eps rho (Matrix.kronecker (traceRight rho) (traceLeft rho))

/-- PDF pp.4,7: smooth max mutual information, with fixed comparison operator. -/
def smoothMutualMax (eps : ℝ) (rho : Mat (I × J)) : EReal :=
  traceSmoothMax eps rho (Matrix.kronecker (traceRight rho) (traceLeft rho))

/-- PDF p.6: support-limit endpoint convention in the Chernoff coefficient.
At s=0 the zero spectral power is the support projector, likewise at s=1. -/
def chernoffCoefficient (rho sigma : Mat I) (s : ℝ) : ℝ :=
  tr (supportPower rho s * supportPower sigma (1 - s))

/-- PDF p.6: Chernoff distance; the theorem also asserts attainment. -/
def chernoff (rho sigma : Mat I) : EReal :=
  -elog (sInf (chernoffCoefficient rho sigma '' Set.Icc (0 : ℝ) 1))

/-- PDF p.7, Definition 5: tensor register at positive length k+1. -/
abbrev PositiveTensorBasis (I : Type) (k : ℕ) := Fin (k + 1) → I

/-- PDF p.7, (40)–(41): positive-part trace of the difference operator.
Every length is k+1, and the threshold is 2^((k+1)*gamma). -/
def spectralMass (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k)) (gamma : ℝ) (k : ℕ) : ℝ :=
  let A := rho k - (((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * gamma)) : ℂ) • sigma k
  tr (weakPositive A * A)

/-- PDF p.7, (40): extended infimum of the limsup-zero thresholds. -/
def spectralSup (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k)) : EReal :=
  sInf {v : EReal | ∃ gamma : ℝ, v = (gamma : EReal) ∧
    Filter.limsup (spectralMass rho sigma gamma) atTop = 0}

/-- PDF p.7, (41): extended supremum of the liminf-one thresholds. -/
def spectralInf (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k)) : EReal :=
  sSup {v : EReal | ∃ gamma : ℝ, v = (gamma : EReal) ∧
    Filter.liminf (spectralMass rho sigma gamma) atTop = 1}

/-- PDF p.8, (53): inner asymptotic limsup, taken before eps tends to zero. -/
def maxAsymptotic (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k)) (eps : ℝ) : EReal :=
  Filter.limsup (fun k => (((1 / ((k + 1 : ℕ) : ℝ)) : ℝ) : EReal) *
    traceSmoothMax eps (rho k) (sigma k)) atTop

/-- PDF p.9, (67): inner asymptotic liminf, taken before eps tends to zero. -/
def minAsymptotic (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k)) (eps : ℝ) : EReal :=
  Filter.liminf (fun k => (((1 / ((k + 1 : ℕ) : ℝ)) : ℝ) : EReal) *
    traceSmoothMin eps (rho k) (sigma k)) atTop

section Bipartite

variable [Nonempty I] [Nonempty J]

/-- PDF p.6, (35): optimization over every separable density matrix. -/
def eMax (rho : Mat (I × J)) : EReal :=
  sInf {v | ∃ sigma : Mat (I × J), IsSeparableDensity sigma ∧ v = maxRelative rho sigma}

/-- PDF p.7, Lemma 13: relative entropy of entanglement. -/
def eRelative (rho : Mat (I × J)) : EReal :=
  sInf {v | ∃ sigma : Mat (I × J), IsSeparableDensity sigma ∧ v = unnormalizedRelativeBits rho sigma}

end Bipartite

/-- PDF p.6, (35): convert the accepted dependent two-party basis to a product basis. -/
def bundledMatrix (s : FiniteState 2) :
    Mat (Fin (s.dims 0) × Fin (s.dims 1)) :=
  fun x y => s.rho (Fin.cases x.1 (Fin.cases x.2 (fun i => Fin.elim0 i)))
    (Fin.cases y.1 (Fin.cases y.2 (fun i => Fin.elim0 i)))

/-- PDF pp.6,12: Emax on accepted bundled states. Theorem 1 asserts finiteness
on every density, so toReal here is never an infinity fallback in the LOCC claim. -/
def bundledEMax (s : FiniteState 2) : ℝ :=
  letI : Nonempty (Fin (s.dims 0)) := ⟨⟨0, s.positive 0⟩⟩
  letI : Nonempty (Fin (s.dims 1)) := ⟨⟨0, s.positive 1⟩⟩
  (eMax (bundledMatrix s)).toReal

/-! Elementary sanity checks for the new definitions. -/

example : elog 0 = ⊥ := by simp [elog]

example : elog 1 = 0 := by simp [elog]

example : elog 2 = 1 := by norm_num [elog, Real.logb_self_eq_one]

example {rho : Mat I} : IsSubnormalized rho → rho.PosSemidef := fun h => h.1

example (A : Mat I) : Le A A := by
  simpa only [Le, sub_self] using (Matrix.PosSemidef.zero : (0 : Mat I).PosSemidef)

example (rho : Mat I) : hMin rho = -maxRelative rho 1 := rfl

example (rho : Mat (I × J)) (sigma : Mat J) (eps : ℝ) :
    smoothConditionalMax eps rho sigma =
      -traceSmoothMin eps rho (Matrix.kronecker (1 : Mat I) sigma) := rfl

example (rho : Mat (I × J)) (eps : ℝ) :
    smoothMutualMax eps rho =
      traceSmoothMax eps rho (Matrix.kronecker (traceRight rho) (traceLeft rho)) := rfl

example (rho sigma : Mat I) :
    chernoffCoefficient rho sigma 0 = tr (supportPower rho 0 * supportPower sigma 1) := by
  simp only [chernoffCoefficient, sub_zero]

example (rho : Mat I) : dMin rho 0 = ⊤ := by
  simp [dMin, tr, elog]

example (rho sigma : Mat I) (h : ¬ SupportIncluded rho sigma) :
    unnormalizedRelativeBits rho sigma = ⊤ := by simp [unnormalizedRelativeBits, h]

example : strictPositive (0 : Mat I) = 0 := by
  simp [strictPositive, cfc_zero]

example (rho : Mat I) (h : rho.PosSemidef) : rho ∈ traceSmoothingBall 0 rho := by
  simp [traceSmoothingBall, h, traceNorm, cfc_zero]

example (rho : Mat I) : maxRelative rho rho ≤ 0 := by
  unfold maxRelative
  apply sInf_le
  refine ⟨0, by simp, ?_⟩
  simpa only [Real.rpow_zero, Complex.ofReal_one, one_smul, sub_self] using
    (Matrix.PosSemidef.zero : (0 : Mat I).PosSemidef)

example (rho sigma : Mat I) (h : rho ∈ traceSmoothingBall 0 rho) :
    traceSmoothMax 0 rho sigma ≤ maxRelative rho sigma := by
  unfold traceSmoothMax
  exact sInf_le ⟨rho, h, rfl⟩

example (rho sigma : Mat I) (h : rho ∈ traceSmoothingBall 0 rho) :
    dMin rho sigma ≤ traceSmoothMin 0 rho sigma := by
  unfold traceSmoothMin
  exact le_sSup ⟨rho, h, rfl⟩

example (rho : Mat I) : 1 ∈ thresholdSet rho rho := by
  simp [thresholdSet, tr]

example (s : FiniteState 2) (x y : Fin (s.dims 0) × Fin (s.dims 1)) :
    bundledMatrix s x y = s.rho (Fin.cases x.1 (Fin.cases x.2 (fun i => Fin.elim0 i)))
      (Fin.cases y.1 (Fin.cases y.2 (fun i => Fin.elim0 i))) := rfl

section Statements

variable [Nonempty I] [Nonempty J]

end Statements

end QAlgorithms.Papers.Independent.Support50.P21


