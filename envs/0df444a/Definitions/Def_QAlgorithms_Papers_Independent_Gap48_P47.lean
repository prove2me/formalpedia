-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47
-- name    : QAlgorithms_Papers_Independent_Gap48_P47
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T06:06:39.844088+00:00
-- url     : https://prove2.me/theorems/2d840341-9753-42d3-be63-c72c93d60634
-- title:
--   Definitions for Conditions for the local manipulation of Gaussian states
-- statement:
--   The objects the formalized statements of *Conditions for the local manipulation of Gaussian states* (arXiv:quant-ph/0109126) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TwoModeGaussianDensity`: PDF pp.1--2 and note [12], p.4: actual normalized two-oscillator Gaussian state, specified finite covariance, arbitrary first moments and finite energy. The accepted characteristic uses W(v)=exp(i v^T O); the source's D(z) is W(Sigma^T z). The covariance normalization is unchanged by this reparametrization.
--   - `NormalVector`: PDF p.2: the four real coordinates of the local symplectic normal form.
--   - `associatedVector`: PDF p.2, below (1): compute the unique associated vector from the four determinants. For physical covariances the marginal determinants are positive and the discriminants are nonnegative. The larger correlation singular value is nonnegative, and the sign of the other is fixed by det B. At c=0 both correlations vanish, so the explicit zero branch avoids division by zero. No assertion about nonphysical matrices is used in any theorem.
--   - `logCriterionPolynomial`: PDF p.2: logCriterionPolynomial, transcribed from its explicit definition, not intermediate (8).
--   - `f1`: PDF p.2: f1 for the source and target covariances.
--   - `f2`: PDF p.2: f2. In the stated criteria w2>0 enforces x*y != 0; ordinary division is therefore used only on its nonzero domain.
--   - `w1`: PDF p.3, (9): upper admissible absolute correlation product.
--   - `w2`: PDF p.3, (9): lower admissible absolute correlation product.
--   - `joinOccupation`: PDF pp.1--2: a single retained oscillator followed by m ancillary oscillators. This is a basis relabeling, not a finite occupation cutoff.
--   - `firstOccupation`: PDF pp.1--2: retained occupation coordinate in a local dilation.
--   - `restOccupation`: PDF pp.1--2: all ancillary occupation coordinates, including m=0.
--   - `appendProduct`: PDF pp.1--2 and Fig.1: independent input and ancillary density product, transported to the completed (1+m)-mode space.
--   - `localDilationOutput`: PDF pp.1--2, Fig.1: actual bounded-unitary conjugation followed by the ancillary partial trace. The unitary and ancilla are fixed for every input.
--   - `IsLocalGaussianDilation`: PDF pp.1--2, Fig.1 and p.4 note [10]: one local LOG, with arbitrary finite ancilla count, actual normalized Gaussian environment, and a Gaussian unitary including translations. Its action on EVERY trace-class input is fixed; complete positivity and trace preservation are explicit.
--   - `localProduct`: PDF pp.1--2: tensor product of the two independent local maps, retaining off-diagonal blocks. The inner map acts on Bob and the outer map on Alice.
--   - `LOGReachable`: PDF pp.1--2: actual state convertibility by LOG. The operations may be chosen for this known input, but each is a lawful channel on all inputs. The two ancillas are independent; no shared randomness is introduced.
--   - `LOGInSystemOne`: Proposition 1, PDF pp.2--3: noisy LOG on Alice with reversible Gaussian unitary/translation on Bob, as the proof expressly permits. Independent normal-form changes are included by composition of the local operations.
--   - `LocalCP`: PDF p.2, (3): the EXACT source plus-i local CP constraint for the passive matrix M in Gamma -> M^T Gamma M+G. No invertibility of M or G is required.
--   - `IsAffineLocalGaussian`: PDF p.2, (2)--(3), and note [14], p.4: the affine Gaussian CPTP map, expressed on all actual density operators by its Weyl characteristic. For W(v)=exp(i v^T O), the source passive covariance convention pulls v back to M v. The noise multiplier has /4 because vacuum covariance is I. Summability excludes total-tsum defaults, including on non-Gaussian inputs.
--   - `localSymplecticMatrix`: PDF p.2 and p.4 note [13]: block diagonal local passive matrix S1 direct-sum S2.
--   - `localCongruence`: PDF p.2 and p.4 note [13]: local symplectic action in the source convention.
-- source:
--   Conditions for the local manipulation of Gaussian states, arXiv:quant-ph/0109126v2, https://arxiv.org/abs/quant-ph/0109126v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

/-!
Eisert--Plenio, arXiv:quant-ph/0109126v2, PDF pp.1--4.
Interleaved (X1,P1,X2,P2), hbar=1, vacuum covariance I. All density
operators act on completed oscillator spaces. New definitions are paper-local.
The source's S acts by S^T Gamma S; the accepted Gaussian unitary stores
an active matrix S^T. No measurement, communication, or correlated ancilla
is part of LOG. Six defective source claims are documented in HARD.md.
Compilation is pending the required batch handoff.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P47

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue modeCovarianceBlock
   standardFormCovariance)
open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)
open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P14 (boundedUnitaryConjugation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1--2 and note [12], p.4: actual normalized two-oscillator Gaussian
state, specified finite covariance, arbitrary first moments and finite energy.
The accepted characteristic uses W(v)=exp(i v^T O); the source's D(z) is
W(Sigma^T z). The covariance normalization is unchanged by this reparametrization. -/
structure TwoModeGaussianDensity where
  density : State (FockIndex 2)
  covariance : Cov 2
  gaussian : GaussianWithCovariance density.coefficients covariance

/-- PDF p.2: the four real coordinates of the local symplectic normal form. -/
structure NormalVector where
  one : ℝ
  two : ℝ
  three : ℝ
  four : ℝ

/-- PDF p.2, below (1): compute the unique associated vector from the four
determinants. For physical covariances the marginal determinants are positive
and the discriminants are nonnegative. The larger correlation singular value
is nonnegative, and the sign of the other is fixed by det B. At c=0 both
correlations vanish, so the explicit zero branch avoids division by zero.
No assertion about nonphysical matrices is used in any theorem. -/
def associatedVector (Gamma : Cov 2) : NormalVector :=
  let a := (modeCovarianceBlock Gamma 0 0).det
  let b := (modeCovarianceBlock Gamma 1 1).det
  let p := (modeCovarianceBlock Gamma 0 1).det
  let q := (p ^ 2 - Gamma.det + a * b) / Real.sqrt (a * b)
  let c := Real.sqrt ((q + Real.sqrt (q ^ 2 - 4 * p ^ 2)) / 2)
  ⟨Real.sqrt a, Real.sqrt b, c, if c = 0 then 0 else p / c⟩

/-- PDF p.2: logCriterionPolynomial, transcribed from its explicit definition, not intermediate (8). -/
def logCriterionPolynomial (a b c d : ℝ) : ℝ :=
  (a ^ 2 - 1) + (b ^ 2 - 1) * c ^ 2 * d ^ 2 + 2 * c * d -
    a * b * (c ^ 2 + d ^ 2)

/-- PDF p.2: f1 for the source and target covariances. -/
def f1 (Gamma target : Cov 2) (x y : ℝ) : ℝ :=
  let s := associatedVector Gamma
  let t := associatedVector target
  logCriterionPolynomial t.one s.one (x / s.three) (y / s.four)

/-- PDF p.2: f2. In the stated criteria w2>0 enforces x*y != 0;
ordinary division is therefore used only on its nonzero domain. -/
def f2 (Gamma target : Cov 2) (x y : ℝ) : ℝ :=
  let s := associatedVector Gamma
  let t := associatedVector target
  logCriterionPolynomial t.two s.two (t.three / x) (t.four / y)

/-- PDF p.3, (9): upper admissible absolute correlation product. -/
def w1 (Gamma target : Cov 2) : ℝ :=
  let s := associatedVector Gamma
  let t := associatedVector target
  |s.three * s.four| * t.one / s.one

/-- PDF p.3, (9): lower admissible absolute correlation product. -/
def w2 (Gamma target : Cov 2) : ℝ :=
  let s := associatedVector Gamma
  let t := associatedVector target
  |t.three * t.four| * s.two / t.two

/-- PDF pp.1--2: a single retained oscillator followed by m ancillary oscillators.
This is a basis relabeling, not a finite occupation cutoff. -/
def joinOccupation {m : ℕ} (u : FockIndex 1) (e : FockIndex m) :
    FockIndex (1 + m) :=
  fun j => if h : j.val = 0 then u 0 else e ⟨j.val - 1, by omega⟩

/-- PDF pp.1--2: retained occupation coordinate in a local dilation. -/
def firstOccupation {m : ℕ} (u : FockIndex (1 + m)) : FockIndex 1 :=
  fun _ => u ⟨0, by omega⟩

/-- PDF pp.1--2: all ancillary occupation coordinates, including m=0. -/
def restOccupation {m : ℕ} (u : FockIndex (1 + m)) : FockIndex m :=
  fun j => u ⟨j.val + 1, by omega⟩

/-- PDF pp.1--2 and Fig.1: independent input and ancillary density product,
transported to the completed (1+m)-mode space. -/
def appendProduct {m : ℕ} (X : DensityKernel 1) (sigma : DensityKernel m) :
    DensityKernel (1 + m) :=
  fun u v => X (firstOccupation u) (firstOccupation v) *
    sigma (restOccupation u) (restOccupation v)

/-- PDF pp.1--2, Fig.1: actual bounded-unitary conjugation followed by the
ancillary partial trace. The unitary and ancilla are fixed for every input. -/
def localDilationOutput {m : ℕ} (U : AffineMultimodeGaussianUnitary (1 + m))
    (sigma : DensityKernel m) (X : DensityKernel 1) : DensityKernel 1 :=
  fun u v => ∑' e : FockIndex m,
    boundedUnitaryConjugation U.unitary (appendProduct X sigma)
      (joinOccupation u e) (joinOccupation v e)

/-- PDF pp.1--2, Fig.1 and p.4 note [10]: one local LOG, with arbitrary finite
ancilla count, actual normalized Gaussian environment, and a Gaussian unitary
including translations. Its action on EVERY trace-class input is fixed;
complete positivity and trace preservation are explicit. -/
def IsLocalGaussianDilation (Phi : DensityKernel 1 → DensityKernel 1) : Prop :=
  IsTraceClassChannel Phi ∧
  ∃ (m : ℕ) (sigma : State (FockIndex m)) (gamma : Cov m)
    (U : AffineMultimodeGaussianUnitary (1 + m)),
    GaussianWithCovariance sigma.coefficients gamma ∧
    ∀ X, IsTraceClass X → Phi X = localDilationOutput U sigma.coefficients X

/-- PDF pp.1--2: tensor product of the two independent local maps, retaining
off-diagonal blocks. The inner map acts on Bob and the outer map on Alice. -/
def localProduct (Phi Psi : DensityKernel 1 → DensityKernel 1)
    (X : DensityKernel 2) : DensityKernel 2 :=
  fun u v =>
    Phi (fun a b =>
      Psi (fun c d => X (joinOccupation a c) (joinOccupation b d))
        (restOccupation (m := 1) u) (restOccupation (m := 1) v))
      (firstOccupation (m := 1) u) (firstOccupation (m := 1) v)

/-- PDF pp.1--2: actual state convertibility by LOG. The operations may be
chosen for this known input, but each is a lawful channel on all inputs.
The two ancillas are independent; no shared randomness is introduced. -/
def LOGReachable (rho target : TwoModeGaussianDensity) : Prop :=
  ∃ Phi Psi, IsLocalGaussianDilation Phi ∧ IsLocalGaussianDilation Psi ∧
    localProduct Phi Psi rho.density.coefficients = target.density.coefficients

/-- Proposition 1, PDF pp.2--3: noisy LOG on Alice with reversible Gaussian
unitary/translation on Bob, as the proof expressly permits. Independent
normal-form changes are included by composition of the local operations. -/
def LOGInSystemOne (rho target : TwoModeGaussianDensity) : Prop :=
  ∃ (Phi : DensityKernel 1 → DensityKernel 1)
    (U : AffineMultimodeGaussianUnitary 1),
    IsLocalGaussianDilation Phi ∧
    localProduct Phi (boundedUnitaryConjugation U.unitary)
      rho.density.coefficients = target.density.coefficients

/-- PDF p.2, (3): the EXACT source plus-i local CP constraint for the passive
matrix M in Gamma -> M^T Gamma M+G. No invertibility of M or G is required. -/
def LocalCP (M G : Cov 1) : Prop :=
  G.transpose = G ∧
    (complexify G + Complex.I • complexify (interleavedSymplecticForm 1) -
      Complex.I • complexify
        (M.transpose * interleavedSymplecticForm 1 * M)).PosSemidef

/-- PDF p.2, (2)--(3), and note [14], p.4: the affine Gaussian CPTP map,
expressed on all actual density operators by its Weyl characteristic.
For W(v)=exp(i v^T O), the source passive covariance convention pulls v back
to M v. The noise multiplier has /4 because vacuum covariance is I.
Summability excludes total-tsum defaults, including on non-Gaussian inputs. -/
def IsAffineLocalGaussian (Phi : DensityKernel 1 → DensityKernel 1)
    (M G : Cov 1) : Prop :=
  IsTraceClassChannel Phi ∧ LocalCP M G ∧
  ∃ d : (Fin 1 × Fin 2) → ℝ, ∀ (rho : State (FockIndex 1)) v,
    CharacteristicSummable rho.coefficients (M.mulVec v) ∧
    CharacteristicSummable (Phi rho.coefficients) v ∧
    multimodeWeylTrace (Phi rho.coefficients) v =
      multimodeWeylTrace rho.coefficients (M.mulVec v) *
        covarianceCharacteristicValue G d v

/-- PDF p.2 and p.4 note [13]: block diagonal local passive matrix S1 direct-sum S2. -/
def localSymplecticMatrix (S1 S2 : Cov 1) : Cov 2 :=
  fun i j => if i.1 = j.1 then
    (if i.1 = 0 then S1 (0, i.2) (0, j.2) else S2 (0, i.2) (0, j.2)) else 0

/-- PDF p.2 and p.4 note [13]: local symplectic action in the source convention. -/
def localCongruence (Gamma : Cov 2) (S1 S2 : Cov 1) : Cov 2 :=
  let S := localSymplecticMatrix S1 S2
  S.transpose * Gamma * S

/-! Sanity examples pin the identity-channel polynomial, actual basis ordering,
empty ancilla, uncertainty sign, and block placement. Source proofs are omitted. -/

example (a : ℝ) : logCriterionPolynomial a a 1 1 = 0 := by
  unfold logCriterionPolynomial
  ring

example (Gamma : Cov 2)
    (hthree : (associatedVector Gamma).three ≠ 0)
    (hfour : (associatedVector Gamma).four ≠ 0) :
    f1 Gamma Gamma (associatedVector Gamma).three
      (associatedVector Gamma).four = 0 := by
  dsimp [f1]
  rw [div_self hthree, div_self hfour]
  unfold logCriterionPolynomial
  ring

example {m : ℕ} (u : FockIndex 1) (e : FockIndex m) :
    firstOccupation (joinOccupation u e) = u := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [firstOccupation, joinOccupation]

example (u : FockIndex 1) (e : FockIndex 0) :
    joinOccupation u e 0 = u 0 := by
  simp [joinOccupation]

example : interleavedSymplecticForm 1 (0, 0) (0, 1) = 1 := by
  simp [interleavedSymplecticForm]

example (S1 S2 : Cov 1) :
    localSymplecticMatrix S1 S2 (1, 0) (1, 1) = S2 (0, 0) (0, 1) := by
  simp [localSymplecticMatrix]

end QAlgorithms.Papers.Independent.Gap48.P47


