-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19
-- name    : QAlgorithms_Papers_Independent_Support50_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T20:21:54.646997+00:00
-- url     : https://prove2.me/theorems/a511f286-1113-42ac-a65a-0ea73dbfaa83
-- title:
--   Definitions for Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy
-- statement:
--   The objects the formalized statements of *Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy* (arXiv:1306.1586) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `classicalRenyiBits`: PDF p.12: unnormalized classical Renyi divergence in bits, for alpha>1. Dependency50.P28.classicalD uses natural logs and a different order interface; its value cannot be substituted here. Test support before a negative power.
--   - `filtered`: PDF p.7, Remark 1: the positive filter is not normalized.
--   - `renyiD`: PDF pp.17,19: true selects sandwiched and false selects traditional Petz entropy.
--   - `renyiEnsembleInformation`: PDF p.17, Definition 12: Renyi cq information, before using the block formula. Dependency50.P07.ensembleInformation instead denotes ordinary Holevo information.
--   - `channelInformation`: PDF p.17, Definition 12: supremum over all finite mixed-state input ensembles.
--   - `fixedRadius`: PDF p.24, Definition 21: fixed-center radius, permitting infinite radius.
--   - `informationRadius`: PDF p.17, Definition 13: minimize over output states AFTER maximizing over inputs.
--   - `blockInformation`: PDF p.17, (14): zero-weight unsupported blocks contribute zero in ENNReal.
--   - `InformationExtrema`: PDF pp.17–19: witnesses for the maxima and minima in Definitions 12 and 13. The semantic extrema are not replaced by unattained suprema or infima.
--   - `outputWeightedNorm`: PDF p.19: alpha-norm of a positive output with weight sigma^((1-alpha)/alpha). On the compatible support domain this is the weighted Schatten norm in the source.
--   - `CompatibleCenter`: PDF pp.19,25: admissible centers for the FINITE weighted-norm expression. Singular centers containing every output support are included.
--   - `normRadiusBefore`: PDF p.19, (16): min max log norm, with the inverse-support domain explicit.
--   - `normRadiusAfter`: PDF p.19, (16): min log max norm; finite-dimensional compatible centers give nonempty bounded norm sets, with positive supremum on channels.
--   - `NormExtrema`: PDF p.19: attainment of the finite-domain norm minima and maxima in (16).
--   - `expTwo`: PDF pp.20,25: base-two exponential on extended reals, retaining BOTH endpoints.
--   - `codingBound`: PDF p.20, (17): success upper bound at one specified normalized radius.
--   - `renyiNu`: PDF p.22: the Renyi comparison constant nu in (20), expressed without converting possibly infinite divergences. Claimed50.P48.nu is an output norm, not this two-state constant. On supported states, these traces are 2^(D_3/2 / 2) and 2^(-D_1/2 / 2).
--   - `CenterControl`: PDF p.22: an attained ordinary information-radius center and a uniform finite renyiNu bound. These are witnesses in the conclusions below, never assumed approximation theorems.
--   - `ExponentialAt`: PDF p.24: exponential strong-converse THRESHOLD, without identifying it with capacity.
--   - `InteriorEB`: PDF p.25: interior relative to the finite-dimensional affine TP/HP map space. Entrywise coefficient balls give its usual topology; no CP constraint is placed on candidate perturbations before testing membership in the EB-channel set.
--   - `InteriorHadamard`: PDF p.25: the EB interior condition is on a complement of this SAME channel.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, https://arxiv.org/abs/1306.1586v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

/-! Wilde–Winter–Yang, arXiv:1306.1586v4. All citations are PDF pages; logs are in bits.
The imported paper modules are pinned accepted libraries. In particular, their spectral
calculus, physical codes, tensor channels, and covariance interface are reused. The
unnormalized divergences of Dependency50.P09 and Q of Information100.P56 implement
Definition 4; the trace-normalized divergence of Dependency50.P35 is not substituted.
All new definitions below are local to this paper. Compilation is pending batch handoff. -/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal
open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)
open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)
open QAlgorithms.Papers.Independent.Information100.P56 (sandwichedTrace)
open QAlgorithms.Papers.Independent.Information100.P27 (average)
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)
open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)
open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)
open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)
open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)
open QAlgorithms.Papers.Independent.Claimed50.P26
  (CovariantIrreducible minOutput UnassistedExponentialConverse)

/-- PDF p.12: unnormalized classical Renyi divergence in bits, for alpha>1.
Dependency50.P28.classicalD uses natural logs and a different order interface;
its value cannot be substituted here. Test support before a negative power. -/
def classicalRenyiBits {I : Type} [Fintype I]
    (a : ℝ) (p q : I → ℝ) : EReal :=
  if ∀ i, q i = 0 → p i = 0 then
    ((1 / (a - 1) : ℝ) : EReal) *
      elog (∑ i, if p i = 0 then 0 else p i ^ a * q i ^ (1 - a))
  else ⊤

/-- PDF p.7, Remark 1: the positive filter is not normalized. -/
def filtered {I J : Type} [Fintype J] (Y : Matrix J J ℂ) (N : Superop I J) : Superop I J :=
  fun X => Y * N X * Y

/-- PDF pp.17,19: true selects sandwiched and false selects traditional Petz entropy. -/
def renyiD {I : Type} [Fintype I] [DecidableEq I]
    (sandwiched : Bool) (a : ℝ) (A B : Matrix I I ℂ) : EReal :=
  if sandwiched then sandwichedD a A B else petzD a A B

/-- PDF p.17, Definition 12: Renyi cq information, before using the block formula.
Dependency50.P07.ensembleInformation instead denotes ordinary Holevo information. -/
def renyiEnsembleInformation {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (s : Bool) (a : ℝ) (p : Fin m → ℝ) (rho : Fin m → Matrix I I ℂ) : EReal :=
  ⨅ sigma : {X : Matrix I I ℂ // IsDensityMatrix X}, renyiD s a (cq p rho) (cq p (fun _ => sigma.1))

/-- PDF p.17, Definition 12: supremum over all finite mixed-state input ensembles. -/
def channelInformation {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (s : Bool) (a : ℝ) (N : Superop I J) : EReal :=
  ⨆ e : Ensemble I, renyiEnsembleInformation s a e.prob (fun x => N (e.state x))

/-- PDF p.24, Definition 21: fixed-center radius, permitting infinite radius. -/
def fixedRadius {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (s : Bool) (a : ℝ) (N : Superop I J) (sigma : Matrix J J ℂ) : EReal :=
  ⨆ rho : {X : Matrix I I ℂ // IsDensityMatrix X}, renyiD s a (N rho.1) sigma

/-- PDF p.17, Definition 13: minimize over output states AFTER maximizing over inputs. -/
def informationRadius {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (s : Bool) (a : ℝ) (N : Superop I J) : EReal :=
  ⨅ sigma : {X : Matrix J J ℂ // IsDensityMatrix X}, fixedRadius s a N sigma.1

/-- PDF p.17, (14): zero-weight unsupported blocks contribute zero in ENNReal. -/
def blockInformation {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (a : ℝ) (p : Fin m → ℝ) (rho : Fin m → Matrix I I ℂ) : EReal :=
  ⨅ sigma : {X : Matrix I I ℂ // IsDensityMatrix X}, ((1 / (a - 1) : ℝ) : EReal) *
    elogNN (∑ x, ENNReal.ofReal (p x) * sandwichedTrace a (rho x) sigma.1)

/-- PDF pp.17–19: witnesses for the maxima and minima in Definitions 12 and 13.
The semantic extrema are not replaced by unattained suprema or infima. -/
def InformationExtrema {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (s : Bool) (a : ℝ) (N : Superop I J) : Prop :=
  (∃ e : Ensemble I, channelInformation s a N =
    renyiEnsembleInformation s a e.prob (fun x => N (e.state x))) ∧
  (∃ sigma : {X : Matrix J J ℂ // IsDensityMatrix X}, informationRadius s a N = fixedRadius s a N sigma.1) ∧
  (∀ sigma : {X : Matrix J J ℂ // IsDensityMatrix X}, ∃ rho : {X : Matrix I I ℂ // IsDensityMatrix X},
    fixedRadius s a N sigma.1 = renyiD s a (N rho.1) sigma.1)

/-- PDF p.19: alpha-norm of a positive output with weight sigma^((1-alpha)/alpha).
On the compatible support domain this is the weighted Schatten norm in the source. -/
def outputWeightedNorm {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (A sigma : Matrix I I ℂ) : ℝ :=
  (rawTrace a A sigma) ^ (1 / a)

/-- PDF pp.19,25: admissible centers for the FINITE weighted-norm expression.
Singular centers containing every output support are included. -/
def CompatibleCenter {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (N : Superop I J) (sigma : Matrix J J ℂ) : Prop :=
  IsDensityMatrix sigma ∧ ∀ rho : {X : Matrix I I ℂ // IsDensityMatrix X}, Dominates sigma (N rho.1)

/-- PDF p.19, (16): min max log norm, with the inverse-support domain explicit. -/
def normRadiusBefore {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (a : ℝ) (N : Superop I J) : EReal :=
  ⨅ sigma : {S : Matrix J J ℂ // CompatibleCenter N S},
    ⨆ rho : {X : Matrix I I ℂ // IsDensityMatrix X}, ((a / (a - 1) : ℝ) : EReal) *
      elog (outputWeightedNorm a (N rho.1) sigma.1)

/-- PDF p.19, (16): min log max norm; finite-dimensional compatible centers give
nonempty bounded norm sets, with positive supremum on channels. -/
def normRadiusAfter {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (a : ℝ) (N : Superop I J) : EReal :=
  ⨅ sigma : {S : Matrix J J ℂ // CompatibleCenter N S},
    ((a / (a - 1) : ℝ) : EReal) *
      elog (sSup (Set.range (fun rho : {X : Matrix I I ℂ // IsDensityMatrix X} => outputWeightedNorm a (N rho.1) sigma.1)))

/-- PDF p.19: attainment of the finite-domain norm minima and maxima in (16). -/
def NormExtrema {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (a : ℝ) (N : Superop I J) : Prop :=
  (∃ sigma : {S : Matrix J J ℂ // CompatibleCenter N S},
    normRadiusAfter a N = ((a / (a - 1) : ℝ) : EReal) *
      elog (sSup (Set.range (fun rho : {X : Matrix I I ℂ // IsDensityMatrix X} => outputWeightedNorm a (N rho.1) sigma.1)))) ∧
  (∀ sigma : {S : Matrix J J ℂ // CompatibleCenter N S}, ∃ rho : {X : Matrix I I ℂ // IsDensityMatrix X},
    sSup (Set.range (fun r : {X : Matrix I I ℂ // IsDensityMatrix X} => outputWeightedNorm a (N r.1) sigma.1)) =
      outputWeightedNorm a (N rho.1) sigma.1)

/-- PDF pp.20,25: base-two exponential on extended reals, retaining BOTH endpoints. -/
def expTwo (x : EReal) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else if x = ⊥ then 0 else ENNReal.ofReal ((2 : ℝ) ^ x.toReal)

/-- PDF p.20, (17): success upper bound at one specified normalized radius. -/
def codingBound (n : ℕ) (a R : ℝ) (v : EReal) : ℝ≥0∞ :=
  expTwo (-(((n : ℝ) * (a - 1) / a : ℝ) : EReal) * ((R : EReal) - v))

/-- PDF p.22: the Renyi comparison constant nu in (20), expressed without
converting possibly infinite divergences. Claimed50.P48.nu is an output norm,
not this two-state constant.
On supported states, these traces are 2^(D_3/2 / 2) and 2^(-D_1/2 / 2). -/
def renyiNu {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) : ℝ :=
  tr (spectralPower rho (3 / 2 : ℝ) * spectralPower sigma (-1 / 2 : ℝ)) +
    tr (spectralPower rho (1 / 2 : ℝ) * spectralPower sigma (1 / 2 : ℝ)) + 1

/-- PDF p.22: an attained ordinary information-radius center and a uniform finite renyiNu bound.
These are witnesses in the conclusions below, never assumed approximation theorems. -/
def CenterControl {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (N : Superop I J) (sigma : Matrix J J ℂ) (c : ℝ) : Prop :=
  CompatibleCenter N sigma ∧ 1 < c ∧
  (⨆ rho : {X : Matrix I I ℂ // IsDensityMatrix X}, relativeD (N rho.1) sigma) = ((QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N) : EReal) ∧
  ∀ rho : {X : Matrix I I ℂ // IsDensityMatrix X}, renyiNu (N rho.1) sigma ≤ c

/-- PDF p.24: exponential strong-converse THRESHOLD, without identifying it with capacity. -/
def ExponentialAt {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) (threshold : ℝ) : Prop :=
  ∀ R : ℝ, threshold < R → ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∀ M : ℕ, 0 < M → R ≤ (Real.logb 2 (M : ℝ) / (n : ℝ)) →
      ∀ K : UACode (Fin n → I) (Fin n → J) M,
        uaCodeSuccess (channelPower N n) K ≤ (2 : ℝ) ^ (-(c * (n : ℝ)))

/-- PDF p.25: interior relative to the finite-dimensional affine TP/HP map space.
Entrywise coefficient balls give its usual topology; no CP constraint is placed on
candidate perturbations before testing membership in the EB-channel set. -/
def InteriorEB {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) : Prop :=
  IsChannel N ∧ IsEB N ∧
  ∃ e : ℝ, 0 < e ∧ ∀ L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ,
    (∀ X, (L X).trace = X.trace) →
    (∀ X, X.IsHermitian → (L X).IsHermitian) →
    (∀ i j k l, ‖L (Matrix.single i j 1) k l - N (Matrix.single i j 1) k l‖ < e) →
    Entanglement.IsCompletelyPositive L ∧ IsEB L

/-- PDF p.25: the EB interior condition is on a complement of this SAME channel. -/
def InteriorHadamard {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ V : Matrix (J × Fin k) I ℂ,
    IsIsometry V ∧ receiverChannel V = N ∧ InteriorEB (complementaryChannel V)

-- Small sanity checks pin support failure, zero operators, zero weights and the code boundary.
example {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (A B : Matrix I I ℂ)
    (h : ¬ Dominates B A) : sandwichedTrace a A B = ⊤ := by
  exact if_neg h

example {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    FiniteKrausCP (fun _ : Matrix I I ℂ => (0 : Matrix J J ℂ)) := by
  refine ⟨0, Fin.elim0, ?_⟩
  funext X
  simp [krausApply]

example {I J : Type} [Fintype J] (N : Superop I J) (X : Matrix I I ℂ) :
    filtered 0 N X = 0 := by simp [filtered]

example : classicalRenyiBits 2 (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) = ⊤ := by
  simp [classicalRenyiBits]

example : Real.logb 2 (1 : ℝ) / (1 : ℝ) = 0 := by simp [Real.logb]

example : binEntropy2 0 = 0 := by simp [binEntropy2]

example (x : ℝ≥0∞) : ENNReal.ofReal 0 * x = 0 := by simp

example : expTwo ⊤ = ⊤ ∧ expTwo ⊥ = 0 := by simp [expTwo]

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

end QAlgorithms.Papers.Independent.Support50.P19


