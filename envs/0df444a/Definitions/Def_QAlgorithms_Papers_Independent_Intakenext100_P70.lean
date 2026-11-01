-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P70
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:39:07.732207+00:00
-- url     : https://prove2.me/theorems/3357f49d-d947-400a-91a2-1bc645ea9c6f
-- title:
--   Definitions for Unbounded number of channel uses are required to see quantum capacity
-- statement:
--   The objects the formalized statements of *Unbounded number of channel uses are required to see quantum capacity* (arXiv:1408.5115) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `cubittBlockInformation`: PDF p.1: Q^(n), with the factor 1/n and a tensor channel on arbitrary joint inputs. Only positive n are used in result statements. The accepted quantumCapacity is the supremum over precisely these normalized positive-block rates.
--   - `cubittWholeErasure`: PDF p.5: E_p on the WHOLE input, with a separate first output flag. The trace factor specifies the linear map on every operator, not only on states.
--   - `cubittSwitched`: PDF p.5: the measured and RETAINED switch, sum_i P_i tensor N_i. Only diagonal switch blocks survive; off-diagonal main-input entries within a block survive.
--   - `cubittSelectedInput`: PDF p.5, proof of Lemma 1: deterministic switch input with arbitrary main density.
--   - `cubittNormalizedChoi`: PDF pp.6--7: normalized Choi matrix, in input:output order.
--   - `cubittOutputTranspose`: PDF p.7: partial transpose on the output in the computational basis.
--   - `CubittPPTBinding`: PDF p.7: a channel is PPT-binding iff its Choi matrix is PPT. CPTP is part of the predicate; no assumption about its coherent information is inserted.
--   - `cubittNoisySwitch`: PDF p.6, S15--S16: switch 0 applies E_kappa after Gamma; switch 1 applies E_p. Both output flags, the switch, and the full main output are retained.
--   - `cubittErasureThreshold`: PDF pp.3,8,11: the lower erasure threshold, with a REAL exponent -1/n.
--   - `CubittParameters`: PDF p.6: paper-specific parameters; admissibility is stated separately.
--   - `CubittValid`: PDF pp.5--7: positive numbers of shares/copies, d>=2, and physical S18 weights. The results choose q=1/3; q<=1/2 is the positivity range of that construction.
--   - `CubittShare`: PDF p.6: A_i consists of r*m d-dimensional factors.
--   - `CubittShield`: PDF p.6: A consists of N shares; finite functions preserve all named factors.
--   - `CubittMain`: PDF p.6: main input aA and equal-dimensional output bB, key qubit first.
--   - `cubittSymmetricState`: PDF p.7: normalized projector onto the symmetric subspace, (I+swap)/(d(d+1)).
--   - `cubittAntisymmetricState`: PDF p.7: normalized antisymmetric projector, (I-swap)/(d(d-1)); used only at d>=2.
--   - `cubittHidingOmega`: PDF p.7: omega on C_k, tensoring the equal mixture over all N*r pairs.
--   - `cubittHidingSigma`: PDF p.7: sigma on C_k, tensoring the symmetric state over all N*r pairs.
--   - `cubittRawChoi`: PDF p.6, S18: the unnormalized three key blocks, reordered across aA:bB. Products over k retain q/2 in EACH copy, including the off-diagonal block's sign.
--   - `cubittZeta`: PDF pp.6--7, S18: COMPUTED normalized Choi state. For admissible parameters its trace normalizer is 2*(q^m+(1/2-q)^m)>0.
--   - `cubittGammaChannel`: PDF pp.6--7: inverse normalized Choi transform; Gamma is computed from S18. Its input-reference marginal is I/dim(CubittMain), so this is CPTP on admissible parameters.
--   - `cubittPaperChannel`: PDF p.6, S15: the fully specified paper channel, without any capacity assumption.
--   - `CubittPPTCondition`: PDF p.7, S19: sufficient PPT condition; the exponent is the product r*N.
--   - `cubittRepetitions`: PDF pp.7--8: integer ceiling retained from Lemma 2 (the p.10 shorthand omits it).
--   - `cubittApproximationParameters`: PDF p.7, Lemma 2: q=1/3 and the prescribed integer repetition count.
--   - `cubittInsertFirst`: PDF p.7, S20: reinsert the first shield share, indexed by 0 in Lean.
--   - `cubittFirstShareState`: PDF p.7, S20: actual partial trace over A_2 B_2 ... A_N B_N of the computed cubittZeta. The rho/cubittZeta change in Lemma 2 is resolved by this marginal, not by an arbitrary state.
--   - `cubittPrivateState`: PDF p.6, S12: twisted Bell pair with arbitrary density sigma and key-controlled unitaries. Coordinates are aA:bB; this is S10--S11 expanded in the fixed basis.
--   - `CubittPerfectPbit`: PDF p.6, S10--S12: normalized perfect private bit; shield dimension is unrestricted.
--   - `cubittApproximationBound`: PDF pp.7--8, Lemma 2: full trace-norm approximation, not half trace distance.
--   - `cubittContinuityLoss`: PDF p.10, S52: continuity loss; applied only with 0<=tau<1.
--   - `cubittExplicitShares`: PDF p.11: final concrete N, which grows with the requested undetectable block length.
--   - `cubittExplicitParameters`: PDF pp.10--11: d=2*N*r, a product (not a power).
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, https://arxiv.org/abs/1408.5115v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

/-!
Statements for arXiv:1408.5115v1. All page numbers are PDF pages.
All spaces are finite matrices in the fixed computational basis; entropy is in bits.
Only the seven result declarations have sorry. Paper-specific constructors have complete bodies.
The capacity definitions are reused from the pinned accepted Information100.P22 (lines 854--877),
under the independent-paper override permitting accepted library imports. Compilation and independent moderation are pending.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- PDF p.1: Q^(n), with the factor 1/n and a tensor channel on arbitrary joint inputs.
Only positive n are used in result statements. The accepted quantumCapacity is the
supremum over precisely these normalized positive-block rates. -/
def cubittBlockInformation {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Superop I J) (n : ℕ) : ℝ :=
  singleUseInformation (piSuperop (fun _ : Fin n => Phi)) / (n : ℝ)

/-- PDF p.5: E_p on the WHOLE input, with a separate first output flag.
The trace factor specifies the linear map on every operator, not only on states. -/
def cubittWholeErasure {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) :
    Superop I (Bool × I) :=
  fun X x y =>
    if x.1 = y.1 then
      if x.1 then (p : ℂ) * X.trace * mixed I x.2 y.2
      else (1 - (p : ℂ)) * X x.2 y.2
    else 0

/-- PDF p.5: the measured and RETAINED switch, sum_i P_i tensor N_i.
Only diagonal switch blocks survive; off-diagonal main-input entries within a block survive. -/
def cubittSwitched {S A B : Type*} (branches : S → Superop A B) :
    Superop (S × A) (S × B) :=
  fun X x y => if x.1 = y.1 then
    branches x.1 (fun a b => X (x.1, a) (x.1, b)) x.2 y.2 else 0

/-- PDF p.5, proof of Lemma 1: deterministic switch input with arbitrary main density. -/
def cubittSelectedInput {S A : Type*} (i : S) (rho : Op A) : Op (S × A) :=
  fun x y => if x.1 = i ∧ y.1 = i then rho x.2 y.2 else 0

/-- PDF pp.6--7: normalized Choi matrix, in input:output order. -/
def cubittNormalizedChoi {I J : Type*} [Fintype I] [DecidableEq I]
    (Phi : Superop I J) : Op (I × J) :=
  fun x y => Phi (Matrix.single x.1 y.1 1) x.2 y.2 / (Fintype.card I : ℂ)

/-- PDF p.7: partial transpose on the output in the computational basis. -/
def cubittOutputTranspose {I J : Type*} (X : Op (I × J)) : Op (I × J) :=
  fun x y => X (x.1, y.2) (y.1, x.2)

/-- PDF p.7: a channel is PPT-binding iff its Choi matrix is PPT.
CPTP is part of the predicate; no assumption about its coherent information is inserted. -/
def CubittPPTBinding {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (Phi : Superop I J) : Prop :=
  IsChannel Phi ∧ (cubittOutputTranspose (cubittNormalizedChoi Phi)).PosSemidef

/-- PDF p.6, S15--S16: switch 0 applies E_kappa after Gamma; switch 1 applies E_p.
Both output flags, the switch, and the full main output are retained. -/
def cubittNoisySwitch {I : Type*} [Fintype I] [DecidableEq I]
    (Gamma : Superop I I) (kappa p : ℝ) : Superop (Bool × I) (Bool × (Bool × I)) :=
  cubittSwitched fun s => if s then cubittWholeErasure p else cubittWholeErasure kappa ∘ Gamma

/-- PDF pp.3,8,11: the lower erasure threshold, with a REAL exponent -1/n. -/
def cubittErasureThreshold (n : ℕ) (kappa : ℝ) : ℝ :=
  (1 + kappa ^ n) ^ (-(1 : ℝ) / (n : ℝ))

/-- PDF p.6: paper-specific parameters; admissibility is stated separately. -/
structure CubittParameters where
  N : ℕ
  r : ℕ
  m : ℕ
  d : ℕ
  q : ℝ

/-- PDF pp.5--7: positive numbers of shares/copies, d>=2, and physical S18 weights.
The results choose q=1/3; q<=1/2 is the positivity range of that construction. -/
def CubittValid (P : CubittParameters) : Prop :=
  0 < P.N ∧ 0 < P.r ∧ 0 < P.m ∧ 2 ≤ P.d ∧ 0 < P.q ∧ P.q ≤ 1 / 2

/-- PDF p.6: A_i consists of r*m d-dimensional factors. -/
abbrev CubittShare (r m d : ℕ) := Fin r → Fin m → Fin d

/-- PDF p.6: A consists of N shares; finite functions preserve all named factors. -/
abbrev CubittShield (P : CubittParameters) := Fin P.N → CubittShare P.r P.m P.d

/-- PDF p.6: main input aA and equal-dimensional output bB, key qubit first. -/
abbrev CubittMain (P : CubittParameters) := Bool × CubittShield P

/-- PDF p.7: normalized projector onto the symmetric subspace, (I+swap)/(d(d+1)). -/
def cubittSymmetricState (d : ℕ) : Op (Fin d × Fin d) :=
  fun x y => ((if x = y then 1 else 0) +
    (if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0)) / ((d : ℂ) * ((d : ℂ) + 1))

/-- PDF p.7: normalized antisymmetric projector, (I-swap)/(d(d-1)); used only at d>=2. -/
def cubittAntisymmetricState (d : ℕ) : Op (Fin d × Fin d) :=
  fun x y => ((if x = y then 1 else 0) -
    (if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0)) / ((d : ℂ) * ((d : ℂ) - 1))

/-- PDF p.7: omega on C_k, tensoring the equal mixture over all N*r pairs. -/
def cubittHidingOmega (P : CubittParameters) (k : Fin P.m)
    (x y : CubittShield P × CubittShield P) : ℂ :=
  ∏ i, ∏ j, (cubittSymmetricState P.d (x.1 i j k, x.2 i j k) (y.1 i j k, y.2 i j k) +
    cubittAntisymmetricState P.d (x.1 i j k, x.2 i j k) (y.1 i j k, y.2 i j k)) / 2

/-- PDF p.7: sigma on C_k, tensoring the symmetric state over all N*r pairs. -/
def cubittHidingSigma (P : CubittParameters) (k : Fin P.m)
    (x y : CubittShield P × CubittShield P) : ℂ :=
  ∏ i, ∏ j, cubittSymmetricState P.d (x.1 i j k, x.2 i j k) (y.1 i j k, y.2 i j k)

/-- PDF p.6, S18: the unnormalized three key blocks, reordered across aA:bB.
Products over k retain q/2 in EACH copy, including the off-diagonal block's sign. -/
def cubittRawChoi (P : CubittParameters) : Op (CubittMain P × CubittMain P) :=
  fun x y =>
    let u := (x.1.2, x.2.2)
    let v := (y.1.2, y.2.2)
    if x.1.1 = x.2.1 ∧ y.1.1 = y.2.1 then
      if x.1.1 = y.1.1 then
        ∏ k, (P.q : ℂ) / 2 * (cubittHidingOmega P k u v + cubittHidingSigma P k u v)
      else
        ∏ k, (P.q : ℂ) / 2 * (cubittHidingOmega P k u v - cubittHidingSigma P k u v)
    else if x.1.1 ≠ x.2.1 ∧ x.1.1 = y.1.1 ∧ x.2.1 = y.2.1 then
      ∏ k, ((1 / 2 : ℂ) - (P.q : ℂ)) * cubittHidingSigma P k u v
    else 0

/-- PDF pp.6--7, S18: COMPUTED normalized Choi state.
For admissible parameters its trace normalizer is 2*(q^m+(1/2-q)^m)>0. -/
def cubittZeta (P : CubittParameters) : Op (CubittMain P × CubittMain P) :=
  (2 * ((P.q : ℂ) ^ P.m + ((1 / 2 : ℂ) - (P.q : ℂ)) ^ P.m))⁻¹ • cubittRawChoi P

/-- PDF pp.6--7: inverse normalized Choi transform; Gamma is computed from S18.
Its input-reference marginal is I/dim(CubittMain), so this is CPTP on admissible parameters. -/
def cubittGammaChannel (P : CubittParameters) : Superop (CubittMain P) (CubittMain P) :=
  fun X b c => (Fintype.card (CubittMain P) : ℂ) *
    ∑ a, ∑ a2, X a a2 * cubittZeta P (a, b) (a2, c)

/-- PDF p.6, S15: the fully specified paper channel, without any capacity assumption. -/
def cubittPaperChannel (P : CubittParameters) (kappa p : ℝ) := cubittNoisySwitch (cubittGammaChannel P) kappa p

/-- PDF p.7, S19: sufficient PPT condition; the exponent is the product r*N. -/
def CubittPPTCondition (P : CubittParameters) : Prop :=
  0 < P.q ∧ P.q ≤ 1 / 3 ∧
    ((P.d : ℝ) / ((P.d : ℝ) - 1)) ^ (P.r * P.N) ≤ (1 - P.q) / P.q

/-- PDF pp.7--8: integer ceiling retained from Lemma 2 (the p.10 shorthand omits it). -/
def cubittRepetitions (m : ℕ) : ℕ := 2 * m + Nat.ceil (Real.logb 2 (m : ℝ))

/-- PDF p.7, Lemma 2: q=1/3 and the prescribed integer repetition count. -/
def cubittApproximationParameters (N m d : ℕ) : CubittParameters :=
  ⟨N, cubittRepetitions m, m, d, 1 / 3⟩

/-- PDF p.7, S20: reinsert the first shield share, indexed by 0 in Lean. -/
def cubittInsertFirst (P : CubittParameters) (hN : 0 < P.N) (x : CubittShare P.r P.m P.d)
    (rest : {i : Fin P.N // i ≠ ⟨0, hN⟩} → CubittShare P.r P.m P.d) : CubittShield P :=
  fun i => if h : i = ⟨0, hN⟩ then x else rest ⟨i, h⟩

/-- PDF p.7, S20: actual partial trace over A_2 B_2 ... A_N B_N of the computed cubittZeta.
The rho/cubittZeta change in Lemma 2 is resolved by this marginal, not by an arbitrary state. -/
def cubittFirstShareState (P : CubittParameters) (hN : 0 < P.N) :
    Op ((Bool × CubittShare P.r P.m P.d) × (Bool × CubittShare P.r P.m P.d)) :=
  fun x y => ∑ aRest, ∑ bRest,
    cubittZeta P ((x.1.1, cubittInsertFirst P hN x.1.2 aRest),
      (x.2.1, cubittInsertFirst P hN x.2.2 bRest))
      ((y.1.1, cubittInsertFirst P hN y.1.2 aRest),
      (y.2.1, cubittInsertFirst P hN y.2.2 bRest))

/-- PDF p.6, S12: twisted Bell pair with arbitrary density sigma and key-controlled unitaries.
Coordinates are aA:bB; this is S10--S11 expanded in the fixed basis. -/
def cubittPrivateState {I : Type*} [Fintype I] [DecidableEq I] (sigma : Op (I × I))
    (U : Bool → Bool → Matrix.unitaryGroup (I × I) ℂ) :
    Op ((Bool × I) × (Bool × I)) :=
  fun x y => if x.1.1 = x.2.1 ∧ y.1.1 = y.2.1 then
    (1 / 2 : ℂ) * (((U x.1.1 x.1.1 : Op (I × I)) * sigma *
      (U y.1.1 y.1.1 : Op (I × I))ᴴ) (x.1.2, x.2.2) (y.1.2, y.2.2))
    else 0

/-- PDF p.6, S10--S12: normalized perfect private bit; shield dimension is unrestricted. -/
def CubittPerfectPbit {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Op ((Bool × I) × (Bool × I))) : Prop :=
  IsDensityMatrix rho ∧ ∃ sigma : Op (I × I), IsDensityMatrix sigma ∧
    ∃ U : Bool → Bool → Matrix.unitaryGroup (I × I) ℂ, rho = cubittPrivateState sigma U

/-- PDF pp.7--8, Lemma 2: full trace-norm approximation, not half trace distance. -/
def cubittApproximationBound (m : ℕ) : ℝ :=
  16 * Real.sqrt (m : ℝ) * (2 : ℝ) ^ (-(m : ℝ) / 4)

/-- PDF p.10, S52: continuity loss; applied only with 0<=tau<1. -/
def cubittContinuityLoss (tau : ℝ) : ℝ := 4 * tau + 2 * binEntropy2 tau

/-- PDF p.11: final concrete N, which grows with the requested undetectable block length. -/
def cubittExplicitShares (n : ℕ) : ℕ := 2 * n * 4 ^ n

/-- PDF pp.10--11: d=2*N*r, a product (not a power). -/
def cubittExplicitParameters (n m : ℕ) : CubittParameters :=
  cubittApproximationParameters (cubittExplicitShares n) m (2 * cubittExplicitShares n * cubittRepetitions m)

/-! Small constructor sanity examples. No result theorem is proved in this stage. -/

example {I : Type*} [Fintype I] [DecidableEq I] (X : Op I) (a b : I) :
    cubittWholeErasure 0 X (false, a) (false, b) = X a b := by
  simp [cubittWholeErasure]

example {I : Type*} [Fintype I] [DecidableEq I] (X : Op I) (a b : I) :
    cubittWholeErasure 1 X (true, a) (true, b) = X.trace * mixed I a b := by
  simp [cubittWholeErasure]

example {A B : Type*} (branches : Bool → Superop A B) (X : Op (Bool × A)) (a b : B) :
    cubittSwitched branches X (false, a) (true, b) = 0 := by
  simp [cubittSwitched]

example {I J : Type*} (X : Op (I × J)) : cubittOutputTranspose (cubittOutputTranspose X) = X := rfl

example : cubittSymmetricState 2 (0, 0) (0, 0) = 1 / 3 := by
  norm_num [cubittSymmetricState]

example : cubittAntisymmetricState 2 (0, 1) (1, 0) = -(1 / 2) := by
  norm_num [cubittAntisymmetricState]

example (P : CubittParameters) (hN : 0 < P.N) (x : CubittShare P.r P.m P.d)
    (rest : {i : Fin P.N // i ≠ ⟨0, hN⟩} → CubittShare P.r P.m P.d) :
    cubittInsertFirst P hN x rest ⟨0, hN⟩ = x := by
  simp [cubittInsertFirst]

example : cubittExplicitShares 1 = 8 := rfl

example (m : ℕ) : (cubittExplicitParameters 1 m).q = 1 / 3 := rfl

end

end QAlgorithms.Papers.Independent.Intakenext100.P70


