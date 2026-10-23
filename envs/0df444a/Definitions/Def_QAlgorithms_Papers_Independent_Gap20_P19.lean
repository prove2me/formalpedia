-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19
-- name    : QAlgorithms_Papers_Independent_Gap20_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T07:26:13.683+00:00
-- url     : https://prove2.me/theorems/6826bab7-dcd9-4be1-bd63-39e4b14b8152
-- title:
--   Definitions for The structure of degradable quantum channels
-- statement:
--   The objects the formalized statements of *The structure of degradable quantum channels* (arXiv:0802.1360) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PseudoDiagonal`: PDF p.19, (51): arbitrary PSD Gram matrix and frame vectors. Trace preservation is imposed separately, not on each frame vector. The output unitary permits the arbitrary orthonormal basis in (51).
--   - `TwistedDiagonal`: PDF pp.18–20: simultaneous diagonalization by invertible left/right factors.
--   - `RectangularUnitaryConjugate`: PDF pp.12–15: independent input/output conjugations for rectangular maps. The accepted P60.UnitaryEquivalent covers only square Fin d channels.
--   - `canonicalKraus`: PDF pp.14,28–29: corrected normalized pair for (85). Printed (39) interchanges the off-diagonal entries of A_minus.
--   - `rankTwoQubitMap`: PDF p.28, (85), on every operator. This is a qubit channel, distinct from the accepted P69.canonical, which constructs a purification vector.
--   - `qutritToQubitKraus`: PDF p.12, (27): the specific qutrit-to-qubit Kraus pair. The accepted Dependency50.P23.qutritKraus instead has qutrit output.
--   - `qutritCanonical`: PDF p.12, (26).
--   - `paulis`: PDF pp.15,28: sigma_0=I and ordered X,Y,Z.
--   - `pauliKraus`: PDF pp.15,28: a_k are Kraus amplitudes.
--   - `qubitPauliMap`: PDF p.28: qubit Kraus amplitudes in I,X,Y,Z order. The accepted Frontier18.P17.pauliChannel uses probability weights and Fin d Weyl labels.
--   - `pauliMultipliers`: PDF p.28, (87): multipliers in X,Y,Z order.
--   - `multiplierChannel`: PDF p.15, (41): linear extension of the unital diagonal Bloch map.
--   - `CPBounds`: PDF pp.15,28,38: both CP inequalities and physical multiplier bounds.
--   - `antiExpression`: PDF p.15, (42): cyclic indices enumerate the other two multipliers.
--   - `WeylProbabilities`: PDF pp.20–22, (55): probabilities, not Kraus amplitudes.
--   - `weylChannel`: PDF pp.20–22: positive-clock, forward-shift X^j Z^k mixture.
--   - `weylMultiplier`: PDF p.21: coefficient computed from Phi with the omitted 1/d restored.
--   - `threeWeyl`: PDF pp.22–23: three-term qutrit family.
--   - `flaggedIdentity`: PDF pp.10–11, (19): identity/noise with orthogonal flags.
--   - `flaggedDilation`: PDF p.10: normalized dilation of (19), none denotes the identity branch.
--   - `flaggedComplement`: PDF p.10, (20): complement order scalar first, noise environment second.
--   - `flaggedDegrader`: PDF p.11, (22): TP extension to every operator, discarding flag coherences. The scalar-first order agrees with flaggedComplement.
--   - `symmetricIsometry`: PDF p.11, (23): an explicit orthonormal symmetric-subspace basis.
--   - `symmetricSubspaceMap`: PDF p.11: the symmetric-subspace quantum channel from six to three dimensions; accepted P06.symmetricChannel is a classical transition matrix.
--   - `coFlags`: PDF p.11, (25): weighted flags on a common input.
--   - `coFlagDilation`: PDF p.11: normalized direct-sum dilation, with distinct environments.
--   - `coherentAt`: PDF p.26, (4): coherent information at an input state.
--   - `feasibilityMatrix`: PDF pp.32–33, (97): direct PSD matrix without a singular Schur inverse.
--   - `pauliAntidegrader`: PDF p.31, (94): the factor 1/2 converts Pauli traces to actual output.
--   - `faceAmplitudes`: PDF pp.34–35: face probability coordinates, a_0=0.
--   - `twoPauliAmplitudes`: PDF p.35: parameter s=t^2, with its boundary s=1/2 retained.
--   - `depolarizingAmplitudes`: PDF pp.35–36: fixed Pauli dilation for a depolarizing multiplier.
--   - `ExtremeIn`: PDF pp.10,35: extremality inside a named convex class of channels.
--   - `twoPauliOrbit`: PDF p.35: orbit of (2/3,2/3,1/3) under permutations and even sign changes.
--   - `wernerIsometry`: PDF p.10: the normalized antisymmetric qutrit dilation of W_3. Its columns are the Levi-Civita tensor divided by sqrt2.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, https://arxiv.org/abs/0802.1360v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

/-! Cubitt–Ruskai–Smith, arXiv:0802.1360v2. PDF pages throughout.
Source corrections: Theorem 3 uses rank rho; (39) has A_minus transposed to
recover (85); Theorem 12 uses output rank d_E, as computed in (54).
Compilation and independent moderation are pending the batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker
open Filter Topology
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)
open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)
open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)
open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)
open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P69 (choi)
open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype E] [DecidableEq E] [Nonempty E]
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype K] [DecidableEq K]
variable [Fintype A2] [DecidableEq A2] [Nonempty A2]
variable [Fintype B2] [DecidableEq B2] [Nonempty B2]
variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

/-- PDF p.19, (51): arbitrary PSD Gram matrix and frame vectors.
Trace preservation is imposed separately, not on each frame vector.
The output unitary permits the arbitrary orthonormal basis in (51). -/
def PseudoDiagonal (Phi : Superop A B) : Prop :=
  ∃ c : Matrix B B ℂ, c.PosSemidef ∧ ∃ w : B → EuclideanSpace ℂ A,
    ∃ V : Matrix.unitaryGroup B ℂ, ∀ rho,
      Phi rho = conjSuperop (V : Matrix B B ℂ) (arbitraryVectorComplement c w rho)

/-- PDF pp.18–20: simultaneous diagonalization by invertible left/right factors. -/
def TwistedDiagonal (Phi : Superop A A) : Prop :=
  ∃ m : ℕ, ∃ H : Fin m → Matrix A A ℂ, IsKrausFamily H ∧ Phi = krausApply H ∧
    ∃ X Y : Matrix A A ℂ, IsUnit X ∧ IsUnit Y ∧
      ∀ k, ∃ v : A → ℂ, Y * H k * X = Matrix.diagonal v

/-- PDF pp.12–15: independent input/output conjugations for rectangular maps.
The accepted P60.UnitaryEquivalent covers only square Fin d channels. -/
def RectangularUnitaryConjugate (Phi Psi : Superop A B) : Prop :=
  ∃ U : Matrix.unitaryGroup A ℂ, ∃ V : Matrix.unitaryGroup B ℂ,
    ∀ rho, Phi rho = conjSuperop (V : Matrix B B ℂ)
      (Psi (conjSuperop (U : Matrix A A ℂ) rho))

/-- PDF pp.14,28–29: corrected normalized pair for (85).
Printed (39) interchanges the off-diagonal entries of A_minus. -/
def canonicalKraus (u v : ℝ) : Bool → Matrix Bool Bool ℂ :=
  fun k b a => if k then
    if b = a then 0 else if b then (Real.sin ((v-u)/2) : ℂ)
      else (Real.sin ((u+v)/2) : ℂ)
  else if b = a then
    if b then (Real.cos ((u+v)/2) : ℂ) else (Real.cos ((v-u)/2) : ℂ)
  else 0

/-- PDF p.28, (85), on every operator. This is a qubit channel, distinct
from the accepted P69.canonical, which constructs a purification vector. -/
def rankTwoQubitMap (u v : ℝ) : Superop Bool Bool := krausApply (canonicalKraus u v)

/-- PDF p.12, (27): the specific qutrit-to-qubit Kraus pair.
The accepted Dependency50.P23.qutritKraus instead has qutrit output. -/
def qutritToQubitKraus : Bool → Matrix Bool (Fin 3) ℂ :=
  fun k b a => if k then
    if b then ![0, 0, 1] a else ![0, ((Real.sqrt 2)⁻¹ : ℂ), 0] a
  else if b then ![0, ((Real.sqrt 2)⁻¹ : ℂ), 0] a else ![1, 0, 0] a

/-- PDF p.12, (26). -/
def qutritCanonical : Superop (Fin 3) Bool := krausApply qutritToQubitKraus

/-- PDF pp.15,28: sigma_0=I and ordered X,Y,Z. -/
def paulis : Fin 4 → Matrix Bool Bool ℂ := ![1, pauliX, pauliY, pauliZ]

/-- PDF pp.15,28: a_k are Kraus amplitudes. -/
def pauliKraus (a : Fin 4 → ℝ) : Fin 4 → Matrix Bool Bool ℂ :=
  fun k => (a k : ℂ) • paulis k

/-- PDF p.28: qubit Kraus amplitudes in I,X,Y,Z order. The accepted
Frontier18.P17.pauliChannel uses probability weights and Fin d Weyl labels. -/
def qubitPauliMap (a : Fin 4 → ℝ) : Superop Bool Bool := krausApply (pauliKraus a)

/-- PDF p.28, (87): multipliers in X,Y,Z order. -/
def pauliMultipliers (a : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![a 0^2+a 1^2-a 2^2-a 3^2, a 0^2-a 1^2+a 2^2-a 3^2,
    a 0^2-a 1^2-a 2^2+a 3^2]

/-- PDF p.15, (41): linear extension of the unital diagonal Bloch map. -/
def multiplierChannel (lam : Fin 3 → ℝ) : Superop Bool Bool :=
  QubitChannels.blochAffineMap 0 (Matrix.diagonal lam)

/-- PDF pp.15,28,38: both CP inequalities and physical multiplier bounds. -/
def CPBounds (lam : Fin 3 → ℝ) : Prop :=
  (∀ k, |lam k| ≤ 1) ∧ ∀ i j k : Fin 3,
    i ≠ j → i ≠ k → j ≠ k →
    (lam i+lam j)^2 ≤ (1+lam k)^2 ∧ (lam i-lam j)^2 ≤ (1-lam k)^2

/-- PDF p.15, (42): cyclic indices enumerate the other two multipliers. -/
def antiExpression (lam : Fin 3 → ℝ) : ℝ :=
  ∑ k : Fin 3, (1-|lam k| + Real.sqrt
    ((1-|lam k|)^2-(|lam (k+1)|-|lam (k+2)|)^2))

/-- PDF pp.20–22, (55): probabilities, not Kraus amplitudes. -/
def WeylProbabilities {d : ℕ} [NeZero d] (a : WeylLabel d → ℝ) : Prop :=
  (∀ j, 0 ≤ a j) ∧ ∑ j, a j = 1

/-- PDF pp.20–22: positive-clock, forward-shift X^j Z^k mixture. -/
def weylChannel (d : ℕ) [NeZero d] (a : WeylLabel d → ℝ) : Superop (Fin d) (Fin d) :=
  fun rho => ∑ k, (a k : ℂ) • conjSuperop (finWeyl d k) rho

/-- PDF p.21: coefficient computed from Phi with the omitted 1/d restored. -/
def weylMultiplier (d : ℕ) [NeZero d] (a : WeylLabel d → ℝ) (m : WeylLabel d) : ℂ :=
  (d : ℂ)⁻¹ * ((finWeyl d m)ᴴ * weylChannel d a (finWeyl d m)).trace

/-- PDF pp.22–23: three-term qutrit family. -/
def threeWeyl (a0 a1 a2 : ℝ) : Superop (Fin 3) (Fin 3) :=
  fun rho => (a0 : ℂ) • rho + (a1 : ℂ) • conjSuperop (finWeyl 3 (1,0)) rho +
    (a2 : ℂ) • conjSuperop (finWeyl 3 (0,1)) rho

/-- PDF pp.10–11, (19): identity/noise with orthogonal flags. -/
def flaggedIdentity (x : ℝ) (N : Superop A A) : Superop A (Bool × A) :=
  fun rho p q => if p.1 = q.1 then
    if p.1 then ((1-x : ℝ) : ℂ)*N rho p.2 q.2 else (x : ℂ)*rho p.2 q.2
  else 0

/-- PDF p.10: normalized dilation of (19), none denotes the identity branch. -/
def flaggedDilation (x : ℝ) (U : Matrix (A × E) A ℂ) :
    Matrix ((Bool × A) × Option E) A ℂ :=
  fun be a => match be.2 with
  | none => if be.1 = (false,a) then (Real.sqrt x : ℂ) else 0
  | some e => if be.1.1 then (Real.sqrt (1-x) : ℂ)*U (be.1.2,e) a else 0

/-- PDF p.10, (20): complement order scalar first, noise environment second. -/
def flaggedComplement (x : ℝ) (U : Matrix (A × E) A ℂ) : Superop A (Option E) :=
  fun rho p q => match p,q with
  | none,none => (x : ℂ)*rho.trace
  | some e,some f => ((1-x : ℝ) : ℂ)*complementaryChannel U rho e f
  | _,_ => 0

/-- PDF p.11, (22): TP extension to every operator, discarding flag coherences.
The scalar-first order agrees with flaggedComplement. -/
def flaggedDegrader (x : ℝ) (U : Matrix (A × E) A ℂ) : Superop (Bool × A) (Option E) :=
  fun rho p q =>
    let r0 : Matrix A A ℂ := fun a b => rho (false,a) (false,b)
    let r1 : Matrix A A ℂ := fun a b => rho (true,a) (true,b)
    match p,q with
    | none,none => (((2*x-1)/x : ℝ) : ℂ)*r0.trace + r1.trace
    | some e,some f => (((1-x)/x : ℝ) : ℂ)*complementaryChannel U r0 e f
    | _,_ => 0

/-- PDF p.11, (23): an explicit orthonormal symmetric-subspace basis. -/
def symmetricIsometry : Matrix (Fin 3 × Fin 3) (Fin 6) ℂ :=
  fun p k => if h : k.val < 3 then
    if p.1.val = k.val ∧ p.2.val = k.val then 1 else 0
  else
    let ij : Fin 3 × Fin 3 := ![(0,1),(0,2),(1,2)] ⟨k.val-3, by omega⟩
    if p = ij ∨ p = (ij.2,ij.1) then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.11: the symmetric-subspace quantum channel from six to three
dimensions; accepted P06.symmetricChannel is a classical transition matrix. -/
def symmetricSubspaceMap : Superop (Fin 6) (Fin 3) := receiverChannel symmetricIsometry

/-- PDF p.11, (25): weighted flags on a common input. -/
def coFlags (M N : Superop A B) : Superop A (Bool × B) :=
  fun rho p q => if p.1 = q.1 then
    (1/2 : ℂ)*(if p.1 then N rho p.2 q.2 else M rho p.2 q.2) else 0

/-- PDF p.11: normalized direct-sum dilation, with distinct environments. -/
def coFlagDilation (U : Matrix (B × E) A ℂ) (V : Matrix (B × F) A ℂ) :
    Matrix ((Bool × B) × (E ⊕ F)) A ℂ :=
  fun be a => match be.2 with
  | .inl e => if be.1.1 then 0 else ((Real.sqrt 2)⁻¹ : ℂ)*U (be.1.2,e) a
  | .inr f => if be.1.1 then ((Real.sqrt 2)⁻¹ : ℂ)*V (be.1.2,f) a else 0

/-- PDF p.26, (4): coherent information at an input state. -/
def coherentAt (U : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) : ℝ :=
  vnEntropy (receiverChannel U rho) - vnEntropy (complementaryChannel U rho)

/-- PDF pp.32–33, (97): direct PSD matrix without a singular Schur inverse. -/
def feasibilityMatrix (x y : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, (x 2 : ℂ), (x 0 : ℂ), (x 1 : ℂ);
     (x 2 : ℂ), 1, (y 1 : ℂ), (y 0 : ℂ);
     (x 0 : ℂ), (y 1 : ℂ), 1, (y 2 : ℂ);
     (x 1 : ℂ), (y 0 : ℂ), (y 2 : ℂ), 1]

/-- PDF p.31, (94): the factor 1/2 converts Pauli traces to actual output. -/
def pauliAntidegrader (x y : Fin 3 → ℝ) : Superop (Fin 4) Bool :=
  fun r => (1/2 : ℂ) • (r.trace • 1 +
    ((x 0 : ℂ)*(r 0 1+r 1 0)+Complex.I*(y 0 : ℂ)*(r 2 3-r 3 2)) • pauliX +
    ((x 1 : ℂ)*(r 0 2+r 2 0)+Complex.I*(y 1 : ℂ)*(r 3 1-r 1 3)) • pauliY +
    ((x 2 : ℂ)*(r 0 3+r 3 0)+Complex.I*(y 2 : ℂ)*(r 1 2-r 2 1)) • pauliZ)

/-- PDF pp.34–35: face probability coordinates, a_0=0. -/
def faceAmplitudes (p : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![0, Real.sqrt (p 0), Real.sqrt (p 1), Real.sqrt (p 2)]

/-- PDF p.35: parameter s=t^2, with its boundary s=1/2 retained. -/
def twoPauliAmplitudes (s : ℝ) : Fin 4 → ℝ :=
  ![Real.sqrt (1-2*s), Real.sqrt s, Real.sqrt s, 0]

/-- PDF pp.35–36: fixed Pauli dilation for a depolarizing multiplier. -/
def depolarizingAmplitudes (lam : ℝ) : Fin 4 → ℝ :=
  ![Real.sqrt ((1+3*lam)/4), Real.sqrt ((1-lam)/4),
    Real.sqrt ((1-lam)/4), Real.sqrt ((1-lam)/4)]

/-- PDF pp.10,35: extremality inside a named convex class of channels. -/
def ExtremeIn (P : Superop A B → Prop) (Phi : Superop A B) : Prop :=
  P Phi ∧ ∀ (N M : Superop A B) (p : ℝ), P N → P M → 0 < p → p < 1 →
    Phi = (fun r => (p : ℂ) • N r + ((1-p : ℝ) : ℂ) • M r) → N = Phi ∧ M = Phi

/-- PDF p.35: orbit of (2/3,2/3,1/3) under permutations and even sign changes. -/
def twoPauliOrbit : Set (Fin 3 → ℝ) :=
  {lam | ∃ perm : Equiv.Perm (Fin 3), ∃ sign : Fin 3 → ℝ,
    (∀ k, sign k = 1 ∨ sign k = -1) ∧ (∏ k, sign k) = 1 ∧
    ∀ k, lam k = sign k * (![2/3,2/3,1/3] : Fin 3 → ℝ) (perm k)}

/-! Definition sanity examples; no source theorem is proved here. -/

example (u v : ℝ) : canonicalKraus u v false false false = Real.cos ((v-u)/2) := by
  simp [canonicalKraus]

example : canonicalKraus 0 0 true = 0 := by
  ext b a
  simp [canonicalKraus]

example : paulis 0 = 1 := rfl

example (x : ℝ) (N : Superop A A) (rho : Matrix A A ℂ) (a b : A) :
    flaggedIdentity x N rho (false,a) (false,b) = (x : ℂ)*rho a b := by
  simp [flaggedIdentity]

example (x : ℝ) (U : Matrix (A × E) A ℂ) (rho : Matrix A A ℂ) :
    flaggedComplement x U rho none none = (x : ℂ)*rho.trace := rfl

example (x y : Fin 3 → ℝ) : feasibilityMatrix x y 0 0 = 1 := rfl

example (p : Fin 3 → ℝ) : faceAmplitudes p 0 = 0 := rfl

example (Phi : Superop A B) (a c : A) (b d : B) :
    choi Phi (a,b) (c,d) = Phi (Matrix.single a c 1) b d := rfl

/-- PDF p.10: the normalized antisymmetric qutrit dilation of W_3.
Its columns are the Levi-Civita tensor divided by sqrt2. -/
def wernerIsometry : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  fun p k => if p.1=p.2 ∨ p.1=k ∨ p.2=k then 0
    else if (p.1.val+1)%3=p.2.val then ((Real.sqrt 2)⁻¹ : ℂ)
    else -((Real.sqrt 2)⁻¹ : ℂ)

example (p : Fin 3 × Fin 3) : wernerIsometry p p.1 = 0 := by
  simp [wernerIsometry]

end QAlgorithms.Papers.Independent.Gap20.P19


