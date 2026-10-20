-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23
-- name    : QAlgorithms_Papers_Independent_Dependency50_P23
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T16:30:12.238376+00:00
-- url     : https://prove2.me/theorems/dbac5e41-7755-4597-bf51-4cc76cb3e242
-- title:
--   Definitions for Semidefinite programming strong converse bounds for classical capacity
-- statement:
--   The objects the formalized statements of *Semidefinite programming strong converse bounds for classical capacity* (arXiv:1610.06381) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PT`: PDF p.4: reuse of the accepted partial transpose on the second register.
--   - `AD`: PDF p.17: reuse of the exact accepted Kraus-form amplitude damping primitive.
--   - `LEop`: PDF p.4: Loewner order, never the pointwise order on matrix entries.
--   - `CodeMatrix`: PDF p.4, Eq.(2): input order (message,B), output order (A,estimate).
--   - `NSCode`: PDF pp.4–6: CP, TP, classical message registers, both NS conditions, and, when requested, PPT on BOTH Bob's input B and output estimate. The normalized marginals below are Eq.(2) in entries. No division by m-1 is used.
--   - `codeSuccess`: PDF p.5, Eqs.(3),(7): link product of the channel and a bipartite code, followed by a uniform average of the diagonal correct-message probabilities.
--   - `nsSuccess`: PDF p.5, Eq.(4): optimization over a code chosen before the uniform message.
--   - `UACode`: PDF pp.4–5: ordinary local mixed-state encoder and a decoding POVM.
--   - `uaCodeSuccess`: PDF p.5, Eq.(3): unassisted average decoding success.
--   - `uaSuccess`: PDF p.5: unassisted codes optimize over arbitrary mixed input states.
--   - `EACode`: PDF p.5: arbitrary finite entangled ancillas, message-dependent local CPTP encoding, and a joint receiver POVM. No extra communication is supplied.
--   - `eaInput`: PDF p.5: the message is encoded locally; Bob's shared subsystem is untouched.
--   - `eaCodeSuccess`: PDF p.5: N acts on Alice's transmitted register and the receiver measures.
--   - `eaSuccess`: PDF p.5: optimize over all finite shared entanglement and local operations.
--   - `ParallelAchievable`: PDF p.5, Eq.(5): arbitrary collective memoryless codes with vanishing average error and liminf rate at least r. Integer messages handle rounding explicitly.
--   - `parallelCapacity`: PDF p.5, Eq.(5): capacity of a semantic family of integer-message codes.
--   - `nsCapacity`: PDF p.5: memoryless n-use NS or NS∩PPT capacity.
--   - `ordinaryClassicalCapacity`: PDF pp.1,5: ordinary unassisted classical capacity.
--   - `eaCapacity`: PDF p.5: entanglement-assisted classical capacity with arbitrary finite ancillas.
--   - `integerOneShot`: PDF p.8, Eq.(23): operational one-shot capacity for integer-message classes.
--   - `SuccessFeasible`: PDF p.6, Eqs.(8),(9): all primal constraints, including normalized rho. eta=1/m for success and eta free for the finite-error minimization.
--   - `successValues`: PDF p.6: the SDP extension to real message parameter lambda≥1. Its integer values are identified with operational success by Theorem 3.
--   - `realSuccess`: PDF pp.6,8–9: continuous success SDP, not a fractional physical code.
--   - `oneShot`: PDF p.8, Eq.(23): continuous extension used for the NS finite-error formulas.
--   - `SuccessDualFeasible`: PDF p.8, Eq.(22): unrestricted Hermitian S; Y=W=0 in the NS dual.
--   - `dualValues`: PDF p.8, Eq.(22): objective values of the full dual success SDP.
--   - `etaValues`: PDF p.9, Eqs.(24),(25): eta values with the required decoding threshold.
--   - `mwEtaValues`: PDF pp.10–11, Eqs.(31),(32): Matthews–Wehner SDP, with inequality marginal.
--   - `mwBound`: PDF p.10: the named finite Matthews–Wehner bound via its supplied SDP.
--   - `testingValues`: PDF p.10, Eq.(33): binary hypothesis-testing type-II objective values. A PPT POVM has BOTH T and I-T PPT, encoded by IsEffect (PT T).
--   - `testingEntropy`: PDF p.10, Eq.(33): the testing entropy is +infinity if type-II error is zero. This avoids Lean's junk value log(0)=0.
--   - `testingAlternatives`: PDF p.10: alternative-state testing values for one normalized input.
--   - `mwTesting`: PDF p.10, Proposition 6: max over density inputs and min over density alternatives. The purification is reference first and its actual reference marginal is used.
--   - `MWTestingAttained`: PDF p.10: attainment of the printed max-min, without silently replacing its extrema by unattained suprema or infima.
--   - `channelMI`: PDF pp.11–12: channel mutual information of a density input, in bits.
--   - `maxMI`: PDF pp.11–12: maximum channel mutual information over normalized inputs.
--   - `cqChannel`: PDF pp.12–13: the cq channel on all operators, dephasing the input basis.
--   - `cqValues`: PDF p.13, Eq.(35): the reduced cq objective values. Positivity of s is implied by 0≤Q≤sI on nonzero B, but is explicit here for clarity.
--   - `simpleCQ`: PDF p.11: two pure qubit outputs a|0> ± sqrt(1-a²)|1>.
--   - `ppvValues`: PDF p.13, Eq.(38): PPV in MESSAGE units. Nonnegativity is inherited from Eq.(35)'s positive diagonal Q; the printed LP suppresses it.
--   - `BetaFeasible`: PDF pp.14–16, Eqs.(41),(45): all four inequalities; PT is applied to J and R.
--   - `plusValues`: PDF pp.14–16: the f+ objective set, from the actual channel choi matrix.
--   - `fPlus`: PDF p.14, Eq.(41): the single-use success upper bound.
--   - `channelBeta`: PDF p.16, Eq.(45): the actual beta program at m=1.
--   - `cBeta`: PDF p.16, Theorem 11: beta bound in bits.
--   - `ZetaFeasible`: PDF pp.16–17, Eqs.(48),(49): V≥J and BOTH partial-transpose inequalities.
--   - `zetaPlusValues`: PDF p.17: objective values of the second success program.
--   - `zetaPlus`: PDF p.17, Eq.(49): the second success upper bound.
--   - `channelZeta`: PDF p.16, Eq.(48): the zeta program.
--   - `cZeta`: PDF p.16, Theorem 12: zeta bound in bits.
--   - `ExponentialConverse`: PDF pp.16–17: uniform exponential success decay above a rate threshold. The constants precede all blocklengths, physical message numbers, and codes.
--   - `qutritKraus`: PDF p.19, §V.C: the two printed qutrit Kraus operators.
--   - `qutrit`: PDF p.19: the qutrit channel constructed from its data, not a free variable.
--   - `qutritDilation`: PDF p.19: fixed Stinespring dilation B⊗E, with E of dimension two.
--   - `IsEB`: PDF p.19: dimension-general entanglement-breaking condition under every finite reference extension; all tested inputs are normalized densities.
--   - `IsHadamard`: PDF p.19: a Hadamard channel has an entanglement-breaking complement of an isometric dilation. No fixed Kraus representation is assumed in this predicate.
--   - `zeroMessages`: PDF p.20: continuous assisted zero-error message number from Theorem 4.
--   - `zeroValues`: PDF pp.20–21, Eq.(52): the unnormalized zero-error feasible set.
--   - `zeroCapacity`: PDF p.21: regularized continuous assisted zero-error rate.
--   - `uaZeroMessages`: PDF pp.20–21: unassisted integer zero-error message optimum.
--   - `bipartiteGraph`: PDF p.21: the bipartite Kraus space K, distinct from span(E_i†E_j).
--   - `lovaszValues`: PDF p.21: naive noncommutative Lovasz number. Orthogonality is complex Hilbert–Schmidt orthogonality to the operator graph S=span(E_i†E_j).
--   - `lovasz`: PDF p.21: optimum of the naive Lovasz program (attainment is recorded below).
--   - `uaZeroCapacity`: PDF p.22: unassisted zero-error classical capacity, with integer codes.
--   - `privateZeroMessages`: PDF p.22: exact private codes have joint state equal to a perfect common classical key tensor a message-independent environment state.
--   - `privateZeroCapacity`: PDF p.22: private zero-error capacity regularizes exact finite-block codes.
--   - `quantumZeroMessages`: PDF p.22: quantum zero-error message dimensions via exact entanglement transmission fidelity one, with the same CPTP code model as ordinary Q.
--   - `quantumZeroCapacity`: PDF p.22: quantum zero-error capacity in qubits per channel use.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, https://arxiv.org/abs/1610.06381v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

/-!
Wang, Xie and Duan, arXiv:1610.06381v4. Page numbers are PDF pages.
The imports from Information100 are pinned accepted libraries, not other draft chunks.
Operational integer message counts are distinct from the continuous NS SDP extension.
All new definitions are specific to this paper. No feedback resource is included.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.4: reuse of the accepted partial transpose on the second register. -/
abbrev PT {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) :=
  QAlgorithms.Papers.Independent.Information100.P03.partialTransposeB X

/-- PDF p.17: reuse of the exact accepted Kraus-form amplitude damping primitive. -/
abbrev AD (gamma : ℝ) :=
  QAlgorithms.Papers.Independent.Information100.P53.amplitudeDamping gamma

/-- PDF p.4: Loewner order, never the pointwise order on matrix entries. -/
def LEop {I : Type*} [Fintype I] (X Y : Matrix I I ℂ) : Prop :=
  (Y - X).PosSemidef

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.4, Eq.(2): input order (message,B), output order (A,estimate). -/
abbrev CodeMatrix (A B : Type) (m : ℕ) :=
  Matrix ((Fin m × B) × (A × Fin m)) ((Fin m × B) × (A × Fin m)) ℂ

/-- PDF pp.4–6: CP, TP, classical message registers, both NS conditions, and,
when requested, PPT on BOTH Bob's input B and output estimate. The normalized
marginals below are Eq.(2) in entries. No division by m-1 is used. -/
def NSCode (ppt : Bool) (m : ℕ) (Z : CodeMatrix A B m) : Prop :=
  0 < m ∧ Z.PosSemidef ∧ traceRight Z = 1 ∧
  (∀ i j b c a d k l,
    Z ((i,b),(a,k)) ((j,c),(d,l)) =
      if i = j ∧ k = l then Z ((i,b),(a,k)) ((j,c),(d,l)) else 0) ∧
  (∀ i j b c k l,
    (∑ a, Z ((i,b),(a,k)) ((j,c),(a,l))) =
      if i = j then (m : ℂ)⁻¹ *
        ∑ h : Fin m, ∑ a, Z ((h,b),(a,k)) ((h,c),(a,l)) else 0) ∧
  (∀ i j b c a d,
    (∑ k, Z ((i,b),(a,k)) ((j,c),(d,k))) =
      if b = c then (Fintype.card B : ℂ)⁻¹ *
        ∑ h : B, ∑ k, Z ((i,h),(a,k)) ((j,h),(d,k)) else 0) ∧
  (ppt = true → Matrix.PosSemidef (fun p q =>
    Z ((p.1.1,q.1.2),(p.2.1,q.2.2))
      ((q.1.1,p.1.2),(q.2.1,p.2.2)) : CodeMatrix A B m))

/-- PDF p.5, Eqs.(3),(7): link product of the channel and a bipartite code,
followed by a uniform average of the diagonal correct-message probabilities. -/
def codeSuccess (N : Superop A B) {m : ℕ} (Z : CodeMatrix A B m) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k : Fin m,
    (∑ a : A, ∑ d : A, ∑ b : B, ∑ c : B,
      choi N (a,b) (d,c) * Z ((k,b),(a,k)) ((k,c),(d,k))).re

/-- PDF p.5, Eq.(4): optimization over a code chosen before the uniform message. -/
def nsSuccess (ppt : Bool) (N : Superop A B) (m : ℕ) : ℝ :=
  sSup {s | ∃ Z : CodeMatrix A B m, NSCode ppt m Z ∧ s = codeSuccess N Z}

/-- PDF pp.4–5: ordinary local mixed-state encoder and a decoding POVM. -/
structure UACode (A B : Type) [Fintype A] [Fintype B] [DecidableEq B] (m : ℕ) where
  state : Fin m → Matrix A A ℂ
  density : ∀ k, IsDensityMatrix (state k)
  measurement : Fin m → Matrix B B ℂ
  povm : IsPOVM measurement

/-- PDF p.5, Eq.(3): unassisted average decoding success. -/
def uaCodeSuccess (N : Superop A B) {m : ℕ} (K : UACode A B m) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k, effectProb (K.measurement k) (N (K.state k))

/-- PDF p.5: unassisted codes optimize over arbitrary mixed input states. -/
def uaSuccess (N : Superop A B) (m : ℕ) : ℝ :=
  sSup {s | ∃ K : UACode A B m, s = uaCodeSuccess N K}

/-- PDF p.5: arbitrary finite entangled ancillas, message-dependent local CPTP
encoding, and a joint receiver POVM. No extra communication is supplied. -/
structure EACode (A B : Type) [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (m : ℕ) where
  aDim : ℕ
  bDim : ℕ
  aPos : 0 < aDim
  bPos : 0 < bDim
  shared : Matrix (Fin aDim × Fin bDim) (Fin aDim × Fin bDim) ℂ
  shared_density : IsDensityMatrix shared
  encode : Fin m → Superop (Fin aDim) A
  encode_channel : ∀ k, IsChannel (encode k)
  measurement : Fin m → Matrix (B × Fin bDim) (B × Fin bDim) ℂ
  povm : IsPOVM measurement

/-- PDF p.5: the message is encoded locally; Bob's shared subsystem is untouched. -/
def eaInput {m : ℕ} (K : EACode A B m) (k : Fin m) :
    Matrix (A × Fin K.bDim) (A × Fin K.bDim) ℂ :=
  fun p q => K.encode k (fun x y => K.shared (x,p.2) (y,q.2)) p.1 q.1

/-- PDF p.5: N acts on Alice's transmitted register and the receiver measures. -/
def eaCodeSuccess (N : Superop A B) {m : ℕ} (K : EACode A B m) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k, effectProb (K.measurement k)
    (fun p q => N (fun x y => eaInput K k (x,p.2) (y,q.2)) p.1 q.1)

/-- PDF p.5: optimize over all finite shared entanglement and local operations. -/
def eaSuccess (N : Superop A B) (m : ℕ) : ℝ :=
  sSup {s | ∃ K : EACode A B m, s = eaCodeSuccess N K}

/-- PDF p.5, Eq.(5): arbitrary collective memoryless codes with vanishing average
error and liminf rate at least r. Integer messages handle rounding explicitly. -/
def ParallelAchievable (f : ℕ → ℕ → ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ M : ℕ → ℕ, (∀ n, 0 < M n) ∧
    Tendsto (fun n => f n (M n)) atTop (nhds 1) ∧
    ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop,
      r - delta ≤ log2 (M n) / (n : ℝ)

/-- PDF p.5, Eq.(5): capacity of a semantic family of integer-message codes. -/
def parallelCapacity (f : ℕ → ℕ → ℝ) : ℝ := sSup {r | ParallelAchievable f r}

/-- PDF p.5: memoryless n-use NS or NS∩PPT capacity. -/
def nsCapacity (ppt : Bool) (N : Superop A B) : ℝ :=
  parallelCapacity (fun n => nsSuccess ppt (piSuperop (fun _ : Fin n => N)))

/-- PDF pp.1,5: ordinary unassisted classical capacity. -/
def ordinaryClassicalCapacity (N : Superop A B) : ℝ :=
  parallelCapacity (fun n => uaSuccess (piSuperop (fun _ : Fin n => N)))

/-- PDF p.5: entanglement-assisted classical capacity with arbitrary finite ancillas. -/
def eaCapacity (N : Superop A B) : ℝ :=
  parallelCapacity (fun n => eaSuccess (piSuperop (fun _ : Fin n => N)))

/-- PDF p.8, Eq.(23): operational one-shot capacity for integer-message classes. -/
def integerOneShot (f : ℕ → ℝ) (e : ℝ) : ℝ :=
  sSup {r | ∃ m : ℕ, 0 < m ∧ 1 - e ≤ f m ∧ r = log2 m}

/-- PDF p.6, Eqs.(8),(9): all primal constraints, including normalized rho.
eta=1/m for success and eta free for the finite-error minimization. -/
def SuccessFeasible (ppt : Bool) (eta : ℝ) (rho : Matrix A A ℂ)
    (F : Matrix (A × B) (A × B) ℂ) : Prop :=
  IsDensityMatrix rho ∧ F.PosSemidef ∧ LEop F (Matrix.kronecker rho 1) ∧
  traceLeft F = (eta : ℂ) • 1 ∧
  (ppt = true → (PT F).PosSemidef ∧ LEop (PT F) (Matrix.kronecker rho 1))

/-- PDF p.6: the SDP extension to real message parameter lambda≥1.
Its integer values are identified with operational success by Theorem 3. -/
def successValues (ppt : Bool) (N : Superop A B) (lambda : ℝ) : Set ℝ :=
  {s | ∃ (rho : Matrix A A ℂ) (F : Matrix (A × B) (A × B) ℂ),
    SuccessFeasible ppt lambda⁻¹ rho F ∧ s = effectProb (choi N) F}

/-- PDF pp.6,8–9: continuous success SDP, not a fractional physical code. -/
def realSuccess (ppt : Bool) (N : Superop A B) (lambda : ℝ) : ℝ :=
  sSup (successValues ppt N lambda)

/-- PDF p.8, Eq.(23): continuous extension used for the NS finite-error formulas. -/
def oneShot (ppt : Bool) (N : Superop A B) (e : ℝ) : ℝ :=
  sSup {r | ∃ lambda : ℝ, 1 ≤ lambda ∧
    1 - e ≤ realSuccess ppt N lambda ∧ r = log2 lambda}

/-- PDF p.8, Eq.(22): unrestricted Hermitian S; Y=W=0 in the NS dual. -/
def SuccessDualFeasible (ppt : Bool) (N : Superop A B) (m t : ℝ)
    (S : Matrix B B ℂ) (X Y W : Matrix (A × B) (A × B) ℂ) : Prop :=
  S.IsHermitian ∧ X.PosSemidef ∧ Y.PosSemidef ∧ W.PosSemidef ∧
  (ppt = false → Y = 0 ∧ W = 0) ∧
  LEop (choi N) (X + Matrix.kronecker 1 S + PT (W - Y)) ∧
  LEop (traceRight (X + W)) ((t : ℂ) • 1)

/-- PDF p.8, Eq.(22): objective values of the full dual success SDP. -/
def dualValues (ppt : Bool) (N : Superop A B) (m : ℝ) : Set ℝ :=
  {s | ∃ (t : ℝ) (S : Matrix B B ℂ) (X Y W : Matrix (A × B) (A × B) ℂ),
    SuccessDualFeasible ppt N m t S X Y W ∧ s = t + S.trace.re / m}

/-- PDF p.9, Eqs.(24),(25): eta values with the required decoding threshold. -/
def etaValues (ppt : Bool) (N : Superop A B) (e : ℝ) : Set ℝ :=
  {eta | ∃ (rho : Matrix A A ℂ) (F : Matrix (A × B) (A × B) ℂ),
    SuccessFeasible ppt eta rho F ∧ 1 - e ≤ effectProb (choi N) F}

/-- PDF pp.10–11, Eqs.(31),(32): Matthews–Wehner SDP, with inequality marginal. -/
def mwEtaValues (ppt : Bool) (N : Superop A B) (e : ℝ) : Set ℝ :=
  {eta | ∃ (rho : Matrix A A ℂ) (F : Matrix (A × B) (A × B) ℂ),
    IsDensityMatrix rho ∧ F.PosSemidef ∧ LEop F (Matrix.kronecker rho 1) ∧
    LEop (traceLeft F) ((eta : ℂ) • 1) ∧ 1 - e ≤ effectProb (choi N) F ∧
    (ppt = true → (PT F).PosSemidef ∧ LEop (PT F) (Matrix.kronecker rho 1))}

/-- PDF p.10: the named finite Matthews–Wehner bound via its supplied SDP. -/
def mwBound (ppt : Bool) (N : Superop A B) (e : ℝ) : ℝ :=
  -log2 (sInf (mwEtaValues ppt N e))

/-- PDF p.10, Eq.(33): binary hypothesis-testing type-II objective values.
A PPT POVM has BOTH T and I-T PPT, encoded by IsEffect (PT T). -/
def testingValues (ppt : Bool) (rho sigma : Matrix (A × B) (A × B) ℂ)
    (e : ℝ) : Set ℝ :=
  {s | ∃ T : Matrix (A × B) (A × B) ℂ,
    IsEffect T ∧ (ppt = true → IsEffect (PT T)) ∧
    1 - e ≤ effectProb T rho ∧ s = effectProb T sigma}

/-- PDF p.10, Eq.(33): the testing entropy is +infinity if type-II error is zero.
This avoids Lean's junk value log(0)=0. -/
def testingEntropy (ppt : Bool) (rho sigma : Matrix (A × B) (A × B) ℂ)
    (e : ℝ) : EReal :=
  let b := sInf (testingValues ppt rho sigma e)
  if b = 0 then ⊤ else ((-log2 b : ℝ) : EReal)

/-- PDF p.10: alternative-state testing values for one normalized input. -/
def testingAlternatives (ppt : Bool) (N : Superop A B) (e : ℝ)
    (rho : Matrix A A ℂ) : Set EReal :=
  {v | ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
    v = testingEntropy ppt
      (idTensorSuperop (R := A) N (pureDensity (canonicalPurification rho)))
      (Matrix.kronecker (traceRight (pureDensity (canonicalPurification rho))) sigma) e}

/-- PDF p.10, Proposition 6: max over density inputs and min over density alternatives.
The purification is reference first and its actual reference marginal is used. -/
def mwTesting (ppt : Bool) (N : Superop A B) (e : ℝ) : EReal :=
  sSup {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
    v = sInf (testingAlternatives ppt N e rho)}

/-- PDF p.10: attainment of the printed max-min, without silently replacing
its extrema by unattained suprema or infima. -/
def MWTestingAttained (ppt : Bool) (N : Superop A B) (e : ℝ) : Prop :=
  (∀ rho : Matrix A A ℂ, IsDensityMatrix rho →
    IsLeast (testingAlternatives ppt N e rho) (sInf (testingAlternatives ppt N e rho))) ∧
  IsGreatest {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
    v = sInf (testingAlternatives ppt N e rho)} (mwTesting ppt N e)

/-- PDF pp.11–12: channel mutual information of a density input, in bits. -/
def channelMI (N : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  vnEntropy rho + vnEntropy (N rho) -
    vnEntropy (idTensorSuperop (R := A) N (pureDensity (canonicalPurification rho)))

/-- PDF pp.11–12: maximum channel mutual information over normalized inputs. -/
def maxMI (N : Superop A B) : ℝ :=
  sSup {r | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ r = channelMI N rho}

/-- PDF pp.12–13: the cq channel on all operators, dephasing the input basis. -/
def cqChannel (rho : A → Matrix B B ℂ) : Superop A B :=
  fun X => ∑ x, X x x • rho x

/-- PDF p.13, Eq.(35): the reduced cq objective values. Positivity of s is
implied by 0≤Q≤sI on nonzero B, but is explicit here for clarity. -/
def cqValues (rho : A → Matrix B B ℂ) (e : ℝ) : Set ℝ :=
  {v | ∃ (s : A → ℝ) (Q : A → Matrix B B ℂ),
    (∀ x, 0 ≤ s x ∧ (Q x).PosSemidef ∧ LEop (Q x) ((s x : ℂ) • 1)) ∧
    (∑ x, Q x) = 1 ∧
    (1 - e) * (∑ x, s x) ≤ ∑ x, effectProb (Q x) (rho x) ∧ v = ∑ x, s x}

/-- PDF p.11: two pure qubit outputs a|0> ± sqrt(1-a²)|1>. -/
def simpleCQ (a : ℝ) : Superop (Fin 2) (Fin 2) :=
  let b := Real.sqrt (1 - a ^ 2)
  cqChannel (fun x => if x = 0 then
    !![((a^2 : ℝ) : ℂ), ((a*b : ℝ) : ℂ); ((a*b : ℝ) : ℂ), ((b^2 : ℝ) : ℂ)] else
    !![((a^2 : ℝ) : ℂ), ((-a*b : ℝ) : ℂ); ((-a*b : ℝ) : ℂ), ((b^2 : ℝ) : ℂ)])

/-- PDF p.13, Eq.(38): PPV in MESSAGE units. Nonnegativity is inherited from
Eq.(35)'s positive diagonal Q; the printed LP suppresses it. -/
def ppvValues (W : A → B → ℝ) (e : ℝ) : Set ℝ :=
  {v | ∃ (s : A → ℝ) (Q : A → B → ℝ),
    (∀ x, 0 ≤ s x) ∧ (∀ x y, 0 ≤ Q x y ∧ Q x y ≤ s x) ∧
    (∀ y, ∑ x, Q x y ≤ 1) ∧
    (1 - e) * (∑ x, s x) ≤ ∑ x, ∑ y, W x y * Q x y ∧ v = ∑ x, s x}

/-- PDF pp.14–16, Eqs.(41),(45): all four inequalities; PT is applied to J and R. -/
def BetaFeasible (N : Superop A B) (m : ℝ) (S : Matrix B B ℂ)
    (R : Matrix (A × B) (A × B) ℂ) : Prop :=
  S.IsHermitian ∧ R.IsHermitian ∧
  LEop (-R) (PT (choi N)) ∧ LEop (PT (choi N)) R ∧
  LEop (-(m : ℂ) • Matrix.kronecker 1 S) (PT R) ∧
  LEop (PT R) ((m : ℂ) • Matrix.kronecker 1 S)

/-- PDF pp.14–16: the f+ objective set, from the actual channel choi matrix. -/
def plusValues (N : Superop A B) (m : ℝ) : Set ℝ :=
  {s | ∃ (S : Matrix B B ℂ) (R : Matrix (A × B) (A × B) ℂ),
    BetaFeasible N m S R ∧ s = S.trace.re}

/-- PDF p.14, Eq.(41): the single-use success upper bound. -/
def fPlus (N : Superop A B) (m : ℝ) : ℝ := sInf (plusValues N m)

/-- PDF p.16, Eq.(45): the actual beta program at m=1. -/
def channelBeta (N : Superop A B) : ℝ := fPlus N 1

/-- PDF p.16, Theorem 11: beta bound in bits. -/
def cBeta (N : Superop A B) : ℝ := log2 (channelBeta N)

/-- PDF pp.16–17, Eqs.(48),(49): V≥J and BOTH partial-transpose inequalities. -/
def ZetaFeasible (N : Superop A B) (m : ℝ) (S : Matrix B B ℂ)
    (V : Matrix (A × B) (A × B) ℂ) : Prop :=
  S.IsHermitian ∧ V.IsHermitian ∧ LEop (choi N) V ∧
  LEop (-(m : ℂ) • Matrix.kronecker 1 S) (PT V) ∧
  LEop (PT V) ((m : ℂ) • Matrix.kronecker 1 S)

/-- PDF p.17: objective values of the second success program. -/
def zetaPlusValues (N : Superop A B) (m : ℝ) : Set ℝ :=
  {s | ∃ (S : Matrix B B ℂ) (V : Matrix (A × B) (A × B) ℂ),
    ZetaFeasible N m S V ∧ s = S.trace.re}

/-- PDF p.17, Eq.(49): the second success upper bound. -/
def zetaPlus (N : Superop A B) (m : ℝ) : ℝ := sInf (zetaPlusValues N m)

/-- PDF p.16, Eq.(48): the zeta program. -/
def channelZeta (N : Superop A B) : ℝ := zetaPlus N 1

/-- PDF p.16, Theorem 12: zeta bound in bits. -/
def cZeta (N : Superop A B) : ℝ := log2 (channelZeta N)

/-- PDF pp.16–17: uniform exponential success decay above a rate threshold.
The constants precede all blocklengths, physical message numbers, and codes. -/
def ExponentialConverse (N : Superop A B) (bound : ℝ) : Prop :=
  ∀ r : ℝ, bound < r → ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∀ M : ℕ, 0 < M → (n : ℝ) * r ≤ log2 M →
      nsSuccess true (piSuperop (fun _ : Fin n => N)) M ≤ Real.rpow 2 (-c * n)

/-- PDF p.19, §V.C: the two printed qutrit Kraus operators. -/
def qutritKraus (alpha : ℝ) : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, (Real.sin alpha : ℂ), 0; 0, 0, 1; 0, 0, 0],
    !![0, 0, 0; 1, 0, 0; 0, (Real.cos alpha : ℂ), 0]]

/-- PDF p.19: the qutrit channel constructed from its data, not a free variable. -/
def qutrit (alpha : ℝ) : Superop (Fin 3) (Fin 3) := krausApply (qutritKraus alpha)

/-- PDF p.19: fixed Stinespring dilation B⊗E, with E of dimension two. -/
def qutritDilation (alpha : ℝ) : Matrix (Fin 3 × Fin 2) (Fin 3) ℂ :=
  fun p a => qutritKraus alpha p.2 p.1 a

/-- PDF p.19: dimension-general entanglement-breaking condition under every
finite reference extension; all tested inputs are normalized densities. -/
def IsEB (N : Superop A B) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ rho : Matrix (Fin k × A) (Fin k × A) ℂ,
    IsDensityMatrix rho → Entanglement.IsSeparablePositive (idTensorSuperop N rho)

/-- PDF p.19: a Hadamard channel has an entanglement-breaking complement of an
isometric dilation. No fixed Kraus representation is assumed in this predicate. -/
def IsHadamard (N : Superop A B) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ U : Matrix (B × Fin k) A ℂ,
    Uᴴ * U = 1 ∧ (∀ rho : Matrix A A ℂ, traceRight (U * rho * Uᴴ) = N rho) ∧
    IsEB (fun rho : Matrix A A ℂ =>
      (traceLeft (U * rho * Uᴴ) : Matrix (Fin k) (Fin k) ℂ))

/-- PDF p.20: continuous assisted zero-error message number from Theorem 4. -/
def zeroMessages (ppt : Bool) (N : Superop A B) : ℝ :=
  Real.rpow 2 (oneShot ppt N 0)

/-- PDF pp.20–21, Eq.(52): the unnormalized zero-error feasible set. -/
def zeroValues (ppt : Bool) (N : Superop A B) : Set ℝ :=
  {v | ∃ (S : Matrix A A ℂ) (U : Matrix (A × B) (A × B) ℂ),
    S.PosSemidef ∧ U.PosSemidef ∧ LEop U (Matrix.kronecker S 1) ∧
    traceLeft U = 1 ∧ (choi N * (Matrix.kronecker S 1 - U)).trace = 0 ∧
    (ppt = true → (PT U).PosSemidef ∧ LEop (PT U) (Matrix.kronecker S 1)) ∧
    v = S.trace.re}

/-- PDF p.21: regularized continuous assisted zero-error rate. -/
def zeroCapacity (ppt : Bool) (N : Superop A B) : ℝ :=
  sSup {r | ∃ n : ℕ, 0 < n ∧
    r = log2 (zeroMessages ppt (piSuperop (fun _ : Fin n => N))) / (n : ℝ)}

/-- PDF pp.20–21: unassisted integer zero-error message optimum. -/
def uaZeroMessages (N : Superop A B) : ℝ :=
  sSup {r | ∃ m : ℕ, 0 < m ∧ (∃ K : UACode A B m, uaCodeSuccess N K = 1) ∧ r = m}

/-- PDF p.21: the bipartite Kraus space K, distinct from span(E_i†E_j). -/
def bipartiteGraph (N : Superop A B) : Submodule ℂ (Matrix B A ℂ) :=
  Submodule.span ℂ {X | ∃ k : ℕ, ∃ E : Fin k → Matrix B A ℂ,
    IsKrausFamily E ∧ (∀ rho, N rho = krausApply E rho) ∧ ∃ i, X = E i}

/-- PDF p.21: naive noncommutative Lovasz number. Orthogonality is complex
Hilbert–Schmidt orthogonality to the operator graph S=span(E_i†E_j). -/
def lovaszValues (N : Superop A B) : Set ℝ :=
  {r | ∃ T : Matrix A A ℂ, (1 + T).PosSemidef ∧
    (∀ X ∈ QAlgorithms.Papers.Independent.Information100.P62.graph N,
      (Xᴴ * T).trace = 0) ∧ r = specNorm (1 + T)}

/-- PDF p.21: optimum of the naive Lovasz program (attainment is recorded below). -/
def lovasz (N : Superop A B) : ℝ := sSup (lovaszValues N)

/-- PDF p.22: unassisted zero-error classical capacity, with integer codes. -/
def uaZeroCapacity (N : Superop A B) : ℝ :=
  sSup {r | ∃ n : ℕ, 0 < n ∧
    r = log2 (uaZeroMessages (piSuperop (fun _ : Fin n => N))) / (n : ℝ)}

/-- PDF p.22: exact private codes have joint state equal to a perfect common
classical key tensor a message-independent environment state. -/
def privateZeroMessages (alpha : ℝ) (n : ℕ) : ℝ :=
  sSup {r | ∃ K : QAlgorithms.Papers.Independent.Information100.P67.PrivateCode
      (Fin 3) (Fin 3) n,
    K.Valid ∧ (∃ sigma : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      IsDensityMatrix sigma ∧
      QAlgorithms.Papers.Independent.Information100.P67.jointOutput (qutritDilation alpha) K =
      QAlgorithms.Papers.Independent.Information100.P67.idealJoint K.M sigma) ∧ r = K.M}

/-- PDF p.22: private zero-error capacity regularizes exact finite-block codes. -/
def privateZeroCapacity (alpha : ℝ) : ℝ :=
  sSup {r | ∃ n : ℕ, 0 < n ∧ r = log2 (privateZeroMessages alpha n) / (n : ℝ)}

/-- PDF p.22: quantum zero-error message dimensions via exact entanglement
transmission fidelity one, with the same CPTP code model as ordinary Q. -/
def quantumZeroMessages (N : Superop A B) : ℝ :=
  sSup {r | ∃ K : QAlgorithms.Papers.Independent.Information100.P80.TransmissionCode A B,
    QAlgorithms.Papers.Independent.Information100.P80.transmissionFidelity N K = 1 ∧ r = K.M}

/-- PDF p.22: quantum zero-error capacity in qubits per channel use. -/
def quantumZeroCapacity (N : Superop A B) : ℝ :=
  sSup {r | ∃ n : ℕ, 0 < n ∧
    r = log2 (quantumZeroMessages (piSuperop (fun _ : Fin n => N))) / (n : ℝ)}

/-- Sanity: the partial transpose convention is involutive, PDF p.4. -/
example (X : Matrix (A × B) (A × B) ℂ) : PT (PT X) = X := rfl

/-- Sanity: unnormalized choi entries, PDF p.4. -/
example (N : Superop A B) (a d : A) (b c : B) :
    choi N (a,b) (d,c) = N (Matrix.single a d 1) b c := rfl

/-- Sanity: no-message sum contributes zero; theorems exclude m=0, PDF p.5. -/
example (N : Superop A B) (Z : CodeMatrix A B 0) : codeSuccess N Z = 0 := by
  simp [codeSuccess]

/-- Sanity: the qutrit dilation has the printed complementary Kraus amplitudes, p.19. -/
example (alpha : ℝ) : qutritDilation alpha (0,0) 1 = (Real.sin alpha : ℂ) := rfl

/-- Sanity: the NS-only feasible predicate deletes exactly the PPT clause, p.6. -/
example (eta : ℝ) (rho : Matrix A A ℂ) (F : Matrix (A × B) (A × B) ℂ) :
    SuccessFeasible false eta rho F ↔
      IsDensityMatrix rho ∧ F.PosSemidef ∧ LEop F (Matrix.kronecker rho 1) ∧
        traceLeft F = (eta : ℂ) • 1 := by
  simp [SuccessFeasible]

end QAlgorithms.Papers.Independent.Dependency50.P23


