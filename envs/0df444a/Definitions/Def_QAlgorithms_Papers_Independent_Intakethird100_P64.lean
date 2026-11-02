-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P64
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P64
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:32:53.548558+00:00
-- url     : https://prove2.me/theorems/9786b76e-375a-451e-8539-68c8eaa2c74d
-- title:
--   Definitions for A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal
-- statement:
--   The objects the formalized statements of *A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal* (arXiv:quant-ph/0505138) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `feedbackOutputVector`: PDF p.2, (6), and p.3: the output vector is computed from U and phi.
--   - `feedbackEntropyA`: PDF p.2, (8): H(A) for the actual pure tripartite vector.
--   - `mutualRA`: PDF p.2: I(R;A)=H(R)+H(A)-H(RA), without using pure-state identities.
--   - `mutualAB`: PDF p.2: I(A;B)=H(A)+H(B)-H(AB).
--   - `mutualRB`: PDF p.2: I(R;B)=H(R)+H(B)-H(RB).
--   - `localOperation`: PDF pp.2–4: a local operation from a retained isometric dilation. W is local work, discarded only when evaluating the reduced output. V†V=1 is carried by codes. Arbitrary work dimension permits typical-subspace failure flags on the full input.
--   - `FeedbackSimulationCode`: PDF p.2, (5): q transmitted qubits and k supplied Bell pairs; A stays at Alice, B goes to Bob. Local work starts pure through the isometry description. No entropy inequalities or desired performance properties are fields of this code.
--   - `appendBell`: PDF p.2: append exactly k normalized, independently supplied Bell pairs.
--   - `FeedbackSimulationCode.channel`: PDF p.2, (5): the actual simulated channel, before extending by any reference.
--   - `isometryPower`: PDF p.2: U applied independently n times, grouping the A and B outputs.
--   - `RelativeSimulationAchievable`: PDF pp.1–2: FQRS simulation of the relative channel at input rho. For every error and rate slack, a strictly positive marginal tolerance is chosen. All large blocklengths have codes fixed before every reference/input test. Fin d ranges over all finite reference dimensions. The promise constrains the input marginal only; the error tests the entire correlated output. Rate zero allows sublinear resources.
--   - `SlepianWolfCode`: PDF pp.3–4, (12), Fig.4: Alice receives A^n and Bob B^n from the Source. The q-qubit message is sent forward. Alice keeps l Bell halves; Bob outputs the other l halves and S^n, the copy of the original source. Local work remains in the dilations, so no impossible full-input compression isometry is assumed.
--   - `sourceDensity`: PDF pp.3–4: the normalized source purification in grouped copy registers.
--   - `distributedSource`: PDF p.3: apply only the specified source isometry; Alice and Bob cannot encode or choose the S input. The reference is untouched.
--   - `sourceTarget`: PDF pp.3–4: source/reference and generated Bell pairs are tested jointly. The ideal S^n output is a copy at Bob, not a free matrix unrelated to phi.
--   - `SlepianWolfCode.error`: PDF pp.3–4: full joint trace-norm error of the physical FQSW code.
--   - `SourceTransferAchievable`: PDF pp.1,3–4: source transfer with Q forward qubits consumed and E ebits generated per source copy. No initial Bell pairs or other nonlocal assistance. The integer output is rounded down and clipped at zero only when E-delta<0.
--   - `sourceToAlice`: PDF p.3: the identity from the Source to Alice, with Bob's initial share one-dimensional. S, A-hat, A-prime and B-hat are copies of the same basis type.
--   - `RelativeIdentityTest`: PDF pp.2–3: the promise supplied by a relative n-use identity channel. It guarantees a joint reference test for every input with eta-close marginal.
--   - `RoutingCode`: PDF p.3, Fig.3: local encoding, n uses of the supplied relative identity, and local decoding. The middle channel is supplied, not chosen by the code.
--   - `SourceRoutingAchievable`: PDF p.3: direct source/identity concatenation, with the actual encoder marginal tested against the supplied channel's promise. The quantified F represents any physical implementation satisfying that promise, not unrestricted access. The code uses exactly n supplied identity calls for n source copies; no nonlocal ancillas or extra communication are available. delta records allowed rate slack.
-- source:
--   A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal, arXiv:quant-ph/0505138v1, https://arxiv.org/abs/quant-ph/0505138v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

/-!
Devetak, arXiv:quant-ph/0505138v1, PDF pp.1–4.
Only the five results with complete task-specific operational semantics are stated.
Other nodes, including the printed capacity region, are explicitly deferred in HARD.md.
All register bases are finite and nonempty; Unit represents an absent register.
Entropy is in bits. Error is full trace norm, an equivalent vanishing-error convention
to half trace norm. Maps are selected before all test inputs. One forward quantum
message is counted by its actual number of qubits; Bell counters are actual pairs.
Source inputs are supplied by the Source and are never selected by a code.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P64

open QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P20
  (Copies redistributionMarginal subsystemEntropy forwardApply)
open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)
open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (6), and p.3: the output vector is computed from U and phi. -/
def feedbackOutputVector {R S A B : Type} [Fintype S]
    (U : Matrix (A × B) S ℂ) (phi : EuclideanSpace ℂ (R × S)) :
    EuclideanSpace ℂ (R × (A × B)) :=
  WithLp.toLp 2 fun p => ∑ s, U p.2 s * phi (p.1, s)

section Entropies

variable {R A B : Type} [Fintype R] [Fintype A] [Fintype B]

/-- PDF p.2, (8): H(A) for the actual pure tripartite vector. -/
def feedbackEntropyA (psi : EuclideanSpace ℂ (R × (A × B))) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => p.2.1) (fun p => (p.1, p.2.2))

/-- PDF p.2: I(R;A)=H(R)+H(A)-H(RA), without using pure-state identities. -/
def mutualRA (psi : EuclideanSpace ℂ (R × (A × B))) : ℝ :=
  subsystemEntropy (pureDensity psi) Prod.fst Prod.snd + feedbackEntropyA psi -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1)) (fun p => p.2.2)

/-- PDF p.2: I(A;B)=H(A)+H(B)-H(AB). -/
def mutualAB (psi : EuclideanSpace ℂ (R × (A × B))) : ℝ :=
  feedbackEntropyA psi +
    subsystemEntropy (pureDensity psi) (fun p => p.2.2) (fun p => (p.1, p.2.1)) -
    subsystemEntropy (pureDensity psi) Prod.snd Prod.fst

/-- PDF p.2: I(R;B)=H(R)+H(B)-H(RB). -/
def mutualRB (psi : EuclideanSpace ℂ (R × (A × B))) : ℝ :=
  subsystemEntropy (pureDensity psi) Prod.fst Prod.snd +
    subsystemEntropy (pureDensity psi) (fun p => p.2.2) (fun p => (p.1, p.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2)) (fun p => p.2.1)

end Entropies

/-- PDF pp.2–4: a local operation from a retained isometric dilation. W is local
work, discarded only when evaluating the reduced output. V†V=1 is carried by codes.
Arbitrary work dimension permits typical-subspace failure flags on the full input. -/
def localOperation {X Y W : Type} [Fintype X] [Fintype W]
    (V : Matrix (Y × W) X ℂ) : Superop X Y :=
  fun rho y y' => ∑ w, (conjSuperop V rho) (y, w) (y', w)

/-- PDF p.2, (5): q transmitted qubits and k supplied Bell pairs; A stays at
Alice, B goes to Bob. Local work starts pure through the isometry description.
No entropy inequalities or desired performance properties are fields of this code. -/
structure FeedbackSimulationCode (S A B : Type) [Fintype S] [Fintype A] [Fintype B] (n : ℕ) where
  q : ℕ
  k : ℕ
  aliceWork : ℕ
  bobWork : ℕ
  enc : Matrix (((Copies A n × Qubits q) × Fin (aliceWork + 1)))
    (Copies S n × Qubits k) ℂ
  dec : Matrix (Copies B n × Fin (bobWork + 1)) (Qubits q × Qubits k) ℂ
  enc_isometry : encᴴ * enc = 1
  dec_isometry : decᴴ * dec = 1

/-- PDF p.2: append exactly k normalized, independently supplied Bell pairs. -/
def appendBell {X : Type} (k : ℕ) (rho : Matrix X X ℂ) :
    Matrix ((X × Qubits k) × Qubits k) ((X × Qubits k) × Qubits k) ℂ :=
  fun p p' => rho p.1.1 p'.1.1 *
    pureDensity (maxEntangled k) (p.1.2, p.2) (p'.1.2, p'.2)

/-- PDF p.2, (5): the actual simulated channel, before extending by any reference. -/
def FeedbackSimulationCode.channel {S A B : Type} [Fintype S] [Fintype A] [Fintype B]
    {n : ℕ} (P : FeedbackSimulationCode S A B n) :
    Superop (Copies S n) (Copies A n × Copies B n) :=
  fun rho => forwardApply (localOperation P.enc) (localOperation P.dec) (appendBell P.k rho)

/-- PDF p.2: U applied independently n times, grouping the A and B outputs. -/
def isometryPower {S A B : Type} (U : Matrix (A × B) S ℂ) (n : ℕ) :
    Matrix (Copies A n × Copies B n) (Copies S n) ℂ :=
  fun p s => ∏ i, U (p.1 i, p.2 i) (s i)

/-- PDF pp.1–2: FQRS simulation of the relative channel at input rho. For every
error and rate slack, a strictly positive marginal tolerance is chosen. All large
blocklengths have codes fixed before every reference/input test. Fin d ranges over
all finite reference dimensions. The promise constrains the input marginal only;
the error tests the entire correlated output. Rate zero allows sublinear resources. -/
def RelativeSimulationAchievable {S A B : Type} [Fintype S] [Fintype A] [Fintype B]
    (U : Matrix (A × B) S ℂ) (rho : Matrix S S ℂ) (Q E : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ eta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : FeedbackSimulationCode S A B n,
      P.q ≤ ⌊(n : ℝ) * (Q + delta)⌋₊ ∧
      P.k ≤ ⌊(n : ℝ) * (E + delta)⌋₊ ∧
      ∀ d : ℕ, 0 < d →
        ∀ sigma : Matrix (Fin d × Copies S n) (Fin d × Copies S n) ℂ,
          IsDensityMatrix sigma →
          traceNorm (traceLeft sigma - densityPower rho n) ≤ eta →
          traceNorm (idTensorSuperop P.channel sigma -
            idTensorSuperop (conjSuperop (isometryPower U n)) sigma) ≤ eps

/-- PDF pp.3–4, (12), Fig.4: Alice receives A^n and Bob B^n from the Source.
The q-qubit message is sent forward. Alice keeps l Bell halves; Bob outputs the
other l halves and S^n, the copy of the original source. Local work remains in
the dilations, so no impossible full-input compression isometry is assumed. -/
structure SlepianWolfCode (S A B : Type) [Fintype S] [Fintype A] [Fintype B] (n : ℕ) where
  q : ℕ
  l : ℕ
  aliceWork : ℕ
  bobWork : ℕ
  enc : Matrix ((Qubits l × Qubits q) × Fin (aliceWork + 1)) (Copies A n) ℂ
  dec : Matrix ((Qubits l × Copies S n) × Fin (bobWork + 1))
    (Qubits q × Copies B n) ℂ
  enc_isometry : encᴴ * enc = 1
  dec_isometry : decᴴ * dec = 1

/-- PDF pp.3–4: the normalized source purification in grouped copy registers. -/
def sourceDensity {R X : Type} (v : EuclideanSpace ℂ (R × X)) (n : ℕ) :
    Matrix (Copies R n × Copies X n) (Copies R n × Copies X n) ℂ :=
  pureDensity (WithLp.toLp 2 fun p => ∏ i, v (p.1 i, p.2 i))

/-- PDF p.3: apply only the specified source isometry; Alice and Bob cannot
encode or choose the S input. The reference is untouched. -/
def distributedSource {R S A B : Type} [Fintype S]
    (U : Matrix (A × B) S ℂ) (phi : EuclideanSpace ℂ (R × S)) (n : ℕ) :
    Matrix (Copies R n × (Copies A n × Copies B n))
      (Copies R n × (Copies A n × Copies B n)) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    ∏ i, feedbackOutputVector U phi (p.1 i, (p.2.1 i, p.2.2 i)))

/-- PDF pp.3–4: source/reference and generated Bell pairs are tested jointly.
The ideal S^n output is a copy at Bob, not a free matrix unrelated to phi. -/
def sourceTarget {R S : Type} (phi : EuclideanSpace ℂ (R × S)) (n l : ℕ) :
    Matrix (Copies R n × (Qubits l × (Qubits l × Copies S n)))
      (Copies R n × (Qubits l × (Qubits l × Copies S n))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    (∏ i, phi (p.1 i, p.2.2.2 i)) * maxEntangled l (p.2.1, p.2.2.1))

/-- PDF pp.3–4: full joint trace-norm error of the physical FQSW code. -/
def SlepianWolfCode.error {R S A B : Type} [Fintype R] [Fintype S] [Fintype A] [Fintype B]
    {n : ℕ} (P : SlepianWolfCode S A B n) (U : Matrix (A × B) S ℂ)
    (phi : EuclideanSpace ℂ (R × S)) : ℝ :=
  traceNorm (idTensorSuperop
    (forwardApply (localOperation P.enc) (localOperation P.dec)) (distributedSource U phi n) -
      sourceTarget phi n P.l)

/-- PDF pp.1,3–4: source transfer with Q forward qubits consumed and E ebits
generated per source copy. No initial Bell pairs or other nonlocal assistance.
The integer output is rounded down and clipped at zero only when E-delta<0. -/
def SourceTransferAchievable {R S A B : Type}
    [Fintype R] [Fintype S] [Fintype A] [Fintype B]
    (U : Matrix (A × B) S ℂ) (phi : EuclideanSpace ℂ (R × S)) (Q E : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : SlepianWolfCode S A B n,
      P.q ≤ ⌊(n : ℝ) * (Q + delta)⌋₊ ∧
      ⌊(n : ℝ) * (E - delta)⌋₊ ≤ P.l ∧ P.error U phi ≤ eps

/-- PDF p.3: the identity from the Source to Alice, with Bob's initial share
one-dimensional. S, A-hat, A-prime and B-hat are copies of the same basis type. -/
def sourceToAlice (S : Type) : Matrix (S × Unit) S ℂ :=
  fun p s => if p.1 = s then 1 else 0

/-- PDF pp.2–3: the promise supplied by a relative n-use identity channel.
It guarantees a joint reference test for every input with eta-close marginal. -/
def RelativeIdentityTest {S : Type} [Fintype S] (n : ℕ) (rho : Matrix S S ℂ)
    (F : Superop (Copies S n) (Copies S n)) (eta eps : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d →
    ∀ sigma : Matrix (Fin d × Copies S n) (Fin d × Copies S n) ℂ,
      IsDensityMatrix sigma → traceNorm (traceLeft sigma - densityPower rho n) ≤ eta →
      traceNorm (idTensorSuperop F sigma - sigma) ≤ eps

/-- PDF p.3, Fig.3: local encoding, n uses of the supplied relative identity,
and local decoding. The middle channel is supplied, not chosen by the code. -/
structure RoutingCode (S : Type) [Fintype S] (n : ℕ) where
  enc : Superop (Copies S n) (Copies S n)
  dec : Superop (Copies S n) (Copies S n)
  enc_channel : IsChannel enc
  dec_channel : IsChannel dec

/-- PDF p.3: direct source/identity concatenation, with the actual encoder
marginal tested against the supplied channel's promise. The quantified F represents
any physical implementation satisfying that promise, not unrestricted access.
The code uses exactly n supplied identity calls for n source copies; no nonlocal
ancillas or extra communication are available. delta records allowed rate slack. -/
def SourceRoutingAchievable {R S : Type} [Fintype R] [Fintype S]
    (phi : EuclideanSpace ℂ (R × S)) : Prop :=
  let rho := traceLeft (pureDensity phi)
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : RoutingCode S n,
      (n : ℝ) ≤ (n : ℝ) * (1 + delta) ∧
      ∀ eta > (0 : ℝ),
        traceNorm (traceLeft (idTensorSuperop P.enc (sourceDensity phi n)) -
          densityPower rho n) ≤ eta ∧
        ∀ F : Superop (Copies S n) (Copies S n), IsChannel F →
          RelativeIdentityTest n rho F eta eps →
          traceNorm (idTensorSuperop (P.dec ∘ F ∘ P.enc) (sourceDensity phi n) -
            sourceDensity phi n) ≤ eps

/-! Sanity examples for the new definitions; none assumes an entropy identity
or a resource inequality. These are definition checks, not the paper's proofs. -/

example {X : Type} (rho : Matrix X X ℂ) (x y : Copies X 0) :
    densityPower rho 0 x y = 1 := by
  simp [densityPower]

example {R S : Type} (phi : EuclideanSpace ℂ (R × S))
    (r : Copies R 0) (s : Copies S 0) :
    sourceDensity phi 0 (r, s) (r, s) = 1 := by
  simp [sourceDensity, pureDensity]

example {X : Type} [Fintype X] (rho : Matrix X X ℂ) :
    redistributionMarginal rho id (fun _ => ()) = rho := by
  ext a b
  unfold redistributionMarginal
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

example {X Y : Type} [Fintype X] (V : Matrix (Y × Unit) X ℂ)
    (rho : Matrix X X ℂ) (y y' : Y) :
    localOperation V rho y y' = conjSuperop V rho (y, ()) (y', ()) := by
  simp [localOperation]

example (s t : Bool) : sourceToAlice Bool (s, ()) t = if s = t then 1 else 0 := by
  by_cases h : s = t <;> simp [sourceToAlice, h]

example {X : Type} (rho : Matrix X X ℂ) (x y : X) :
    appendBell 0 rho ((x, fun _ => false), fun _ => false)
      ((y, fun _ => false), fun _ => false) = rho x y := by
  simp [appendBell, pureDensity, maxEntangled]

example {R S : Type} [Fintype S] [DecidableEq S] (phi : EuclideanSpace ℂ (R × S)) :
    feedbackOutputVector (sourceToAlice S) phi =
      WithLp.toLp 2 (fun p : R × (S × Unit) => phi (p.1, p.2.1)) := by
  ext p
  simp [feedbackOutputVector, sourceToAlice]

example {S : Type} [Fintype S] (n : ℕ) (rho : Matrix S S ℂ) (eta eps : ℝ)
    (heps : 0 ≤ eps) :
    RelativeIdentityTest n rho (fun X => X) eta eps := by
  intro d hd sigma hs hm
  have h : idTensorSuperop (fun X : Matrix (Copies S n) (Copies S n) ℂ => X) sigma = sigma := by
    ext p q
    rfl
  rw [h, sub_self]
  simpa [traceNorm, cfc_zero] using heps

end QAlgorithms.Papers.Independent.Intakethird100.P64


