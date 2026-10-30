-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29
-- name    : QAlgorithms_Papers_Independent_Extend50_P29
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:07:50.811382+00:00
-- url     : https://prove2.me/theorems/17ef9f89-392e-4812-a71a-71eaf8abdcfe
-- title:
--   Definitions for Error Correction of Quantum Reference Frame Information
-- statement:
--   The objects the formalized statements of *Error Correction of Quantum Reference Frame Information* (arXiv:1709.04471) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RegisterConfig`: PDF pp.2--3: basis configurations of a finite collection of local registers.
--   - `Keep`: PDF pp.2--3: the registers retained in a known-position erasure.
--   - `dependentRegisterTrace`: PDF pp.2--3: partial trace, written on matrix units. The outside indices are equal and summed once; all off-diagonal entries of the retained system survive.
--   - `localTensorMatrix`: PDF p.3, Eq.(4): tensor product of local operators, on the entire tensor space.
--   - `Decoders`: PDF pp.2--3: fixed decoding channels, one for each known erased site.
--   - `SingleCorrects`: PDF pp.2--3: every density matrix is recovered; the decoders precede the input.
--   - `CorrectsErasedSubsets`: PDF pp.3--4: exact recovery after every erased subset of cardinality at most k. The channel D can depend on the subset, but not on the input matrix.
--   - `rotatedEncoding`: PDF pp.2--3, Eqs.(1)--(2): encoding expressed in the rotated reference frame.
--   - `ErasureCovariant`: PDF p.3, Eq.(2): covariance as equality of the rotated and original encoding.
--   - `ReferenceSuccess`: PDF p.2, Eq.(1): recovery by the same decoder for every unknown group element.
--   - `twirledEncoding`: PDF p.3: normalized Haar average of the rotated encoding, not of the decoder.
--   - `copyPermutation`: PDF pp.4--5: permutation of the A-labelled copies, with the inverse in coordinate position, as in the source's U(g)|phi_a> formula.
--   - `tensorEncoding`: PDF p.4: tensor copies of E0, regrouped into n physical shares. Matrix-unit expansion defines the channel also on entangled logical inputs.
--   - `PerfectTensor`: PDF p.5: normalized perfect tensors have every dependentRegisterTrace on at most half the equal-dimensional legs equal to I/d^|R|. Flattenings are scaled isometries.
--   - `invariantOrbitMap`: PDF p.13: explicit orbit map M with the last coordinate equal to g. This entry formula is the source's d^(-1/2) sum over g, with disjoint orbits.
--   - `orbitProjector`: PDF p.13, Eq.(C1): unnormalized invariant projector MM†.
--   - `RegularInvariant`: PDF p.13: invariant vectors under the diagonal regular action.
--   - `positiveMatrixRoot`: PDF pp.9--10: positive square root in the recovered-channel formula.
--   - `reshapedEncoder`: PDF pp.8--9: sqrt(d)<phi+|Psi>, with phi+ UNNORMALIZED.
--   - `polarEncoder`: PDF p.9: T=E(E†E)^(-1/2), constructed from Psi.
--   - `pairMarginal`: PDF p.9: Psi_01. Here there are r+2 physical outputs, hence r+3 total registers. The pair 0,1 is retained and the remaining r+1 registers are traced.
--   - `pairMixed`: PDF p.9: tau_01=I/d², with both registers of dimension |G|.
--   - `recoveredChannel`: PDF pp.9--10, Step 1: the source's Schmidt-decoder recovered channel, written as its derived two-register formula. The final transpose and the input transpose are both essential. This is recovery for erased physical mode 1, not optimization over decoders or over erased positions.
--   - `worstRootFidelity`: PDF pp.9--10: minimum ROOT fidelity for the prescribed decoder and a fixed erasure. Joint concavity permits the minimum over normalized pure inputs. The nonempty set of values lies in [0,1] on normalized full-rank source data.
--   - `Sample`: PDF p.13: Euclidean coordinate space used for the source's Haar sample in H_G^tensor(n). Its indexing is reindexed below, rather than changing its law.
--   - `invariantSampleLaw`: PDF p.13: actual Haar unit-vector law, from the frozen accepted library.
--   - `randomInvariant`: PDF p.13: reindex the Haar vector into the tensor basis and apply M. This samples the invariant subspace, not the full output Hilbert space.
--   - `testTail`: PDF p.12: probability of a fixed density-matrix test, with the absolute value (complex norm) and inclusive threshold printed in the source.
--   - `worstTestTail`: PDF p.12: worst fixed-test tail. The density test is chosen before the Haar sample. This supremum of probabilities is bounded and has a nonempty domain; it is not the probability of a supremum chosen after sampling.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, https://arxiv.org/abs/1709.04471v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

/-!
Statements from Hayden--Nezami--Popescu--Salton, arXiv:1709.04471v1.
Paper-specific interfaces below are local; equivalent accepted primitives are imported. Computational bases index finite
complex Hilbert spaces, including nonuniform local dimensions. Appendix A and the
continuous orthogonal-reference construction are deferred in HARD.md.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)
open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)
open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF pp.2--3: basis configurations of a finite collection of local registers. -/
abbrev RegisterConfig {S : Type} (H : S → Type) := (i : S) → H i

/-- PDF pp.2--3: the registers retained in a known-position erasure. -/
abbrev Keep {S : Type} (H : S → Type) (R : Finset S) := (i : {i // i ∈ R}) → H i.val

/-- PDF pp.2--3: partial trace, written on matrix units. The outside indices
are equal and summed once; all off-diagonal entries of the retained system survive. -/
def dependentRegisterTrace {S : Type} [Fintype S] {H : S → Type} [∀ i, Fintype (H i)]
    (R : Finset S) (X : Matrix (RegisterConfig H) (RegisterConfig H) ℂ) : Matrix (Keep H R) (Keep H R) ℂ :=
  fun a b => ∑ x : RegisterConfig H, ∑ y : RegisterConfig H,
    if (∀ i : {i // i ∈ R}, x i.val = a i) ∧
       (∀ i : {i // i ∈ R}, y i.val = b i) ∧
       (∀ i, i ∉ R → x i = y i) then X x y else 0

/-- PDF p.3, Eq.(4): tensor product of local operators, on the entire tensor space. -/
def localTensorMatrix {S : Type} [Fintype S] {H : S → Type}
    (A : (i : S) → Matrix (H i) (H i) ℂ) : Matrix (RegisterConfig H) (RegisterConfig H) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

/-- PDF pp.2--3: fixed decoding channels, one for each known erased site. -/
abbrev Decoders {S I : Type} [Fintype S] (H : S → Type) :=
  (j : S) → Superop (Keep H (Finset.univ.erase j)) I

/-- PDF pp.2--3: every density matrix is recovered; the decoders precede the input. -/
def SingleCorrects {S I : Type} [Fintype S] [Fintype I] {H : S → Type}
    [∀ i, Fintype (H i)] (E : Superop I (RegisterConfig H)) (D : Decoders (I := I) H) : Prop :=
  ∀ j ρ, IsDensityMatrix ρ → D j (dependentRegisterTrace (Finset.univ.erase j) (E ρ)) = ρ

/-- PDF pp.3--4: exact recovery after every erased subset of cardinality at most k.
The channel D can depend on the subset, but not on the input matrix. -/
def CorrectsErasedSubsets {S I : Type} [Fintype S] [Fintype I] {H : S → Type}
    [∀ i, Fintype (H i)] (k : ℕ) (E : Superop I (RegisterConfig H)) : Prop :=
  ∀ J : Finset S, J.card ≤ k →
    ∃ D : Superop (Keep H (Finset.univ \ J)) I,
      IsChannel D ∧ ∀ ρ, IsDensityMatrix ρ → D (dependentRegisterTrace (Finset.univ \ J) (E ρ)) = ρ

/-- PDF pp.2--3, Eqs.(1)--(2): encoding expressed in the rotated reference frame. -/
def rotatedEncoding {G S I : Type} [Fintype S] [Fintype I] {H : S → Type}
    [∀ i, Fintype (H i)]
    (Ui : G → Matrix I I ℂ) (Uo : G → (i : S) → Matrix (H i) (H i) ℂ)
    (E : Superop I (RegisterConfig H)) (g : G) : Superop I (RegisterConfig H) :=
  fun ρ => conjSuperop (localTensorMatrix (Uo g)) (E (conjSuperop (Ui g)ᴴ ρ))

/-- PDF p.3, Eq.(2): covariance as equality of the rotated and original encoding. -/
def ErasureCovariant {G S I : Type} [Fintype S] [Fintype I] {H : S → Type}
    [∀ i, Fintype (H i)]
    (Ui : G → Matrix I I ℂ) (Uo : G → (i : S) → Matrix (H i) (H i) ℂ)
    (E : Superop I (RegisterConfig H)) : Prop :=
  ∀ g ρ, IsDensityMatrix ρ → rotatedEncoding Ui Uo E g ρ = E ρ

/-- PDF p.2, Eq.(1): recovery by the same decoder for every unknown group element. -/
def ReferenceSuccess {G S I : Type} [Fintype S] [Fintype I] {H : S → Type}
    [∀ i, Fintype (H i)]
    (Ui : G → Matrix I I ℂ) (Uo : G → (i : S) → Matrix (H i) (H i) ℂ)
    (E : Superop I (RegisterConfig H)) (D : Decoders (I := I) H) : Prop :=
  ∀ g, SingleCorrects (rotatedEncoding Ui Uo E g) D

/-- PDF p.3: normalized Haar average of the rotated encoding, not of the decoder. -/
def twirledEncoding {G S I : Type} [MeasurableSpace G] [Fintype S] [Fintype I]
    {H : S → Type} [∀ i, Fintype (H i)] (μ : Measure G)
    (Ui : G → Matrix I I ℂ) (Uo : G → (i : S) → Matrix (H i) (H i) ℂ)
    (E : Superop I (RegisterConfig H)) : Superop I (RegisterConfig H) :=
  fun X => ∫ g, rotatedEncoding Ui Uo E g X ∂μ

/-- PDF pp.4--5: permutation of the A-labelled copies, with the inverse in
coordinate position, as in the source's U(g)|phi_a> formula. -/
def copyPermutation {G A I : Type} [Group G] [MulAction G A]
    (g : G) : Matrix (A → I) (A → I) ℂ :=
  fun x y => if x = (fun a => y (g⁻¹ • a)) then 1 else 0

/-- PDF p.4: tensor copies of E0, regrouped into n physical shares.
Matrix-unit expansion defines the channel also on entangled logical inputs. -/
def tensorEncoding {A I H : Type} [Fintype A] [Fintype I] {n : ℕ}
    (E0 : Superop I (Fin n → H)) : Superop (A → I) (Fin n → A → H) :=
  fun X y z => ∑ x : A → I, ∑ x' : A → I,
    X x x' * ∏ a, E0 (Matrix.single (x a) (x' a) 1)
      (fun i => y i a) (fun i => z i a)

/-- PDF p.5: normalized perfect tensors have every dependentRegisterTrace on at most half
the equal-dimensional legs equal to I/d^|R|. Flattenings are scaled isometries. -/
def PerfectTensor {m d : ℕ} (ψ : EuclideanSpace ℂ (Fin m → Fin d)) : Prop :=
  IsState ψ ∧ ∀ R : Finset (Fin m), 2 * R.card ≤ m →
    dependentRegisterTrace (H := fun _ : Fin m => Fin d) R (pureDensity ψ) =
      (((d : ℂ) ^ R.card)⁻¹) • (1 : Matrix (Keep (fun _ : Fin m => Fin d) R)
        (Keep (fun _ : Fin m => Fin d) R) ℂ)

/-- PDF p.13: explicit orbit map M with the last coordinate equal to g.
This entry formula is the source's d^(-1/2) sum over g, with disjoint orbits. -/
def invariantOrbitMap (G : Type) [Group G] [Fintype G] (n : ℕ) :
    Matrix (Fin (n + 1) → G) (Fin n → G) ℂ :=
  fun z h => if ∀ i : Fin n, z i.castSucc = z (Fin.last n) * h i
    then ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.13, Eq.(C1): unnormalized invariant projector MM†. -/
def orbitProjector (G : Type) [Group G] [Fintype G] (n : ℕ) :
    Matrix (Fin (n + 1) → G) (Fin (n + 1) → G) ℂ :=
  invariantOrbitMap G n * (invariantOrbitMap G n)ᴴ

/-- PDF p.13: invariant vectors under the diagonal regular action. -/
def RegularInvariant {G : Type} [Group G] [Fintype G] {n : ℕ}
    (ψ : EuclideanSpace ℂ (Fin n → G)) : Prop :=
  ∀ g, act (localTensorMatrix (fun _ : Fin n => groupLeftRegular g)) ψ = ψ

/-- PDF pp.9--10: positive square root in the recovered-channel formula. -/
def positiveMatrixRoot {I : Type} [Fintype I] (X : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => Real.sqrt x) X

/-- PDF pp.8--9: sqrt(d)<phi+|Psi>, with phi+ UNNORMALIZED. -/
def reshapedEncoder {G : Type} [Fintype G] {n : ℕ}
    (ψ : EuclideanSpace ℂ (Fin (n + 1) → G)) : Matrix (Fin n → G) G ℂ :=
  fun z x => (Real.sqrt (Fintype.card G : ℝ) : ℂ) * ψ (Fin.cons x z)

/-- PDF p.9: T=E(E†E)^(-1/2), constructed from Psi. -/
def polarEncoder {G : Type} [Fintype G] {n : ℕ}
    (ψ : EuclideanSpace ℂ (Fin (n + 1) → G)) : Matrix (Fin n → G) G ℂ :=
  let E := reshapedEncoder ψ
  E * inverseSqrt (Eᴴ * E)

/-- PDF p.9: Psi_01. Here there are r+2 physical outputs, hence r+3 total
registers. The pair 0,1 is retained and the remaining r+1 registers are traced. -/
def pairMarginal {G : Type} [Fintype G] {r : ℕ}
    (ψ : EuclideanSpace ℂ (Fin (r + 3) → G)) : Matrix (G × G) (G × G) ℂ :=
  fun a b => ∑ z : Fin (r + 1) → G,
    ψ (Fin.cons a.1 (Fin.cons a.2 z)) *
      conj (ψ (Fin.cons b.1 (Fin.cons b.2 z)))

/-- PDF p.9: tau_01=I/d², with both registers of dimension |G|. -/
def pairMixed (G : Type) [Fintype G] : Matrix (G × G) (G × G) ℂ :=
  (((Fintype.card G : ℂ) ^ 2)⁻¹) • 1

/-- PDF pp.9--10, Step 1: the source's Schmidt-decoder recovered channel,
written as its derived two-register formula. The final transpose and the input
transpose are both essential. This is recovery for erased physical mode 1,
not optimization over decoders or over erased positions. -/
def recoveredChannel {G : Type} [Fintype G]
    (A : Matrix (G × G) (G × G) ℂ) : Superop G G :=
  fun X =>
    let B := inverseSqrt (traceRight A)
    (traceRight (positiveMatrixRoot A * Matrix.kronecker (B * X.transpose * B) (1 : Matrix G G ℂ) *
      positiveMatrixRoot A)).transpose

/-- PDF pp.9--10: minimum ROOT fidelity for the prescribed decoder and a
fixed erasure. Joint concavity permits the minimum over normalized pure inputs.
The nonempty set of values lies in [0,1] on normalized full-rank source data. -/
def worstRootFidelity {G : Type} [Fintype G]
    (A : Matrix (G × G) (G × G) ℂ) : ℝ :=
  sInf {f : ℝ | ∃ κ : EuclideanSpace ℂ G, IsState κ ∧
    f = Real.sqrt (effectProb (pureDensity κ) (recoveredChannel A (pureDensity κ)))}

/-- PDF p.13: Euclidean coordinate space used for the source's Haar sample
in H_G^tensor(n). Its indexing is reindexed below, rather than changing its law. -/
abbrev Sample (G : Type) [Fintype G] (n : ℕ) :=
  EuclideanSpace ℂ (Fin (Fintype.card (Fin n → G)))

/-- PDF p.13: actual Haar unit-vector law, from the frozen accepted library. -/
def invariantSampleLaw (G : Type) [Group G] [Fintype G] (n : ℕ) : Measure (Sample G n) :=
  QuditFidelity.haarPureStateLaw (Fintype.card (Fin n → G)) Fintype.card_pos

/-- PDF p.13: reindex the Haar vector into the tensor basis and apply M.
This samples the invariant subspace, not the full output Hilbert space. -/
def randomInvariant {G : Type} [Group G] [Fintype G] (n : ℕ)
    (φ : Sample G n) : EuclideanSpace ℂ (Fin (n + 1) → G) :=
  rectAct (invariantOrbitMap G n)
    (WithLp.toLp 2 (fun h : Fin n → G => φ (Fintype.equivFin (Fin n → G) h)))

/-- PDF p.12: probability of a fixed density-matrix test, with the absolute
value (complex norm) and inclusive threshold printed in the source. -/
def testTail {G : Type} [Group G] [Fintype G] (r : ℕ) (δ : ℝ)
    (σ : Matrix (G × G) (G × G) ℂ) : ℝ :=
  ((invariantSampleLaw G (r + 2)) {φ | δ / (Fintype.card G : ℝ) ^ 2 ≤
    ‖(σ * (pairMarginal (randomInvariant (r + 2) φ) - pairMixed G)).trace‖}).toReal

/-- PDF p.12: worst fixed-test tail. The density test is chosen before the
Haar sample. This supremum of probabilities is bounded and has a nonempty domain;
it is not the probability of a supremum chosen after sampling. -/
def worstTestTail (G : Type) [Group G] [Fintype G] (r : ℕ) (δ : ℝ) : ℝ :=
  sSup {p : ℝ | ∃ σ : Matrix (G × G) (G × G) ℂ, IsDensityMatrix σ ∧ p = testTail r δ σ}

/-- Small sanity check: partial trace sends zero to zero. -/
example {S : Type} [Fintype S] {H : S → Type} [∀ i, Fintype (H i)] (R : Finset S) :
    dependentRegisterTrace (H := H) R 0 = 0 := by
  ext a b
  simp [dependentRegisterTrace]

example (H : Fin 0 → Type) (A : (i : Fin 0) → Matrix (H i) (H i) ℂ)
    (x y : RegisterConfig H) : localTensorMatrix A x y = 1 := by
  simp [localTensorMatrix]

example {I : Type} [Fintype I] (T : Matrix I I ℂ) : evolution T 0 = 1 := by
  simp [evolution, NormedSpace.exp_zero]

example {G : Type} [Group G] (g y : G) : groupLeftRegular g (g * y) y = 1 := by
  simp [groupLeftRegular]

example (z : Fin 1 → Unit) (h : Fin 0 → Unit) : invariantOrbitMap Unit 0 z h = 1 := by
  simp [invariantOrbitMap]

example {G : Type} [Fintype G] {n : ℕ} (ψ : EuclideanSpace ℂ (Fin (n + 1) → G))
    (z : Fin n → G) (x : G) :
    reshapedEncoder ψ z x = (Real.sqrt (Fintype.card G : ℝ) : ℂ) * ψ (Fin.cons x z) := rfl

example {G : Type} [Fintype G] (A : Matrix (G × G) (G × G) ℂ) (X : Matrix G G ℂ) :
    recoveredChannel A X =
      (traceRight (positiveMatrixRoot A * Matrix.kronecker
        (inverseSqrt (traceRight A) * X.transpose * inverseSqrt (traceRight A)) 1 *
          positiveMatrixRoot A)).transpose := rfl

example (G : Type) [Group G] [Fintype G] (n : ℕ) : invariantSampleLaw G n Set.univ = 1 :=
  QuditFidelity.haarPureStateLaw_univ _ _

end QAlgorithms.Papers.Independent.Extend50.P29


