-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31
-- name    : QAlgorithms_Papers_Independent_Intake100_P31
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T17:40:41.41598+00:00
-- url     : https://prove2.me/theorems/7f1e3ef4-5cc1-4806-b659-ea34dc13f5ea
-- title:
--   Definitions for Dual universality of hash functions and its applications to quantum cryptography
-- statement:
--   The objects the formalized statements of *Dual universality of hash functions and its applications to quantum cryptography* (arXiv:1101.0064) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BinaryBlock`: PDF p.3: binary block words, with coordinates in the field F_2.
--   - `BinaryLinearCode`: PDF p.3: a binary linear code is an actual vector subspace.
--   - `avg`: PDF p.3: uniform indexed average; repeated values retain multiplicity.
--   - `seedProbability`: PDF p.3: probability of an event on the uniformly sampled seed.
--   - `minDim`: PDF p.4: actual attained minimum dimension, with a nonempty seed type.
--   - `maxDim`: PDF p.4: actual attained maximum dimension.
--   - `UniversalAt`: PDF p.4 (6),(7): inclusion bound at the specified dimension parameter.
--   - `HashUniversal`: PDF p.3 (1): declared codomain size is retained, without a rank assumption.
--   - `optimalParameter`: PDF p.4: the optimal parameter for minimum dimension t.
--   - `dualParameter`: PDF p.4 Theorem 1: the transformed universality parameter.
--   - `SubUniversalAt`: PDF p.6 Definition 10: subcodes; the ambient dimension is dim B.
--   - `ExtUniversalAt`: PDF p.6 Definition 9: extended codes, tested outside the fixed inner code.
--   - `PairUniversalAt`: PDF p.7 Definition 12: both codes vary on the same seed.
--   - `wt`: PDF p.8: Hamming weight.
--   - `codeWeightCount`: PDF p.8 (31): the number A_k of codewords, not its normalized distribution.
--   - `weightParameter`: PDF p.8 (31): epsilon_k(C).
--   - `spectrumParameter`: PDF p.8 (32): max over 1 through n; the unused n=0 convention is zero.
--   - `pairSpectrumParameter`: PDF p.9: the maximum encloses the entire difference.
--   - `permLinear`: PDF p.8 (30): coordinate permutation x maps to x composed with sigma.
--   - `permCode`: PDF p.8 (30): one code for each permutation, retaining all repetitions.
--   - `ErrorLaw`: PDF p.9: a normalized additive error law, independent of word and seed.
--   - `mlDecode`: PDF pp.9--11: ML word decoder, with a fixed deterministic choice among ties. The maximization is over the noise coset determined by the syndrome; its fixed choice depends only on that coset. Subtracting this error representative gives an ML codeword, not a maximum-likelihood quotient-message decoder.
--   - `cosetWordError`: PDF p.11: uniform coset message, uniform word within that coset; ML word recovery in large followed by projection modulo small. Averaging over all words of large counts each quotient coset equally.
--   - `hammingBad`: PDF p.9 (35), corrected translation: any tied-or-better nonzero competitor. This conservative indicator includes all ties and dominates any Hamming decoder.
--   - `bsc`: PDF p.10: the iid BSC probability including endpoints p=0 and p=1.
--   - `weightMass`: PDF p.9: the actual weight marginal of the additive law.
--   - `noiseBound`: PDF p.10 (37),(38): the full weight sum, including the harmless k=0 term.
--   - `wordNoiseBound`: PDF p.10 (38): word-error bound sums k=1,...,n, excluding zero noise.
--   - `E0`: PDF p.10 (40): Gallager E0 in bits.
--   - `gallagerExponent`: PDF p.10 (42): supremum on the compact interval; continuous for p in [0,1], so nonempty, bounded and attained in every theorem below.
--   - `gallagerBound`: PDF p.10 (39): eps^s remains inside the minimization.
--   - `bernoulliDivergenceBits`: PDF p.10: bernoulliDivergenceBits in bits, with infinite off-support values.
--   - `typeExponent`: PDF p.10 (43),(44): complete-lattice infimum, including deterministic channels.
--   - `expFactor`: PDF p.10 (43): 2^(-n A), with 2^(-infinity)=0.
--   - `tiltedBernoulli`: PDF p.17: support-preserving tiltedBernoulli Bernoulli law, including theta=0.
--   - `tiltedExponent`: PDF p.17 (73): the tiltedBernoulli variational expression in the extended reals.
--   - `entropyEnvelope`: PDF p.13 (53): valid also when a union bound exceeds one.
--   - `seededToeplitz`: PDF p.3 Example 2: a Toeplitz seed. One unused uniform seed bit gives identical multiplicities for the usual a+b-1 diagonal-bit construction.
--   - `modifiedM`: PDF p.6: M=(T,I_b).
--   - `modifiedN`: PDF p.6: N=(I_a,T^transpose), over the same seed.
--   - `Env`: PDF p.12 (50): environment label (phase x, bit z).
--   - `phaseBitPauli`: PDF p.12 (50): Z^x X^z, in the computational basis labelled by F_2^n.
--   - `iidPauli`: PDF p.13, iid assumption: the phase and bit errors are independent per qubit.
--   - `pauliDilation`: PDF pp.12--13: actual Pauli Stinespring dilation, with the entire error label in Eve's register. For a normalized law this is an isometry.
--   - `pauliComplement`: PDF p.13: complementary output obtained by tracing out Bob, with no postprocessing, dephasing, or deletion of environment coherences.
--   - `cosetDensity`: PDF p.13: the actual uniform MIXTURE on a coset, not the coherent CSS state.
--   - `coherentCoset`: PDF p.13: normalized virtual coherent CSS coset vector, explicitly separate from the actual mixture sent by Alice.
--   - `cosetEve`: PDF p.13: conditional Eve density for the actual coset-mixture encoder.
--   - `meanEve`: PDF p.13: Eve marginal for the uniform large-code input.
--   - `traceLeak`: PDF pp.13--14: full trace norm of the actual cq state minus the independent uniform-key state. Each quotient coset has exactly card(small) representatives, so averaging over a in large is exactly averaging uniform quotient messages.
--   - `holevoLeak`: PDF pp.13--14: Holevo information in bits of the same physical cq ensemble.
--   - `phaseMass`: PDF p.12: the phase marginal of the actual joint Pauli law.
--   - `phaseError`: PDF p.13 (54)--(56): actual dual quotient decoding error. No scalar success probability is supplied by the caller. Logical success is modulo large-perp.
--   - `residualPhase`: PDF p.13: virtual phase correction subtracts the selected syndrome noise representative. The remaining phase label is this decoded dual codeword; phase correction succeeds exactly when it lies in large-perp.
--   - `phaseRecovered`: PDF p.13: physical phase-recovered Pauli map on the CSS code space before logical decoding; bit errors are left in place. The phase correction depends only on the measured small-code syndrome, by the noise-coset tie convention.
--   - `messageLength`: PDF p.13: message length of a specific seed's quotient.
--   - `iidPhaseBound`: PDF p.14 (59)--(61): common upper bound on average residual phase error.
--   - `logRate`: PDF p.14: exponential rate in bits, with perfect secrecy assigned +infinity. Only positive block lengths are passed by the asymptotic statement.
--   - `phaseTraceBound`: PDF p.14 (60): the phase-error trace bound.
--   - `deltaTraceBound`: PDF p.14 (64): the delta-biased trace bound used in the comparison.
--   - `classicalCosetEve`: PDF p.15, separate classical broadcast model: Bob gets the noiseless word; Eve gets BSC(p). This is Eve's conditional distribution for a uniform coset input.
--   - `classicalLeak`: PDF p.15: mutual information of the actual classical quotient-message/Eve law, averaged over uniform messages. Eve's marginal is uniform on F_2^n; zero terms contribute zero, including the deterministic BSC endpoints.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, https://arxiv.org/abs/1101.0064v4

import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
Statements from Tsurumaru--Hayashi, arXiv:1101.0064v4.
All local definitions belong to this paper. Logarithms and entropies are in bits.
Deferred claims and printed corrections are inventoried in the unit artifacts.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate
open QAlgorithms

/-- PDF p.3: binary block words, with coordinates in the field F_2. -/
abbrev BinaryBlock (n : ℕ) := Fin n → ZMod 2

/-- PDF p.3: a binary linear code is an actual vector subspace. -/
abbrev BinaryLinearCode (n : ℕ) := Submodule (ZMod 2) (BinaryBlock n)

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.3: uniform indexed average; repeated values retain multiplicity. -/
def avg {I : Type*} [Fintype I] (f : I → ℝ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ∑ r, f r

/-- PDF p.3: probability of an event on the uniformly sampled seed. -/
def seedProbability {I : Type*} [Fintype I] (P : I → Prop) : ℝ := by
  classical
  exact avg (fun r => if P r then 1 else 0)

/-- PDF p.4: actual attained minimum dimension, with a nonempty seed type. -/
def minDim {n : ℕ} {I : Type*} [Fintype I] [Nonempty I] (C : I → BinaryLinearCode n) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun r => Module.finrank (ZMod 2) (C r))

/-- PDF p.4: actual attained maximum dimension. -/
def maxDim {n : ℕ} {I : Type*} [Fintype I] [Nonempty I] (C : I → BinaryLinearCode n) : ℕ :=
  Finset.univ.sup' Finset.univ_nonempty (fun r => Module.finrank (ZMod 2) (C r))

/-- PDF p.4 (6),(7): inclusion bound at the specified dimension parameter. -/
def UniversalAt {n : ℕ} {I : Type*} [Fintype I]
    (C : I → BinaryLinearCode n) (t : ℕ) (eps : ℝ) : Prop :=
  ∀ x : BinaryBlock n, x ≠ 0 → seedProbability (fun r => x ∈ C r) ≤
    eps * (2 : ℝ) ^ ((t : ℝ) - n)

/-- PDF p.3 (1): declared codomain size is retained, without a rank assumption. -/
def HashUniversal {n m : ℕ} {I : Type*} [Fintype I]
    (f : I → BinaryBlock n →ₗ[ZMod 2] BinaryBlock m) (eps : ℝ) : Prop :=
  ∀ a b, a ≠ b → seedProbability (fun r => f r a = f r b) ≤ eps / (2 : ℝ) ^ m

/-- PDF p.4: the optimal parameter for minimum dimension t. -/
def optimalParameter (n t : ℕ) : ℝ :=
  ((2 : ℝ) ^ n - (2 : ℝ) ^ ((n : ℝ) - t)) / ((2 : ℝ) ^ n - 1)

/-- PDF p.4 Theorem 1: the transformed universality parameter. -/
def dualParameter (n t : ℕ) (eps : ℝ) : ℝ :=
  2 * (1 - (2 : ℝ) ^ ((t : ℝ) - n) * eps) + (eps - 1) * (2 : ℝ) ^ t

/-- PDF p.6 Definition 10: subcodes; the ambient dimension is dim B. -/
def SubUniversalAt {n : ℕ} {I : Type*} [Fintype I]
    (B : BinaryLinearCode n) (C : I → BinaryLinearCode n) (t : ℕ) (eps : ℝ) : Prop :=
  (∀ r, C r ≤ B) ∧ ∀ x ∈ B, x ≠ 0 → seedProbability (fun r => x ∈ C r) ≤
    eps * (2 : ℝ) ^ ((t : ℝ) - Module.finrank (ZMod 2) B)

/-- PDF p.6 Definition 9: extended codes, tested outside the fixed inner code. -/
def ExtUniversalAt {n : ℕ} {I : Type*} [Fintype I]
    (B : BinaryLinearCode n) (C : I → BinaryLinearCode n) (t : ℕ) (eps : ℝ) : Prop :=
  (∀ r, B ≤ C r) ∧ ∀ x, x ∉ B → seedProbability (fun r => x ∈ C r) ≤
    eps * (2 : ℝ) ^ ((t : ℝ) - n)

/-- PDF p.7 Definition 12: both codes vary on the same seed. -/
def PairUniversalAt {n : ℕ} {I : Type*} [Fintype I]
    (small large : I → BinaryLinearCode n) (t : ℕ) (eps : ℝ) : Prop :=
  (∀ r, small r ≤ large r) ∧ ∀ x : BinaryBlock n, x ≠ 0 →
    seedProbability (fun r => x ∈ large r ∧ x ∉ small r) ≤
      eps * (2 : ℝ) ^ ((t : ℝ) - n)

/-- PDF p.8: Hamming weight. -/
def wt {n : ℕ} (x : BinaryBlock n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- PDF p.8 (31): the number A_k of codewords, not its normalized distribution. -/
def codeWeightCount {n : ℕ} (C : BinaryLinearCode n) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : BinaryBlock n => x ∈ C ∧ wt x = k)).card

/-- PDF p.8 (31): epsilon_k(C). -/
def weightParameter {n : ℕ} (C : BinaryLinearCode n) (k : ℕ) : ℝ :=
  (codeWeightCount C k : ℝ) / (Nat.choose n k : ℝ) *
    (2 : ℝ) ^ ((n : ℝ) - Module.finrank (ZMod 2) C)

/-- PDF p.8 (32): max over 1 through n; the unused n=0 convention is zero. -/
def spectrumParameter {n : ℕ} (C : BinaryLinearCode n) : ℝ :=
  if h : n = 0 then 0 else
    (Finset.range n).sup' (Finset.nonempty_range_iff.mpr h)
      (fun k => weightParameter C (k + 1))

/-- PDF p.9: the maximum encloses the entire difference. -/
def pairSpectrumParameter {n : ℕ} (small large : BinaryLinearCode n) : ℝ :=
  if h : n = 0 then 0 else
    (Finset.range n).sup' (Finset.nonempty_range_iff.mpr h)
      (fun k => weightParameter large (k + 1) - weightParameter small (k + 1) *
        (Fintype.card small : ℝ) / (Fintype.card large : ℝ))

/-- PDF p.8 (30): coordinate permutation x maps to x composed with sigma. -/
def permLinear {n : ℕ} (s : Equiv.Perm (Fin n)) : BinaryBlock n →ₗ[ZMod 2] BinaryBlock n where
  toFun x := fun i => x (s i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- PDF p.8 (30): one code for each permutation, retaining all repetitions. -/
def permCode {n : ℕ} (C : BinaryLinearCode n) (s : Equiv.Perm (Fin n)) : BinaryLinearCode n :=
  C.comap (permLinear s.symm)

/-- PDF p.9: a normalized additive error law, independent of word and seed. -/
structure ErrorLaw (n : ℕ) where
  mass : BinaryBlock n → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

/-- PDF pp.9--11: ML word decoder, with a fixed deterministic choice among ties.
The maximization is over the noise coset determined by the syndrome; its fixed
choice depends only on that coset. Subtracting this error representative gives
an ML codeword, not a maximum-likelihood quotient-message decoder. -/
def mlDecode {n : ℕ} (C : BinaryLinearCode n) (P : BinaryBlock n → ℝ) (y : BinaryBlock n) : C := by
  classical
  let S : Finset (BinaryBlock n) := Finset.univ.filter (fun e => y - e ∈ C)
  have hS : S.Nonempty := ⟨y, by simp [S]⟩
  let h := Finset.exists_max_image S P hS
  exact ⟨y - Classical.choose h, (Finset.mem_filter.mp (Classical.choose_spec h).1).2⟩

/-- PDF p.11: uniform coset message, uniform word within that coset; ML word
recovery in large followed by projection modulo small. Averaging over all words
of large counts each quotient coset equally. -/
def cosetWordError {n : ℕ} (small large : BinaryLinearCode n) (P : BinaryBlock n → ℝ) : ℝ := by
  classical
  exact (Fintype.card large : ℝ)⁻¹ * ∑ a : large, ∑ x : BinaryBlock n,
    P x * (if (mlDecode large P (a.val + x)).val - a.val ∈ small then 0 else 1)

/-- PDF p.9 (35), corrected translation: any tied-or-better nonzero competitor.
This conservative indicator includes all ties and dominates any Hamming decoder. -/
def hammingBad {n : ℕ} (C : BinaryLinearCode n) (x : BinaryBlock n) : ℝ := by
  classical
  exact if ∃ c : C, c.val ≠ 0 ∧ wt (x - c.val) ≤ wt x then 1 else 0

/-- PDF p.10: the iid BSC probability including endpoints p=0 and p=1. -/
def bsc {n : ℕ} (p : ℝ) (x : BinaryBlock n) : ℝ :=
  ∏ i, if x i = 0 then 1 - p else p

/-- PDF p.9: the actual weight marginal of the additive law. -/
def weightMass {n : ℕ} (P : BinaryBlock n → ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ x : BinaryBlock n, if wt x = k then P x else 0

/-- PDF p.10 (37),(38): the full weight sum, including the harmless k=0 term. -/
def noiseBound {n : ℕ} (P : BinaryBlock n → ℝ) (R eps : ℝ) : ℝ :=
  eps * ∑ k ∈ Finset.range (n + 1), weightMass P k *
    (2 : ℝ) ^ (-(n : ℝ) * max (1 - binEntropy2 (min ((k : ℝ) / n) (1 / 2)) - R) 0)

/-- PDF p.10 (38): word-error bound sums k=1,...,n, excluding zero noise. -/
def wordNoiseBound {n : ℕ} (P : BinaryBlock n → ℝ) (R eps : ℝ) : ℝ :=
  eps * ∑ j ∈ Finset.range n, weightMass P (j + 1) *
    (2 : ℝ) ^ (-(n : ℝ) * max (1 - binEntropy2 (min (((j + 1 : ℕ) : ℝ) / n) (1 / 2)) - R) 0)

/-- PDF p.10 (40): Gallager E0 in bits. -/
def E0 (s p : ℝ) : ℝ :=
  s - (1 + s) * Real.logb 2 (p ^ (1 / (1 + s)) + (1 - p) ^ (1 / (1 + s)))

/-- PDF p.10 (42): supremum on the compact interval; continuous for p in [0,1],
so nonempty, bounded and attained in every theorem below. -/
def gallagerExponent (R p : ℝ) : ℝ :=
  sSup ((fun s : ℝ => -s * R + E0 s p) '' Set.Icc 0 1)

/-- PDF p.10 (39): eps^s remains inside the minimization. -/
def gallagerBound (n : ℕ) (R p eps : ℝ) : ℝ :=
  sInf ((fun s : ℝ => eps ^ s * (2 : ℝ) ^ (-(n : ℝ) * (-s * R + E0 s p))) ''
    Set.Icc 0 1)

/-- PDF p.10: bernoulliDivergenceBits in bits, with infinite off-support values. -/
def bernoulliDivergenceBits (q p : ℝ) : EReal :=
  if (p = 0 ∧ q ≠ 0) ∨ (p = 1 ∧ q ≠ 1) then ⊤ else
    ((q * Real.logb 2 (q / p) + (1 - q) * Real.logb 2 ((1 - q) / (1 - p)) : ℝ) : EReal)

/-- PDF p.10 (43),(44): complete-lattice infimum, including deterministic channels. -/
def typeExponent (R p : ℝ) : EReal :=
  sInf ((fun q : ℝ => ((max (1 - binEntropy2 q - R) 0 : ℝ) : EReal) +
    bernoulliDivergenceBits q p) '' Set.Icc 0 (1 / 2))

/-- PDF p.10 (43): 2^(-n A), with 2^(-infinity)=0. -/
def expFactor (n : ℕ) (A : EReal) : ℝ :=
  if A = ⊤ then 0 else (2 : ℝ) ^ (-(n : ℝ) * A.toReal)

/-- PDF p.17: support-preserving tiltedBernoulli Bernoulli law, including theta=0. -/
def tiltedBernoulli (p theta : ℝ) : ℝ :=
  if p = 0 then 0 else if p = 1 then 1 else
    p ^ theta / (p ^ theta + (1 - p) ^ theta)

/-- PDF p.17 (73): the tiltedBernoulli variational expression in the extended reals. -/
def tiltedExponent (R p : ℝ) : EReal :=
  sInf ((fun theta : ℝ => bernoulliDivergenceBits (tiltedBernoulli p theta) p +
    ((max (1 - binEntropy2 (tiltedBernoulli p theta) - R) 0 : ℝ) : EReal)) '' Set.Icc 0 1)

/-- PDF p.13 (53): valid also when a union bound exceeds one. -/
def entropyEnvelope (l : ℕ) (u : ℝ) : ℝ :=
  if u ≤ 1 / 2 then binEntropy2 u + l * u else 1 + l * u

/-- PDF p.3 Example 2: a Toeplitz seed. One unused uniform seed bit gives
identical multiplicities for the usual a+b-1 diagonal-bit construction. -/
def seededToeplitz (a b : ℕ) (r : Fin (a + b) → ZMod 2) : Matrix (Fin b) (Fin a) (ZMod 2) :=
  fun i j => r ⟨i.val + (a - 1 - j.val), by omega⟩

/-- PDF p.6: M=(T,I_b). -/
def modifiedM (a b : ℕ) (r : Fin (a + b) → ZMod 2) :
    Matrix (Fin b) (Fin (a + b)) (ZMod 2) :=
  fun i j => if h : j.val < a then seededToeplitz a b r i ⟨j.val, h⟩
    else if j.val = a + i.val then 1 else 0

/-- PDF p.6: N=(I_a,T^transpose), over the same seed. -/
def modifiedN (a b : ℕ) (r : Fin (a + b) → ZMod 2) :
    Matrix (Fin a) (Fin (a + b)) (ZMod 2) :=
  fun i j => if h : j.val < a then (if j.val = i.val then 1 else 0)
    else seededToeplitz a b r ⟨j.val - a, by omega⟩ i

/-! Small definition tests; theorem proofs below are intentionally omitted. -/

example : avg (fun _ : Unit => (3 : ℝ)) = 3 := by simp [avg]

example : bernoulliDivergenceBits 0 0 = 0 := by simp [bernoulliDivergenceBits]

example : bernoulliDivergenceBits 1 0 = ⊤ := by simp [bernoulliDivergenceBits]

example : tiltedBernoulli 0 0 = 0 := by simp [tiltedBernoulli]

example : entropyEnvelope 4 0 = 0 := by simp [entropyEnvelope, binEntropy2]

example {n : ℕ} (x : BinaryBlock n) : bsc (n := n) (1 / 2) x = (1 / 2 : ℝ) ^ n := by
  unfold bsc
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [hhalf, ite_self, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- PDF p.12 (50): environment label (phase x, bit z). -/
abbrev Env (n : ℕ) := BinaryBlock n × BinaryBlock n

/-- PDF p.12 (50): Z^x X^z, in the computational basis labelled by F_2^n. -/
def phaseBitPauli {n : ℕ} (x z : BinaryBlock n) : Matrix (BinaryBlock n) (BinaryBlock n) ℂ := by
  classical
  exact fun b a => if b = a + z then (-1 : ℂ) ^ (∑ i, x i * b i).val else 0

/-- PDF p.13, iid assumption: the phase and bit errors are independent per qubit. -/
def iidPauli {n : ℕ} (pPhase pBit : ℝ) (e : Env n) : ℝ :=
  bsc pPhase e.1 * bsc pBit e.2

/-- PDF pp.12--13: actual Pauli Stinespring dilation, with the entire error label
in Eve's register. For a normalized law this is an isometry. -/
def pauliDilation {n : ℕ} (W : Env n → ℝ) :
    Matrix (BinaryBlock n × Env n) (BinaryBlock n) ℂ :=
  fun be a => (Real.sqrt (W be.2) : ℂ) * phaseBitPauli be.2.1 be.2.2 be.1 a

/-- PDF p.13: complementary output obtained by tracing out Bob, with no
postprocessing, dephasing, or deletion of environment coherences. -/
def pauliComplement {n : ℕ} (W : Env n → ℝ) (rho : Matrix (BinaryBlock n) (BinaryBlock n) ℂ) :
    Matrix (Env n) (Env n) ℂ :=
  traceLeft (pauliDilation W * rho * (pauliDilation W).conjTranspose)

/-- PDF p.13: the actual uniform MIXTURE on a coset, not the coherent CSS state. -/
def cosetDensity {n : ℕ} (small : BinaryLinearCode n) (a : BinaryBlock n) :
    Matrix (BinaryBlock n) (BinaryBlock n) ℂ := by
  classical
  exact Matrix.diagonal (fun b => if b - a ∈ small then
    ((Fintype.card small : ℝ)⁻¹ : ℂ) else 0)

/-- PDF p.13: normalized virtual coherent CSS coset vector, explicitly separate
from the actual mixture sent by Alice. -/
def coherentCoset {n : ℕ} (small : BinaryLinearCode n) (a : BinaryBlock n) : EuclideanSpace ℂ (BinaryBlock n) := by
  classical
  exact WithLp.toLp 2 (fun b => if b - a ∈ small then
    ((Real.sqrt (Fintype.card small))⁻¹ : ℂ) else 0)

/-- PDF p.13: conditional Eve density for the actual coset-mixture encoder. -/
def cosetEve {n : ℕ} (small : BinaryLinearCode n) (W : Env n → ℝ) (a : BinaryBlock n) :
    Matrix (Env n) (Env n) ℂ := pauliComplement W (cosetDensity small a)

/-- PDF p.13: Eve marginal for the uniform large-code input. -/
def meanEve {n : ℕ} (large : BinaryLinearCode n) (W : Env n → ℝ) : Matrix (Env n) (Env n) ℂ :=
  ((Fintype.card large : ℝ)⁻¹ : ℂ) • ∑ a : large,
    pauliComplement W (cosetDensity (⊥ : BinaryLinearCode n) a.val)

/-- PDF pp.13--14: full trace norm of the actual cq state minus the independent
uniform-key state. Each quotient coset has exactly card(small) representatives,
so averaging over a in large is exactly averaging uniform quotient messages. -/
def traceLeak {n : ℕ} (small large : BinaryLinearCode n) (W : Env n → ℝ) : ℝ :=
  (Fintype.card large : ℝ)⁻¹ * ∑ a : large,
    traceNorm (cosetEve small W a.val - meanEve large W)

/-- PDF pp.13--14: Holevo information in bits of the same physical cq ensemble. -/
def holevoLeak {n : ℕ} (small large : BinaryLinearCode n) (W : Env n → ℝ) : ℝ :=
  vnEntropy (meanEve large W) -
    (Fintype.card large : ℝ)⁻¹ * ∑ a : large, vnEntropy (cosetEve small W a.val)

/-- PDF p.12: the phase marginal of the actual joint Pauli law. -/
def phaseMass {n : ℕ} (W : Env n → ℝ) (x : BinaryBlock n) : ℝ := ∑ z, W (x, z)

/-- PDF p.13 (54)--(56): actual dual quotient decoding error. No scalar success
probability is supplied by the caller. Logical success is modulo large-perp. -/
def phaseError {n : ℕ} (small large : BinaryLinearCode n) (W : Env n → ℝ) : ℝ :=
  cosetWordError (binDual large) (binDual small) (phaseMass W)

/-- PDF p.13: virtual phase correction subtracts the selected syndrome noise
representative. The remaining phase label is this decoded dual codeword;
phase correction succeeds exactly when it lies in large-perp. -/
def residualPhase {n : ℕ} (small : BinaryLinearCode n) (W : Env n → ℝ) (x : BinaryBlock n) : BinaryBlock n :=
  (mlDecode (binDual small) (phaseMass W) x).val

/-- PDF p.13: physical phase-recovered Pauli map on the CSS code space before
logical decoding; bit errors are left in place. The phase correction depends
only on the measured small-code syndrome, by the noise-coset tie convention. -/
def phaseRecovered {n : ℕ} (small : BinaryLinearCode n) (W : Env n → ℝ)
    (rho : Matrix (BinaryBlock n) (BinaryBlock n) ℂ) : Matrix (BinaryBlock n) (BinaryBlock n) ℂ :=
  ∑ e : Env n, (W e : ℂ) •
    (phaseBitPauli (residualPhase small W e.1) e.2 * rho *
      (phaseBitPauli (residualPhase small W e.1) e.2).conjTranspose)

/-- PDF p.13: message length of a specific seed's quotient. -/
def messageLength {n : ℕ} (small large : BinaryLinearCode n) : ℕ :=
  Module.finrank (ZMod 2) large - Module.finrank (ZMod 2) small

/-- PDF p.14 (59)--(61): common upper bound on average residual phase error. -/
def iidPhaseBound (n t : ℕ) (p eps : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) * gallagerExponent (1 - (t : ℝ) / n) p) * max eps 1

example {n : ℕ} (small : BinaryLinearCode n) (a b c : BinaryBlock n) (h : b ≠ c) :
    cosetDensity small a b c = 0 := by
  classical
  simp [cosetDensity, Matrix.diagonal, h]

example {n : ℕ} (rho : Matrix (BinaryBlock n) (BinaryBlock n) ℂ) :
    pauliComplement (fun _ : Env n => 0) rho = 0 := by
  have hd : pauliDilation (fun _ : Env n => 0) = 0 := by
    ext be a
    simp only [pauliDilation, Real.sqrt_zero, Complex.ofReal_zero, zero_mul,
      Matrix.zero_apply]
  simp only [pauliComplement, hd, zero_mul]
  ext a b
  simp [traceLeft]

/-- PDF p.14: exponential rate in bits, with perfect secrecy assigned +infinity.
Only positive block lengths are passed by the asymptotic statement. -/
def logRate (n : ℕ) (e : ℝ) : EReal :=
  if e = 0 then ⊤ else ((-Real.logb 2 e / n : ℝ) : EReal)

/-- PDF p.14 (60): the phase-error trace bound. -/
def phaseTraceBound (n : ℕ) (S p eps : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(1 / 2 : ℝ) * n * gallagerExponent (1 - S) p + 3 / 2) * max (Real.sqrt eps) 1

/-- PDF p.14 (64): the delta-biased trace bound used in the comparison. -/
def deltaTraceBound (n : ℕ) (S p eps : ℝ) : ℝ :=
  (4 + Real.sqrt (n + 1) * Real.sqrt eps) *
    (2 : ℝ) ^ (-(1 / 2 : ℝ) * n * gallagerExponent (1 - S) p)

/-- PDF p.15, separate classical broadcast model: Bob gets the noiseless word;
Eve gets BSC(p). This is Eve's conditional distribution for a uniform coset input. -/
def classicalCosetEve {n : ℕ} (small : BinaryLinearCode n) (p : ℝ) (a y : BinaryBlock n) : ℝ :=
  (Fintype.card small : ℝ)⁻¹ * ∑ b : small, bsc p (y - (a + b.val))

/-- PDF p.15: mutual information of the actual classical quotient-message/Eve
law, averaged over uniform messages. Eve's marginal is uniform on F_2^n;
zero terms contribute zero, including the deterministic BSC endpoints. -/
def classicalLeak {n : ℕ} (small : BinaryLinearCode n) (p : ℝ) : ℝ :=
  avg (fun a : BinaryBlock n => ∑ y : BinaryBlock n, classicalCosetEve small p a y *
    Real.logb 2 (classicalCosetEve small p a y * (2 : ℝ) ^ n))

example : logRate 1 0 = ⊤ := by simp [logRate]

example (u : ℝ) (hu : (1 / 2 : ℝ) < u) (l : ℕ) : entropyEnvelope l u = 1 + l * u := by
  unfold entropyEnvelope
  exact if_neg (not_le.mpr hu)

end QAlgorithms.Papers.Independent.Intake100.P31


