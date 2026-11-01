-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P14
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:52:17.172124+00:00
-- url     : https://prove2.me/theorems/942921c5-3b9a-440a-92b6-a33f619e5568
-- title:
--   Definitions for Polar codes for classical-quantum channels
-- statement:
--   The objects the formalized statements of *Polar codes for classical-quantum channels* (arXiv:1109.2591) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Bit`: PDF p.3: the two classical letters, with addition equal to XOR.
--   - `OutputCoefficients`: PDF p.3: unrestricted coefficients in a complete orthonormal basis.
--   - `IsBinaryCqChannel`: PDF p.3: binary cq channels; only this validity predicate is an input hypothesis. All synthesized channels are computed from the input channel.
--   - `basisKet`: PDF p.3: the basis vector at i in the completed Hilbert space.
--   - `coefficientOperator`: PDF p.3: bounded operators reconstructed from their coefficients. The unique matching operator is chosen whenever it exists. The zero fallback is only for arrays that are not bounded operators; all density, tensor, mixture, and split kernels occurring in the statements have a matching operator.
--   - `cqOperatorCoefficients`: PDF p.3: coefficients of an actual bounded operator.
--   - `basisTrace`: PDF p.3: basis trace, used on trace-class operators and their bounded products. Its series is absolutely convergent on every use in a theorem.
--   - `positiveBoundedRoot`: PDF p.3: the unique positive bounded square root, chosen by its defining identity. On positive bounded operators a positive root exists and is unique; only operators outside that domain can reach the zero fallback. This avoids requiring a functional-calculus instance as an additional channel hypothesis.
--   - `densitySqrt`: PDF p.3: positive square root of the reconstructed density operator.
--   - `cqRootFidelity`: PDF p.3: ROOT fidelity Tr sqrt(sqrt(rho_0) rho_1 sqrt(rho_0)), on the full completed output Hilbert space.
--   - `squaredCqFidelity`: PDF p.3: the paper's SQUARED fidelity F(W).
--   - `uniformMixture`: PDF p.3: uniform output mixture, constructed from the two outputs.
--   - `cqRelativeEntropyBits`: PDF p.3: extended Umegaki relative entropy in bits via finite orthogonal compressions. Copied from accepted Dependency50.P13.relativeEntropy and Support50.P44.compressedRelativeEntropy. The generalized trace correction inside qRelEntropy is essential on subnormalized compressions; the support guard retains infinity. No difference of infinite entropies is taken.
--   - `symmetricInformation`: PDF p.3: intrinsic uniform-prior Holevo information, in bits. Extended values are retained; on every channel it is at most one. This avoids infinity minus infinity when individual output entropies are infinite.
--   - `PolarWire`: PDF p.4: N=2^n wires, indexed from zero.
--   - `reverseWire`: PDF p.4: the numerical n-bit reversal, B_N; the modulo makes this a total Fin-valued definition without assuming a separately supplied permutation.
--   - `polarKernel`: PDF p.4: the two-by-two polar kernel F, with row-vector convention.
--   - `polarMatrix`: PDF p.4, (5): G_N=B_N F^(tensor n), F=[[1,0],[1,1]], acting on ROW vectors. A tensor-kernel entry is one exactly when every 1 column digit is a 1 row digit. Bit reversal is applied to the row index before that test.
--   - `polarEncode`: PDF pp.4–5, (5),(10): the actual binary linear encoding map uG_N.
--   - `EncodingGate`: PDF pp.1–2,4: primitive classical XOR and swap gates, each charged once.
--   - `EncodingGate.apply`: PDF p.4: gate interpretation, with both old values read before a swap.
--   - `runEncoder`: PDF pp.1–2,4: cost is the length of the interpreted gate list.
--   - `toggleWire`: PDF p.4: flip address digit k, keeping the other wire-address digits.
--   - `recursivePolarEncoder`: PDF pp.1–2,4: explicit circuit for B_N followed by the n butterfly layers. Each bit-reversal pair is swapped once, and each zero-address-digit wire receives one XOR from its partner in that layer.
--   - `combinedOutput`: PDF p.4: combined channel W_N from (5).
--   - `filledWord`: PDF p.4, (8): fill known history and current bit. Dummy coordinates of v are ignored where history or the current bit has already fixed the value.
--   - `futureAverage`: PDF p.4, (8): uniform average over future bits. Averaging a full dummy word gives precisely the same average: each unused coordinate cancels a factor of two in the denominator. No frozen future bits are conditioned on.
--   - `SplitLabel`: PDF p.4, (6)–(7): previous bits are an actual classical output register.
--   - `splitChannel`: PDF p.4, (6)–(8): the synthesized split channel, including its uniform classical history flag.
--   - `channelMinus`: PDF p.7, (14): the computed bad channel.
--   - `channelPlus`: PDF p.7, (15): the computed good channel, with the uniformly random previous bit retained as an output flag.
--   - `childIndex`: PDF pp.7–8: children 2i and 2i+1 in zero-based indexing.
--   - `parentLabels`: PDF p.7, (16)–(17): pull a child label back to the two old histories. The histories are (odd XOR even, even), and the physical outputs are the first and second N-use blocks. The newly exposed odd bit is omitted from this map.
--   - `plusLabel`: PDF p.7: the retained new odd-bit flag in the plus recursion.
--   - `negativeCompactProjection`: PDF p.5: negative spectral subspace of a compact self-adjoint difference of square roots. The closed span of all strictly negative eigenvectors includes all negative spectrum for this compact operator. Its orthogonal complement assigns the entire zero eigenspace to outcome zero.
--   - `bitProjector`: PDF p.5, (11)–(12): prescribed root-density bit test on the full output.
--   - `previousBits`: PDF p.5: restriction to the already decoded history.
--   - `decodingBranch`: PDF pp.5–6: correct-branch Kraus operator, in chronological measurement order. Frozen positions apply identity; the other tests use previous outcomes. All branches of the adaptive decoder are specified by allowing arbitrary u.
--   - `decodingEffect`: PDF p.6, (13): the actual palindromic POVM effect K-adjoint K. For a fixed frozen vector its branches are indexed by information messages.
--   - `decodingSuccess`: PDF p.6, (13): probability of decoding the whole transmitted word u correctly, as the actual POVM trace pairing.
--   - `InformationWord`: PDF pp.5–6: information messages and frozen vectors have their actual coordinate domains, including the unique empty message when A is empty.
--   - `Frozen`: PDF pp.5–6: frozen coordinates, known to the receiver.
--   - `cosetWord`: PDF p.5, (10): assemble the message and the specified frozen vector.
--   - `frozenError`: PDF p.6: block error averaged uniformly over information messages.
--   - `ensembleError`: PDF p.6: further uniform average over all frozen vectors, not maximum error.
--   - `PolarRule`: PDF p.6, Definition 5: minimal-fidelity information set at rate R; all choices among ties are allowed.
--   - `polarDecay`: PDF pp.5–6,9: reference decay, with real beta and N=2^n.
--   - `branchIndex`: PDF p.8: index of a branch after n fair bits, using i-1 in the source's one-based indexing. Array entry B 0 represents the source's B_1.
--   - `fidelityProcess`: PDF p.8: root-fidelity process of the constructed channel tree.
--   - `informationProcess`: PDF p.8: information process. The lemma explicitly concludes finiteness of the extended information before using its real conversion.
--   - `bitFiltration`: PDF p.8: exactly the sigma algebra of the first n bits; time zero is trivial. No extra bit is exposed at time n.
--   - `PureOutputs`: PDF pp.9–10: pure outputs on an arbitrary physical Hilbert space.
--   - `BinaryBlockCode`: PDF pp.9–10: unrestricted finite-message classical code for N uses of the fixed binary-alphabet cq channel. The decoder is an actual bounded POVM; message count is positive even for zero rate.
--   - `BinaryBlockCode.error`: PDF pp.9–10: uniform-message error of an arbitrary physical block code.
--   - `BinaryAchievableRate`: PDF pp.9–10: operational achievability, independently of the information formula, at all sufficiently large positive blocklengths.
--   - `binaryOperationalCapacity`: PDF pp.9–10: full classical capacity of the fixed binary-input channel, not a bosonic capacity optimized over arbitrary input alphabets or energies.
--   - `PolarAchieves`: PDF pp.6,9–10: polar attainment at a fixed rate by actual ensemble-error families. One family is chosen before beta, with all tied polar choices allowed by PolarRule. Theorem 6 separately quantifies every such family.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, https://arxiv.org/abs/1109.2591v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

/-!
Wilde and Guha, arXiv:1109.2591v3. All citations are PDF pages.
Pinned accepted Dependency50.P13/P33 and Renew46.P44 definitions are imported
under the independent-paper workflow override. Exact density, compression, and
memoryless-output definitions are reused without redeclaration. Other
coefficient-coordinate interfaces below retain arbitrary output dimension. Completed output Hilbert
spaces are l2 of arbitrary basis labels. There is no finite-dimensional cutoff.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory
open scoped ENNReal NNReal ComplexOrder BigOperators
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)
open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: the two classical letters, with addition equal to XOR. -/
abbrev Bit := ZMod 2

/-- PDF p.3: unrestricted coefficients in a complete orthonormal basis. -/
abbrev OutputCoefficients (I : Type) := Matrix I I ℂ

/-- PDF p.3: binary cq channels; only this validity predicate is an input
hypothesis. All synthesized channels are computed from the input channel. -/
def IsBinaryCqChannel {I : Type} (W : Bit → OutputCoefficients I) : Prop := ∀ b, IsDensity (W b)

/-- PDF p.3: the basis vector at i in the completed Hilbert space. -/
def basisKet {I : Type} (i : I) : Hilbert I := lp.single 2 i 1

/-- PDF p.3: bounded operators reconstructed from their coefficients. The
unique matching operator is chosen whenever it exists. The zero fallback is
only for arrays that are not bounded operators; all density, tensor, mixture,
and split kernels occurring in the statements have a matching operator. -/
def coefficientOperator {I : Type} (X : OutputCoefficients I) : Hilbert I →L[ℂ] Hilbert I :=
  if h : ∃ T : Hilbert I →L[ℂ] Hilbert I, ∀ i j, T (basisKet j) i = X i j then
    h.choose
  else 0

/-- PDF p.3: coefficients of an actual bounded operator. -/
def cqOperatorCoefficients {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) : OutputCoefficients I :=
  fun i j => T (basisKet j) i

/-- PDF p.3: basis trace, used on trace-class operators and their bounded
products. Its series is absolutely convergent on every use in a theorem. -/
def basisTrace {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) : ℂ :=
  ∑' i, T (basisKet i) i

/-- PDF p.3: the unique positive bounded square root, chosen by its defining
identity. On positive bounded operators a positive root exists and is unique;
only operators outside that domain can reach the zero fallback. This avoids
requiring a functional-calculus instance as an additional channel hypothesis. -/
def positiveBoundedRoot {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) :
    Hilbert I →L[ℂ] Hilbert I :=
  if h : ∃ S : Hilbert I →L[ℂ] Hilbert I, S.IsPositive ∧ S.comp S = T then
    h.choose
  else 0

/-- PDF p.3: positive square root of the reconstructed density operator. -/
def densitySqrt {I : Type} (X : OutputCoefficients I) : Hilbert I →L[ℂ] Hilbert I :=
  positiveBoundedRoot (coefficientOperator X)

/-- PDF p.3: ROOT fidelity Tr sqrt(sqrt(rho_0) rho_1 sqrt(rho_0)),
on the full completed output Hilbert space. -/
def cqRootFidelity {I : Type} (W : Bit → OutputCoefficients I) : ℝ :=
  (basisTrace (positiveBoundedRoot
    ((densitySqrt (W 0)).comp ((coefficientOperator (W 1)).comp (densitySqrt (W 0)))))).re

/-- PDF p.3: the paper's SQUARED fidelity F(W). -/
def squaredCqFidelity {I : Type} (W : Bit → OutputCoefficients I) : ℝ := (cqRootFidelity W) ^ 2

/-- PDF p.3: uniform output mixture, constructed from the two outputs. -/
def uniformMixture {I : Type} (W : Bit → OutputCoefficients I) : OutputCoefficients I :=
  (1 / 2 : ℂ) • (W 0 + W 1)

/-- PDF p.3: extended Umegaki relative entropy in bits via finite orthogonal
compressions. Copied from accepted Dependency50.P13.relativeEntropy and
Support50.P44.compressedRelativeEntropy. The generalized trace correction
inside qRelEntropy is essential on subnormalized compressions; the support
guard retains infinity. No difference of infinite entropies is taken. -/
def cqRelativeEntropyBits {I : Type} (X Y : OutputCoefficients I) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ v : {v : Fin n → Hilbert I // Orthonormal ℂ v},
    if LinearMap.ker (compression v.val (coefficientOperator Y)).mulVecLin ≤
        LinearMap.ker (compression v.val (coefficientOperator X)).mulVecLin then
      ENNReal.ofReal (QAlgorithms.qRelEntropy
        (compression v.val (coefficientOperator X)) (compression v.val (coefficientOperator Y)) / Real.log 2)
    else ⊤

/-- PDF p.3: intrinsic uniform-prior Holevo information, in bits. Extended
values are retained; on every channel it is at most one. This avoids infinity
minus infinity when individual output entropies are infinite. -/
def symmetricInformation {I : Type} (W : Bit → OutputCoefficients I) : ℝ≥0∞ :=
  (cqRelativeEntropyBits (W 0) (uniformMixture W) +
    cqRelativeEntropyBits (W 1) (uniformMixture W)) / 2

/-- PDF p.4: N=2^n wires, indexed from zero. -/
abbrev PolarWire (n : ℕ) := Fin (2 ^ n)

/-- PDF p.4: the numerical n-bit reversal, B_N; the modulo makes this a total
Fin-valued definition without assuming a separately supplied permutation. -/
def reverseWire (n : ℕ) (i : PolarWire n) : PolarWire n :=
  ⟨(∑ k : Fin n, if i.val.testBit k.val then 2 ^ (n - 1 - k.val) else 0) % 2 ^ n,
    Nat.mod_lt _ (pow_pos (by decide) _)⟩

/-- PDF p.4: the two-by-two polar kernel F, with row-vector convention. -/
def polarKernel : Matrix Bit Bit Bit := fun r c => if c = 0 then 1 else r

/-- PDF p.4, (5): G_N=B_N F^(tensor n), F=[[1,0],[1,1]], acting on ROW
vectors. A tensor-kernel entry is one exactly when every 1 column digit is a
1 row digit. Bit reversal is applied to the row index before that test. -/
def polarMatrix (n : ℕ) : Matrix (PolarWire n) (PolarWire n) Bit :=
  fun r c => ∏ k : Fin n,
    polarKernel (if (reverseWire n r).val.testBit k.val then 1 else 0)
      (if c.val.testBit k.val then 1 else 0)

/-- PDF pp.4–5, (5),(10): the actual binary linear encoding map uG_N. -/
def polarEncode (n : ℕ) (u : PolarWire n → Bit) : PolarWire n → Bit :=
  fun c => ∑ r, u r * polarMatrix n r c

/-- PDF pp.1–2,4: primitive classical XOR and swap gates, each charged once. -/
inductive EncodingGate (n : ℕ) where
  | xor (source target : PolarWire n)
  | swap (a b : PolarWire n)

/-- PDF p.4: gate interpretation, with both old values read before a swap. -/
def EncodingGate.apply {n : ℕ} (g : EncodingGate n) (u : PolarWire n → Bit) :
    PolarWire n → Bit :=
  match g with
  | .xor s t => Function.update u t (u t + u s)
  | .swap a b => Function.update (Function.update u a (u b)) b (u a)

/-- PDF pp.1–2,4: cost is the length of the interpreted gate list. -/
def runEncoder {n : ℕ} (gates : List (EncodingGate n)) (u : PolarWire n → Bit) :
    PolarWire n → Bit := gates.foldl (fun v g => g.apply v) u

/-- PDF p.4: flip address digit k, keeping the other wire-address digits. -/
def toggleWire (n : ℕ) (k : Fin n) (i : PolarWire n) : PolarWire n :=
  ⟨(Nat.xor i.val (2 ^ k.val)) % 2 ^ n, Nat.mod_lt _ (pow_pos (by decide) _)⟩

/-- PDF pp.1–2,4: explicit circuit for B_N followed by the n butterfly layers.
Each bit-reversal pair is swapped once, and each zero-address-digit wire
receives one XOR from its partner in that layer. -/
def recursivePolarEncoder (n : ℕ) : List (EncodingGate n) :=
  ((Finset.univ.filter (fun i : PolarWire n => i.val < (reverseWire n i).val)).toList.map
    (fun i => EncodingGate.swap i (reverseWire n i))) ++
  (List.finRange n).flatMap (fun k =>
    ((Finset.univ.filter (fun i : PolarWire n => ¬ i.val.testBit k.val)).toList.map
      (fun i => EncodingGate.xor (toggleWire n k i) i)))

/-- PDF p.4: combined channel W_N from (5). -/
def combinedOutput {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ) (u : PolarWire n → Bit) :
    OutputCoefficients (PolarWire n → I) := wordOutput W (polarEncode n u)

/-- PDF p.4, (8): fill known history and current bit. Dummy coordinates of v
are ignored where history or the current bit has already fixed the value. -/
def filledWord {n : ℕ} (i : PolarWire n) (h : Fin i.val → Bit) (b : Bit)
    (v : PolarWire n → Bit) : PolarWire n → Bit :=
  fun j => if hj : j.val < i.val then h ⟨j.val, hj⟩ else if j = i then b else v j

/-- PDF p.4, (8): uniform average over future bits. Averaging a full dummy
word gives precisely the same average: each unused coordinate cancels a factor
of two in the denominator. No frozen future bits are conditioned on. -/
def futureAverage {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ) (i : PolarWire n)
    (h : Fin i.val → Bit) (b : Bit) : OutputCoefficients (PolarWire n → I) :=
  ((Fintype.card (PolarWire n → Bit) : ℂ)⁻¹) •
    ∑ v : PolarWire n → Bit, combinedOutput W n (filledWord i h b v)

/-- PDF p.4, (6)–(7): previous bits are an actual classical output register. -/
abbrev SplitLabel (I : Type) (n : ℕ) (i : PolarWire n) :=
  (Fin i.val → Bit) × (PolarWire n → I)

/-- PDF p.4, (6)–(8): the synthesized split channel, including its uniform
classical history flag. -/
def splitChannel {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ) (i : PolarWire n) :
    Bit → OutputCoefficients (SplitLabel I n i) :=
  fun b p q => if p.1 = q.1 then
    ((2 : ℂ) ^ i.val)⁻¹ * futureAverage W n i p.1 b p.2 q.2 else 0

/-- PDF p.7, (14): the computed bad channel. -/
def channelMinus {I : Type} (W : Bit → OutputCoefficients I) : Bit → OutputCoefficients (I × I) :=
  fun b p q => (1 / 2 : ℂ) * ∑ c : Bit, W (b + c) p.1 q.1 * W c p.2 q.2

/-- PDF p.7, (15): the computed good channel, with the uniformly random
previous bit retained as an output flag. -/
def channelPlus {I : Type} (W : Bit → OutputCoefficients I) : Bit → OutputCoefficients (Bit × (I × I)) :=
  fun c p q => if p.1 = q.1 then
    (1 / 2 : ℂ) * W (p.1 + c) p.2.1 q.2.1 * W c p.2.2 q.2.2 else 0

/-- PDF pp.7–8: children 2i and 2i+1 in zero-based indexing. -/
def childIndex {n : ℕ} (i : PolarWire n) (good : Bool) : PolarWire (n + 1) :=
  ⟨2 * i.val + (if good then 1 else 0), by
    have hi := i.isLt
    simp only [pow_succ]
    split <;> omega⟩

/-- PDF p.7, (16)–(17): pull a child label back to the two old histories.
The histories are (odd XOR even, even), and the physical outputs are the first
and second N-use blocks. The newly exposed odd bit is omitted from this map. -/
def parentLabels {I : Type} {n : ℕ} (i : PolarWire n) (good : Bool)
    (p : SplitLabel I (n + 1) (childIndex i good)) :
    SplitLabel I n i × SplitLabel I n i :=
  (((fun k => p.1 ⟨2 * k.val, by
        have hk := k.isLt
        simp only [childIndex]
        split <;> omega⟩ +
      p.1 ⟨2 * k.val + 1, by
        have hk := k.isLt
        simp only [childIndex]
        split <;> omega⟩),
    fun j => p.2 ⟨j.val, by have hj := j.isLt; simp only [pow_succ]; omega⟩),
   ((fun k => p.1 ⟨2 * k.val + 1, by
        have hk := k.isLt
        simp only [childIndex]
        split <;> omega⟩),
    fun j => p.2 ⟨2 ^ n + j.val, by
      have hj := j.isLt; simp only [pow_succ]; omega⟩))

/-- PDF p.7: the retained new odd-bit flag in the plus recursion. -/
def plusLabel {I : Type} {n : ℕ} (i : PolarWire n)
    (p : SplitLabel I (n + 1) (childIndex i true)) :
    Bit × (SplitLabel I n i × SplitLabel I n i) :=
  (p.1 ⟨2 * i.val, by simp [childIndex]⟩, parentLabels i true p)

/-- PDF p.5: negative spectral subspace of a compact self-adjoint difference
of square roots. The closed span of all strictly negative eigenvectors includes
all negative spectrum for this compact operator. Its orthogonal complement
assigns the entire zero eigenspace to outcome zero. -/
def negativeCompactProjection {J : Type} (T : Hilbert J →L[ℂ] Hilbert J) :
    Hilbert J →L[ℂ] Hilbert J :=
  ((Submodule.span ℂ {v : Hilbert J | ∃ a : ℝ, a < 0 ∧ T v = (a : ℂ) • v}).topologicalClosure).starProjection

/-- PDF p.5, (11)–(12): prescribed root-density bit test on the full output. -/
def bitProjector {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ) (i : PolarWire n)
    (h : Fin i.val → Bit) (b : Bit) :
    Hilbert (PolarWire n → I) →L[ℂ] Hilbert (PolarWire n → I) :=
  let P := negativeCompactProjection
    (densitySqrt (futureAverage W n i h 0) - densitySqrt (futureAverage W n i h 1))
  if b = 0 then 1 - P else P

/-- PDF p.5: restriction to the already decoded history. -/
def previousBits {n : ℕ} (i : PolarWire n) (u : PolarWire n → Bit) : Fin i.val → Bit :=
  fun k => u ⟨k.val, lt_trans k.isLt i.isLt⟩

/-- PDF pp.5–6: correct-branch Kraus operator, in chronological measurement
order. Frozen positions apply identity; the other tests use previous outcomes.
All branches of the adaptive decoder are specified by allowing arbitrary u. -/
def decodingBranch {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ)
    (A : Finset (PolarWire n)) (u : PolarWire n → Bit) :
    Hilbert (PolarWire n → I) →L[ℂ] Hilbert (PolarWire n → I) :=
  (List.finRange (2 ^ n)).foldl (fun K i =>
    (if i ∈ A then bitProjector W n i (previousBits i u) (u i) else 1).comp K) 1

/-- PDF p.6, (13): the actual palindromic POVM effect K-adjoint K.
For a fixed frozen vector its branches are indexed by information messages. -/
def decodingEffect {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ)
    (A : Finset (PolarWire n)) (u : PolarWire n → Bit) :
    Hilbert (PolarWire n → I) →L[ℂ] Hilbert (PolarWire n → I) :=
  let K := decodingBranch W n A u
  K.adjoint.comp K

/-- PDF p.6, (13): probability of decoding the whole transmitted word u
correctly, as the actual POVM trace pairing. -/
def decodingSuccess {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ)
    (A : Finset (PolarWire n)) (u : PolarWire n → Bit) : ℝ :=
  (basisTrace ((decodingEffect W n A u).comp
    (coefficientOperator (combinedOutput W n u)))).re

/-- PDF pp.5–6: information messages and frozen vectors have their actual
coordinate domains, including the unique empty message when A is empty. -/
abbrev InformationWord (n : ℕ) (A : Finset (PolarWire n)) := {i : PolarWire n // i ∈ A} → Bit

/-- PDF pp.5–6: frozen coordinates, known to the receiver. -/
abbrev Frozen (n : ℕ) (A : Finset (PolarWire n)) := {i : PolarWire n // i ∉ A} → Bit

/-- PDF p.5, (10): assemble the message and the specified frozen vector. -/
def cosetWord {n : ℕ} {A : Finset (PolarWire n)} (m : InformationWord n A) (f : Frozen n A) :
    PolarWire n → Bit := fun i => if hi : i ∈ A then m ⟨i, hi⟩ else f ⟨i, hi⟩

/-- PDF p.6: block error averaged uniformly over information messages. -/
def frozenError {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ) (A : Finset (PolarWire n))
    (f : Frozen n A) : ℝ :=
  1 - (∑ m : InformationWord n A, decodingSuccess W n A (cosetWord m f)) /
    (Fintype.card (InformationWord n A) : ℝ)

/-- PDF p.6: further uniform average over all frozen vectors, not maximum error. -/
def ensembleError {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ) (A : Finset (PolarWire n)) : ℝ :=
  (∑ f : Frozen n A, frozenError W n A f) / (Fintype.card (Frozen n A) : ℝ)

/-- PDF p.6, Definition 5: minimal-fidelity information set at rate R;
all choices among ties are allowed. -/
def PolarRule {I : Type} (W : Bit → OutputCoefficients I) (n : ℕ) (R : ℝ)
    (A : Finset (PolarWire n)) : Prop :=
  A.card = ⌊(2 ^ n : ℕ) * R⌋₊ ∧
    ∀ i ∈ A, ∀ j, j ∉ A →
      squaredCqFidelity (splitChannel W n i) ≤ squaredCqFidelity (splitChannel W n j)

/-- PDF pp.5–6,9: reference decay, with real beta and N=2^n. -/
def polarDecay (beta : ℝ) (scale : ℝ) (n : ℕ) : ℝ :=
  Real.rpow 2 (-scale * Real.rpow (2 ^ n : ℕ) beta)

/-- PDF p.8: index of a branch after n fair bits, using i-1 in the source's
one-based indexing. Array entry B 0 represents the source's B_1. -/
def branchIndex {Omega : Type} (B : ℕ → Omega → Bool) (n : ℕ) (w : Omega) : PolarWire n :=
  ⟨(∑ k : Fin n, if B k.val w then 2 ^ (n - 1 - k.val) else 0) % 2 ^ n,
    Nat.mod_lt _ (pow_pos (by decide) _)⟩

/-- PDF p.8: root-fidelity process of the constructed channel tree. -/
def fidelityProcess {I Omega : Type} (W : Bit → OutputCoefficients I)
    (B : ℕ → Omega → Bool) (n : ℕ) (w : Omega) : ℝ :=
  Real.sqrt (squaredCqFidelity (splitChannel W n (branchIndex B n w)))

/-- PDF p.8: information process. The lemma explicitly concludes finiteness
of the extended information before using its real conversion. -/
def informationProcess {I Omega : Type} (W : Bit → OutputCoefficients I)
    (B : ℕ → Omega → Bool) (n : ℕ) (w : Omega) : ℝ :=
  (symmetricInformation (splitChannel W n (branchIndex B n w))).toReal

/-- PDF p.8: exactly the sigma algebra of the first n bits; time zero is
trivial. No extra bit is exposed at time n. -/
def bitFiltration {Omega : Type} [m : MeasurableSpace Omega]
    (B : ℕ → Omega → Bool) (hB : ∀ k, Measurable (B k)) : Filtration ℕ m where
  seq n := ⨆ k : Fin n, MeasurableSpace.comap (B k.val) inferInstance
  mono' := by
    intro n m hnm
    refine iSup_le fun k => ?_
    exact le_iSup_of_le (⟨k.val, lt_of_lt_of_le k.isLt hnm⟩ : Fin m) le_rfl
  le' := by
    intro n
    exact iSup_le fun k => (hB k.val).comap_le

/-- PDF pp.9–10: pure outputs on an arbitrary physical Hilbert space. -/
def PureOutputs {I : Type} (W : Bit → OutputCoefficients I) : Prop :=
  ∀ b, ∃ v : Hilbert I, ‖v‖ = 1 ∧ W b = fun i j => v i * star (v j)

/-- PDF pp.9–10: unrestricted finite-message classical code for N uses of
the fixed binary-alphabet cq channel. The decoder is an actual bounded POVM;
message count is positive even for zero rate. -/
structure BinaryBlockCode (I : Type) (N : ℕ) where
  messages : ℕ
  positive : 0 < messages
  encode : Fin messages → Fin N → Bit
  decode : Fin messages → Hilbert (Fin N → I) →L[ℂ] Hilbert (Fin N → I)
  nonnegative : ∀ m, (decode m).IsPositive
  complete : ∑ m, decode m = 1

/-- PDF pp.9–10: uniform-message error of an arbitrary physical block code. -/
def BinaryBlockCode.error {I : Type} {N : ℕ} (C : BinaryBlockCode I N)
    (W : Bit → OutputCoefficients I) : ℝ :=
  1 - (∑ m, (basisTrace
    ((C.decode m).comp (coefficientOperator (wordOutput W (C.encode m))))).re) / C.messages

/-- PDF pp.9–10: operational achievability, independently of the information
formula, at all sufficiently large positive blocklengths. -/
def BinaryAchievableRate {I : Type} (W : Bit → OutputCoefficients I) (R : ℝ≥0) : Prop :=
  ∀ e : ℝ, 0 < e → ∀ d : ℝ, 0 < d → ∃ N0 : ℕ, 0 < N0 ∧
    ∀ N ≥ N0, ∃ C : BinaryBlockCode I N,
      (R : ℝ) - d ≤ Real.logb 2 C.messages / N ∧ C.error W ≤ e

/-- PDF pp.9–10: full classical capacity of the fixed binary-input channel,
not a bosonic capacity optimized over arbitrary input alphabets or energies. -/
def binaryOperationalCapacity {I : Type} (W : Bit → OutputCoefficients I) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ≥0 // BinaryAchievableRate W R}, (R.val : ℝ≥0∞)

/-- PDF pp.6,9–10: polar attainment at a fixed rate by actual ensemble-error
families. One family is chosen before beta, with all tied polar choices allowed
by PolarRule. Theorem 6 separately quantifies every such family. -/
def PolarAchieves {I : Type} (W : Bit → OutputCoefficients I) (R : ℝ) : Prop :=
  ∃ A : (n : ℕ) → Finset (PolarWire n), (∀ n, PolarRule W n R (A n)) ∧
    ∀ beta : ℝ, beta < 1 / 2 →
      Asymptotics.IsLittleO atTop (fun n => ensembleError W n (A n)) (polarDecay beta (1 / 2))

/-! Sanity examples test definitions only; all source theorems remain admitted. -/

example {I : Type} (T : Hilbert I →L[ℂ] Hilbert I)
    (h : ∃ S : Hilbert I →L[ℂ] Hilbert I, S.IsPositive ∧ S.comp S = T) :
    (positiveBoundedRoot T).IsPositive ∧
      (positiveBoundedRoot T).comp (positiveBoundedRoot T) = T := by
  simpa only [positiveBoundedRoot, dif_pos h] using h.choose_spec

example {I : Type} : ¬ IsDensity (0 : OutputCoefficients I) := by
  simp [IsDensity, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass]

example {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) (i j : I) :
    cqOperatorCoefficients T i j = T (basisKet j) i := rfl

example {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) :
    ∀ i j, coefficientOperator (cqOperatorCoefficients T) (basisKet j) i = cqOperatorCoefficients T i j := by
  have h : ∃ S : Hilbert I →L[ℂ] Hilbert I,
      ∀ i j, S (basisKet j) i = cqOperatorCoefficients T i j := ⟨T, fun _ _ => rfl⟩
  simp only [coefficientOperator, dif_pos h]
  exact h.choose_spec

example {I : Type} : basisTrace (0 : Hilbert I →L[ℂ] Hilbert I) = 0 := by
  simp [basisTrace]

example {I : Type} : uniformMixture (fun _ : Bit => (0 : OutputCoefficients I)) = 0 := by
  simp [uniformMixture]

example {I : Type} (W : Bit → OutputCoefficients I) : squaredCqFidelity W = (cqRootFidelity W) ^ 2 := rfl

example : polarKernel 0 1 = 0 ∧ polarKernel 1 0 = 1 := by
  norm_num [polarKernel]

example : polarMatrix 0 = (fun _ _ => (1 : Bit)) := by
  funext r c
  simp [polarMatrix]

example {n : ℕ} (u : PolarWire n → Bit) : runEncoder [] u = u := rfl

example {n : ℕ} (a b : PolarWire n) (u : PolarWire n → Bit) :
    (EncodingGate.swap a b).apply u a = u b := by
  by_cases h : a = b
  · subst b; simp [EncodingGate.apply]
  · simp [EncodingGate.apply, h]

example {I : Type} (W : Bit → OutputCoefficients I) (x : Fin 0 → Bit) :
    wordOutput W x = fun _ _ => 1 := by
  funext a b
  simp [wordOutput]

example {n : ℕ} (i : PolarWire n)
    (h : Fin i.val → Bit) (v : PolarWire n → Bit) (b : Bit) : filledWord i h b v i = b := by
  simp [filledWord]

example {I : Type} (W : Bit → OutputCoefficients I) (b : Bit)
    (p q : Bit × (I × I)) (hpq : p.1 ≠ q.1) : channelPlus W b p q = 0 := by
  simp [channelPlus, hpq]

example {n : ℕ} (A : Finset (PolarWire n)) (m : InformationWord n A) (f : Frozen n A)
    (i : PolarWire n) (hi : i ∉ A) : cosetWord m f i = f ⟨i, hi⟩ := by
  simp [cosetWord, hi]

example (beta : ℝ) (n : ℕ) : polarDecay beta 0 n = 1 := by
  simp [polarDecay]

end QAlgorithms.Papers.Independent.Intakethird100.P14


